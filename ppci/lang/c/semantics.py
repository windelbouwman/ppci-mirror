""" Semantics handling for the C programming language.

This class is called whenever the parser has found something. So the interface
between parser and semantics is via a set of function calls.

What this module does:
- Type checking expressions
- Introduction of implicit casting
- Checking initializers for variable declarations

What this logic does not do:
- Evaluating constant values
- Evaluating enum values
- Evaluating sizeof expressions

The result of parser-semantic actions is a type-checked AST.

"""

import difflib
import logging
from .nodes import nodes, types, declarations, statements, expressions
from . import utils, init
from .scope import Scope, RootScope
from .printer import expr_to_str, type_to_str


class CSemantics:
    """ This class handles the C semantics """

    logger = logging.getLogger("semantics")

    def __init__(self, context):
        self.context = context
        self.scope = None
        self._root_scope = RootScope()

        # Define the type for a string:
        self.int_type = self.get_type(["int"])
        self.long_type = self.get_type(["long"])
        self.char_type = self.get_type(["char"])
        self.intptr_type = self.int_type.pointer_to()

        # Choose proper integer type for difference:
        if self.context.sizeof(self.int_type) == self.context.sizeof(
            self.intptr_type
        ):
            self.size_t_type = self.int_type
        else:
            # TODO: this might be 4 bytes on LP64 mode:
            self.size_t_type = self.long_type

        # Working variables:
        self.compounds = []
        self.switch_stack = []  # switch case levels

    def begin(self):
        """ Enter a new file / compilation unit. """
        self.scope = Scope()

    def finish_compilation_unit(self):
        """ Called at the end of a file / compilation unit. """
        assert self.scope.parent is None  # Must be the topscope now.
        declarations = self.scope.get_declarations()
        compilation_unit = nodes.CompilationUnit(declarations)
        return compilation_unit

    def enter_function(self, function):
        self.logger.debug(
            "Entering function %s %s:%s",
            function.name,
            function.location.filename,
            function.location.row,
        )
        # Nice clean slate:
        assert not self.switch_stack
        self.current_function = function
        self.enter_scope()

        # Define function parameters:
        for argument in function.typ.arguments:
            if argument.name:
                if self.scope.is_defined(argument.name, all_scopes=False):
                    self.error("Illegal redefine", argument.location)
                self.scope.insert(argument)

    def end_function(self, body):
        """ Called at the end of a function """
        # Pop scope and function
        self.leave_scope()
        function = self.current_function
        self.current_function = None

        if self.scope.is_definition(function.name):
            self.error("invalid redefinition", function.location)
        function.body = body
        assert not self.switch_stack

    def apply_type_modifiers(self, type_modifiers, typ):
        """ Apply the set of type modifiers to the given type """
        # Apply type modifiers in reversed order, starting outwards, going
        # from the outer type to the inside name.
        assert isinstance(typ, types.CType), str(typ)
        for modifier in reversed(type_modifiers):
            if modifier[0] == "POINTER":
                typ = typ.pointer_to()
                type_qualifiers = modifier[1]
                typ = self.on_type_qualifiers(type_qualifiers, typ)
            elif modifier[0] == "ARRAY":
                size = modifier[1]
                if size and size != "vla":
                    if not self._root_scope.is_const_expr(size):
                        self.error(
                            "Array dimension must be constant", size.location
                        )
                    size = self.coerce(size, self.get_type(["int"]))
                typ = types.ArrayType(typ, size)
            elif modifier[0] == "FUNCTION":
                arguments = modifier[1]
                # print(arguments)
                is_vararg = False
                if arguments and arguments[-1] == "...":
                    # Variadic function!
                    arguments = arguments[:-1]
                    is_vararg = True
                elif len(arguments) == 1 and arguments[0].typ.is_void:
                    # Special case 'int function1(void);'
                    arguments = []

                typ = types.FunctionType(arguments, typ, is_vararg=is_vararg)
            else:  # pragma: no cover
                raise NotImplementedError(str(modifier))
        assert isinstance(typ, types.CType), str(typ)
        return typ

    def on_function_argument(self, typ, name, modifiers, location):
        """ Process a function argument into the proper class """
        typ = self.apply_type_modifiers(modifiers, typ)

        # Change 'int a[]' into the equivalent int* a
        if typ.is_array:
            # TODO: figure out behavior of:
            # 'int a[10]' --> clang turns it into 'int* a'?
            typ = typ.decay()
        parameter = declarations.ParameterDeclaration(
            None, typ, name, location
        )
        return parameter

    def on_variable_declaration(
        self, storage_class, typ, name, modifiers, location
    ):
        """ Given a declaration, and a declarator, create the proper object """
        typ = self.apply_type_modifiers(modifiers, typ)
        if isinstance(typ, types.FunctionType):
            declaration = self.on_function_declaration(
                storage_class, typ, name, [], location
            )
        else:
            declaration = declarations.VariableDeclaration(
                storage_class, typ, name, None, location
            )

        return declaration

    # Variable initialization!
    def on_variable_initialization(self, variable, expression):
        """ Handle a variable initialized to some value """
        # This is a good point to determine array size and check
        # initial values
        assert isinstance(variable, declarations.VariableDeclaration)

        # Check double initializations
        if self.scope.is_definition(variable.name):
            self.error("Invalid redefinition.", variable.location)

        variable.typ = self.patch_size_from_initializer(
            variable.typ,
            expression
        )
        variable.initial_value = expression

    def patch_size_from_initializer(self, typ, initializer):
        """ Fill array type size from elements if the type size is unknown.
            Return a new type if modified 
        """
        if typ.is_array and typ.size is None:
            if isinstance(initializer, expressions.ArrayInitializer):
                new_type = types.ArrayType(
                    typ.element_type,
                    len(initializer.values)
                ) 
                initializer.typ = new_type
                return new_type
            else:  # pragma: no cover
                raise NotImplementedError(
                    "What else could be used to init an array?"
                )
        else:
            return typ

    def new_init_cursor(self):
        return init.InitCursor(self.context)

    def on_init_compound_enter(self, init_cursor, typ, location, implicit):
        self.logger.debug("Entering compound at cursor %s", init_cursor)
        if not typ.is_compound:
            self.error("Cannot init non-compound type", location)
        init_cursor.enter_compound(typ, location, implicit)
        return init_cursor

    def init_store(self, init_cursor, value):
        """ Store an initial value at position pointed by cursor. """

        if init_cursor.at_end():
            self.warning("Excess elements!", value.location)

        # Determine if we need implicit init levels:
        target_typ = init_cursor.at_typ()
        while not self.equal_types(value.typ, target_typ):
            # If we are at a complex type, implicit descend otherwise cast:
            if target_typ.is_compound:
                init_cursor.enter_compound(target_typ, value.location, True)
                target_typ = init_cursor.at_typ()
            else:
                value = self.pointer(value)
                value = self.coerce(value, target_typ)
                break

        self.logger.debug("Storing %s at cursor %s", value, init_cursor)

        # Retrieve current value to check overwrite:
        previous_value = init_cursor.get_value()
        if previous_value:
            self.warning(
                "This overwrites other initial value.", value.location
            )
            self.warning("previously defined here.", previous_value.location)
        init_cursor.set_value(value)

    def on_array_designator(self, init_cursor, index, location):
        """ Handle array designator. """
        # TODO: Handle things like [4..30] = 23
        # Calculate position:
        pos = self.context.eval_expr(index)

        # Array index must be positive:
        if pos < 0:
            self.error("Array desgnator must be positive", location)

        if not init_cursor.level.typ.is_array:
            self.error(
                "Cannot use array position designators in non-array", location
            )

        # Update current position:
        init_cursor.level.go_to_pos(pos)

    def on_field_designator(self, init_cursor, field_name, location):
        """ Check field designator. """
        typ = init_cursor.level.typ

        if not typ.is_struct_or_union:
            self.error(
                "Cannot use designator in non-struct/union type", location
            )

        if typ.has_field(field_name):
            init_cursor.select_field(field_name, location)
        else:
            self.error("No such field {}".format(field_name), location)

    # Declarations:
    def on_typedef(self, typ, name, modifiers, location):
        """ Handle typedef declaration """
        typ = self.apply_type_modifiers(modifiers, typ)
        declaration = declarations.Typedef(typ, name, location)
        if self.scope.is_defined(name, all_scopes=False):
            sym = self.scope.get_identifier(name)
            self.check_redeclaration_type(sym, declaration)
            sym.add_redeclaration(declaration)
        else:
            self.scope.insert(declaration)

    @property
    def in_compound(self):
        return bool(self.compounds)

    def on_function_declaration(
        self, storage_class, typ, name, modifiers, location
    ):
        """ Handle function declaration """
        typ = self.apply_type_modifiers(modifiers, typ)
        declaration = declarations.FunctionDeclaration(
            storage_class, typ, name, location
        )

        return declaration

    # declaration insertion into symbol table.
    def register_declaration(self, declaration):
        """ Register declaration into the scope. """
        # Check if the declared name is already defined:
        if self.scope.is_defined(declaration.name, all_scopes=False):
            # Get the already declared name and figure out what now!
            sym = self.scope.get_identifier(declaration.name)
            self.check_redeclaration_type(sym, declaration)

            # re-declarations are only allowed on top level
            if self.in_compound:
                self.invalid_redeclaration(sym, declaration)

            self.check_redeclaration_storage_class(sym, declaration)

            assert not declaration.is_definition()

            # Check initial value?

            # Redefine previous extern is OK!
            sym.add_redeclaration(declaration)
        else:
            # Insert into the current scope:
            self.scope.insert(declaration)

        if self.in_compound:
            statement = statements.DeclarationStatement(
                declaration, declaration.location
            )
            self.add_statement(statement)

    def check_redeclaration_type(self, sym, declaration):
        # The type should match in any case:
        if not self.equal_types(sym.typ, declaration.typ):
            self.invalid_redeclaration(sym, declaration)

        if not isinstance(declaration, type(sym.declaration)):
            self.invalid_redeclaration(sym, declaration)

    def check_redeclaration_storage_class(self, sym, declaration):
        """ Test if we specified an invalid combo of storage class. """
        prev_storage_class = sym.declaration.storage_class
        new_storage_class = declaration.storage_class
        # None == automatic storage class.
        was_static = prev_storage_class == "static"
        is_static = new_storage_class == "static"

        # Prevent change of static-ness after first declaration
        if is_static and not was_static:
            message = (
                "Invalid redefine of storage class. Was {}, but now {}".format(
                    prev_storage_class, new_storage_class
                )
            )
            self.invalid_redeclaration(sym, declaration, message)

        # update current declarations storage class
        if (
            not declaration.storage_class
            and prev_storage_class
            and prev_storage_class != "extern"
        ):
            declaration.storage_class = sym.declaration.storage_class

    def invalid_redeclaration(
        self, sym, declaration, message="Invalid redefinition"
    ):
        """ Raise an invalid redeclaration error. """
        hint = "First defined here %s" % sym.location
        self.logger.info(hint)
        self.error(message, declaration.location, hints=[hint])

    # Types!
    def on_basic_type(self, type_specifiers, location):
        """ Handle basic type """
        if self._root_scope.is_valid(type_specifiers):
            ctyp = self._root_scope.get_type(type_specifiers)
        else:
            self.error("Invalid type specifiers", location)
        return ctyp

    def on_typename(self, name, location):
        """ Handle the case when a typedef is refered """
        # Lookup typedef
        typedef = self.scope.get_identifier(name).declaration
        assert isinstance(typedef, declarations.Typedef)
        ctyp = typedef.typ
        return ctyp  # types.IdentifierType(name, ctyp)

    def on_type(self, typ, modifiers, location):
        """ Called when a type itself is described """
        return self.apply_type_modifiers(modifiers, typ)

    def on_struct_or_union(self, kind, tag, is_definition, fields, location):
        """Handle struct or union definition.

        A definition of a struct occurs when we have:
        struct S;
        struct S { int f; };
        struct { int f; };
        """
        # Layout the struct here!
        assert tag or fields is not None

        mp = {"struct": types.StructType, "union": types.UnionType}
        klass = mp[kind]

        if is_definition:
            # Struct definition.
            if tag:
                ctyp = self.define_tag_type(tag, klass, location)
            else:
                ctyp = klass()

            if fields is not None:
                ctyp.fields = fields
        else:
            assert tag
            # Struct usage / declaration:
            if self.scope.has_tag(tag, all_scopes=True):
                ctyp = self.scope.get_tag(tag, all_scopes=True)
                if not isinstance(ctyp, klass):
                    self.error("Wrong tag kind", location)
            else:
                ctyp = klass()
                self.scope.add_tag(tag, ctyp)

        return ctyp

    def on_field_def(
        self, storage_class, ctyp, name, modifiers, bitsize, location
    ):
        """ Handle a struct/union field declaration """
        ctyp = self.apply_type_modifiers(modifiers, ctyp)
        if bitsize is None:
            pass
        else:
            # Bit fields must be of integer type:
            if not ctyp.is_integer:
                self.error(
                    "Invalid type ({}) for bit-field".format(
                        type_to_str(ctyp)
                    ),
                    location,
                )

        field = types.Field(ctyp, name, bitsize)
        return field

    def on_enum(self, tag, is_definition, location):
        """ Handle enum declaration """
        if is_definition:
            if tag:
                ctyp = self.define_tag_type(tag, types.EnumType, location)
            else:
                ctyp = types.EnumType()
        else:
            assert tag
            if self.scope.has_tag(tag, all_scopes=True):
                ctyp = self.scope.get_tag(tag, all_scopes=True)
                if not isinstance(ctyp, types.EnumType):
                    self.error("This tag does not refer to an enum", location)
            else:
                ctyp = types.EnumType()
                self.scope.add_tag(tag, ctyp)
        return ctyp

    def on_enum_value(self, ctyp, name, value, location):
        """ Handle a single enum value definition """
        if value:
            if not self._root_scope.is_const_expr(value):
                self.error("Enum value must be constant value", value.location)
        declaration = declarations.EnumConstantDeclaration(
            ctyp, name, value, location
        )

        if self.scope.is_defined(name, all_scopes=False):
            sym = self.scope.get_identifier(declaration.name)
            self.invalid_redeclaration(sym, declaration)
        else:
            self.scope.insert(declaration)
        return declaration

    def exit_enum_values(self, ctyp, constants, location):
        if len(constants) == 0:
            self.error("Empty enum is not allowed", location)
        ctyp.constants = constants
        # TODO: determine min and max enum values
        # min(enum_values)
        # max(enum_values)
        # TODO: determine storage type!

    def define_tag_type(self, tag: str, klass: types.TaggedType, location):
        """ Get or create a tagged type with the given tag kind. """
        if self.scope.has_tag(tag, all_scopes=False):
            ctyp = self.scope.get_tag(tag, all_scopes=False)
            if not isinstance(ctyp, klass):
                self.error("Wrong tag kind", location)

            if ctyp.complete:
                self.error("Multiple definitions", location)

        else:
            ctyp = klass()
            self.scope.add_tag(tag, ctyp)
        return ctyp

    @staticmethod
    def on_type_qualifiers(type_qualifiers, ctyp):
        """ Handle type qualifiers """
        if type_qualifiers:
            ctyp.qualifiers = type_qualifiers
        return ctyp

    # Statements!
    @staticmethod
    def on_expression_statement(expression):
        return statements.ExpressionStatement(expression)

    @staticmethod
    def on_label(name, statement, location):
        return statements.Label(name, statement, location)

    def enter_scope(self):
        """ Enter a new symbol scope. """
        self.scope = Scope(self.scope)

    def leave_scope(self):
        """ Leave a symbol scope. """
        self.scope = self.scope.parent

    def enter_compound_statement(self, location):
        self.enter_scope()
        self.compounds.append([])

    def on_compound_statement(self, location):
        self.leave_scope()
        inner_statements = self.compounds.pop()
        return statements.Compound(inner_statements, location)

    def add_statement(self, statement):
        """ Helper to emit a statement into the current block. """
        self.compounds[-1].append(statement)

    def check_condition(self, condition):
        condition = self.pointer(condition)
        if not condition.typ.is_integer:
            condition = self.coerce(condition, self.get_type(["int"]))
        return condition

    def on_if(self, condition, then_statement, no, location):
        """ Check if statement """
        condition = self.check_condition(condition)
        return statements.If(condition, then_statement, no, location)

    def on_switch_enter(self, expression):
        self.switch_stack.append(expression.typ)

    def on_switch_exit(self, expression, statement, location):
        """ Handle switch statement """
        self.switch_stack.pop(-1)
        return statements.Switch(expression, statement, location)

    def on_case(self, value, statement, location):
        """ Handle a case statement """
        if not self.switch_stack:
            self.error("Case statement outside of a switch!", location)

        if isinstance(value, tuple):
            value1, value2 = value
            value1 = self.coerce(value1, self.switch_stack[-1])
            value2 = self.coerce(value2, self.switch_stack[-1])
            return statements.RangeCase(value1, value2, statement, location)
        else:
            value = self.coerce(value, self.switch_stack[-1])
            return statements.Case(value, statement, location)

    def on_default(self, statement, location):
        """ Handle a default label """
        if not self.switch_stack:
            self.error("Default statement outside of a switch!", location)

        return statements.Default(statement, location)

    def on_while(self, condition, body, location):
        """ Handle the while statement """
        condition = self.check_condition(condition)
        return statements.While(condition, body, location)

    def on_do(self, body, condition, location):
        """ The almost extinct dodo! """
        condition = self.check_condition(condition)
        return statements.DoWhile(body, condition, location)

    def on_for(self, initial, condition, post, body, location):
        """ Check for loop construction """
        if condition:
            condition = self.check_condition(condition)
        return statements.For(initial, condition, post, body, location)

    def on_return(self, value, location):
        """ Check return statement """
        return_type = self.current_function.typ.return_type
        if value:
            if return_type.is_void:
                self.error(
                    "Cannot return a value from this function", location
                )
            value = self.pointer(value)
            value = self.coerce(value, return_type)
        else:
            if not return_type.is_void:
                self.error("Must return a value from this function", location)
        return statements.Return(value, location)

    def on_asm(
        self, template, output_operands, input_operands, clobbers, location
    ):
        output_operands2 = []
        for constraint, asm_output_expr in output_operands:
            assert constraint == "=r"

            # Output must be l-value:
            if not asm_output_expr.lvalue:
                self.error("Expected lvalue", asm_output_expr.location)

            output_operands2.append((constraint, asm_output_expr))

        input_operands2 = []
        for constraint, asm_input_expr in input_operands:
            if constraint == "r":
                # TODO: how to determine what type to cast to?
                asm_input_expr = self.coerce(
                    asm_input_expr, self.get_type(["long"])
                )
            else:
                raise NotImplementedError(
                    "Inline asm constraint not implemented: {}".format(
                        constraint
                    )
                )
            input_operands2.append((constraint, asm_input_expr))

        clobbers2 = []
        for clobber_register_name in clobbers:
            if self.context.arch_info.has_register(clobber_register_name):
                clobber_register = self.context.arch_info.get_register(
                    clobber_register_name
                )
                clobbers2.append(clobber_register)
            else:
                self.error(
                    "target machine does not have register {}".format(
                        clobber_register_name
                    ),
                    location,
                )

        return statements.InlineAssemblyCode(
            template, output_operands2, input_operands2, clobbers2, location
        )

    # Expressions!
    def on_string(self, value, location):
        """ React on string literal """
        cstr_type = types.ArrayType(self.char_type, len(value) + 1)
        return expressions.StringLiteral(value, cstr_type, location)

    def on_number(self, value, location):
        """ React on integer numeric literal """
        # Get value from string:
        value, type_specifiers = utils.cnum(value)

        assert isinstance(value, int)
        if type_specifiers:
            typ = self.get_type(type_specifiers)
        else:
            # Use larger type to fit the value if required:
            # Try unsigned long,
            ulonglong_type = self.get_type(["unsigned", "long", "long"])
            longlong_type = self.get_type(["long", "long"])
            ulong_type = self.get_type(["unsigned", "long"])
            long_type = self.get_type(["long"])
            uint_type = self.get_type(["unsigned", "int"])

            if value <= self.context.limit_max(self.int_type):
                typ = self.int_type
            elif value <= self.context.limit_max(uint_type):
                typ = uint_type
            elif value <= self.context.limit_max(long_type):
                typ = long_type
            elif value <= self.context.limit_max(ulong_type):
                typ = ulong_type
            elif value <= self.context.limit_max(longlong_type):
                typ = longlong_type
            else:
                typ = ulonglong_type

        assert typ.is_integer
        # Check limits of integer
        # Note, an integer is always positive
        max_value = self.context.limit_max(typ)
        if value > max_value:
            self.error(
                "Integer value too big for type ({})".format(max_value),
                location,
            )
        return expressions.NumericLiteral(value, typ, location)

    def on_float(self, value, location):
        """ Process floating point literal. """
        value, type_specifiers = utils.float_num(value)
        typ = self.get_type(type_specifiers)
        return expressions.NumericLiteral(value, typ, location)

    def on_char(self, value, location):
        """ Process a character literal """
        # Get value from string:
        char_value, kind = utils.charval(value)
        typ = self.get_type(kind)
        return expressions.CharLiteral(char_value, typ, location)

    def on_ternop(self, lhs, op, mid, rhs, location):
        """ Handle ternary operator 'a ? b : c' """
        lhs = self.pointer(lhs)
        lhs = self.coerce(lhs, self.int_type)
        # TODO: For now, we use the common type of b and c as the result
        # But is this correct?
        mid = self.pointer(mid)
        rhs = self.pointer(rhs)
        common_type = self.get_common_type(mid.typ, rhs.typ, location)
        mid = self.coerce(mid, common_type)
        rhs = self.coerce(rhs, common_type)
        return expressions.TernaryOperator(
            lhs, op, mid, rhs, common_type, False, location
        )

    def on_binop(self, lhs, op, rhs, location):
        """ Check binary operator """
        lhs = self.pointer(lhs)
        rhs = self.pointer(rhs)

        if op in ["||", "&&"]:
            lhs = self.check_condition(lhs)
            rhs = self.check_condition(rhs)

            # Booleans are integer type:
            result_typ = self.int_type
        elif op in [
            "=",
            "+=",
            "-=",
            "*=",
            "%=",
            "/=",
            ">>=",
            "<<=",
            "&=",
            "|=",
            "~=",
            "^=",
        ]:
            # TODO: recurse twice (as '+' and as '=')?
            result_typ = lhs.typ
            if not lhs.lvalue:
                self.error("Expected lvalue", lhs.location)

            if op[0] in ["+", "-"] and lhs.typ.is_pointer:
                self.ensure_integer(rhs)
                lhs = self.ensure_no_void_ptr(lhs)
            rhs = self.coerce(rhs, result_typ)
        elif op == ",":
            result_typ = rhs.typ
        elif op == "+":
            # Handle pointer arithmatic
            if lhs.typ.is_pointer:
                # pointer + integer
                self.ensure_integer(rhs)
                lhs = self.ensure_no_void_ptr(lhs)
                result_typ = lhs.typ
            elif rhs.typ.is_pointer:
                # integer + pointer
                self.ensure_integer(lhs)
                rhs = self.ensure_no_void_ptr(rhs)
                result_typ = rhs.typ

                # Swap left and right to ease code generation:
                rhs, lhs = lhs, rhs
            else:
                # numeric + numeric
                lhs = self.promote(lhs)
                rhs = self.promote(rhs)

                result_typ = self.get_common_type(lhs.typ, rhs.typ, location)
                lhs = self.coerce(lhs, result_typ)
                rhs = self.coerce(rhs, result_typ)
        elif op == "-":
            # Handle pointer arithmatic:
            if lhs.typ.is_pointer:
                if rhs.typ.is_pointer:
                    # pointer - pointer
                    # operands must of compatible types and should
                    # not be void *
                    # result is a signed integer arge enough to contain
                    # pointer difference

                    # Ensure compatible pointer types:
                    lhs = self.ensure_no_void_ptr(lhs)
                    rhs = self.ensure_no_void_ptr(rhs)
                    if not self.equal_types(
                        lhs.typ.element_type, rhs.typ.element_type
                    ):
                        self.error(
                            "Operands must point to compatible types,"
                            " got {} and {}".format(
                                type_to_str(lhs.typ), type_to_str(rhs.typ)
                            ),
                            location,
                        )

                    result_typ = self.size_t_type

                else:
                    # pointer - integer
                    self.ensure_integer(rhs)
                    lhs = self.ensure_no_void_ptr(lhs)
                    result_typ = lhs.typ
            else:
                # numeric - numeric
                lhs = self.promote(lhs)
                rhs = self.promote(rhs)

                result_typ = self.get_common_type(lhs.typ, rhs.typ, location)
                lhs = self.coerce(lhs, result_typ)
                rhs = self.coerce(rhs, result_typ)
        elif op in ["<", ">", "==", "!=", "<=", ">="]:
            if not (lhs.typ.is_scalar or lhs.typ.is_pointer):
                self.error("Expected scalar or pointer", lhs.location)

            if not (rhs.typ.is_scalar or rhs.typ.is_pointer):
                self.error("Expected scalar or pointer", rhs.location)

            common_typ = self.get_common_type(lhs.typ, rhs.typ, location)
            lhs = self.coerce(lhs, common_typ)
            rhs = self.coerce(rhs, common_typ)

            # Booleans are integer type:
            result_typ = self.int_type
        elif op in ["<<", ">>", "|", "&", "^"]:  # Bit shifting operators
            self.ensure_integer(lhs)
            self.ensure_integer(rhs)

            lhs = self.promote(lhs)
            rhs = self.promote(rhs)

            result_typ = self.get_common_type(lhs.typ, rhs.typ, location)
            lhs = self.coerce(lhs, result_typ)
            rhs = self.coerce(rhs, result_typ)
        elif op in ["*", "/", "%"]:  # Multiplication operators
            if not lhs.typ.is_scalar:
                self.error("Expected scalar", lhs.location)

            if not rhs.typ.is_scalar:
                self.error("Expected scalar", rhs.location)

            lhs = self.promote(lhs)
            rhs = self.promote(rhs)

            result_typ = self.get_common_type(lhs.typ, rhs.typ, location)
            lhs = self.coerce(lhs, result_typ)
            rhs = self.coerce(rhs, result_typ)
        else:  # pragma: no cover
            raise NotImplementedError(op)

        return expressions.BinaryOperator(
            lhs, op, rhs, result_typ, False, location
        )

    def on_unop(self, op, a, location):
        """ Check unary operator semantics """
        if op in ["x++", "x--", "--x", "++x"]:
            # Increment and decrement in pre and post form
            if not a.lvalue:
                self.error("Expected lvalue", a.location)

            if not (a.typ.is_scalar or a.typ.is_pointer):
                self.error("Expected scalar or pointer", a.location)

            expr = expressions.UnaryOperator(op, a, a.typ, False, location)
        elif op == "-":
            a = self.pointer(a)
            expr = expressions.UnaryOperator(op, a, a.typ, False, location)
        elif op == "~":
            a = self.pointer(a)
            self.ensure_integer(a)
            expr = expressions.UnaryOperator(op, a, a.typ, False, location)
        elif op == "+":
            expr = self.pointer(a)
        elif op == "*":
            a = self.pointer(a)
            if not a.typ.is_pointer:
                self.error(
                    "Cannot dereference type {}".format(type_to_str(a.typ)),
                    a.location,
                )
            a = self.ensure_no_void_ptr(a)
            typ = a.typ.element_type
            expr = expressions.UnaryOperator(op, a, typ, True, location)
        elif op == "&":
            expr = self.on_take_address(a, location)
        elif op == "!":
            a = self.check_condition(a)
            expr = expressions.UnaryOperator(
                op, a, self.int_type, False, location
            )
        else:  # pragma: no cover
            raise NotImplementedError(str(op))
        return expr

    def on_take_address(self, a, location):
        if isinstance(a, expressions.VariableAccess) and isinstance(
            a.variable.declaration, declarations.FunctionDeclaration
        ):
            # Function pointer:
            expr = a
        else:
            # L-value access:
            if not a.lvalue:
                self.error("Expected lvalue", a.location)
            typ = a.typ.pointer_to()
            expr = expressions.UnaryOperator("&", a, typ, False, location)
        return expr

    def on_sizeof(self, typ, location):
        """ Handle sizeof contraption """
        expr = expressions.Sizeof(typ, self.size_t_type, False, location)
        return expr

    def on_cast(self, to_typ, casted_expr, location):
        """ Check explicit casting """
        return expressions.Cast(casted_expr, to_typ, False, location)

    def on_compound_literal(self, typ, init, location):
        """ Check the consistency of compound literals. """
        self.patch_size_from_initializer(typ, init)
        expr = expressions.CompoundLiteral(typ, init, location)
        return expr

    def on_array_index(self, base, index, location):
        """ Check array indexing """
        index = self.coerce(index, self.int_type)

        if not base.lvalue:
            # TODO: must array base be an lvalue?
            self.error("Expected lvalue", location)

        if not isinstance(base.typ, types.IndexableType):
            self.error(
                "Cannot index non array type {}".format(type_to_str(base.typ)),
                location,
            )

        typ = base.typ.element_type
        return expressions.ArrayIndex(base, index, typ, True, location)

    def on_field_select(self, base, field_name, location):
        """ Check field select expression """
        if not base.typ.is_struct_or_union:
            # Maybe we have a pointer to a struct?
            # If so, give a hint about this.
            hints = []
            if (
                base.typ.is_pointer
                and base.typ.element_type.is_struct_or_union
            ):
                lhs = expr_to_str(base)
                hints.append(
                    'Did you mean "{0}->{1}" instead of "{0}.{1}"?'.format(
                        lhs, field_name
                    )
                )
            self.error(
                "Selecting a field of non-struct type ({})".format(
                    type_to_str(base.typ)
                ),
                location,
                hints=hints,
            )

        if not base.lvalue:
            self.error("Expected lvalue", location)
        # TODO: handle qualifiers?

        if not self.context.has_field(base.typ, field_name):
            valid_field_names = base.typ.get_field_names()
            hint = "This type has those fields: {}".format(valid_field_names)
            self.error(
                "Field {} not part of struct".format(field_name),
                location,
                hints=[hint],
            )

        field = self.context.get_field(base.typ, field_name)
        expr = expressions.FieldSelect(base, field, field.typ, True, location)
        return expr

    def on_builtin_va_start(self, arg_pointer, location):
        """ Check va_start builtin function """
        if not self.equal_types(arg_pointer.typ, self.intptr_type):
            self.error("Invalid type for va_start", arg_pointer.location)
        if not arg_pointer.lvalue:
            self.error("Expected lvalue", arg_pointer.location)
        return expressions.BuiltInVaStart(arg_pointer, location)

    def on_builtin_va_arg(self, arg_pointer, typ, location):
        """ Check va_arg builtin function """
        if not self.equal_types(arg_pointer.typ, self.intptr_type):
            self.error("Invalid type for va_arg", arg_pointer.location)
        if not arg_pointer.lvalue:
            self.error("Expected lvalue", arg_pointer.location)
        return expressions.BuiltInVaArg(arg_pointer, typ, location)

    def on_builtin_va_copy(self, dest, src, location):
        """ Check va_copy builtin function """
        if not self.equal_types(dest.typ, self.intptr_type):
            self.error("Invalid type for va_copy", dest.location)
        if not dest.lvalue:
            self.error("Expected lvalue", dest.location)
        if not self.equal_types(src.typ, self.intptr_type):
            self.error("Invalid type for va_copy", src.location)
        return expressions.BuiltInVaCopy(dest, src, location)

    def on_builtin_offsetof(self, typ, member_name, location):
        """ Check offsetof builtin function """
        if not isinstance(typ, types.StructOrUnionType):
            self.error(
                "Can only apply offsetof on structs and unions", location
            )

        # Test if member is a member of the given type now?
        if not self.context.has_field(typ, member_name):
            self.error("Cannot find member {}".format(member_name), location)

        # Test if field is a bitfield:
        field = self.context.get_field(typ, member_name)
        if field.is_bitfield:
            self.error(
                'Attempt to take address of bit-field "{}"'.format(
                    member_name
                ),
                location,
            )

        return expressions.BuiltInOffsetOf(
            typ, member_name, self.int_type, location
        )

    def on_call(self, callee, arguments, location):
        """ Check function call for validity """
        callee = self.pointer(callee)
        if callee.typ.is_pointer and isinstance(
            callee.typ.element_type, types.FunctionType
        ):
            # Function pointer
            function_type = callee.typ.element_type
        else:
            self.error("Calling a non-function", location)

        # Check argument count:
        num_expected = len(function_type.argument_types)
        num_given = len(arguments)
        if function_type.is_vararg:
            if num_given < num_expected:
                self.error(
                    "Expected at least {} arguments, but got {}".format(
                        num_expected, num_given
                    ),
                    location,
                )
        else:
            if num_given != num_expected:
                self.error(
                    "Expected {} arguments, but got {}".format(
                        num_expected, num_given
                    ),
                    location,
                )

        # Check argument types:
        coerced_arguments = []
        for argument, argument_type in zip(
            arguments, function_type.argument_types
        ):
            argument = self.pointer(argument)
            argument = self.coerce(argument, argument_type)
            coerced_arguments.append(argument)

        # Append evetual variadic arguments:
        if num_given > num_expected:
            for argument in arguments[num_expected:]:
                argument = self.pointer(argument)
                argument = self.promote(argument)
                coerced_arguments.append(argument)

        # Determine lvalue. If we return a struct, we return an lvalue.
        # otherwise we have an rvalue.
        lvalue = function_type.return_type.is_struct

        expr = expressions.FunctionCall(
            callee,
            coerced_arguments,
            function_type.return_type,
            lvalue,
            location,
        )
        return expr

    def on_variable_access(self, name, location):
        """ Handle variable access """
        if not self.scope.is_defined(name):
            defined_names = self.scope.get_defined_names()
            suggestions = difflib.get_close_matches(name, defined_names)
            hints = []
            for suggestion in suggestions:
                hints.append(
                    '"{}" was not defined, did you mean "{}"?'.format(
                        name, suggestion
                    )
                )
            self.error(
                'Undeclared identifier: "{}"'.format(name),
                location,
                hints=hints,
            )
        symbol = self.scope.get_identifier(name)
        declaration = symbol.declaration
        typ = declaration.typ

        # Determine lvalue and type:
        if isinstance(declaration, declarations.VariableDeclaration):
            lvalue = True
        elif isinstance(declaration, declarations.EnumConstantDeclaration):
            lvalue = False
        elif isinstance(declaration, declarations.ParameterDeclaration):
            lvalue = True
        elif isinstance(declaration, declarations.FunctionDeclaration):
            lvalue = False
        else:  # pragma: no cover
            self.not_impl("Access to {}".format(declaration), location)

        expr = expressions.VariableAccess(symbol, typ, lvalue, location)
        return expr

    # Helpers!
    def coerce(self, expr: expressions.CExpression, typ: types.CType):
        """Try to fit the given expression into the given type."""
        assert isinstance(typ, types.CType)
        assert isinstance(expr, expressions.CExpression)

        do_cast = False
        from_type = expr.typ
        to_type = typ

        # TBD: in a ternary operator, void might be the result type.
        # if from_type.is_void:
        #     self.error(
        #         "Value expected but got 'void'", expr.location,
        #     )

        if self.equal_types(from_type, to_type):
            pass
        elif isinstance(
            from_type, (types.PointerType, types.EnumType)
        ) and isinstance(to_type, types.BasicType):
            do_cast = True
        elif from_type.is_pointer and to_type.is_pointer:
            do_cast = True
        elif isinstance(from_type, types.BasicType) and isinstance(
            to_type, types.IndexableType
        ):
            do_cast = True
        elif isinstance(
            from_type, (types.BasicType, types.EnumType)
        ) and isinstance(to_type, (types.BasicType, types.EnumType)):
            # TODO: implement stricter checks
            do_cast = True
        else:
            self.error(
                "Cannot convert {} to {}".format(from_type, to_type),
                expr.location,
            )

        if do_cast:
            expr = expressions.ImplicitCast(expr, typ, False, expr.location)
        return expr

    def pointer(self, expr):
        """Handle several conversions.

        Things handled:
        - Array to pointer decay.
        - Function to function pointer
        """
        if isinstance(expr.typ, types.ArrayType):
            typ = expr.typ.decay()
            conversion = expressions.ImplicitCast(
                expr, typ, False, expr.location
            )
        elif isinstance(expr.typ, types.FunctionType):
            typ = expr.typ.pointer_to()
            conversion = expressions.ImplicitCast(
                expr, typ, False, expr.location
            )
        else:
            conversion = expr
        return conversion

    def promote(self, expr):
        """Perform integer promotion on expression.

        Integer promotion happens when using char and short
        types in expressions. Those values are promoted
        to int type before performing the operation.
        """
        if expr.typ.is_promotable:
            expr = self.coerce(expr, self.int_type)
        return expr

    def equal_types(self, typ1, typ2):
        """ Compare two types for equality. """
        return self._root_scope.equal_types(typ1, typ2)

    def get_type(self, type_specifiers):
        """ Retrieve a type by type specifiers """
        return self._root_scope.get_type(type_specifiers)

    def ensure_integer(self, expr: expressions.CExpression):
        """ Ensure typ is of any integer type. """
        if not expr.typ.is_integer_or_enum:
            self.error(
                "integer or enum type expected but got {}".format(
                    type_to_str(expr.typ)
                ),
                expr.location,
            )

    def ensure_no_void_ptr(self, expr):
        """Test if expr has type void*, and if so, generate
        a warning and an implicit cast statement.
        """
        assert expr.typ.is_pointer
        if expr.typ.element_type.is_void:
            self.warning(
                "'void *' cannot be used, assuming 'char*'", expr.location
            )
            char_ptr = self.char_type.pointer_to()
            return expressions.ImplicitCast(
                expr, char_ptr, False, expr.location
            )
        else:
            return expr

    def get_common_type(self, typ1, typ2, location):
        """Given two types, determine the common type.

        The common type is a type they can both be cast to.
        """

        return max([typ1, typ2], key=lambda t: self._get_rank(t, location))

    basic_ranks = {
        types.BasicType.LONGDOUBLE: 110,
        types.BasicType.DOUBLE: 100,
        types.BasicType.FLOAT: 90,
        types.BasicType.ULONGLONG: 71,
        types.BasicType.LONGLONG: 70,
        types.BasicType.ULONG: 61,
        types.BasicType.LONG: 60,
        types.BasicType.UINT: 51,
        types.BasicType.INT: 50,
        types.BasicType.USHORT: 41,
        types.BasicType.SHORT: 40,
        types.BasicType.UCHAR: 31,
        types.BasicType.CHAR: 30,
        # TODO: is void rank-able? for now give it a low rank.
        types.BasicType.VOID: 0,
    }

    def _get_rank(self, typ, location):
        if isinstance(typ, types.BasicType):
            if typ.type_id in self.basic_ranks:
                return self.basic_ranks[typ.type_id]
            else:
                self.error(
                    "Cannot determine type rank for '{}'".format(
                        type_to_str(typ)
                    ),
                    location,
                )
        elif isinstance(typ, types.EnumType):
            return 80
        elif typ.is_pointer:
            return 83
        elif isinstance(typ, types.ArrayType):
            return 83
        else:
            self.error(
                "Cannot determine type rank for '{}'".format(type_to_str(typ)),
                location,
            )

    def error(self, message, location, hints=None):
        """ Trigger an error at the given location """
        self.context.error(message, location, hints=hints)

    def warning(self, message, location, hints=None):
        """ Trigger a warning at the given location """
        self.context.warning(message, location, hints=hints)

    def not_impl(self, message, location):  # pragma: no cover
        """ Call this function to mark unimplemented code """
        self.error(message, location)
        raise NotImplementedError(message)
