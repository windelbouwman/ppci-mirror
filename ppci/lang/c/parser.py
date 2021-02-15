""" C parsing logic.

The C parsing is implemented in a recursive descent parser.

The following parts can be distinguished:
- Declaration parsing: parsing types and declarations
- Statement parsing: dealing with the C statements, like for, if, etc..
- Expression parsing: parsing the C expressions.

Sources of inspiration:

- https://github.com/libfirm/cparser/blob/master/src/parser/parser.c
- https://github.com/gcc-mirror/gcc/blob/master/gcc/c/c-parser.c
- https://github.com/rui314/8cc/blob/master/parse.c

"""

import logging
from ..tools.recursivedescent import RecursiveDescentParser
from .nodes import statements, expressions
from .printer import type_to_str


LEFT_ASSOCIATIVE = "left-associative"
RIGHT_ASSOCIATIVE = "right-associative"


class CParser(RecursiveDescentParser):
    """C Parser.

    Implemented in a recursive descent way, like the CLANG[1]
    frontend for llvm, also without the lexer hack[2]. See for the gcc
    c parser code [3]. Also interesting is the libfim cparser frontend [4].

    The clang parser is very versatile, it can handle C, C++, objective C
    and also do code completion. This one is very simple, it can only
    parse C.

    [1] http://clang.org/
    [2] https://en.wikipedia.org/wiki/The_lexer_hack
    [3] https://raw.githubusercontent.com/gcc-mirror/gcc/master/gcc/c/
    c-parser.c

    [4] https://github.com/libfirm/cparser/blob/
    0cc43ed4bb4d475728583eadcf9e9726682a838b/src/parser/parser.c
    """

    logger = logging.getLogger("cparser")
    verbose = False

    def __init__(self, coptions, semantics):
        super().__init__()
        self.coptions = coptions
        self.semantics = semantics
        self.type_qualifiers = {"volatile", "const"}
        self.storage_classes = {
            "typedef",
            "static",
            "extern",
            "register",
            "auto",
        }
        self.type_specifiers = {
            "void",
            "char",
            "int",
            "float",
            "double",
            "short",
            "long",
            "signed",
            "unsigned",
        }

        self.keywords = {
            "true",
            "false",
            "else",
            "if",
            "while",
            "do",
            "for",
            "return",
            "goto",
            "switch",
            "case",
            "default",
            "break",
            "continue",
            "sizeof",
            "struct",
            "union",
            "enum",
            "asm",
            "__builtin_va_arg",
            "__builtin_va_start",
            "__builtin_va_copy",
            "__builtin_offsetof",
        }

        # gcc extensions:
        self.keywords.add("__attribute__")

        # Some additions from C99:
        if self.is_c99:
            self.type_qualifiers.add("restrict")
            self.keywords.add("inline")

        # Complete the set of keywords:
        self.keywords |= self.storage_classes
        self.keywords |= self.type_qualifiers
        self.keywords |= self.type_specifiers

        # Define a priority map for operators:
        # See also:
        # https://en.cppreference.com/w/cpp/language/operator_precedence
        self.prio_map = {
            ",": (LEFT_ASSOCIATIVE, 3),
            "=": (RIGHT_ASSOCIATIVE, 10),
            "+=": (RIGHT_ASSOCIATIVE, 10),
            "-=": (RIGHT_ASSOCIATIVE, 10),
            "*=": (RIGHT_ASSOCIATIVE, 10),
            "/=": (RIGHT_ASSOCIATIVE, 10),
            "%=": (RIGHT_ASSOCIATIVE, 10),
            ">>=": (RIGHT_ASSOCIATIVE, 10),
            "<<=": (RIGHT_ASSOCIATIVE, 10),
            "|=": (RIGHT_ASSOCIATIVE, 10),
            "&=": (RIGHT_ASSOCIATIVE, 10),
            "^=": (RIGHT_ASSOCIATIVE, 10),
            # '++': (LEFT_ASSOCIATIVE, 50),
            # '--': (LEFT_ASSOCIATIVE, 50),
            "?": (RIGHT_ASSOCIATIVE, 17),
            "||": (LEFT_ASSOCIATIVE, 20),
            "&&": (LEFT_ASSOCIATIVE, 30),
            "|": (LEFT_ASSOCIATIVE, 40),
            "^": (LEFT_ASSOCIATIVE, 50),
            "&": (LEFT_ASSOCIATIVE, 60),
            "<": (LEFT_ASSOCIATIVE, 70),
            "<=": (LEFT_ASSOCIATIVE, 70),
            ">": (LEFT_ASSOCIATIVE, 70),
            ">=": (LEFT_ASSOCIATIVE, 70),
            "!=": (LEFT_ASSOCIATIVE, 70),
            "==": (LEFT_ASSOCIATIVE, 70),
            ">>": (LEFT_ASSOCIATIVE, 80),
            "<<": (LEFT_ASSOCIATIVE, 80),
            "+": (LEFT_ASSOCIATIVE, 90),
            "-": (LEFT_ASSOCIATIVE, 90),
            "*": (LEFT_ASSOCIATIVE, 100),
            "/": (LEFT_ASSOCIATIVE, 100),
            "%": (LEFT_ASSOCIATIVE, 100),
        }

        # Set work variables:
        self.typedefs = set()

    def is_c99(self):
        return self.coptions["std"] == "c99"

    # Entry points:
    def parse(self, tokens):
        """Here the parsing of C is begun ...

        Parse the given tokens.
        """
        self.logger.debug("Parsing some nice C code!")
        self.init_lexer(tokens)
        self.typedefs = set()
        cu = self.parse_translation_unit()
        self.logger.info("Parsing finished")
        return cu

    def parse_translation_unit(self):
        """ Top level start of parsing """
        self.semantics.begin()
        while not self.at_end:
            self.parse_declarations()
        return self.semantics.finish_compilation_unit()

    # Declarations part:
    def parse_declarations(self):
        """ Parse normal declarations """
        decl_spec = self.parse_decl_specifiers()
        # TODO: perhaps not parse functions here?
        if not self.has_consumed(";"):
            self.parse_decl_group(decl_spec)

    def parse_decl_specifiers(self, allow_storage_class=True):
        """Parse declaration specifiers.

        At the end we know type, storage class and qualifiers.

        Gathers storage classes:
        - typedef
        - extern
        - static

        One of the following type specifiers:
        - void, char, int, unsigned, long, ...
        - typedef-ed type
        - struct, union or enum

        Type qualifiers:
        - const
        - volatile
        """

        storage_class = None
        type_specifiers = []
        type_qualifiers = set()
        typ = None
        attributes = []

        while True:
            if self.at_type_id():
                # We got a typedef type!
                if typ or type_specifiers:
                    break  # We already have a type.
                else:
                    type_name = self.consume()
                    typ = self.semantics.on_typename(
                        type_name.val, type_name.loc
                    )
            elif self.peek in self.type_specifiers:
                type_specifier = self.consume(self.type_specifiers)
                location = type_specifier.loc
                if typ:
                    self.error("Type already determined", type_specifier)
                else:
                    type_specifiers.append(type_specifier.val)
            elif self.peek == "enum":
                if typ or type_specifiers:
                    self.error("Unexpected enum")
                else:
                    typ = self.parse_enum()
            elif self.peek in ["struct", "union"]:
                if typ or type_specifiers:
                    self.error("Type already determined")
                else:
                    typ = self.parse_struct_or_union()
            elif self.peek in self.storage_classes:
                klass = self.consume(self.storage_classes)
                if not allow_storage_class:
                    self.error("Unexpected storage class", klass.loc)
                elif storage_class:
                    self.error("Multiple storage classes", klass.loc)
                else:
                    storage_class = klass.val
            elif self.peek in self.type_qualifiers:
                type_qualifier = self.consume(self.type_qualifiers)
                if type_qualifier.val in type_qualifiers:
                    self.error("Double type qualifier", type_qualifier.loc)
                else:
                    type_qualifiers.add(type_qualifier.val)
            elif self.peek in ["inline"]:
                self.consume("inline")
                # inline is a compiler hint. For now, ignore this hint :)
                self.logger.debug("Ignoring inline for now")
            elif self.peek in ["__attribute__"]:
                attributes = self.parse_attributes()
                self.logger.error("Ignoring %s", attributes)
            else:
                break

        # Now that we are here, the type must be determined
        if type_specifiers:
            if typ:
                self.error(
                    "Type specifiers {} given in addition to type '{}'".format(
                        type_specifiers, type_to_str(typ)
                    ),
                    location,
                )
            else:
                typ = self.semantics.on_basic_type(type_specifiers, location)

        if not typ:
            location = self.current_location
            typ = self.semantics.on_basic_type(["int"], location)
            self.logger.warning("No type given (%s), assuming int!", location)
            # self.error('Expected at least one type specifier')

        typ = self.semantics.on_type_qualifiers(type_qualifiers, typ)
        decl_spec = DeclSpec(storage_class, typ)
        return decl_spec

    def parse_struct_or_union(self):
        """ Parse a struct or union """
        keyword = self.consume({"struct", "union"})

        # We might have an optional tag:
        if self.peek == "ID":
            tag = self.consume("ID").val
        elif self.peek == "{":
            tag = None
        else:
            # print(self.typedefs)
            self.error(
                'Expected tag name or "{{", but got {}'.format(self.peek),
                keyword.loc,
            )

        is_definition = (self.peek == "{") or (
            (tag is not None) and self.peek == ";"
        )

        if self.peek == "{":
            fields = self.parse_struct_fields()
        else:
            fields = None

        return self.semantics.on_struct_or_union(
            keyword.val, tag, is_definition, fields, keyword.loc
        )

    def parse_struct_fields(self):
        """ Parse struct or union fields """
        # We have a struct declarations:
        self.consume("{")
        fields = []
        while self.peek != "}":
            decl_spec = self.parse_decl_specifiers(allow_storage_class=False)
            while True:
                type_modifiers, name = self.parse_type_modifiers(abstract=True)
                if name:
                    name, loc = name.val, name.loc
                else:
                    name = loc = None

                # Handle optional struct field size:
                if self.peek == ":":
                    self.consume(":")
                    bitsize = self.parse_constant_expression()
                else:
                    bitsize = None

                field = self.semantics.on_field_def(
                    decl_spec.storage_class,
                    decl_spec.typ,
                    name,
                    type_modifiers,
                    bitsize,
                    loc,
                )
                fields.append(field)
                if self.has_consumed(","):
                    continue
                else:
                    break
            self.consume(";")
        self.consume("}")
        return fields

    def parse_enum(self):
        """ Parse an enum definition """
        keyword = self.consume("enum")

        # We might have an optional tag:
        if self.peek == "ID":
            tag = self.consume("ID").val
        elif self.peek == "{":
            tag = None
        else:
            self.error(
                "Expected tag name or enum declaration, but got {}".format(
                    self.peek
                ),
                keyword.loc,
            )

        is_definition = (self.peek == "{") or (
            (tag is not None) and self.peek == ";"
        )

        ctyp = self.semantics.on_enum(tag, is_definition, keyword.loc)

        # If we have a body, either after tag or directly, parse it:
        if self.peek == "{":
            self.parse_enum_fields(ctyp, keyword.loc)

        return ctyp

    def parse_enum_fields(self, ctyp, location):
        """ Parse enum declarations """
        self.consume("{")
        constants = []
        while self.peek != "}":
            name = self.consume("ID")
            if self.has_consumed("="):
                value = self.parse_constant_expression()
            else:
                value = None
            constant = self.semantics.on_enum_value(
                ctyp, name.val, value, name.loc
            )
            constants.append(constant)
            if not self.has_consumed(","):
                break
        self.consume("}")
        self.semantics.exit_enum_values(ctyp, constants, location)

    def parse_attributes(self):
        """Parse some attributes.

        Examples are:

        __attribute__((noreturn))
        """
        attributes = []
        while True:
            if self.peek == "__attribute__":
                attribute = self.parse_gnu_attribute()
            else:
                break
            attributes.append(attribute)
        return attributes

    def parse_gnu_attribute(self):
        """ Parse a gnu attribute like __attribute__((noreturn)) """
        self.consume("__attribute__")
        self.consume("(")
        self.consume("(")
        gnu_attribute = {}
        if self.peek != ")":
            while True:
                name = self.consume("ID")
                # TODO: how use this?
                gnu_attribute[name.val] = 1
                if self.has_consumed(","):
                    continue
                else:
                    break
        self.consume(")")
        self.consume(")")
        return gnu_attribute

    def parse_decl_group(self, decl_spec):
        """Parse the rest after the first declaration spec.

        For example we have parsed 'static int' and we will now parse the rest.
        This can be either a function, or a sequence of initializable
        variables. At least it will probably contain some sort of
        identifier and an optional pointer stuff.
        """
        declarator = self.parse_declarator()
        if decl_spec.storage_class == "typedef":
            self.parse_typedef(decl_spec, declarator)
            while self.has_consumed(","):
                declarator = self.parse_declarator()
                self.parse_typedef(decl_spec, declarator)
            self.consume(";")
        elif self.peek == "{":
            # if function, parse implementation.
            # func_def = None
            self.parse_function_declaration(decl_spec, declarator)
        else:
            # We have variables here
            self.parse_variable_declaration(decl_spec, declarator)
            while self.has_consumed(","):
                declarator = self.parse_declarator()
                self.parse_variable_declaration(decl_spec, declarator)
            self.consume(";")

    def parse_function_declaration(self, decl_spec, declarator):
        """ Parse a function declaration with implementation """
        function = self.semantics.on_function_declaration(
            decl_spec.storage_class,
            decl_spec.typ,
            declarator.name,
            declarator.type_modifiers,
            declarator.location,
        )
        self.semantics.register_declaration(function)
        self.semantics.enter_function(function)
        body = self.parse_compound_statement()
        self.semantics.end_function(body)

    def parse_variable_declaration(self, decl_spec, declarator):
        """ Parse variable declaration optionally followed by initializer. """
        # Create the variable:
        variable = self.semantics.on_variable_declaration(
            decl_spec.storage_class,
            decl_spec.typ,
            declarator.name,
            declarator.type_modifiers,
            declarator.location,
        )

        self.semantics.register_declaration(variable)

        # Handle the initial value:
        if self.has_consumed("="):
            initializer = self.parse_initializer(variable.typ)
            self.semantics.on_variable_initialization(variable, initializer)

    def parse_typedef(self, decl_spec, declarator):
        """ Process typedefs """
        self.typedefs.add(declarator.name)
        self.semantics.on_typedef(
            decl_spec.typ,
            declarator.name,
            declarator.type_modifiers,
            declarator.location,
        )

    def parse_declarator(self, abstract=False):
        """Given a declaration specifier, parse the rest.

        This involves parsing optionally pointers and qualifiers
        and next the declaration itself.
        """

        type_modifiers, name = self.parse_type_modifiers(abstract=abstract)
        if name:
            name, location = name.val, name.loc
        else:
            name = location = None

        # Handle typedefs:
        # if decl_spec.storage_class == 'typedef':
        #    assert name is not None
        #    self.typedefs.add(name)
        return Declarator(name, type_modifiers, location)

    # Initialization section:
    def parse_initializer(self, typ):
        """Parse the C-style array or struct initializer stuff.

        Heavily copied from: https://github.com/rui314/8cc/blob/master/parse.c

        Argument is the type to initialize.

        An initialization can be one of:
        = 1;
        = {1, 2, 3};
        = {[0] = 3};  // C99
        = {.foobar = {23, 3}}; // C99
        = {[2..5] = 2}; // C99
        """
        if self.peek == "{":
            initializer = self.parse_initializer_list(typ)
        elif typ.is_char_array and self.peek == "STRING":
            initializer = self.parse_array_string_initializer(typ)
        else:
            expr = self.parse_constant_expression()
            expr = self.semantics.pointer(expr)
            initializer = self.semantics.coerce(expr, typ)

        return initializer

    def parse_array_string_initializer(self, typ):
        """Handle the special case where an array is initialized with
        a string.
        """
        # isinstance(initializer, expressions.StringLiteral):
        string = self.consume("STRING")
        # Turn into sequence of characters:
        il = []
        location = string.loc
        for c in string.val:
            il.append(
                expressions.CharLiteral(
                    ord(c), self.semantics.char_type, location
                )
            )
        il.append(
            expressions.CharLiteral(0, self.semantics.char_type, location)
        )
        initializer = expressions.ArrayInitializer(typ, il, location)
        return initializer

    def parse_initializer_list(self, typ):
        """Parse braced initializer list.

        Parse opening brace, elements and closing brace.
        """

        init_cursor = self.semantics.new_init_cursor()
        return self.parse_initializer_list_sub(init_cursor, typ)

    def parse_initializer_list_sub(self, init_cursor, typ):
        """Parse braced initializer list.

        Parse opening brace, elements and closing brace.
        """
        location = self.consume("{").loc
        self.semantics.on_init_compound_enter(
            init_cursor, typ, location, False
        )

        # TODO: an initializer list must not be empty, or can it be empty?
        # TBD: this might depend upon an option / gcc behavior
        while self.peek != "}":
            self.parse_initializer_list_element(init_cursor)

            if not self.has_consumed(","):
                break

        self.consume("}")
        init_cursor.unwind()
        return init_cursor.leave_compound()

    def parse_initializer_list_element(self, init_cursor):
        """Parse an initializer list element with optional designators."""
        # Load eventual designators:
        if self.is_c99 and self.peek in [".", "["]:
            # We face designated initializer here...
            designators = True
            # Retreat to top-level!
            init_cursor.unwind()
            while self.peek in [".", "["]:
                # Select proper location:
                if self.peek == "[":
                    location = self.parse_array_designator(init_cursor)
                else:
                    location = self.parse_struct_designator(init_cursor)

                # Maybe we require to descend if we face more designators:
                if self.peek in [".", "["]:
                    typ = init_cursor.at_typ()
                    self.semantics.on_init_compound_enter(
                        init_cursor, typ, location, True
                    )

            self.consume("=")
        else:
            designators = False

        # Parse actual initializer.
        typ = init_cursor.level.element_typ()
        if self.peek == "{":
            initializer = self.parse_initializer_list_sub(init_cursor, typ)
        else:
            initializer = self.parse_constant_expression()
            self.semantics.init_store(init_cursor, initializer)

        # Pop designators:
        if designators:
            init_cursor.unwind()

        # Go to next element:
        init_cursor.next_element()

    def parse_array_designator(self, init_cursor):
        """ Parse array designator like '{2, [10]=4}' """
        location = self.consume("[").loc
        index = self.parse_constant_expression()
        self.consume("]")
        self.semantics.on_array_designator(init_cursor, index, location)
        return location

    def parse_struct_designator(self, init_cursor):
        """ Parse a struct designator in an initializer list. """
        location = self.consume(".").loc
        field = self.consume("ID")
        field_name = field.val
        self.semantics.on_field_designator(init_cursor, field_name, location)
        return location

    def skip_initializer_lists(self):
        """ Skip superfluous initial values. """
        while self.peek != "}":
            self.next_token()

    # Types section:
    def parse_function_arguments(self):
        """Parse function postfix.

        We have type and name, now parse function arguments.
        """
        # TODO: allow K&R style arguments
        arguments = []
        # self.consume('(')
        if self.peek != ")":
            while True:
                if self.peek == "...":
                    # Variable arguments found!
                    self.consume("...")
                    arguments.append("...")
                    break
                else:
                    decl_spec = self.parse_decl_specifiers()
                    d = self.parse_declarator(abstract=True)
                    arg = self.semantics.on_function_argument(
                        decl_spec.typ, d.name, d.type_modifiers, d.location
                    )
                    arguments.append(arg)
                    if not self.has_consumed(","):
                        break
        # self.consume(')')
        return arguments

    def parse_type_modifiers(self, abstract=False):
        """Parse the pointer, name and array or function suffixes.

        Can be abstract type, and if so, the type may be nameless.

        The result of all this action is a type modifier list with
        the proper type modifications required by the given code.
        """

        first_modifiers = []
        # Handle the pointer:
        while self.has_consumed("*"):
            type_qualifiers = set()
            while self.peek in self.type_qualifiers:
                type_qualifier = self.consume(self.type_qualifiers)
                if type_qualifier.val in type_qualifiers:
                    self.error("Duplicate type qualifier", type_qualifier)
                else:
                    type_qualifiers.add(type_qualifier.val)
            first_modifiers.append(("POINTER", type_qualifiers))

        # First parse some id, or something else
        middle_modifiers = []
        last_modifiers = []  # TODO: maybe move id detection in seperate part?
        if self.peek == "ID":
            name = self.consume("ID")
        elif self.peek == "(":
            # May be pointer to function?
            self.consume("(")
            if self.is_declaration_statement():
                # we are faced with function arguments
                arguments = self.parse_function_arguments()
                last_modifiers.append(("FUNCTION", arguments))
                name = None
            else:
                # These are grouped type modifiers.
                sub_modifiers, name = self.parse_type_modifiers(
                    abstract=abstract
                )
                middle_modifiers.extend(sub_modifiers)
            self.consume(")")
        else:
            if abstract:
                name = None
            else:
                self.error("Expected a name")
            # self.not_impl()
            # raise NotImplementedError(str(self.peek))

        # Now we have name, check for function decl:
        while True:
            if self.peek == "(":
                self.consume("(")
                arguments = self.parse_function_arguments()
                self.consume(")")
                last_modifiers.append(("FUNCTION", arguments))
            elif self.peek == "[":
                # Handle array type suffix:
                self.consume("[")
                if self.peek == "*":
                    # Handle VLA arrays:
                    amount = "vla"
                elif self.peek == "]":
                    amount = None
                else:
                    amount = self.parse_expression()
                self.consume("]")
                last_modifiers.append(("ARRAY", amount))
            else:
                break

        # Type modifiers: `go right when you can, go left when you must`
        first_modifiers.reverse()
        type_modifiers = middle_modifiers + last_modifiers + first_modifiers
        return type_modifiers, name

    def parse_typename(self):
        """ Parse a type specifier used in sizeof(int) for example. """
        decl_spec = self.parse_decl_specifiers(allow_storage_class=False)
        assert not decl_spec.storage_class
        type_modifiers, name = self.parse_type_modifiers(abstract=True)
        if name:
            self.error("Unexpected name for type declaration", name)
        location = self.current_location
        return self.semantics.on_type(decl_spec.typ, type_modifiers, location)

    # Statement part:
    def parse_statement_or_declaration(self):
        """Parse either a statement or a declaration

        Returns: a list of statements
        """

        if self.is_declaration_statement():
            self.parse_declarations()
        else:
            self.semantics.add_statement(self.parse_statement())

    def is_declaration_statement(self):
        """ Determine whether we are facing a declaration or not """
        if self.peek in self.storage_classes:
            return True
        elif self.peek in self.type_qualifiers:
            return True
        elif self.peek in self.type_specifiers:
            return True
        elif self.peek in ("struct", "union", "enum"):
            return True
        elif self.peek == "ID":
            if self.look_ahead(1).val == ":":
                # We face a label here.
                return False
            else:
                return self.at_type_id()
        else:
            return False

    def parse_statement(self):
        """ Parse a statement """
        m = {
            "for": self.parse_for_statement,
            "if": self.parse_if_statement,
            "do": self.parse_do_statement,
            "while": self.parse_while_statement,
            "switch": self.parse_switch_statement,
            "case": self.parse_case_statement,
            "default": self.parse_default_statement,
            "break": self.parse_break_statement,
            "continue": self.parse_continue_statement,
            "goto": self.parse_goto_statement,
            "return": self.parse_return_statement,
            "asm": self.parse_asm_statement,
            "{": self.parse_compound_statement,
            ";": self.parse_empty_statement,
        }
        if self.peek in m:
            statement = m[self.peek]()
        elif self.peek == "ID" and self.look_ahead(1).val == ":":
            statement = self.parse_label()
        else:
            # Expression statement!
            expression = self.parse_expression()
            statement = self.semantics.on_expression_statement(expression)
            self.consume(";")
        return statement

    def parse_label(self):
        """ Parse a label statement """
        name = self.consume("ID")
        self.consume(":")
        statement = self.parse_statement()
        return self.semantics.on_label(name.val, statement, name.loc)

    def parse_empty_statement(self):
        """ Parse a statement that does nothing! """
        location = self.consume(";").loc
        return statements.Empty(location)

    def parse_compound_statement(self):
        """ Parse a series of statements surrounded by '{' and '}' """
        location = self.consume("{").loc
        self.semantics.enter_compound_statement(location)
        while self.peek != "}":
            self.parse_statement_or_declaration()
        self.consume("}")
        return self.semantics.on_compound_statement(location)

    def parse_if_statement(self):
        """ Parse an if statement """
        location = self.consume("if").loc
        condition = self.parse_condition()
        then_statement = self.parse_statement()
        if self.has_consumed("else"):
            else_statement = self.parse_statement()
        else:
            else_statement = None
        return self.semantics.on_if(
            condition, then_statement, else_statement, location
        )

    def parse_switch_statement(self):
        """ Parse an switch statement """
        location = self.consume("switch").loc
        self.consume("(")
        expression = self.parse_expression()
        self.consume(")")
        # expression type can be changed by integer promotion
        prom_expression = self.semantics.on_switch_enter(expression)
        statement = self.parse_statement()
        return self.semantics.on_switch_exit(prom_expression, statement, location)

    def parse_case_statement(self):
        """Parse a case.

        For example:
        'case 5:'

        Or, a gnu extension:

        'case 5 ... 10:'
        """
        location = self.consume("case").loc
        value = self.parse_constant_expression()
        if self.peek == "...":
            # gnu extension!
            self.consume("...")
            value2 = self.parse_constant_expression()
            value = (value, value2)

        self.consume(":")
        statement = self.parse_statement()
        return self.semantics.on_case(value, statement, location)

    def parse_default_statement(self):
        """ Parse the default case """
        location = self.consume("default").loc
        self.consume(":")
        statement = self.parse_statement()
        return self.semantics.on_default(statement, location)

    def parse_break_statement(self):
        """ Parse a break """
        location = self.consume("break").loc
        self.consume(";")
        return statements.Break(location)

    def parse_continue_statement(self):
        """ Parse a continue statement """
        location = self.consume("continue").loc
        self.consume(";")
        return statements.Continue(location)

    def parse_goto_statement(self):
        """ Parse a goto """
        location = self.consume("goto").loc
        label = self.consume("ID").val
        self.consume(";")
        return statements.Goto(label, location)

    def parse_while_statement(self):
        """ Parse a while statement """
        location = self.consume("while").loc
        condition = self.parse_condition()
        body = self.parse_statement()
        return self.semantics.on_while(condition, body, location)

    def parse_do_statement(self):
        """ Parse a do-while statement """
        location = self.consume("do").loc
        body = self.parse_statement()
        self.consume("while")
        condition = self.parse_condition()
        self.consume(";")
        return self.semantics.on_do(body, condition, location)

    def parse_for_statement(self):
        """ Parse a for statement """
        location = self.consume("for").loc
        self.semantics.enter_scope()  # for loops have their own scope.
        self.consume("(")
        if self.peek == ";":
            initial = None
        else:
            if self.is_declaration_statement():
                # C99 only, declaration inside for-loop!
                decl_spec = self.parse_decl_specifiers()
                declaration = self.parse_declarator()
                variable_declaration = self.parse_variable_declaration(
                    decl_spec, declaration
                )
                initial = variable_declaration
            else:
                initial = self.parse_expression()
        self.consume(";")

        if self.peek == ";":
            condition = None
        else:
            condition = self.parse_expression()
        self.consume(";")

        if self.peek == ")":
            post = None
        else:
            post = self.parse_expression()
        self.consume(")")

        body = self.parse_statement()
        self.semantics.leave_scope()
        return self.semantics.on_for(initial, condition, post, body, location)

    def parse_return_statement(self):
        """ Parse a return statement """
        location = self.consume("return").loc
        if self.peek == ";":
            value = None
        else:
            value = self.parse_expression()
        self.consume(";")
        return self.semantics.on_return(value, location)

    # Inline assembly section!
    def parse_asm_statement(self):
        """Parse an inline assembly statement.

        See also: https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html
        """
        location = self.consume("asm").loc
        valid_qualifiers = ["volatile", "inline", "goto"]
        # while self.peek in
        # TODO qualifiers
        self.consume("(")
        template = self.parse_string()

        output_operands = self.parse_asm_operands()
        input_operands = self.parse_asm_operands()
        clobbers = self.parse_clobbers()

        self.consume(")")
        return self.semantics.on_asm(
            template, output_operands, input_operands, clobbers, location
        )

    def parse_asm_operands(self):
        """ Parse a series of assembly operands. Empty list is allowed. """
        operands = []
        if self.has_consumed(":"):
            if self.peek not in [")", ":"]:
                operand = self.parse_asm_operand()
                operands.append(operand)
                while self.has_consumed(","):
                    operand = self.parse_asm_operand()
                    operands.append(operand)
        return operands

    def parse_asm_operand(self):
        """ Parse a single asm operand. """
        constraint = self.parse_string()
        self.consume("(")
        variable = self.parse_expression()
        self.consume(")")
        return (constraint, variable)

    def parse_clobbers(self):
        clobbers = []
        if self.has_consumed(":"):
            if self.peek != ")":
                clobber = self.parse_string()
                clobbers.append(clobber)
                while self.has_consumed(","):
                    clobber = self.parse_string()
                    clobbers.append(clobber)
        return clobbers

    # Expression parts:
    def parse_condition(self):
        """ Parse an expression between parenthesis """
        self.consume("(")
        condition = self.parse_expression()
        self.consume(")")
        return condition

    def parse_constant_expression(self):
        """ Parse a constant expression """
        return self.parse_binop_with_precedence(17)

    def parse_assignment_expression(self):
        return self.parse_binop_with_precedence(10)

    def parse_expression(self):
        """Parse an expression.

        See also: http://en.cppreference.com/w/c/language/operator_precedence
        """
        return self.parse_binop_with_precedence(0)

    def _binop_take(self, op, priority):
        """Decide whether to group.

        This is a helper function that determines whether or not to group
        a certain operator further, given the current priority.
        """
        # TODO: rename this function
        if op not in self.prio_map:
            return False

        op_associativity, op_prio = self.prio_map[op]
        if op_associativity == LEFT_ASSOCIATIVE:
            return op_prio > priority
        else:
            return op_prio >= priority

    def parse_binop_with_precedence(self, priority):
        lhs = self.parse_primary_expression()

        # print('prio=', prio, self.peek)
        while self._binop_take(self.peek, priority):
            op = self.consume()
            op_prio = self.prio_map[op.val][1]
            if op.val == "?":
                # Eat middle part:
                middle = self.parse_expression()
                self.consume(":")
                rhs = self.parse_binop_with_precedence(op_prio)
                lhs = self.semantics.on_ternop(
                    lhs, op.val, middle, rhs, op.loc
                )
            else:
                rhs = self.parse_binop_with_precedence(op_prio)
                lhs = self.semantics.on_binop(lhs, op.val, rhs, op.loc)
        return lhs

    def parse_primary_expression(self):
        """ Parse a primary expression """
        if self.peek == "ID":
            identifier = self.consume("ID")
            expr = self.semantics.on_variable_access(
                identifier.val, identifier.loc
            )
        elif self.peek == "NUMBER":
            number = self.consume()
            expr = self.semantics.on_number(number.val, number.loc)
        elif self.peek == "FLOAT":
            number = self.consume()
            expr = self.semantics.on_float(number.val, number.loc)
        elif self.peek == "CHAR":
            char = self.consume()
            expr = self.semantics.on_char(char.val, char.loc)
        elif self.peek == "STRING":
            txt = self.consume()
            expr = self.semantics.on_string(txt.val, txt.loc)
        elif self.peek in ["!", "*", "+", "-", "~", "&", "--", "++"]:
            op = self.consume()
            if op.val in ["--", "++"]:
                operator = op.val + "x"
            else:
                operator = op.val
            expr = self.parse_primary_expression()
            expr = self.semantics.on_unop(operator, expr, op.loc)
        elif self.peek == "__builtin_va_start":
            location = self.consume("__builtin_va_start").loc
            self.consume("(")
            ap = self.parse_assignment_expression()
            self.consume(")")
            expr = self.semantics.on_builtin_va_start(ap, location)
        elif self.peek == "__builtin_va_arg":
            location = self.consume("__builtin_va_arg").loc
            self.consume("(")
            ap = self.parse_assignment_expression()
            self.consume(",")
            typ = self.parse_typename()
            self.consume(")")
            expr = self.semantics.on_builtin_va_arg(ap, typ, location)
        elif self.peek == "__builtin_va_copy":
            location = self.consume("__builtin_va_copy").loc
            self.consume("(")
            dest = self.parse_assignment_expression()
            self.consume(",")
            src = self.parse_assignment_expression()
            self.consume(")")
            expr = self.semantics.on_builtin_va_copy(dest, src, location)
        elif self.peek == "__builtin_offsetof":
            location = self.consume("__builtin_offsetof").loc
            self.consume("(")
            typ = self.parse_typename()
            self.consume(",")
            member = self.consume("ID").val
            self.consume(")")
            expr = self.semantics.on_builtin_offsetof(typ, member, location)
        elif self.peek == "sizeof":
            location = self.consume("sizeof").loc
            if self.peek == "(":
                self.consume("(")
                if self.is_declaration_statement():
                    typ = self.parse_typename()
                else:
                    typ = self.parse_expression()
                self.consume(")")
                expr = self.semantics.on_sizeof(typ, location)
            else:
                sizeof_expr = self.parse_primary_expression()
                expr = self.semantics.on_sizeof(sizeof_expr, location)
        elif self.peek == "(":
            loc = self.consume("(").loc
            # Is this a type cast?
            if self.is_declaration_statement():
                # Cast or compound literal!
                to_typ = self.parse_typename()
                self.consume(")")
                if self.peek == "{":
                    init = self.parse_initializer_list(to_typ)
                    expr = self.semantics.on_compound_literal(
                        to_typ, init, loc
                    )
                else:
                    casted_expr = self.parse_primary_expression()
                    expr = self.semantics.on_cast(to_typ, casted_expr, loc)
            else:
                # Parenthized expression (reset precedence)
                expr = self.parse_expression()
                self.consume(")")
        else:
            self.error("Expected expression")

        # Postfix operations (have the highest precedence):
        while self.peek in ["--", "++", "[", ".", "->", "("]:
            if self.peek in ["--", "++"]:
                op = self.consume()
                expr = self.semantics.on_unop("x" + op.val, expr, op.loc)
            elif self.peek == "[":
                location = self.consume("[").loc
                index = self.parse_expression()
                self.consume("]")
                expr = self.semantics.on_array_index(expr, index, location)
            elif self.peek == "(":
                expr = self.parse_call(expr)
            elif self.peek == ".":
                location = self.consume(".").loc
                field = self.consume("ID").val
                expr = self.semantics.on_field_select(expr, field, location)
            elif self.peek == "->":
                location = self.consume("->").loc
                field = self.consume("ID").val
                # Dereference pointer:
                expr = self.semantics.on_unop("*", expr, location)
                expr = self.semantics.on_field_select(expr, field, location)
            else:  # pragma: no cover
                self.not_impl()
        return expr

    def parse_call(self, callee):
        """ Parse a function call """
        location = self.consume("(").loc
        args = []
        while self.peek != ")":
            args.append(self.parse_assignment_expression())
            if self.peek != ")":
                self.consume(",")
        expr = self.semantics.on_call(callee, args, location)
        self.consume(")")
        return expr

    # Lexer helpers:
    def next_token(self):
        """ Advance to the next token """
        tok = super().next_token()
        if self.verbose:  # pragma: no cover
            self.logger.debug("Token: %s", tok)
        return tok

    def at_type_id(self):
        """ Check if the upcoming token is a typedef identifier """
        # Implement lexer hack here:
        if self.token:
            # Also implement lexer hack here:
            if self.token.typ == "ID" and self.token.val in self.typedefs:
                return True
        return False

    def parse_string(self):
        return self.consume("STRING").val


class DeclSpec:
    """ Contains a type and a set of modifiers """

    def __init__(self, storage_class, typ):
        self.storage_class = storage_class
        self.typ = typ  # The later determined type!

    def __repr__(self):
        return "[decl-spec storage={}, type={}]".format(
            self.storage_class, self.typ
        )


class Declarator:
    def __init__(self, name, type_modifiers, location):
        self.name = name
        self.type_modifiers = type_modifiers
        self.location = location
