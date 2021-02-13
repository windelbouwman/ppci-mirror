from collections import namedtuple
import logging
from ..tools.recursivedescent import RecursiveDescentParser
from . import nodes


class LlvmIrParser(RecursiveDescentParser):
    """Recursive descent parser for llvm-ir

    Closely modeled after LLParser.cpp at:
    https://github.com/llvm-mirror/llvm/blob/master/lib/AsmParser/LLParser.cpp
    """

    logger = logging.getLogger("llvm-parse")

    def __init__(self, context):
        super().__init__()
        self.context = context
        self._pfs = None
        self.module = None
        # Counter to form implicit names.
        self.numbered_val = 0

    # LLVM IR has a habbit of using implicit names in various places, from
    # function params to block labels. In this case, a "numbered name" is
    # used.
    def get_implicit_name(self):
        name = "%{}".format(self.numbered_val)
        self.numbered_val += 1
        return name

    def parse_module(self):
        """ Parse a module """
        self.logger.debug("Parsing module")
        self.module = nodes.Module(self.context)
        self.forward_refs = {}
        while not self.at_end:
            if self.peek == "define":
                self.parse_define()
            elif self.peek == "declare":
                self.parse_declare()
            elif self.peek == "target":
                self.parse_target_definition()
            elif self.peek == "LID":
                self.parse_unnamed_type()
            elif self.peek == "LID":
                self.parse_named_type()
            elif self.peek == "GID":
                self.parse_named_global()
            elif self.peek == "attributes":
                self.parse_unnamed_attr_group()
            elif self.peek == "MDVAR":
                self.parse_named_metadata()
            elif self.peek == "!":
                self.parse_standalone_metadata()
            else:  # pragma: no cover
                self.error("TODO")
                raise NotImplementedError(str(self.peek))
        return self.module

    def parse_unnamed_type(self):
        """ Parse LocalVarID '=' 'type' type """
        name = self.consume("LID")
        print(name)
        self.consume("=")
        self.consume("type")
        self.parse_struct_definition()

    def parse_named_type(self):
        """ Parse LocalVar '=' 'type' type """
        self.consume("=")
        self.consume("type")
        self.parse_struct()

    def parse_define(self):
        """ Parse a function """
        self.consume("define")
        function = self.parse_function_header()
        self.parse_function_body(function)

    def parse_named_global(self):
        self.consume("GID")
        self.consume("=")
        self.parse_optional_linkage()
        self.parse_global()

    def parse_global(self):
        is_constant = self.parse_global_type()
        ty = self.parse_type()
        self.parse_global_value(ty)
        print(is_constant)

    def parse_global_type(self):
        if self.has_consumed("constant"):
            return True
        elif self.has_consumed("global"):
            return False
        else:
            self.error("Expected 'global' or 'constant'")

    def parse_function_body(self, function):
        self._pfs = PerFunctionState(self, function)
        self.consume("{")
        while self.peek != "}":
            self.parse_basic_block()
        self.consume("}")
        self._pfs = None

    def parse_declare(self):
        """ Parse a function declaration """
        self.consume("declare")
        function = self.parse_function_header()
        print(function)

    def parse_function_header(self):
        return_type = self.parse_type()
        name = self.parse_name(global_name=True)
        arg_list = self.parse_argument_list()
        attributes = self.parse_fn_attribute_value_pairs()
        print(attributes)
        param_types = [a.type for a in arg_list]
        if self.peek == "ATTRID":
            self.consume("ATTRID")
        function_type = nodes.FunctionType.get(return_type, param_types)
        function = nodes.Function.create(function_type, name, self.module)
        for argument, arg_info in zip(function.arguments, arg_list):
            if arg_info.name:
                argument.set_name(arg_info.name)
            else:
                name = self.get_implicit_name()
                argument.set_name(name)
        return function

    def parse_target_definition(self):
        """ Parse a target top level entity """
        self.consume("target")
        if self.peek == "triple":
            self.consume("triple")
            self.consume("=")
            val = self.parse_string_constant()
        else:
            self.consume("datalayout")
            self.consume("=")
            val = self.parse_string_constant()
            self.module.data_layout = nodes.DataLayout.from_string(val)
        return val

    def parse_unnamed_attr_group(self):
        self.consume("attributes")
        attr_id = self.consume("ATTRID")
        self.consume("=")
        self.consume("{")
        attributes = self.parse_fn_attribute_value_pairs()
        print(attributes)
        self.consume("}")
        return attr_id

    def parse_fn_attribute_value_pairs(self):
        attributes = []
        while True:
            if self.peek in ["nounwind", "sspstrong", "uwtable", "readonly"]:
                a = self.consume().val
                attributes.append(a)
            elif self.peek == "STR":
                key = self.parse_string_constant()
                if self.has_consumed("="):
                    val = self.parse_string_constant()
                else:
                    val = None
                attributes.append((key, val))
            else:
                break
        return attributes

    def create_global_fwd_ref(self, module, pty, name):
        if isinstance(pty.el_type, nodes.FunctionType):
            self.not_impl()
        else:
            return nodes.GlobalVariable(pty.el_type, name, module=module)

    def get_global_val(self, name, ty):
        """ Get a global with the given id """
        if not isinstance(ty, nodes.PointerType):
            self.error("global variable reference must have pointer type")

        if name in self.module.vmap:
            val = self.module.vmap[name]
        elif name in self.forward_refs:
            val = self.forward_refs[name]
        else:
            print(self.module, ty, name)
            val = self.create_global_fwd_ref(self.module, ty, name)
            self.forward_refs[name] = val
        return val

    def parse_named_metadata(self):
        """ Parse meta data starting with '!my.var'  """
        self.consume("MDVAR")
        self.consume("=")
        self.consume("!")
        self.consume("{")
        while self.peek != "}":
            self.consume()
        self.consume("}")

    def parse_standalone_metadata(self):
        """ Parse meta data starting with '!' 'num' """
        self.consume("!")
        self.parse_number()
        self.consume("=")
        self.consume("!")
        self.parse_md_node_vector()

    def parse_md_node_vector(self):
        self.consume("{")
        elements = []
        while self.peek != "}":
            self.consume()
            # TODO: parse meta data!
            # if elements:
            #    self.consume(',')
            # metadata = self.parse_metadata()
            # elements.append(metadata)
        self.consume("}")
        return elements

    def parse_metadata(self):
        """Parse meta data

        !42
        !{...}
        !"string"

        """
        if self.peek == "!":
            self.consume("!")
        else:
            md = 1
        return md

    def parse_string_constant(self):
        return self.consume("STR").val

    def parse_basic_block(self):
        if self.peek == "LBL":
            label = self.consume("LBL").val
        else:
            label = self.get_implicit_name()
        bb = self._pfs.define_bb(label)

        # Parse instructions until terminator
        while True:
            if self.peek == "LID":
                name = self.parse_name()
                self.consume("=")
            else:
                name = None

            instruction = self.parse_instruction()
            bb.instructions.append(instruction)
            if name:
                self._pfs.set_instruction_name(name, instruction)
            if instruction.is_terminator:
                break
        return bb

    def parse_argument_list(self):
        """ Parse '(' ... ')' """
        self.consume("(")
        args = []
        if self.peek == ")":
            pass
        else:
            args.append(self.parse_arg())
            while self.has_consumed(","):
                args.append(self.parse_arg())
        self.consume(")")
        return args

    def parse_arg(self):
        ty = self.parse_type()
        attrs = self.parse_optional_param_attrs()
        print(attrs)
        if self.peek == "LID":
            name = self.consume("LID").val
        else:
            name = None
        return ArgInfo(ty, name)

    def parse_optional_param_attrs(self):
        attrs = []
        while True:
            if self.peek in ["nocapture", "nonnull"]:
                attr = self.consume().val
                attrs.append(attr)
            else:
                break
        return attrs

    def parse_optional_linkage(self):
        if self.has_consumed("private"):
            pass
        else:
            pass

    def parse_type(self):
        if self.peek == "type":
            typ = self.consume("type").val
        elif self.peek == "{":
            typ = self.parse_anon_struct_type(packed=False)
        elif self.peek == "[":
            typ = self.parse_array_vector_type(False)
        elif self.peek == "<":
            typ = self.parse_array_vector_type(True)
        elif self.peek == "LID":
            lid = self.consume("LID")
            # named_types[lid]
            print(lid)
            typ = nodes.StructType.get(self.context, [], False)
        else:  # pragma: no cover
            self.not_impl()

        assert isinstance(typ, nodes.Type), str(typ)

        # Parse suffix:
        while True:
            if self.peek == "*":
                self.consume("*")
                typ = nodes.PointerType.get_unequal(typ)
            elif self.peek == "(":
                typ = self.parse_function_type(typ)
            else:
                break
        return typ

    def parse_function_type(self, result):
        arg_list = self.parse_argument_list()
        return nodes.FunctionType.get(result, arg_list)

    def parse_anon_struct_type(self, packed=False):
        elts = self.parse_struct_body()
        return nodes.StructType.get(self.context, elts, packed)

    def parse_struct_definition(self):
        body = self.parse_struct_body()
        print(body)

    def parse_struct_body(self):
        """Parse struct body.

        Can be either of:
        '{' '}'
        '{' type (',' type)* '}'
        """
        body = []
        self.consume("{")
        if self.has_consumed("}"):
            return body
        ty = self.parse_type()
        body.append(ty)
        while self.has_consumed(","):
            ty = self.parse_type()
            body.append(ty)
        self.consume("}")
        return body

    def parse_array_vector_type(self, is_vector):
        if is_vector:
            self.consume("<")
        else:
            self.consume("[")
        size = self.parse_number()
        self.consume("x")
        ty = self.parse_type()
        if is_vector:
            self.consume(">")
            return nodes.VectorType.get(ty, size)
        else:
            self.consume("]")
            return nodes.ArrayType.get(ty, size)

    def parse_number(self):
        return self.consume("NUMBER").val

    def parse_name(self, global_name=False):
        if global_name:
            return self.consume("GID").val
        else:
            return self.consume("LID").val

    def parse_global_value(self, ty):
        v = self.parse_val_id()
        v2 = self.convert_val_id_to_value(ty, v)
        return v2

    def parse_value(self, ty):
        """ Parse a value with a certain type """
        v = self.parse_val_id()
        v2 = self.convert_val_id_to_value(ty, v)
        return v2

    def parse_val_id(self):
        """ Some more abstract value parsing """
        if self.peek == "zeroinitializer":
            self.consume("zeroinitializer")
            v = ValId("zero", None)
        elif self.peek == "LID":
            v = ValId("local", self.parse_name())
        elif self.peek == "GID":
            v = ValId("global", self.parse_name(global_name=True))
        elif self.peek == "NUMBER":
            v = ValId("int", self.consume("NUMBER").val)
        elif self.peek == "HEXDOUBLE":
            v = ValId("float", self.consume("HEXDOUBLE").val)
        elif self.peek == "undef":
            self.consume("undef")
            v = ValId("undef", None)
        elif self.peek == "true":
            self.consume("true")
            v = ValId("constant", nodes.ConstantInt.get_true(self.context))
        elif self.peek == "false":
            self.consume("false")
            v = ValId("constant", nodes.ConstantInt.get_false(self.context))
        elif self.peek == "{":
            self.consume("{")
            elts = self.parse_global_value_vector()
            self.consume("}")
            v = ValId("constant_struct", elts)
        elif self.peek == "<":
            # '<' constvect '>'
            self.consume("<")
            elts = self.parse_global_value_vector()
            self.consume(">")
            v = ValId("constant", nodes.ConstantVector.get(elts))
        elif self.peek == "getelementptr":
            self.consume("getelementptr")
            in_bounds = self.has_consumed("inbounds")
            print(in_bounds)
            self.consume("(")
            ty = self.parse_type()
            print(ty)
            self.consume(",")
            elts = self.parse_global_value_vector()
            self.consume(")")
            v = ValId("constant_gep", elts)
        else:  # pragma: no cover
            self.not_impl()
        assert isinstance(v, ValId), str(v)
        return v

    def convert_val_id_to_value(self, ty, val_id):
        if val_id.kind == "local":
            v = self._pfs.get_val(val_id.val, ty)
        elif val_id.kind == "global":
            v = self.get_global_val(val_id.val, ty)
        elif val_id.kind == "int":
            if not ty.is_integer:
                self.error("integer constant must have integer type")
            v = nodes.ConstantInt.get(ty, val_id.val)
        elif val_id.kind == "float":
            if not ty.is_floating_point:
                self.error("Floating point constant invalid for type")
            v = nodes.ConstantFP.get(ty, val_id.val)
        elif val_id.kind == "zero":
            v = nodes.Constant.get_null_value(ty)
        elif val_id.kind == "undef":
            v = nodes.UndefValue.get(ty)
        elif val_id.kind == "constant":
            v = val_id.val
            if v.ty is not ty:
                self.error("constant expression type mismatch")
        else:
            raise NotImplementedError(str(val_id))
        return v

    def parse_type_and_value(self):
        ty = self.parse_type()
        val = self.parse_value(ty)
        return val

    def parse_type_and_basic_block(self):
        value = self.parse_type_and_value()
        if not isinstance(value, nodes.BasicBlock):
            self.error("Expected a basic block")
        return value

    def parse_global_value_vector(self):
        """ """
        v = []
        v.append(self.parse_global_type_and_value())
        while self.has_consumed(","):
            v.append(self.parse_global_type_and_value())
        return v

    def parse_global_type_and_value(self):
        ty = self.parse_type()
        val = self.parse_global_value(ty)
        return val

    # Instructions
    def parse_instruction(self):
        """ Parse a single instruction """
        if self.peek == "store":
            instruction = self.parse_store()
        elif self.peek == "call":
            instruction = self.parse_call()
        elif self.peek == "ret":
            instruction = self.parse_ret()
        elif self.peek == "br":
            instruction = self.parse_br()
        elif self.peek == "alloca":
            instruction = self.parse_alloca()
        elif self.peek == "load":
            instruction = self.parse_load()
        elif self.peek == "extractelement":
            instruction = self.parse_extract_element()
        elif self.peek == "insertelement":
            instruction = self.parse_insert_element()
        elif self.peek == "shufflevector":
            instruction = self.parse_shuffle_vector()
        elif self.peek in [
            "add",
            "fadd",
            "sub",
            "fsub",
            "mul",
            "fmul",
            "udiv",
            "sdiv",
            "fdiv",
            "urem",
            "srem",
            "shl",
            "lshr",
            "ashr",
        ]:
            instruction = self.parse_arithmatic()
        elif self.peek in ["and", "or"]:
            instruction = self.parse_arithmatic()
        elif self.peek in [
            "sext",
            "zext",
            "trunc",
            "fptrunc",
            "uitofp",
            "fptoui",
            "sitofp",
            "fptosi",
            "ptrtoint",
            "inttoptr",
        ]:
            instruction = self.parse_cast()
        elif self.peek == "select":
            instruction = self.parse_select()
        elif self.peek in ["icmp", "fcmp"]:
            instruction = self.parse_compare()
        elif self.peek == "getelementptr":
            instruction = self.parse_getelementptr()
        else:  # pragma: no cover
            self.not_impl()
        return instruction

    def parse_arithmatic(self):
        op = self.consume().val
        lhs = self.parse_type_and_value()
        self.consume(",")
        rhs = self.parse_value(lhs.ty)
        return nodes.BinaryOperator.create(op, lhs, rhs)

    def parse_cast(self):
        op = self.consume()
        val = self.parse_type_and_value()
        self.consume("to")
        dest_ty = self.parse_type()
        return nodes.CastInst.create(op, val, dest_ty)

    def parse_select(self):
        self.consume("select")
        op0 = self.parse_type_and_value()
        self.consume(",")
        op1 = self.parse_type_and_value()
        self.consume(",")
        op2 = self.parse_type_and_value()
        return nodes.SelectInst.create(op0, op1, op2)

    def parse_compare(self):
        icmp = self.peek == "icmp"
        if icmp:
            self.consume("icmp")
        else:
            self.consume("fcmp")
        pred = self.parse_cmp_predicate(icmp)
        lhs = self.parse_type_and_value()
        self.consume(",")
        rhs = self.parse_value(lhs.ty)
        return nodes.ICmpInst(pred, lhs, rhs)

    def parse_cmp_predicate(self, icmp):
        if icmp:
            predicates = {
                "eq": nodes.CmpInst.ICMP_EQ,
                "ne": nodes.CmpInst.ICMP_NE,
                "slt": nodes.CmpInst.ICMP_SLT,
                "sgt": nodes.CmpInst.ICMP_SGT,
                "sle": nodes.CmpInst.ICMP_SLE,
                "sge": nodes.CmpInst.ICMP_SGE,
                "ult": nodes.CmpInst.ICMP_ULT,
                "ugt": nodes.CmpInst.ICMP_UGT,
                "ule": nodes.CmpInst.ICMP_ULE,
                "uge": nodes.CmpInst.ICMP_UGE,
            }
        else:
            predicates = {"ueq": nodes.CmpInst.FCMP_UEQ}
        if self.peek in predicates:
            v = self.consume().val
            return predicates[v]
        else:
            self.error("Expected one of {}".format(predicates.keys()))

    def parse_alloca(self):
        self.consume("alloca")
        ty = self.parse_type()
        size = 0
        alignment = 0
        if self.peek == ",":
            self.consume(",")
            self.consume("align")
            self.parse_number()
        return nodes.AllocaInst(ty, size, alignment)

    def parse_extract_element(self):
        self.consume("extractelement")
        op1 = self.parse_type_and_value()
        self.consume(",")
        op2 = self.parse_type_and_value()
        return nodes.ExtractElementInst(op1, op2)

    def parse_insert_element(self):
        self.consume("insertelement")
        op1 = self.parse_type_and_value()
        self.consume(",")
        op2 = self.parse_type_and_value()
        self.consume(",")
        op3 = self.parse_type_and_value()
        return nodes.InsertElementInst(op1, op2, op3)

    def parse_shuffle_vector(self):
        """ Parse the shuffle vector """
        self.consume("shufflevector")
        op1 = self.parse_type_and_value()
        self.consume(",")
        op2 = self.parse_type_and_value()
        self.consume(",")
        op3 = self.parse_type_and_value()
        return nodes.ShuffleVectorInst(op1, op2, op3)

    def parse_load(self):
        """Parse load instruction

        'load' 'volatile'? typeandvalue (',' 'align' i32)?
        """
        self.consume("load")
        atomic = self.has_consumed("atomic")
        volatile = self.has_consumed("volatile")
        print(atomic, volatile)
        ty = self.parse_type()
        self.consume(",")
        val = self.parse_type_and_value()
        if self.has_consumed(","):
            self.consume("align")
            self.parse_number()
        return nodes.LoadInst(ty, val)

    def parse_store(self):
        """ Parse store instruction """
        self.consume("store")
        val = self.parse_type_and_value()
        self.consume(",")
        ptr = self.parse_type_and_value()
        if self.has_consumed(","):
            self.consume("align")
            self.parse_number()
        return nodes.StoreInst(val, ptr)

    def parse_getelementptr(self):
        """ parse the get element ptr (GEP) """
        self.consume("getelementptr")
        inbounds = self.has_consumed("inbounds")
        ty = self.parse_type()
        self.consume(",")
        ptr = self.parse_type_and_value()
        indices = []
        while self.has_consumed(","):
            val = self.parse_type_and_value()
            indices.append(val)
        gep = nodes.GetElementPtrInst(ty, ptr, indices)
        gep.inbounds = inbounds
        return gep

    def parse_call(self):
        self.consume("call")
        ret_type = self.parse_type()
        name = self.parse_name(global_name=True)
        args = self.parse_parameter_list()
        return nodes.CallInst(ret_type, name, args)

    def parse_parameter_list(self):
        self.consume("(")
        args = []
        while self.peek != ")":
            if args:
                self.consume(",")
            ty = self.parse_type()
            v = self.parse_value(ty)
            args.append(v)
        self.consume(")")
        return args

    def parse_ret(self):
        """ Parse return instruction """
        self.consume("ret")
        ty = self.parse_type()
        if ty.is_void:
            return nodes.ReturnInst(ty)
        else:
            val = self.parse_value(ty)
            return nodes.ReturnInst(ty, val)

    def parse_br(self):
        """ Parse a branch instruction """
        self.consume("br")
        op0 = self.parse_type_and_value()
        if isinstance(op0, nodes.BasicBlock):
            return nodes.BranchInst(op0)
        else:
            self.consume(",")
            op1 = self.parse_type_and_basic_block()
            self.consume(",")
            op2 = self.parse_type_and_basic_block()
            return nodes.BranchInst(op1, op2, op0)

    def parse_phi(self):
        """Parse a phi instruction.

        For example 'phi' Type '[' Value ',' Value ']' (',' ...) *
        """
        self.parse_type()
        self.consume("[")
        self.parse_value()
        self.consume(",")
        self.parse_value()
        self.consume("]")
        while self.has_consumed(","):
            self.consume("[")
            self.parse_value()
            self.consume(",")
            self.parse_value()
            self.consume("]")


class PerFunctionState:
    """ Keep track of parsing stuff in a function """

    def __init__(self, parser, function):
        self.parser = parser
        self.function = function
        self.forward = {}

    def get_val(self, name, ty):
        """ Get a value with a name and a given type """
        # Lookup the name:
        if name in self.function.vmap:
            val = self.function.vmap[name]
        elif name in self.forward:
            val = self.forward[name]
        else:
            if ty.is_label:
                val = nodes.BasicBlock.create(
                    self.function.context, name, self.function
                )
            else:
                raise NotImplementedError(str(ty))
            self.forward[name] = val

        if ty is not val.ty:
            self.parser.error("{} != {}".format(ty, val.ty))
        return val

    def get_bb(self, name):
        return self.get_val(name, self.function.context.label_ty)

    def define_bb(self, name):
        bb = self.get_bb(name)

        # Move basic block from forward to function:
        self.function.basic_blocks.append(bb)
        self.forward.pop(name)
        return bb

    def set_instruction_name(self, name, instruction):
        # This will update the symbol table:
        instruction.set_name(name)

        # Remove placeholder:
        if name in self.forward:
            sentinel = self.forward.pop(name)
            if sentinel.ty is not instruction.ty:
                self.parser.error(
                    "Instruction forward referenced with type {}".format(
                        sentinel.ty
                    )
                )
            sentinel.replace_all_uses_with(instruction)


ValId = namedtuple("ValId", ["kind", "val"])
ArgInfo = namedtuple("ArgInfo", ["type", "name"])
