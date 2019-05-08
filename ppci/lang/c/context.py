""" A context where other parts share global state.


"""

import struct
from ...common import CompilerError
from ...utils.bitfun import value_to_bits, bits_to_bytes
from ...arch.arch_info import Endianness
from ... import ir
from .nodes.types import BasicType
from .nodes import types, expressions, declarations
from .utils import required_padding


class CContext:
    """ A context as a substitute for global data """

    def __init__(self, coptions, arch_info):
        self.coptions = coptions
        self.arch_info = arch_info

        self._field_offsets = {}
        self._enum_values = {}
        int_size = self.arch_info.get_size("int")
        int_alignment = self.arch_info.get_alignment("int")
        ptr_size = self.arch_info.get_size("ptr")
        double_size = self.arch_info.get_size(ir.f64)
        double_alignment = self.arch_info.get_alignment(ir.f64)
        self.type_size_map = {
            BasicType.CHAR: (1, 1),
            BasicType.UCHAR: (1, 1),
            BasicType.SHORT: (2, 2),
            BasicType.USHORT: (2, 2),
            BasicType.INT: (int_size, int_alignment),
            BasicType.UINT: (int_size, int_alignment),
            BasicType.LONG: (4, 4),
            BasicType.ULONG: (4, 4),
            BasicType.LONGLONG: (8, 8),
            BasicType.ULONGLONG: (8, 8),
            BasicType.FLOAT: (4, 4),
            BasicType.DOUBLE: (double_size, double_alignment),
            BasicType.LONGDOUBLE: (10, 10),
        }

        int_map = {2: "h", 4: "i", 8: "q"}

        if self.arch_info.endianness == Endianness.LITTLE:
            byte_order = "<"
        else:
            byte_order = ">"

        if double_size == 4:
            ftype = "f"
        else:
            ftype = "d"

        ctypes = {
            BasicType.CHAR: "b",
            BasicType.UCHAR: "B",
            BasicType.SHORT: "h",
            BasicType.USHORT: "H",
            BasicType.INT: int_map[int_size].lower(),
            BasicType.UINT: int_map[int_size].upper(),
            "ptr": int_map[ptr_size].upper(),
            BasicType.LONG: "l",
            BasicType.ULONG: "L",
            BasicType.LONGLONG: "q",
            BasicType.ULONGLONG: "Q",
            BasicType.FLOAT: "f",
            BasicType.DOUBLE: ftype,
        }

        self.ctypes_names = {t: byte_order + v for t, v in ctypes.items()}

    def sizeof(self, typ: types.CType):
        """ Given a type, determine its size in whole bytes """
        if not isinstance(typ, types.CType):
            raise TypeError("typ should be CType: {}".format(typ))

        if isinstance(typ, types.ArrayType):
            element_size = self.sizeof(typ.element_type)
            if typ.size is None:
                self.error(
                    "Size of array could not be determined!", typ.location
                )
            if isinstance(typ.size, int):
                array_size = typ.size
            else:
                array_size = self.eval_expr(typ.size)
            return element_size * array_size
        elif isinstance(typ, types.BasicType):
            return self.type_size_map[typ.type_id][0]
        elif isinstance(typ, types.StructType):
            if not typ.complete:
                self.error("Storage size unknown", typ.location)
            return self._get_field_offsets(typ)[0]
        elif isinstance(typ, types.UnionType):
            if not typ.complete:
                self.error("Type is incomplete, size unknown", typ)
            return max(self.sizeof(part.typ) for part in typ.fields)
        elif isinstance(typ, types.EnumType):
            if not typ.complete:
                self.error("Storage size unknown", typ)
            # For enums take int as the type
            return self.arch_info.get_size("int")
        elif isinstance(typ, (types.PointerType, types.FunctionType)):
            return self.arch_info.get_size("ptr")
        else:  # pragma: no cover
            raise NotImplementedError(str(typ))

    def alignment(self, typ: types.CType):
        """ Given a type, determine its alignment in bytes """
        assert isinstance(typ, types.CType)
        if isinstance(typ, types.ArrayType):
            return self.alignment(typ.element_type)
        elif isinstance(typ, types.BasicType):
            return self.type_size_map[typ.type_id][1]
        elif isinstance(typ, types.StructType):
            if not typ.complete:
                self.error("Storage size unknown", typ.location)
            return max(self.alignment(part.typ) for part in typ.fields)
        elif isinstance(typ, types.UnionType):
            if not typ.complete:
                self.error("Type is incomplete, size unknown", typ)
            return max(self.alignment(part.typ) for part in typ.fields)
        elif isinstance(typ, types.EnumType):
            if not typ.complete:
                self.error("Storage size unknown", typ)
            # For enums take int as the type
            return self.arch_info.get_alignment("int")
        elif isinstance(typ, (types.PointerType, types.FunctionType)):
            return self.arch_info.get_alignment("ptr")
        elif isinstance(typ, types.BitFieldType):
            return 1
        else:  # pragma: no cover
            raise NotImplementedError(str(typ))

    def layout_struct(self, kind, fields):
        """ Layout the fields in the struct """
        offsets = {}
        offset = 0  # Offset in bits
        for field in fields:
            # Calculate bit size:
            if field.bitsize:
                bitsize = self.eval_expr(field.bitsize)
                alignment = 1  # Bitfields are 1 bit aligned
            else:
                bitsize = self.sizeof(field.typ) * 8
                alignment = self.alignment(field.typ) * 8

            # alignment handling:
            offset += required_padding(offset, alignment)

            offsets[field] = offset
            if kind == "struct":
                offset += bitsize

        # TODO: should we take care here of maximum alignment as well?
        # Finally align at 8 bits:
        offset += required_padding(offset, 8)
        assert offset % 8 == 0
        offset //= 8
        return offset, offsets

    def _get_field_offsets(self, typ):
        """ Get a dictionary with offset of fields """
        if typ not in self._field_offsets:
            kind = "struct" if isinstance(typ, types.StructType) else "union"
            size, offsets = self.layout_struct(kind, typ.fields)
            self._field_offsets[typ] = size, offsets
        return self._field_offsets[typ]

    def offsetof(self, typ, field):
        """ Returns the offset of a field in a struct/union in bytes """
        field_offset = self._get_field_offsets(typ)[1][field]
        # Note that below assert will not always hold.
        # It is also used to create debug types.
        # assert field_offset % 8 == 0
        return field_offset // 8

    def has_field(self, typ, field_name):
        """ Check if the given type has the given field. """
        if not isinstance(typ, types.StructOrUnionType):
            raise TypeError("typ must be union or struct type")

        return field_name in typ.get_field_names()

    def get_field(self, typ, field_name):
        """ Get the given field. """
        if not isinstance(typ, types.StructOrUnionType):
            raise TypeError("typ must be union or struct type")

        for field in typ.get_named_fields():
            if field.name == field_name:
                return field
        raise KeyError(field_name)

    def get_enum_value(self, enum_typ, enum_constant):
        if enum_constant not in self._enum_values:
            self._calculate_enum_values(enum_typ)
        return self._enum_values[enum_constant]

    def _calculate_enum_values(self, ctyp):
        """ Determine enum values """
        value = 0
        for constant in ctyp.constants:
            if constant.value:
                value = self.eval_expr(constant.value)
            self._enum_values[constant] = value

            # Increase for next enum value:
            value += 1

    def pack(self, typ, value):
        """ Pack a type into proper memory format """
        if isinstance(typ, types.PointerType):
            tid = "ptr"
        else:
            assert isinstance(typ, types.BasicType)
            tid = typ.type_id
        fmt = self.ctypes_names[tid]
        # Check format with arch options:
        assert self.sizeof(typ) == struct.calcsize(fmt)
        return struct.pack(fmt, value)

    def _make_ival(self, typ, ival):
        """ Try to make ival a proper initializer """
        if isinstance(ival, list):
            if isinstance(typ, types.ArrayType):
                elements = [self._make_ival(typ.element_type, i) for i in ival]
                ival = expressions.ArrayInitializer(typ, elements, None)
            elif isinstance(typ, types.StructType):
                ival2 = expressions.StructInitializer(typ, None)
                for field, value in zip(typ.fields, ival):
                    value = self._make_ival(field.typ, value)
                    ival2.values[field] = value
                ival = ival2
            else:
                raise NotImplementedError(str(typ))
        elif isinstance(ival, int):
            int_type = types.BasicType(types.BasicType.INT)
            ival = expressions.NumericLiteral(ival, int_type, None)
        return ival

    def gen_global_ival(self, typ, ival):
        """ Create memory image for initial value of global variable """
        # Handle arguments:
        ival = self._make_ival(typ, ival)

        # Check initial value type:
        if not isinstance(ival, expressions.Expression):
            raise TypeError("ival must be an Expression")

        if isinstance(typ, types.ArrayType):
            mem = self._initialize_array(typ, ival)
        elif isinstance(typ, types.StructType):
            mem = self._initialize_struct(typ, ival)
        elif isinstance(typ, types.UnionType):
            mem = self._initialize_union(typ, ival)
        elif isinstance(typ, (types.BasicType, types.PointerType)):
            cval = self.eval_expr(ival)
            if isinstance(cval, tuple):
                assert cval[0] is ir.ptr and len(cval) == 2
                mem = (cval,)
            else:
                mem = (self.pack(typ, cval),)
        else:  # pragma: no cover
            raise NotImplementedError(str(typ))
        assert isinstance(mem, tuple)
        return mem

    def _initialize_array(self, typ, ival):
        """ Properly fill an array with initial values """
        assert isinstance(ival, expressions.ArrayInitializer)
        assert ival.typ is typ

        element_size = self.sizeof(typ.element_type)
        implicit_value = tuple([bytes([0] * element_size)])

        mem = tuple()
        for iv in ival.values:
            # TODO: handle alignment
            if iv is None:
                element_mem = implicit_value
            else:
                element_mem = self.gen_global_ival(typ.element_type, iv)
            mem = mem + element_mem

        array_size = self.eval_expr(typ.size)

        if len(ival.values) < array_size:
            extra_implicit = array_size - len(ival.values)
            mem = mem + implicit_value * extra_implicit
        return mem

    def _initialize_union(self, typ, ival):
        """ Initialize a union type """
        assert isinstance(ival, expressions.UnionInitializer)
        assert ival.typ is typ
        mem = tuple()
        # Initialize the first field!
        field = ival.field
        mem = mem + self.gen_global_ival(field.typ, ival.value)
        size = self.sizeof(typ)
        filling = size - len(mem)
        assert filling >= 0
        mem = mem + (bytes([0] * filling),)
        return mem

    def _initialize_struct(self, typ, ival):
        """ Properly fill global struct variable with content """
        assert isinstance(ival, expressions.StructInitializer)
        assert ival.typ is typ
        mem = tuple()
        bits = []  # A working list of bytes

        field_offsets = self._get_field_offsets(typ)[1]
        for field in typ.fields:
            if field.is_bitfield:
                # Special case for bitfields
                if field in ival.values:
                    iv = ival.values[field]
                    cval = self.eval_expr(iv)
                else:
                    cval = 0
                bitsize = self.eval_expr(field.bitsize)
                new_bits = value_to_bits(cval, bitsize)
                bits.extend(new_bits)
            else:
                # Flush bits:
                if bits:
                    mem = mem + (bits_to_bytes(bits),)
                    bits.clear()
                # Apply some padding:
                field_offset = field_offsets[field] // 8
                # TODO: how to handle bit fields?
                mem_len = self.mem_len(mem)
                if mem_len < field_offset:
                    padding_count = field_offset - mem_len
                    mem = mem + (bytes([0] * padding_count),)

                # Add field data, if any:
                if field in ival.values:
                    iv = ival.values[field]
                    mem = mem + self.gen_global_ival(field.typ, iv)
                else:
                    field_size = self.sizeof(field.typ)
                    mem = mem + (bytes([0] * field_size),)

        # Purge last remaining bits:
        if bits:
            mem = mem + (bits_to_bytes(bits),)
            bits.clear()
        return mem

    def mem_len(self, mem):
        """ Determine the bytesize of a memory slab """
        size = 0
        for part in mem:
            if isinstance(part, bytes):
                size += len(part)
            elif isinstance(part, tuple) and part[0] is ir.ptr:
                size += self.arch_info.get_size(part[0])
            else:  # pragma: no cover
                raise NotImplementedError(repr(part))
        return size

    @staticmethod
    def error(message, location, hints=None):
        """ Trigger an error at the given location """
        raise CompilerError(message, loc=location, hints=hints)

    def eval_expr(self, expr):
        """ Evaluate an expression right now! (=at compile time) """
        if isinstance(expr, expressions.BinaryOperator):
            lhs = self.eval_expr(expr.a)
            rhs = self.eval_expr(expr.b)
            op = expr.op

            op_map = {
                "+": lambda x, y: x + y,
                "-": lambda x, y: x - y,
                "*": lambda x, y: x * y,
            }

            # Ensure division is integer division:
            if expr.typ.is_integer:
                op_map["/"] = lambda x, y: x // y
                op_map[">>"] = lambda x, y: x >> y
                op_map["<<"] = lambda x, y: x << y
            else:
                op_map["/"] = lambda x, y: x / y

            value = op_map[op](lhs, rhs)
        elif isinstance(expr, expressions.UnaryOperator):
            if expr.op in ["-"]:
                a = self.eval_expr(expr.a)
                op_map = {"-": lambda x: -x}
                value = op_map[expr.op](a)
            else:  # pragma: no cover
                raise NotImplementedError(str(expr))
        elif isinstance(expr, expressions.VariableAccess):
            if isinstance(expr.variable, declarations.EnumConstantDeclaration):
                value = self.get_enum_value(expr.variable.typ, expr.variable)
            elif isinstance(expr.variable, declarations.VariableDeclaration):
                # emit reference to global symbol
                value = (ir.ptr, expr.variable.name)
            elif isinstance(expr.variable, declarations.FunctionDeclaration):
                # emit reference to global symbol
                value = (ir.ptr, expr.variable.name)
            else:
                raise NotImplementedError(str(expr.variable))
        elif isinstance(expr, expressions.NumericLiteral):
            value = expr.value
        elif isinstance(expr, expressions.CharLiteral):
            value = expr.value
        elif isinstance(expr, expressions.Cast):
            # TODO: do some real casting!
            value = self.eval_expr(expr.expr)
        elif isinstance(expr, expressions.Sizeof):
            if isinstance(expr.sizeof_typ, types.CType):
                value = self.sizeof(expr.sizeof_typ)
            else:
                value = self.sizeof(expr.sizeof_typ.typ)
        elif isinstance(expr, int):
            value = expr
        else:  # pragma: no cover
            raise NotImplementedError(str(expr))
        return value
