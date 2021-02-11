import logging
from . import nodes
from ... import ir, irutils


class CodeGenerator:
    """Transform llvm-ir into ppci-ir

    This class has the humble job to convert llvm-IR into ppci-IR.

    llvm variables are prefixed with ll_
    """

    logger = logging.getLogger("llvm-gen")

    def __init__(self):
        self.builder = irutils.Builder()
        self.val_map = {}
        self.forward = {}

    def generate(self, ll_module):
        """ Convert LLVM IR-module to ppci IR-module """
        assert isinstance(ll_module, nodes.Module)
        self.logger.debug("generating ir-code from llvm ir-code")
        self.logger.warning("ir code generation not functional yet")
        self.builder.module = ir.Module("TODO")
        self.ll_module = ll_module
        for function in ll_module.functions:
            self.gen_function(function)
        self.ll_module = None
        return self.builder.module

    def gen_function(self, function):
        """ Generate code for an llvm function """
        self.logger.debug("generating ir-code for %s", function)
        name = "b"
        ir_function = self.builder.new_procedure(name)
        self.builder.set_function(ir_function)
        for ll_arg in function.arguments:
            arg_name = ll_arg.name
            arg_ty = self.get_ir_type(ll_arg.ty)
            pp_arg = ir.Parameter(arg_name, arg_ty)
            self.val_map[ll_arg] = pp_arg
            ir_function.add_parameter(pp_arg)
        for basic_block in function.basic_blocks:
            block = self.builder.new_block()
            self.builder.set_block(block)
            for instruction in basic_block.instructions:
                self.gen_instruction(instruction)

    def gen_instruction(self, instruction):
        """ Transform an llvm instruction into the right ppci ir part """
        if isinstance(instruction, nodes.BinaryOperator):
            lhs = self.get_val(instruction.lhs)
            op_map = {"mul": "*", "add": "+"}
            op = op_map[instruction.op]
            rhs = self.get_val(instruction.rhs)
            name = "binop"
            ty = self.get_ir_type(instruction.ty)
            ir_val = self.emit(ir.Binop(lhs, op, rhs, name, ty))
            self.val_map[instruction] = ir_val
        elif isinstance(instruction, nodes.AllocaInst):
            amount = self.ll_module.data_layout.get_type_alloc_size(
                instruction.allocated_ty
            )
            name = instruction.name
            ir_ins = self.emit(ir.Alloc(name, amount))
            self.val_map[instruction] = ir_ins
        elif isinstance(instruction, nodes.GetElementPtrInst):
            # Implement arithmetic here!
            ir_ins = self.get_val(instruction.ptr)
            print(instruction.indices)
            # raise NotImplementedError(str(instruction))
            # TODO
            self.val_map[instruction] = ir_ins
        elif isinstance(instruction, nodes.LoadInst):
            ty = self.get_ir_type(instruction.ptr.ty.el_type)
            ptr = self.get_val(instruction.ptr)
            ir_ins = self.emit(ir.Load(ptr, "load", ty))
            self.val_map[instruction] = ir_ins
        elif isinstance(instruction, nodes.StoreInst):
            val = self.get_val(instruction.val)
            ptr = self.get_val(instruction.ptr)
            self.emit(ir.Store(val, ptr))
        elif isinstance(instruction, nodes.InsertElementInst):
            pp_ptr = self.get_val(instruction.address)
            pp_val = self.get_val(instruction.value)
            # TODO: type check?
            # pp_ty = self.get_type(instruction.ty.el_type)
            # assert
            self.emit(ir.Store(pp_ptr, pp_val))
            self.val_map[instruction] = pp_val
        elif isinstance(instruction, nodes.ExtractElementInst):
            pp_ptr = self.get_val(instruction.val)
            pp_ty = self.get_type(instruction.ty)
            # TODO: offset?
            # TODO: what if loaded type is not a basetype?
            # pp_ptr = self.emit(ir.add())
            pp_val = self.emit(ir.Load(pp_ptr, "load", pp_ty))
            self.val_map[instruction] = pp_val
        elif isinstance(instruction, nodes.ShuffleVectorInst):
            raise NotImplementedError()
        elif isinstance(instruction, nodes.SelectInst):
            raise NotImplementedError()
        elif isinstance(instruction, nodes.PhiNode):
            phi = ir.Phi()
            for incoming in instruction:
                value = self.get_val()
                block = 1
                phi.set_incoming(block, value)
            self.emit(phi)
        elif isinstance(instruction, nodes.ICmpInst):
            a = self.get_val(instruction.lhs)
            b = self.get_val(instruction.rhs)
            block0 = self.builder.new_block()
            block1 = self.builder.new_block()
            final = self.builder.new_block()
            self.emit(ir.CJump(a, "=", b, block1, block0))
            self.builder.set_block(block0)
            zero = self.emit(ir.Const(0, "zero", ir.i8))
            self.emit(ir.Jump(final))
            self.builder.set_block(block1)
            one = self.emit(ir.Const(1, "one", ir.i8))
            self.emit(ir.Jump(final))
            self.builder.set_block(final)
            phi = ir.Phi("icmp", ir.i8)
            phi.set_incoming(block0, zero)
            phi.set_incoming(block1, one)
            self.emit(phi)
            self.val_map[instruction] = phi
        elif isinstance(instruction, nodes.BranchInst):
            if isinstance(instruction.op1, nodes.BasicBlock):
                # Unconditional jump:
                block = self.get_block(instruction.op1)
                self.emit(ir.Jump(block))
            else:
                # conditional jump:
                block1 = self.get_block(instruction.op1)
                block2 = self.get_block(instruction.op2)
                val = self.get_val(instruction.op3)
                one = self.emit(ir.Const(1, "one", ir.i8))
                self.emit(ir.CJump(val, "==", one, block1, block2))
        elif isinstance(instruction, nodes.ReturnInst):
            # Is this return void?
            if instruction.ty.is_void:
                self.emit(ir.Exit())
            else:
                pp_val = self.get_val(instruction.value)
                self.emit(ir.Return(pp_val))
        elif isinstance(instruction, nodes.CallInst):
            # Is it a void call?
            fname = instruction.fname
            arguments = []
            if instruction.ty.is_void:
                self.emit(ir.ProcedureCall(fname, arguments))
            else:
                self.emit(ir.FunctionCall(fname, arguments))
        else:  # pragma: no cover
            raise NotImplementedError(str(instruction))

    def get_val(self, llvm_val):
        val = self.val_map[llvm_val]
        # print(self.val_map)
        # print(llvm_val, val)
        return val

    def get_ir_type(self, ll_ty):
        if ll_ty.type_id == nodes.integer_ty_id:
            mapping = {8: ir.i8, 16: ir.i16, 32: ir.i32, 64: ir.i64}
            return mapping[ll_ty.bits]
        elif ll_ty.type_id == nodes.pointer_ty_id:
            return ir.ptr
        elif ll_ty.type_id == nodes.vector_ty_id:
            return ir.ptr
        else:
            raise NotImplementedError(str(ll_ty))

    def emit(self, instruction):
        return self.builder.emit(instruction)
