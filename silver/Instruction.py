from typing import List
from silver.VarRef import VarRef


class Instruction():
    def __init__(self) -> None:
        pass
    
    def __repr__(self) -> str:
        return "Instruction()"
    
    def __eq__(self, other: object) -> bool:
        if isinstance(other, self.__class__):
            return self.__dict__ == other.__dict__
        return NotImplemented

class QINIT(Instruction):
    def __init__(self, value, size, variable=None) -> None:
        super().__init__()
        if value >= 2**size:
            raise Exception("InstructionError: Value provided is greater than representation.")
        self.__variable = variable
        self.__value = value
        self.__size = size
    
    @property
    def variable(self):
        return self.__variable

    @variable.setter
    def variable(self, value):
        self.__variable = value
    
    @property
    def size(self):
        return self.__size

    @size.setter
    def size(self, value):
        self.__size = value
    
    @property
    def value(self):
        return self.__value

    @value.setter
    def value(self, value):
        self.__value = value
        
    def __repr__(self) -> str:
        return "QINIT(" + repr(self.__value) + ", " + repr(self.__size) + ", " + repr(self.variable) + ")"

class CINIT(Instruction):
    def __init__(self, value, size, variable=None) -> None:
        super().__init__()
        if isinstance(size, int):
            if value >= 2**size: raise Exception("InstructionError: Value provided is greater than representation.")
        self.__variable = variable
        self.__value = value
        self.__size = size
    
    @property
    def variable(self):
        return self.__variable

    @variable.setter
    def variable(self, value):
        self.__variable = value
    
    @property
    def size(self):
        return self.__size

    @size.setter
    def size(self, value):
        self.__size = value
    
    @property
    def value(self):
        return self.__value

    @value.setter
    def value(self, value):
        self.__value = value
        
    def __repr__(self) -> str:
        return "QINIT(" + repr(self.__value) + ", " + repr(self.__size) + ", " + repr(self.variable) + ")"
        
class QOP(Instruction):
    def __init__(self, operation, arg=None, out=None) -> None:
        super().__init__()
        self.__operation = operation
        self.__arg = arg
        self.__out = out

    @property
    def operation(self):
        return self.__operation

    @operation.setter
    def operation(self, value):
        self.__operation = value
        
    @property
    def arg(self):
        return self.__arg

    @arg.setter
    def arg(self, value):
        self.__arg = value

    @property
    def out(self):
        return self.__out

    @out.setter
    def out(self, value):
        self.__out = value

    def __repr__(self) -> str:
        return "QOP(" + repr(self.__operation) + ", " + repr(self.__arg) + ", " + repr(self.__out) + ")"

class QPAR(Instruction):
    def __init__(self, operations) -> None:
        super().__init__()
        self.__operations = operations
        
    @property
    def operations(self):
        return self.__operations

    @operations.setter
    def operations(self, value):
        self.__operations = value
        
    def __repr__(self) -> str:
        return "QPAR(" + repr(self.__operations) + ")"


class QPHASE(Instruction):
    def __init__(self, phase) -> None:
        super().__init__()
        self.__phase = phase
        
    @property
    def phase(self):
        return self.__phase

    @phase.setter
    def phase(self, phase):
        self.__phase = phase
    
    def __repr__(self) -> str:
        return "QPHASE(" + repr(self.__phase) + ")"

class QFORGET(Instruction):
    def __init__(self, variable, value) -> None:
        super().__init__()
        self.__variable = variable
        self.__value = value
        
    @property
    def variable(self):
        return self.__variable

    @variable.setter
    def variable(self, value):
        self.__variable = value
        
    @property
    def value(self):
        return self.__value

    @value.setter
    def value(self, value):
        self.__value = value
        
    def __repr__(self) -> str:
        return "QFORGET(" + repr(self.variable) + ", " + repr(self.value) + ")"

class QMEAS(Instruction):
    __quantum_ref : VarRef
    __classical_ref : VarRef
    
    def __init__(self, quantum_ref, classical_ref=VarRef(None)) -> None:
        super().__init__()
        self.__quantum_ref = quantum_ref
        self.__classical_ref = classical_ref
        
    @property
    def quantum_ref(self):
        return self.__quantum_ref

    @quantum_ref.setter
    def quantum_ref(self, value):
        self.__quantum_ref = value
        
    @property
    def classical_ref(self):
        return self.__classical_ref

    @classical_ref.setter
    def classical_ref(self, value):
        self.__classical_ref = value
        
    def __repr__(self) -> str:
        return "QMEAS(" + repr(self.__quantum_ref) + ")"

class BOOLOP(Instruction):
    def __init__(self, lhs, comparitor, rhs) -> None:
        super().__init__()
        self.__left = lhs
        self.__right = rhs
        self.__comparitor = comparitor
        
    @property
    def left(self):
        return self.__left
    
    @left.setter
    def left(self, value):
        self.__left = value
        
    @property
    def right(self):
        return self.__right
    
    @right.setter
    def right(self, value):
        self.__right = value
        
    @property
    def comparitor(self):
        return self.__comparitor
    
    @comparitor.setter
    def comparitor(self, value):
        self.__comparitor = value
        
    def __repr__(self) -> str:
        return "BOOLOP(" + repr(self.left) + "," + repr(self.comparitor) + "," + repr(self.right) + ")"

class CMEAS(Instruction):
    def __init__(self, quantum_ref, classical_ref) -> None:
        super().__init__()
        self.__quantum_ref = quantum_ref
        self.__classical_ref = classical_ref
        
    @property
    def quantum_ref(self):
        return self.__quantum_ref
    
    @quantum_ref.setter
    def quantum_ref(self, value):
        self.__quantum_ref = value

    @property
    def classical_ref(self):
        return self.__classical_ref
    
    @classical_ref.setter
    def classical_ref(self, value):
        self.__classical_ref = value
        
    def __repr__(self) -> str:
        return "CMEAS(" + repr(self.__quantum_ref) + ", " + repr(self.__classical_ref) + ")"

# TODO: Leave empty with no attributes?
class RETURN(Instruction):
    def __init__(self, value_refs, function_name) -> None:
        super().__init__()
        self.__value_refs = value_refs
        self.__function_name = function_name
        
    @property
    def value_refs(self):
        return self.__value_refs

    @value_refs.setter
    def value_refs(self, value):
        self.__value_refs = value
        
    @property
    def function_name(self):
        return self.__function_name
    
    @function_name.setter
    def function_name(self, value):
        self.__function_name = value
        
    def __repr__(self) -> str:
        return "RETURN(" + repr(self.__value_refs) + ", " + repr(self.__function_name) + ")"