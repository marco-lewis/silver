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
        return "QINIT(" + repr(self.__value) + ", " + repr(self.__size) + ")"
        
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

class QPHASE(Instruction):
    def __init__(self, phase) -> None:
        super().__init__()
        self.__phase = phase
        
    @property
    def phase(self):
        return self.__phase

    @phase.setter
    def phase(self, phase):
        self.__phase = phase#
    
    def __repr__(self) -> str:
        return "QPHASE(" + repr(self.__phase) + ")"

class QMEAS(Instruction):
    def __init__(self, variable_ref, measured_variable=None) -> None:
        super().__init__()
        self.__variable_ref = variable_ref
        self.__measured_variable = measured_variable
        
    @property
    def variable_ref(self):
        return self.__variable_ref

    @variable_ref.setter
    def variable(self, value):
        self.__variable_ref = value
        
    @property
    def measured_variable(self):
        return self.__measured_variable

    @measured_variable.setter
    def measured_variable(self, value):
        self.__measured_variable = value
        
    def __repr__(self) -> str:
        return "QMEAS(" + repr(self.__variable_ref) + ")"

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
    def __init__(self, values) -> None:
        super().__init__()
        self.__values = values
        
    @property
    def values(self):
        return self.__values

    @values.setter
    def values(self, values):
        self.__values = values
        
    def __repr__(self) -> str:
        return "RETURN(" + repr(self.__values) + ")"