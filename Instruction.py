class Instruction():
    def __init__(self) -> None:
        pass
    
    def __repr__(self) -> str:
        return "Instruction()"

class QINIT(Instruction):
    def __init__(self, value, size) -> None:
        super().__init__()
        if value >= 2**size:
            raise Exception("InstructionError: Value provided is greater than representation.")
        self.__value = value
        self.__size = size
    
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
    def __init__(self, operation, arg=None) -> None:
        super().__init__()
        self.__operation = operation
        self.__arg = arg
        
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

    def __repr__(self) -> str:
        return "QOP(" + repr(self.__operation) + ", " + repr(self.__arg) + ")"

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
    def __init__(self, variable_ref) -> None:
        super().__init__()
        self.__variable_ref = variable_ref
        
    @property
    def variable_ref(self):
        return self.__variable_ref

    @variable_ref.setter
    def variable(self, value):
        self.__variable_ref = value
        
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