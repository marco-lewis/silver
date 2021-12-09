class Instruction():
    def __init__(self) -> None:
        pass

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
    def __init__(self, operation, out_var=None) -> None:
        super().__init__()
        self.__operation = operation
        
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
        return "QOP(" + repr(self.__operation) + ")"

class QMEAS(Instruction):
    pass

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