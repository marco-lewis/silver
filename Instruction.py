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

    @size.setter
    def value(self, value):
        self.__value = value
        
    def __repr__(self) -> str:
        return "QINIT(" + repr(self.__value) + ", " + repr(self.__size) + ")"
        
class QOP(Instruction):
    pass

class QMEAS(Instruction):
    pass

class RETURN(Instruction):
    pass