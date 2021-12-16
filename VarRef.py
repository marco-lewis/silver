# TODO: Change name to something more appropriate (Z3 has IntRef)
class VarRef():
    def __init__(self, variable, index=0) -> None:
        self.__variable = variable
        self.__index = index
    
    @property
    def variable(self):
        return self.__variable

    @variable.setter
    def operation(self, value):
        self.__variable = value
        
    @property
    def index(self):
        return self.__index

    @index.setter
    def index(self, value):
        self.__index = value 
        
    def __repr__(self) -> str:
        return "VarRef(" + self.__variable + ", " + repr(self.__index) + ")"