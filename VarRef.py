class VarRef():
    def __init__(self, variable) -> None:
        self.__variable = variable
        self.__index = 0
    
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