# TODO: Change name to something more appropriate (Z3 has IntRef)
# If index is none - use whole variable
# Otherwise just use index
class VarRef():
    def __init__(self, variable, index=None, isquantum=True, time=0) -> None:
        self.__variable = variable
        self.__index = index
        self.__isquantum = isquantum
        self.__time = time
    
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

    @property
    def isquantum(self):
        return self.__isquantum

    @isquantum.setter
    def isquantum(self, value):
        self.__isquantum = value

    @property
    def time(self):
        return self.__time

    @time.setter
    def time(self, value):
        self.__time = value

    def __eq__(self, other: object) -> bool:
        if isinstance(other, self.__class__):
            v = self.variable == other.variable
            i = self.index == other.index
            q = self.isquantum == other.isquantum
            t = self.time == other.time
            return all([v,i,q,t])
        return NotImplemented
        
    def __repr__(self) -> str:
        return "VarRef(" + self.__variable + ", " + repr(self.__index) + ", " + repr(self.__isquantum) + ", " + repr(self.__time) + ")"