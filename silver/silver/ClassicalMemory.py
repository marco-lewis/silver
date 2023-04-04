from z3 import Int

from silver.silver.VarRef import VarRef

class ClassicalRegister:
    def __init__(self, var, size = 0, version = 0, z3type=Int) -> None:
        self.var = var
        self.size = size
        self.version = version
        self.z3type = z3type
        
    def iterate(self):
        self.version += 1

    def get_z3speqarg(self):
        return self.z3type(self.var)

    def get_z3instance(self):
        return self.z3type(self.__str__())
        
    def __str__(self) -> str:
        return self.var + "_v" + str(self.version) + "c"
        
    def __repr__(self) -> str:
        return "ClassicalRegister(" + repr(self.var) + ", " + repr(self.size) + ", " + repr(self.version) + ", " + repr(self.z3type) + ")"

class ClassicalMemory:
    registers : dict[str, ClassicalRegister] = {}
    
    def __init__(self) -> None:
        pass

    def verify_size(self, size):
        if not(type(size) == int):
            raise TypeError("Size is not an int")
            
    def get_obligation_variable(self, variable) -> str:
        return str(self.registers[variable])
    
    def is_stored(self, var):
        return self.registers.__contains__(var)

    def get_z3variable(self, var_ref: VarRef):
        if self.is_stored(var_ref.variable):
            return self.registers[var_ref.variable].get_z3instance()
        raise Exception("Unable to do that")
        
    def append(self, var, size=0):
        self.verify_size(size)
        self.registers[var] = ClassicalRegister(var, size=size)
        
    def __repr__(self):
        return "ClassicalMemory(" + repr(self.registers) + ")"