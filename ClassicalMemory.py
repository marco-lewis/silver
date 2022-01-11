class ClassicalRegister:
    def __init__(self, var, version=0) -> None:
        self.var = var
        self.version = version
        
    def iterate(self):
        self.version += 1
        
    def __repr__(self) -> str:
        return "ClassicalRegister(" + repr(self.var) + ", " + repr(self.version) + ")"

class ClassicalMemory:    
    def __init__(self, registers={}) -> None:
        self.registers = registers
        
    def add_var(self, var):
        self.registers[var] = ClassicalRegister(var)
        
    def __repr__(self):
        return "ClassicalMemory(" + repr(self.registers) + ")"