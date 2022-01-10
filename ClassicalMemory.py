class ClassicalRegister:
    def __init__(self, var) -> None:
        self.var = var
        self.version = 0
        
    def iterate(self):
        self.version += 1
        
    def __repr__(self) -> str:
        return "ClassicalRegister(" + repr(self.var) + ", " + repr(self.version) + ")"

class ClassicalMemory:    
    def __init__(self) -> None:
        self.registers = {}
        
    def add_var(self, var):
        self.registers[var] = ClassicalRegister(var)
        
    def __repr__(self):
        return "ClassicalMemory(" + repr(self.registers) + ")"