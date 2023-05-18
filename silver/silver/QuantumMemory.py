from silver.silver.VarRef import VarRef


class QuantumRegister:
    def __init__(self, var, size, version = 0):
        self.var = var
        self.size = size
        self.version = version

    def iterate(self):
        self.version += 1

    def __str__(self):
        return str(self.var) + "_v" + str(self.version)
    
    def __repr__(self) -> str:
        return "QuantumRegister(" + repr(self.var) + "," + repr(self.size) + "," + repr(self.version) + ")" 

class QuantumMemory:
    registers : dict[str, QuantumRegister] = {}
    
    def __init__(self):
        pass

    def verify_size(self, size):
        if not(type(size) == int):
            raise TypeError("Size is not an int")

    def get_obligation_variables(self) -> list[str]:
        return self.__generate_strings()

    def __generate_strings(self) -> list[str]:
        registers = self.registers
        out = []
        for key, qreg in registers.items():
            t = []
            for i in range(0, 2**qreg.size):
                tok = self.__make_token(qreg, i)
                t += [tok + "!" + obl for obl in out] if not(out == []) else [tok]
            out = t
        return out

    def __make_token(self, qvar, num):
        return qvar.__str__() + "q" + str(num)

    def append(self, var, size):
        self.verify_size(size)
        self.registers[var] = QuantumRegister(var, size, 0)

    def ammend_size(self, var, new_size):
        self.verify_size(new_size)
        self.registers[var].size = new_size
        
    def update_reg(self, prev_var, new_var):
        self.registers = {new_var if k == prev_var else k:v for k,v in self.registers.items()}
        
    def measure_reg(self, var):
        del self.registers[var]
        
    def iterate_reg(self, var):
        self.registers[var].iterate()
    
    def iterate_all(self):
        for key in self.registers:
            self.registers[key].iterate()

    def is_empty(self):
        return self.registers == {}

    def is_single(self):
        return len(self.registers) == 1

    def is_stored(self, var):
        return self.registers.__contains__(var)
    
    def get_size(self, var):
        return self.registers[var].size

    # TODO: Handle None case differently
    def get_loc(self, var, offset = 0):
        if offset == None:
            offset = 0
        
        loc = 0
        for key, qreg in self.registers.items():
            if key == var:
                if offset >= qreg.size:
                    raise ValueError("Offset is larger than register size: offset="+str(offset)+", size="+str(qreg.size))
                return loc + offset
            loc += qreg.size
        return None
    
    def get_loc_from_VarRef(self, var_ref :VarRef):
        return self.get_loc(var_ref.variable, var_ref.index)        
            
    def get_reg_string(self, var):
        return self.registers[var].__str__()
        
    def get_total_size(self):
        return sum(qreg.size for key, qreg in self.registers.items())

    def get_version(self, var):
        return self.registers[var].version
    
    def __repr__(self) -> str:
        return "QuantumMemory(" + repr(self.registers) + ")"