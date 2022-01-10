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
    q_mem = {}
    
    def __init__(self):
        pass

    def verify_size(self, size):
        if not(type(size) == int):
            raise TypeError("Size is not an int")

    def get_obligation_variables(self):
        return self.__generate_strings()

    def __generate_strings(self):
        q_mem = self.q_mem
        out = []
        for key, qreg in q_mem.items():
            t = []
            for i in range(0, 2**qreg.size):
                tok = self.__make_token(qreg, i)
                t += [obl + "|" + tok for obl in out] if not(out == []) else [tok]
            out = t
        return out

    def __make_token(self, qvar, num):
        return qvar.__str__() + "q" + str(num)

    def append(self, var, size):
        self.verify_size(size)
        self.q_mem[var] = QuantumRegister(var, size, 0)

    def ammend_size(self, var, new_size):
        self.verify_size(new_size)
        self.q_mem[var].size = new_size
        
    def update_reg(self, prev_var, new_var):
        self.q_mem = {new_var if k == prev_var else k:v for k,v in self.q_mem.items()}
        
    def measure_reg(self, var):
        del self.q_mem[var]
        
    def iterate_reg(self, var):
        self.q_mem[var].iterate()
    
    def iterate_all(self):
        for key in self.q_mem:
            self.q_mem[key].iterate()

    def is_empty(self):
        return self.q_mem == {}

    def is_single(self):
        return len(self.q_mem) == 1

    def is_stored(self, var):
        return self.q_mem.__contains__(var)
    
    def get_size(self, var):
        return self.q_mem[var].size

    def get_loc(self, var, offset = 0):
        loc = 0
        for key, qreg in self.q_mem.items():
            if key == var:
                if offset >= qreg.size:
                    raise ValueError("Offset is larger than varister size")
                return loc + offset
            loc += qreg.size
        return None
            
    def get_reg_string(self, var):
        return self.q_mem[var].__str__()
        
    def get_total_size(self):
        return sum(qreg.size for key, qreg in self.q_mem.items())

    def get_version(self, var):
        return self.q_mem[var].version
    
    def __repr__(self) -> str:
        return "QuantumMemory(" + repr(self.q_mem) + ")"