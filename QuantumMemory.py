class QuantumRegister:
    def __init__(self, reg, size, version = 0):
        self.reg = reg
        self.size = size
        self.version = version

    def iterate(self):
        self.version += 1

    def __str__(self):
        return str(self.reg) + "_v" + str(self.version)

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
        return t

    def __make_token(self, qreg, num):
        return qreg.__str__() + "q" + str(num)

    def append(self, reg, size):
        self.verify_size(size)

        self.q_mem[reg] = QuantumRegister(reg, size, 0)

    def ammend_size(self, reg, new_size):
        self.verify_size(new_size)
        self.q_mem[reg].size = new_size
        
    def update_reg(self, prev_reg, new_reg):
        self.q_mem = {new_reg if k == prev_reg else k:v for k,v in self.q_mem.items()}
        
    def measure_reg(self, reg):
        del self.q_mem[reg]
        
    def iterate_var(self, reg):
        self.q_mem[reg].iterate()

    def is_empty(self):
        return self.q_mem == {}

    def is_single(self):
        return len(self.q_mem) == 1

    def is_stored(self, reg):
        return self.q_mem.__contains__(reg)
    
    def get_size(self, reg):
        return self.q_mem[reg].size

    def get_loc(self, reg, offset = 0):
        loc = 0
        for key, qreg in self.q_mem.items():
            if key == reg:
                if offset >= qreg.size:
                    raise ValueError("Offset is larger than register size")
                return loc + offset
            loc += qreg.size
        return None
            
    def get_reg_string(self, reg):
        return self.q_mem[reg].__str__()
        
    def get_total_size(self):
        return sum(reg.size for key, reg in self.q_mem.items())

    def get_version(self, reg):
        return self.q_mem[reg].version