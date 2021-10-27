class QRef:
    def __init__(self, name, size, version = 0):
        self.name = name
        self.size = size
        self.version = version

    def iterate(self):
        self.version += 1

    def __str__(self):
        return str(self.name) + "_v" + str(self.version)

class QuantumReferencer:
    q_refs = []
    
    def __init__(self):
        pass
    
    def verify_name(self, name):
        if not(type(name) == str):
            raise TypeError("Name: (", name, ") is not a string")

    def verify_size(self, size):
        if not(type(size) == int):
            raise TypeError("Size (", size,") is not an int")

    def get_obligation_variables(self):
        return self.__generate_strings(self.q_refs)

    def __generate_strings(self, q_refs):
        if len(q_refs) == 0:
            return []
        elif len(q_refs) == 1:
            return [self.__make_token(q_refs[0], i) for i in range(0, 2**q_refs[0].size)]
        else:
            out = []
            ob_vars = self.__generate_strings(q_refs[1:])
            for i in range(0, 2**q_refs[0].size):
                out += [self.__make_token(q_refs[0], i) + "|" + ob for ob in ob_vars]
            return out

    def __make_token(self, q_ref, num):
        return q_ref.__str__() + "q" + str(num)

    def append(self, name, size):
        self.verify_name(name)
        self.verify_size(size)
            
        self.q_refs.append(QRef(name, size, 0))

    def ammend_size(self, new_size):
        self.verify_size(new_size)
        ref = self.q_refs[-1]
        ref.size = new_size

    def iterate_var(self, name):
        self.verify_name(name)
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                ref.iterate()
            
    def valid_name(self, ref, name):
        return ref.name == name

    def is_empty(self):
        return self.q_refs == []

    def is_single(self):
        return len(self.q_refs) == 1

    def is_stored(self, name):
        for ref in self.q_refs:
            if self.valid_name(ref, name): return True
        return False

    def get_size(self, name):
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                return ref.size
            
        raise ValueError("No reference with that name")

    def get_last_item_size(self):
        return self.q_refs[-1].size

    def get_loc(self, name, offset = 0):
        self.verify_name(name)
        loc = 0
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                if offset >= ref.size:
                    raise ValueError("Offset is larger than register size")
                else: return loc + offset
            else: loc += ref.size
        
        raise ValueError("No reference with that name")
        
    def get_total_size(self):
        return sum(ref.size for ref in self.q_refs)

    def get_version(self, name):
        self.verify_name(name)
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                return ref.version

        raise ValueError("No reference with that name")