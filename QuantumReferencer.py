class QRef:
    def __init__(self, name, size, version):
        self.name = name
        self.size = size
        self.version = version

    def __str__(self):
        return str(self.name) + "_v" + str(self.version)

class QuantumReferencer:
    q_refs = []
    
    def __init__(self):
        pass

    def get_obligation_variables(self):
        return self.__generate_strings(self.q_refs)

    def __make_token(self, q_ref, num):
        return q_ref.__str__() + "t" + str(num)

    def __generate_strings(self, q_refs):
        if q_refs == []:
            return [""]
        elif len(q_refs) == 1:
            return [self.__make_token(q_refs[0], i) for i in range(0, q_refs[0].size)]
        else:
            out = []
            ob_vars = self.__generate_strings(q_refs[1:])
            for i in range(0, q_refs[0].size):
                out += [self.__make_token(q_refs[0], i) + "|" + ob for ob in ob_vars]
            return out

    def add(self, name, size):
        if not(type(name) == str):
            raise TypeError("Name is not a string")
        if not(type(size) == int):
            raise TypeError("Size is not an int")
            
        self.q_refs.append(QRef(name, size, 0))
        
    def valid_name(self, ref, name):
        return ref.name == name

    def is_empty(self):
        return self.q_refs == []

    def is_stored(self, name):
        for ref in self.q_refs:
            if self.valid_name(ref, name): return True
        return False

    def get_size(self, name):
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                return ref.size
            
        raise ValueError("No reference with that name")
        
    def get_loc(self, name, offset = 0):
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
        for ref in self.q_refs:
            if self.valid_name(ref, name):
                return ref.version