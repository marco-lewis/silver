class QRef:
    def __init__(self, name, size, version):
        self.name = name
        self.size = size
        self.version = version

class QuantumReferencer:
    def __init__(self):
        self.q_refs = []
        
    def add(self, name, size):
        if not(type(name) == str):
            raise TypeError("Name is not a string")
        if not(type(size) == int):
            raise TypeError("Size is not an int")
            
        self.q_refs.append(QRef(name, size, 0))
        
    def valid_name(self, ref, name):
        return ref.name == name

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