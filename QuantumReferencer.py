class QuantumReferencer:
    def __init__(self):
        self.q_refs = []
        
    def add(self, name, size):
        if not(type(name) == str):
            raise TypeError("Name is not a string")
        if not(type(size) == int):
            raise TypeError("Size is not an int")
            
        self.q_refs.append((name, size))
        
    def get_size(self, name):
        for ref in self.q_refs:
            if ref[0] == name:
                return ref[1]
            
        raise ValueError("No reference with that name")
        
    def get_loc(self, name, offset = 0):
        loc = 0
        for ref in self.q_refs:
            if ref[0] == name:
                if offset >= ref[1]:
                    raise ValueError("Offset is larger than register size")
                else: return loc + offset
            else: loc += ref[1]
        
        raise ValueError("No reference with that name")
        
    def get_total_size(self):
        return sum(ref[1] for ref in self.q_refs)