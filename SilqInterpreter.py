# Goal: take in a Silq file and interpret it into a format 
# that can be used in combination with another class later
# for the QuantumChecker().

class SilqInterpreter:
    def __init__(self):
        self.commands = []
        self.vars = {}
        
    def InterpFile(self, file):
        with open('Silq_Programs/prog.slq', 'r') as slq_prog:
            prog = slq_prog.readlines()
        self.InterpSilq(prog)
        
    def InterpSilq(slq):
        for line in slq:
            return 0