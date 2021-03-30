# Goal: take in a Silq file and interpret it into a format 
# that can be used in combination with another class later
# for the QuantumChecker().

from enum import Enum
class Prog(Enum):
    QINIT = 1
    QOP = 2
#     MEAS = 3
#     RET = 4

class SilqInterpreter:
    def __init__(self):
        self.commands = []
        self.vars = {}
        
    def InterpFile(self, file):
        with open('Silq_Programs/prog.slq', 'r') as slq_prog:
            prog = slq_prog.readlines()
        self.InterpSilq(prog)
        
    def InterpSilq(self, slq):
        for line in slq:
            line_type = self.identify_line(line)
            if line_type == QINIT:
                self.handle_qinit(line)
            elif line_type == QOP:
                return False
                            
    def identify_line(self, line):
        return QINIT
    
    def handle_qinit(self, line):
# Get info
        name, size, val = self.get_qinit_info(line)
# Add a new variable interpretation to vars
# Might need to consider creating new names?
        self.vars[name] = name
# Add a new initialisation command to list (QINIT, var, reg_size, init)
# e.g. x := 0:B; -> (INIT, var1, 1, 0)
        self.commands.append((QINIT, name, size, val)
    
    def get_qinit_info(self, line):
        return False

    def handle_qop(self, line):
# Get info
        q_op, var_in, var_out = self.get_qop_info(line)

# Check var interpretations and change them (or add to vars if necc.)
        var_in[0] = self.vars[var_in[0]]
        if not(self.vars[var_out[0]]):
            self.vars[var_out[0]] = self.vars[var_in[0]]
        var_out[0] = self.vars[var_in[0]]

# Add command to list (QOP, var_out, out_addr, operation, var_in, in_addr)
# e.g. y := H(x); -> (QOP, var1, 0, H, var1, 0)
        self.commands.append((QOP, var_out[0], var_out[1], q_op, var_in[0], var_in[1]))
                             
    def get_qop_info(self, line):
        return False