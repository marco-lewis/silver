# Goal: Take in a Silq file and interpret it into a format 
# that can be used in combination with another class later
# for the QuantumChecker().
import re
from Prog import Prog

# TODO: Regex for valid variables (atm. only a-z)
# TODO: Handle arrays in operations
# TODO: Handle classical functionality
# TODO: Handle mutli-variable functions
# TODO: Handle controls
# TODO: Handle custom functions

class SilqInterpreter:
    def __init__(self):
        self.commands = []
        self.vars = {}
        
    def print_commands(self):
        for c in self.commands:
            print(c)
        
    def interpret_file(self, file):
        self.commands = []
        with open('Silq_Programs/prog.slq', 'r') as slq_prog:
            prog = slq_prog.readlines()
        self.interpret_silq(prog)
        return self.commands
        
    def interpret_silq(self, slq):
        for line in slq:
            line_type = self.identify_line(line)
            if line_type == Prog.QINIT:
                self.handle_qinit(line)
            elif line_type == Prog.QOP:
                self.handle_qop(line)
            else: 
                print("No id")
                            
    def identify_line(self, line):
        if re.search('[a-z]+ := [01]:B;', line):
            return Prog.QINIT
        elif re.search('[a-z]+ := [HXYZ]\([a-z]+\);', line) or re.search('[a-z]+ := rot[XYZ]\([a-z]+\)', line):
            return Prog.QOP
    
    def handle_qinit(self, line):
        # Get info
        name, size, val = self.get_qinit_info(line)
        # Add a new variable interpretation to vars
        # Might need to consider creating new names?
        self.vars[name] = name
        # Add a new initialisation command to list (QINIT, var, reg_size, init)
        # e.g. x := 0:B; -> (INIT, var1, 1, 0)
        self.commands.append((Prog.QINIT, name, size, val))

    def get_qinit_info(self, line):
        s = line.split()
        name = s[0]
        val = int(s[2].partition(':')[0])
        qtype = s[2].partition(':')[2]
        if qtype == "B;":
            size = 1
        return name, size, val

    def handle_qop(self, line):
        # Get info
        q_op, var_in, var_out = self.get_qop_info(line)

        # Check var interpretations and change them (or add to vars if necc.)
        if not(var_out[0] in self.vars):
            self.vars[var_out[0]] = self.vars[var_in[0]]

        # Add command to list (QOP, var_out, out_addr, operation, var_in, in_addr)
        # e.g. y := H(x); -> (QOP, var1, 0, H, var1, 0)
        # x[1] := Y(x[i]); -> (QOP, x, 1, Y, x, 1)
        self.commands.append((Prog.QOP, self.vars[var_out[0]], var_out[1], q_op, self.vars[var_in[0]], var_in[1]))
                             
    def get_qop_info(self, line):
        s = line.split()
        out_name = s[0]
        op = s[2].partition('(')[0]
        
        in_name = s[2].partition('(')[2].partition(')')[0]
        
        return op, (in_name, 0), (out_name, 0)
