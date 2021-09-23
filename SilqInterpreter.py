# DEPRECATED

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
        with open(file, 'r') as slq_prog:
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
            elif line_type == Prog.QORACLE:
                self.handle_qor(line)
            else: 
                print("No id")
                            
    def identify_line(self, line):
        if re.search('[a-z]+ := [01]:B;', line) or re.search('[a-z]+ := [0-9]+:[u]?int\[[0-9]+\];', line):
            return Prog.QINIT
        elif re.search('[a-z]+[\[[0-9]+\]]* := [HXYZ]\([a-z]+[\[[0-9]+\]]*\);', line) or re.search('[a-z]+[\[[0-9]+\]]* := rot[XYZ]\([a-z]+[\[[0-9]+\]]*\)', line):
            return Prog.QOP
        elif re.search('if f\([a-z]+\)\{ phase\(pi\); \}', line):
            return Prog.QORACLE
    
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
        if re.match("u?int\[[0-9]+\];", qtype):
            size = int(qtype.split('[')[1].split(']')[0])
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

        # Handle output name
        out_name, out_size = self.handle_var(s[0])
        # Handle operation
        op = s[2].partition('(')[0]
        
        # Handle input name
        in_name, in_size = self.handle_var(s[2].partition('(')[2].partition(')')[0])
        
        return op, (in_name, in_size), (out_name, out_size)
    
    def handle_var(self, var):
        if '[' in var:
            t = var.partition('[')
            name = t[0]
            size = int(t[2].partition(']')[0])
            return name, size
        return var, 0
    
    def handle_qor(self, line):
        s = line.split()
        name = s[1].partition('(')[2].partition(')')[0]
        
        self.commands.append((Prog.QORACLE, name))