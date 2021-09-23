# DEPRECATED

# Goal: Create or be given a blank QuantumChecker.
# When given interpreted commands, "run" them on 
# the QuantumChecker by adding commands to the solver

from Prog import Prog
import QuantumOps as qo

# TODO: Handle non-0 initialisation
# TODO: Handle new commands that get added to the SilqInterpreter

class InterpretationTranslator:
    def __init__(self, checker):
        self.checker = checker
        
    def translate_commands(self, commands):
        for command in commands:
            print(command)
            if command[0] == Prog.QINIT:
                self.checker.init_new_qreg(command[1], command[2], command[3])
            elif command[0] == Prog.QOP:
                self.translate_operation(command)
            elif command[0] == Prog.QORACLE:
                self.checker.apply_oracle(command[1])
                
                
    def translate_operation(self, command):
        q_op = command[3]
        if q_op == 'H':
            self.checker.apply_H(command[4], command[5])
        if q_op == 'X':
            self.checker.apply_sing_op(qo.X, command[4], command[5])
        if q_op == 'Y':
            self.checker.apply_sing_op(qo.Y, command[4], command[5])
        if q_op == 'Z':
            self.checker.apply_sing_op(qo.Z, command[4], command[5])