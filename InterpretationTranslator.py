from Prog import Prog

# TODO: Handle non-0 initialisation

class InterpretationTranslator:
    def __init__(self, checker):
        self.checker = checker
        
    def translate_commands(self, commands):
        for command in commands:
            print(command)
            if command[0] == Prog.QINIT:
                self.checker.init_new_qreg(command[1], command[2])
            elif command[0] == Prog.QOP:
                print(False)