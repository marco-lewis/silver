from QuantumOps import *


class Command():
    def __init__(self) -> None:
        pass
    

# Stores the operation, variables (with renaming) and what controls are on the operation
class QuantumCommand(Command):
    operation = None
    
    in_vars = None
    out_vars = None
    
    def __init__(self, in_vars = [], out_vars = [], operation = ID) -> None:
        self.in_vars = in_vars
        self.out_vars = out_vars
        self.operation = operation
    
# IGNORE UNTIL QUANTUM DONE
# Stores operation to be performed, variables used and where they are being assigned to
class ClassicalCommand(Command):
    command = None
    
    in_vars = None
    out_vars = None
    
    def __init__(self) -> None:
        pass