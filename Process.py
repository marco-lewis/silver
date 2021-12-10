from Command import *

# Stores the command and memory together as a process
class Process():
    # Change {} to a Memory() class?
    def __init__(self, end_memory = {}, command = Command()) -> None:
        self.end_memory = end_memory
        self.command = command

class QuantumProcess(Process):
    command = QuantumCommand()
    def __init__(self, end_memory = {}, command = Command()) -> None:
        super().__init__(end_memory, command)
        
    def __repr__(self) -> str:
        return "QuantumProcess(" + repr(self.end_memory) + "," + repr(self.command) + ")"

# IGNORE UNTIL QUANTUM DONE
# Store classical commands as Obligations?
class ClassicalProcess(Process):
    def __init__(self) -> None:
        super().__init__()