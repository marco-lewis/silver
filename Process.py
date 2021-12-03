import Command

# Stores the command and memory together as a process
class Process():
    command = Command()
    # Change {} to a Memory() class?
    memory = {}
    
    def __init__(self) -> None:
        pass


class QuantumProcess(Process):
    def __init__(self) -> None:
        super().__init__()

# Store classical commands as Obligations?
class ClassicalProcess(Process):
    def __init__(self) -> None:
        super().__init__()