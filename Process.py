from ClassicalMemory import ClassicalMemory
from Command import *
from QuantumMemory import QuantumMemory

# Stores the command and memory together as a process
class Process():
    # Change {} to a Memory() class?
    def __init__(self, end_memory = {}, command = Command()) -> None:
        self.end_memory = end_memory
        self.command = command

class QuantumProcess(Process):
    command = QuantumCommand()
    end_memory = QuantumMemory()
    def __init__(self, end_memory = QuantumMemory(), command = Command()) -> None:
        super().__init__(end_memory, command)
        
    def __repr__(self) -> str:
        return "QuantumProcess(" + repr(self.end_memory) + "," + repr(self.command) + ")"

class ClassicalProcess(Process):
    def __init__(self, end_memory = ClassicalMemory(), command = Command()) -> None:
        super().__init__(end_memory, command)
        
    def __repr__(self) -> str:
        return "ClassicalProcess(" + repr(self.end_memory) + "," + repr(self.command) + ")"