from ClassicalMemory import ClassicalMemory
from Instruction import Instruction
from QuantumMemory import QuantumMemory

# Stores the instruction and memory together as a process
class Process():
    # Change {} to a Memory() class?
    def __init__(self, instruction : Instruction, end_memory = {}) -> None:
        self.end_memory = end_memory
        self.instruction = instruction

class QuantumProcess(Process):
    instruction = Instruction()
    end_memory = QuantumMemory()
    def __init__(self, instruction : Instruction, end_memory = QuantumMemory()) -> None:
        super().__init__(instruction = instruction, end_memory=end_memory)
        
    def __repr__(self) -> str:
        return "QuantumProcess(" + repr(self.instruction) + "," + repr(self.end_memory) + ")"

class ClassicalProcess(Process):
    instruction : Instruction
    end_memory : ClassicalMemory
    
    def __init__(self, instruction : Instruction, end_memory = ClassicalMemory()) -> None:
        super().__init__(instruction = instruction, end_memory=end_memory)
                
    def __repr__(self) -> str:
        return "ClassicalProcess(" + repr(self.instruction) + "," + repr(self.end_memory) + ")"