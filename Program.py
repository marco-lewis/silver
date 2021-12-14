from Process import *
from QuantumMemory import QuantumMemory

# Class for representation of programs from Silq
# Should convert JSON into processes
# As advance program, update memory for each command
# Then convert program to proof obligations using the ObligationGenerator
class Program():
    def __init__(self) -> None:
        self.current_time = 0
        self.quantum_processes = {}
        self.classical_processes = {}  
    
    def add_quantum_process(self, command, new_memory):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=new_memory, command=command) 
        self.classical_processes[self.current_time] = None
        self.current_time += 1

    def add_classical_process(self, command, memory):
        pass
    
    def get_current_quantum_memory(self) -> QuantumMemory:
        if self.quantum_processes:
            return self.quantum_processes[self.current_time - 1].end_memory
        return QuantumMemory()
        
    def __str__(self) -> str:
        quantum_str = self.quantum_processes.__str__()
        classical_str = self.classical_processes.__str__()
        return "Quantum: " + quantum_str + "\nClassical: " + classical_str