from Process import *

# Class for representation of programs from Silq
# Should convert JSON into processes
# As advance program, update memory for each command
# Then convert program to proof obligations using the ObligationGenerator
class Program():
    current_time = 0
    quantum_processes = {}
    classical_processes = {}
    
    def __init__(self) -> None:
        pass
    
    def add_quantum_process(self, command, memory):
        self.current_time += 1
        self.quantum_process[self.current_time] = QuantumProcess(command, memory) 
        self.classical_processes[self.current_time] = None
        
    def add_classical_process(self, command, memory):
        pass