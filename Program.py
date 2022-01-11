from copy import deepcopy
from Instruction import CMEAS
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
        self.controls = {}

    def add_classical_process(self, command, memory):
        pass
            
    def add_quantum_process(self, command, new_memory, controls = []):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=new_memory, command=command) 
        self.classical_processes[self.current_time] = ClassicalProcess(end_memory=self.copy_current_classical_memory() ,command=ClassicalCommand())
        self.controls[self.current_time] = controls
        self.current_time += 1

    def add_quantum_to_classical(self, command : Command, new_quantum_memory, new_c_var, controls = []):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=new_quantum_memory, command=command)
        new_c_mem = self.copy_current_classical_memory()
        new_c_mem.add_var(new_c_var)
        q_var = command.instruction.variable_ref.variable
        
        self.classical_processes[self.current_time] = ClassicalProcess(end_memory=new_c_mem ,command=ClassicalCommand(instruction=CMEAS(q_var, new_c_var)))
        self.controls[self.current_time] = controls
        self.current_time += 1
    
    def get_current_quantum_memory(self) -> QuantumMemory:
        if self.quantum_processes:
            return self.quantum_processes[self.current_time - 1].end_memory
        return QuantumMemory()
    
    def copy_current_classical_memory(self):
        try:
            classical_mem = ClassicalMemory()
            classical_mem.c_mem = deepcopy(self.classical_processes[self.current_time - 1].end_memory)
            return classical_mem
        except:
            return ClassicalMemory()
        
    def __str__(self) -> str:
        quantum_str = self.quantum_processes.__str__()
        classical_str = self.classical_processes.__str__()
        return "Quantum: " + quantum_str + "\nClassical: " + classical_str + "\nControls: " + str(self.controls)