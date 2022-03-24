from copy import deepcopy
from Instruction import CMEAS
from Process import *
from QuantumMemory import QuantumMemory
from VarRef import VarRef

# Class for representation of programs from Silq
# Should convert JSON into processes
# As advance program, update memory for each instruction
# Then convert program to proof obligations using the ObligationGenerator

# TODO: Classical memory isn't getting copied over correctly
class Program():
    quantum_processes : dict[int, QuantumProcess]
    classical_processes : dict[int, ClassicalProcess]
    
    def __init__(self) -> None:
        self.current_time = 0
        self.quantum_processes = {}
        self.classical_processes = {}
        self.controls = {}
        self.quantum_processes[-1] = QuantumProcess()
        self.classical_processes[-1] = ClassicalProcess(Instruction())
        
    def iterate_time(self):
        self.current_time += 1

    def add_classical_process(self, instruction : Instruction, memory : ClassicalMemory, controls = []):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=self.copy_current_quantum_memory(), instruction=Instruction()) 
        self.classical_processes[self.current_time] = ClassicalProcess(end_memory=memory, instruction=instruction)
        self.controls[self.current_time] = controls
        self.iterate_time()
            
    def add_quantum_process(self, instruction : Instruction, new_memory : QuantumMemory, controls = []):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=new_memory, instruction=instruction) 
        c_mem = self.copy_current_classical_memory()
        self.classical_processes[self.current_time] = ClassicalProcess(end_memory=c_mem, instruction=Instruction())
        self.controls[self.current_time] = controls
        self.iterate_time()
        
    # TODO: Change name to just measurement process?
    def add_quantum_to_classical(self, instruction : Instruction, new_quantum_memory, classical_instruction : Instruction, controls = []):
        self.quantum_processes[self.current_time] = QuantumProcess(end_memory=new_quantum_memory, instruction=instruction)
        new_c_mem = self.copy_current_classical_memory()
        new_c_mem.add_var(classical_instruction.classical_ref.variable)
        
        self.classical_processes[self.current_time] = ClassicalProcess(end_memory=new_c_mem ,instruction=classical_instruction)
        self.controls[self.current_time] = controls
        self.iterate_time()
        
    def add_quantum_to_initial_memory(self, var, size):
        if not(-1 in self.quantum_processes.keys()):
            self.quantum_processes[-1] = QuantumProcess()
        self.quantum_processes[-1].end_memory.append(var, size)
        return
    
    def add_classical_to_initial_memory(self, var, size):
        if not(-1 in self.classical_processes.keys()):
            self.classical_processes[-1] = ClassicalProcess()
        self.classical_processes[-1].end_memory.append(var, size)
        return
        
    def get_current_quantum_memory(self) -> QuantumMemory:
        if self.quantum_processes:
            return self.quantum_processes[self.current_time - 1].end_memory
        return QuantumMemory()
    
    def get_current_classical_memory(self) -> ClassicalMemory:
        if self.classical_processes:
            return self.classical_processes[self.current_time - 1].end_memory
        return ClassicalMemory()
    
    def copy_current_classical_memory(self):
        try:
            classical_mem = ClassicalMemory()
            classical_mem.registers = deepcopy(self.classical_processes[self.current_time - 1].end_memory.registers)
            return classical_mem
        except:
            return ClassicalMemory()
        
    def copy_current_quantum_memory(self):
        try:
            quantum_memory = QuantumMemory()
            quantum_memory.registers = deepcopy(self.quantum_processes[self.current_time - 1].end_memory.registers)
            return quantum_memory
        except:
            return QuantumMemory()
        
    def is_variable_ref_quantum(self, var_ref : VarRef):
        try:
            # TODO: change to handle lists/multiple variables
            var = var_ref.variable
            if self.quantum_processes[self.current_time - 1].end_memory.registers[var]:
                return True
        except:
            return False
        
    def __str__(self) -> str:
        quantum_str = self.quantum_processes.__str__()
        classical_str = self.classical_processes.__str__()
        return "Quantum: " + quantum_str + "\nClassical: " + classical_str + "\nControls: " + str(self.controls)