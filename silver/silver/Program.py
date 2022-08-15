from copy import deepcopy
from silver.Instruction import CMEAS, QOP, QPAR
from silver.Process import *
from silver.QuantumMemory import QuantumMemory
from silver.VarRef import VarRef

# Class for representation of programs from Silq
# Should convert JSON into processes
# As advance program, update memory for each instruction
# Then convert program to proof obligations using the ObligationGenerator

# TODO: Classical memory isn't getting copied over correctly (okay?)
# TODO: Combine quantum operations together (chiefly on single qubits) - get one matrix instead of n, reduces number of variables in SMT
# Loses idea of doing things step by step though
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
        self.controls[-1] = []
        
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

    # TODO: Correctly modify end memory
    def optimise(self):
        self.parallelise_quantum_ops()

    def parallelise_quantum_ops(self):
        counter = 0
        while counter + 1 < self.current_time:
            # Identify if current process is a quantum op or a quantum parallel
            proc, next_proc = self.quantum_processes[counter], self.quantum_processes[counter + 1]
            ctrl, next_ctrl = self.controls[counter], self.controls[counter + 1]
            if self.can_parallelise(proc, next_proc, ctrl, next_ctrl):
                # 1: Combine into quantum parallel
                if isinstance(proc.instruction, QOP): self.quantum_processes[counter].instruction = QPAR([proc.instruction])
                self.quantum_processes[counter].instruction.operations.append(next_proc.instruction)
                # 2: Decrement key values in quantum process and current_time
                self.decrement_processes(counter + 1)
            else: counter += 1

    def can_parallelise(self, proc:QuantumProcess, next_proc:QuantumProcess, ctrl, next_ctrl):
        b = (isinstance(proc.instruction, QOP) or isinstance(proc.instruction, QPAR)) 
        b = b and isinstance(next_proc.instruction, QOP) and ctrl == next_ctrl
        return b and not(self.intersecting_memory(proc.instruction, next_proc.instruction))

    def intersecting_memory(self, proc1 : QOP|QPAR, proc2 : QOP):
        intersecting = lambda a, b: a.arg.variable == b.arg.variable and a.arg.index == b.arg.index
        if isinstance(proc1, QOP): return intersecting(proc1, proc2)
        else: return any([intersecting(p, proc2) for p in proc1.operations])

    def decrement_processes(self, rem):
        self.current_time -= 1
        for i in range(rem, self.current_time):
            self.quantum_processes[i] = self.quantum_processes[i+1]
            self.classical_processes[i] = self.classical_processes[i+1]
            self.controls[i] = self.controls[i+1]
        del self.quantum_processes[self.current_time]
        del self.classical_processes[self.current_time]
        del self.controls[self.current_time]

    def __str__(self) -> str:
        quantum_str, classical_str, controls_str = "", "", ""
        for k in self.quantum_processes:
            quantum_str += str(k) + ": " + str(self.quantum_processes[k]) + "\n"
            classical_str += str(k) + ": " + str(self.classical_processes[k]) + "\n"
            controls_str += str(k) + ": " + str(self.controls[k]) + "\n"
        return "Quantum\n" + quantum_str + "\nClassical\n" + classical_str + "\nControls\n" + controls_str