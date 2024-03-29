import logging
from typing import List
import numbers
import numpy as np
from z3 import *

from silver.silspeq.SilSpeqZ3Interpreter import Equiv
from silver.silver.ClassicalMemory import ClassicalMemory
from silver.silver.complex import *
from silver.silver.ComplexVector import *
from silver.silver.Instruction import *
from silver.silver.Process import ClassicalProcess, QuantumProcess
from silver.silver.Program import Program
from silver.MeasureOptions import *
from silver.silver.QuantumMemory import QuantumMemory
from silver.silver.QuantumOps import *
from silver.silver.utils import *

# ENHANCE: Handle return statements differently based on quantum or classical

logger = logging.getLogger("OblGen")

class ObilgationGenerator:
    def __init__(self, program : Program, config = {}):
        self.program = program
        self.__config = config
    
    def make_obligations(self):
        obs : list[BoolRef] = []
        for key, creg in self.program.classical_processes[-1].end_memory.registers.items():
            obs.append(creg.get_z3speqarg() == creg.get_z3instance())
        for time in range(self.program.current_time):
            if self.program.quantum_processes[time].instruction != Instruction():
                prev_memory = self.get_prev_quantum_memory(time)
                if time == 0: obs += self.make_quantum_memory_initial_obligations(prev_memory)
                process_obligation = self.make_quantum_process_obligation(self.program.quantum_processes[time], prev_memory, self.program.controls[time])
                obs += process_obligation
            if self.program.classical_processes[time].instruction != Instruction():
                # TODO: Handle classical obligation
                prev_memory = self.get_prev_classical_memory(time)
                classical_obligation = self.make_classical_process_obligation(self.program.classical_processes[time], prev_memory, self.program.controls[time])
                obs += classical_obligation
        return obs
    
    def get_prev_quantum_memory(self, time): return self.program.quantum_processes[time - 1].end_memory
    
    def get_prev_classical_memory(self, time): return self.program.classical_processes[time - 1].end_memory

    def make_classical_process_obligation(self, c_process : ClassicalProcess, prev_mem : ClassicalMemory, controls : list) -> list[BoolRef]:
        instruction = c_process.instruction
        if isinstance(instruction, CMEAS):
            return self.cmeas_obligation(instruction, prev_mem, c_process.end_memory)
        if isinstance(instruction, RETURN):
            # TODO: fetch return variables differently depending on what is being returned
            to_return = Int(prev_mem.get_obligation_variable(instruction.value_refs[0].variable))
            return_z3var = Int(instruction.function_name + "_ret")
            return [return_z3var == to_return]
        if isinstance(instruction, COP):
            z3_var = self.program.get_z3var_from_VarRef(instruction.variable)
            value = self.interpret_val(instruction.value)
            ctrl_obls = self.get_classical_control_obls(controls)
            if prev_mem.is_stored(instruction.variable.variable):
                prev_z3_var = prev_mem.get_z3variable(instruction.variable)
                return [z3.simplify(If(And(ctrl_obls), z3_var == value, z3_var == prev_z3_var))]
            return [z3.simplify(If(And(ctrl_obls), z3_var == value, True))]
        log_error("GenerationError: Unable to make obligation for instruction %s", logger, repr(instruction))
    
    def cmeas_obligation(self, instruction: CMEAS, prev_memory : ClassicalMemory, end_memory : ClassicalMemory):
        meas = Int('meas_' + instruction.quantum_ref.variable)
        value = Int(end_memory.get_obligation_variable(instruction.classical_ref.variable))
        return [value == meas]

    # Adding bounds to the lhs make it harder to find sat instances 
    def make_quantum_process_obligation(self, q_process : QuantumProcess, prev_mem : QuantumMemory, controls : list) -> list[BoolRef]:
        instruction = q_process.instruction
        lhs = self.quantum_memory_to_literals(q_process.end_memory)
        obs = []
        if isinstance(instruction, QINIT):
            rhs = self.qinit_obligation(instruction, prev_mem)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        elif isinstance(instruction, QOP):
            rot = 0
            if isinstance(instruction, QROT):
                rot = self.interpret_val(instruction.rot)
            rhs = self.qop_obligation(instruction, prev_mem, controls, rot=rot)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        elif isinstance(instruction, QPAR):
            rhs = self.qpar_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        elif isinstance(instruction, QPHASE):
            rhs = self.qphase_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        elif isinstance(instruction, QMEAS):
            return self.obligation_quantum_measurement(q_process, prev_mem, self.__config[MEASURE_OPTION])
        elif isinstance(instruction, QFORGET):
            return self.obligation_quantum_forget(q_process, prev_mem)
        elif isinstance(instruction, RETURN):
            return [True]
        log_error("GenerationError: Unable to make obligation for instruction %s", logger, repr(instruction))
    
    def quantum_memory_to_literals(self, memory : QuantumMemory):
        return [Complex(string) for string in memory.get_obligation_variables()]
    
    def qinit_obligation(self, instruction : QINIT, prev_mem : QuantumMemory):
        if prev_mem.is_empty(): return self.obligation_quantum_literal(instruction.size, instruction.value)
        lits = self.quantum_memory_to_literals(prev_mem)
        obligations = []
        prev_size = 2**(prev_mem.get_total_size())
        for j in range(2**instruction.size):
            obligations += [0 if j != instruction.value else lits[i] for i in range(prev_size)]
        return obligations
    
    def make_quantum_memory_initial_obligations(self, initial_memory : QuantumMemory):
        lits = self.quantum_memory_to_literals(initial_memory)
        if lits == []: return []
        sum_of_sqrs = 0
        for i in range(2**(initial_memory.get_total_size())):
            sum_of_sqrs += lits[i].len_sqr()
        obligations = [sum_of_sqrs == 1]
        return obligations
    
    def qop_obligation(self, instruction : QOP, prev_mem : QuantumMemory, controls : list, rot = 0):
        loc = prev_mem.get_loc(instruction.arg.variable, instruction.arg.index)
        matrix = self.matrix_from_string(instruction.operation, rot=rot)
        op = self.make_operation([loc], [matrix], prev_mem, controls)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))

    def qpar_obligation(self, instruction : QPAR, prev_mem : QuantumMemory, controls : list):
        locs = [prev_mem.get_loc(inst.arg.variable, inst.arg.index) for inst in instruction.operations]
        matrices = [self.matrix_from_string(inst.operation) for inst in instruction.operations]
        op = self.make_operation(locs, matrices, prev_mem, controls)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))

    def qphase_obligation(self, instruction : QPHASE, prev_mem : QuantumMemory, controls : list):
        phase = PHASE(self.interpret_val(instruction.phase))
        op = self.make_operation([], [], prev_mem, controls, phase=phase)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
        
    def make_operation(self, op_locs, matrices, prev_mem : QuantumMemory, controls : list, phase = 1):
        s = prev_mem.get_total_size()
        U = np.array(self.make_quantum_op(op_locs, matrices, s))
        if not controls: return (phase*U).tolist()
        I = np.identity(2**s, dtype=int)
        F = np.array(self.make_control_vector(prev_mem, controls))
        return (I + (phase*U - I) * F[:, np.newaxis]).tolist()

    def make_quantum_op(self, locs : list, matrices : list, size : int):
        final_op = [[1]]
        for l in range(size):
            if l in locs: final_op = kronecker(matrices[locs.index(l)], final_op)
            else: final_op = kronecker(ID, final_op)
        return final_op
    
    def make_control_vector(self, prev_mem: QuantumMemory, controls : list):
        size = prev_mem.get_total_size()
        states = 2**size
        if controls == []: return ID_N(states)
        varrefs, control_ops = self.get_control_variables_and_ops(controls)
        control_qlocs, control_qops, control_qsizes = [], [], []
        for var, op in zip(varrefs, control_ops):
            if var.isquantum:
                control_qlocs.append(prev_mem.get_loc_from_VarRef(var))
                control_qops.append(op)
                control_qsizes.append(var.index if var.index else prev_mem.get_size(var.variable))
        classical_ctrls_obls = self.get_classical_control_obls(controls)

        F = [0]*states
        for state in range(states):
            bitstate = bin(state)[2:].zfill(size)
            control_states = [int(bitstate[size-l-s:size-l], 2) for l, s in zip(control_qlocs, control_qsizes)]
            control_term = [op(s) for s, op in zip(control_states, control_qops)]
            F[state] = z3.simplify(If(And([c for c in control_term] + classical_ctrls_obls), RealVal(1), RealVal(0)))
        return F
    
    def get_classical_control_obls(self, controls):
        varrefs, control_ops = self.get_control_variables_and_ops(controls)
        for varref in varrefs: varref.time -= 1
        control_cz3vars, control_cops = [], []
        for var, op in zip(varrefs, control_ops):
            if not(var.isquantum):
                control_cz3vars.append(self.program.get_z3var_from_VarRef(var))
                control_cops.append(op)
        classical_ctrls = []
        for z3_var, op in zip(control_cz3vars, control_cops):
            classical_ctrls.append(op(z3_var))
        return classical_ctrls if len(classical_ctrls) > 0 else [True]

    def get_control_variables_and_ops(self, controls : list):
        vars = []
        ops = []
        for control in controls:
            # TODO: Combine?
            if isinstance(control, UNARYOP):
                v, f = self.get_control_variable_and_function(control.arg)
                vars.append(v)
                ops.append(lambda x: control.op(f(x)) == 1)
            if isinstance(control, BINARYOP):
                v, f = self.get_control_variable_and_function(control.left)
                if v : ops.append(lambda x: control.op(f(x), control.right))
                else:
                    v, f = self.get_control_variable_and_function(control.right)
                    ops.append(lambda x: control.op(control.left, f(x)))
                vars.append(v)
        return vars, ops

    def get_control_variable_and_function(self, control):
        if isinstance(control, QOP): return control.arg, lambda t: control.operation(t)
        if isinstance(control, VarRef): return control, lambda t: t
        log_error("Unable to handle %s", logger, str(control))

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs): log_error("LengthError: lengths of lists don't match", logger)
        return [simplify(lhs[i] == rhs[i]) for i in range(len(lhs))]

    def obligation_quantum_literal(self, size, literal = 0):
        return [1 if i == literal else 0 for i in range(0, 2**size)]
            
    def obligation_quantum_measurement(self, q_process : QuantumProcess, prev_memory : QuantumMemory, measure_option=[HIGH_PROB]):
        instruction : QMEAS = q_process.instruction
        quantum_ref = instruction.quantum_ref
        variable = quantum_ref.variable
        index = quantum_ref.index
        
        # Set up labels for probabilities
        loc = prev_memory.get_loc(variable, index)
        size = prev_memory.get_size(variable)
        prob_strs = ["Pr_" + prev_memory.get_reg_string(variable) + "_" + str(i) 
                 for i in range(2**size)]
        probs_z3_vars = [Real(p) for p in prob_strs]

        # Obligations for probabilities
        obligations = []
        obligations.append(And([And(p <= 1, p >= 0) for p in probs_z3_vars]))
        probs_sum = Real("Pr_" + prev_memory.get_reg_string(variable) + "_sum")
        obligations.append(probs_sum == Sum(probs_z3_vars))
        obligations.append(probs_sum == 1)
        # Calculate probabilities based on amplitudes of memory
        memory_obligation_variables = [Complex(memory_str) for memory_str in prev_memory.get_obligation_variables()]
        for meas_value in range(len(probs_z3_vars)):
            mem_locs = [x for x in range(2**prev_memory.get_total_size()) 
                        if (x & (2**(size)- 1<<loc) == (meas_value) << loc)]
            s = [memory_obligation_variables[l].len_sqr() for l in mem_locs]
            obligations.append(probs_z3_vars[meas_value] == Sum(s))
        
        # Measurement options
        classical_value = Int('meas_' + variable)
        meas_obligations = [classical_value >= 0, classical_value < 2**size]
        if RAND in measure_option: pass
        if HIGH_PROB in measure_option:
            meas_obligations += self.obligation_qmeas_with_high_prob(variable, probs_z3_vars, classical_value, prob_bound=self.__config[MEASURE_BOUND])
        if CERTAINTY in measure_option:
            meas_obligations += self.obligation_qmeas_with_certainty(variable, probs_z3_vars, classical_value)
        if SPECIFIC_VALUE in measure_option:
            meas_obligations += self.obligation_qmeas_with_specific_value(variable, probs_z3_vars, classical_value, self.__config[MEASURE_MARK])
        for meas_value in range(2**size): meas_obligations.append(Implies(classical_value == meas_value, Not(probs_z3_vars[meas_value] == 0)))

        # State after measurement
        post_memory = q_process.end_memory
        post_state_obligations = []
        if not(post_memory.is_empty()):
            post_z3_vars = [Complex(obl_var) for obl_var in post_memory.get_obligation_variables()]
            meas_possibilities = []
            for meas_value in range(2**size):
                norm = Sqrt(probs_z3_vars[meas_value])
                post_state_obligations.append(norm >= 0)
                prev_mem_locs = [memory_obligation_variables[j] for j in range(len(memory_obligation_variables)) 
                                 if not((j & (2**size-1) << loc) ^ (meas_value << loc))]
                post_prev_eq = simplify(And([And(Implies(prev_var.r == 0, post_var.r == 0),
                                                 Implies(prev_var.i == 0, post_var.i == 0),
                                                 norm * post_var.r == prev_var.r,
                                                 norm * post_var.i == prev_var.i)
                                 for (post_var, prev_var) in zip(post_z3_vars, prev_mem_locs)]))
                meas_possibilities.append(And(classical_value == meas_value, post_prev_eq))
            post_state_obligations += [Or(meas_possibilities)]
        else: post_state_obligations.append(True)

        return obligations + meas_obligations + post_state_obligations
    
    def obligation_qmeas_with_specific_value(self, var, probs_z3_vars, classical_value, mark):
        obligations = []
        obligations += [Implies(And(classical_value == i, mark == i), And([probs_z3_vars[i] >= p for p in probs_z3_vars]))
                        for i in range(len(probs_z3_vars))]
        return obligations

    def obligation_qmeas_with_certainty(self, var, probs_z3_vars, classical_value):
        obligations = []
        obligations += [Or([p == 1 for p in probs_z3_vars])]
        obligations += [Implies(classical_value == i, probs_z3_vars[i] == 1)
                        for i in range(len(probs_z3_vars))]
        return obligations
    
    def obligation_qmeas_with_high_prob(self, var, probs_z3_vars, classical_value, prob_bound=1/2):
        obligations = [Implies(classical_value == i, prob_bound <= probs_z3_vars[i])
                        for i in range(len(probs_z3_vars))]
        return obligations
    
    def obligation_quantum_forget(self, q_process : QuantumProcess, prev_mem : QuantumMemory):
        instruction : QFORGET = q_process.instruction
        prev_vars = self.quantum_memory_to_literals(prev_mem)
        new_vars = self.quantum_memory_to_literals(q_process.end_memory)
        loc = prev_mem.get_loc_from_VarRef(instruction.variable)
        
        obligations = []
        
        # Check probability of value is 1
        # TODO: Check perform correct comparison
        prev_vars_at_value = [prev_vars[i] for i in range(len(prev_vars)) if i >> loc == instruction.value]
        s = simplify(Sum([q.len_sqr() for q in prev_vars_at_value]))
        forget_sum = Real("forget_" + instruction.variable.variable)
        obligations = [s == forget_sum, forget_sum == 1]
        
        # Set new state based on prev. variables
        if new_vars != []: obligations += [new == prev for (new, prev) in zip(new_vars, prev_vars_at_value)]
        return obligations
    
    def obligation_operation(self, operation, obligations):
        out_obligations = []
        for row in operation:
            out_obligations.append(Sum([to_complex(row[col]) * obligations[col] for col in range(len(row))]))
        return out_obligations
    
    def interpret_val(self, val):
        if isinstance(val, UNARYOP): return val.op(self.interpret_val(val.arg))
        if isinstance(val, BINARYOP): return val.op(self.interpret_val(val.left), self.interpret_val(val.right))
        if val == "pi": return np.pi
        if isinstance(val, numbers.Number): return val
        if isinstance(val, VarRef):
            if not(val.isquantum): return self.program.get_z3var_from_VarRef(val)
        # TODO: Fix in Silq fork
        if isinstance(val, QOP):
            if val.operation == 'X':
                z3var = self.program.get_z3var_from_VarRef(val.arg)
                if isinstance(z3var, BoolRef): return Not(z3var)
                else: return 1 - z3var
        log_error("TODO: an instruction (%s, %s) is not interpretted.", logger, val, type(val))
    
    def matrix_from_string(self, op, rot=0):
        if op == 'X': return X
        if op == 'Y': return Y
        if op == 'Z\'': return Z
        if op == 'H': return H
        if op == "rotX": return ROTX(rot)
        if op == "rotY": return ROTY(rot)
        if op == "rotZ": return ROTZ(rot)
        log_error("ConversionError: no matrix for %s", logger, op)