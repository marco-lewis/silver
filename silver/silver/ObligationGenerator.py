from math import floor
from typing import List
from z3 import *

from silver.silspeq.SilSpeqZ3Interpreter import Equiv
from silver.silver.ClassicalMemory import ClassicalMemory
from silver.silver.complex import *
from silver.silver.ComplexVector import *
from silver.silver.Instruction import *
from silver.silver.Process import ClassicalProcess, QuantumProcess
from silver.MeasureOptions import *
from silver.silver.QuantumMemory import QuantumMemory
from silver.silver.QuantumOps import *
from silver.silver.utils import *

# ENHANCE: Handle return statements differently based on quantum or classical

class ObilgationGenerator:
    def __init__(self, config = {}):
        self.__config = config
    
    def make_classical_process_obligation(self, c_process : ClassicalProcess, prev_mem : ClassicalMemory, control : list) -> list[BoolRef]:
        instruction = c_process.instruction
        if isinstance(instruction, CMEAS):
            return self.cmeas_obligation(instruction, prev_mem, c_process.end_memory)
        if isinstance(instruction, RETURN):
            # TODO: fetch return variables differently depending on what is being returned
            to_return = Int(prev_mem.get_obligation_variable(instruction.value_refs[0].variable))
            return_z3var = Int(instruction.function_name + "_ret")
            return [return_z3var == to_return]
        raise Exception("GenerationError: Unable to make obligation for instruction " +  repr(instruction))
    
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
        if isinstance(instruction, QOP):
            rhs = self.qop_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QPAR):
            rhs = self.qpar_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QPHASE):
            rhs = self.qphase_obligation(instruction, prev_mem, controls)
            obs += self.obligation_quantum_assignment(lhs, rhs)
            return obs
        if isinstance(instruction, QMEAS):
            return self.obligation_quantum_measurement(q_process, prev_mem, self.__config[MEASURE_OPTION])
        if isinstance(instruction, QFORGET):
            return self.obligation_quantum_forget(q_process, prev_mem)
        if isinstance(instruction, RETURN):
            return [True]
        raise Exception("GenerationError: Unable to make obligation for instruction " +  repr(instruction))
    
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
    
    def qop_obligation(self, instruction : QOP, prev_mem : QuantumMemory, controls : list):
        loc = prev_mem.get_loc(instruction.arg.variable, instruction.arg.index)
        matrix = self.matrix_from_string(instruction.operation)
        op = self.make_operation([loc], [matrix], prev_mem, controls)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))

    def qpar_obligation(self, instruction : QPAR, prev_mem : QuantumMemory, controls : list):
        locs = [prev_mem.get_loc(inst.arg.variable, inst.arg.index) for inst in instruction.operations]
        matrices = [self.matrix_from_string(inst.operation) for inst in instruction.operations]
        op = self.make_operation(locs, matrices, prev_mem, controls)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))

    def qphase_obligation(self, instruction : QPHASE, prev_mem : QuantumMemory, controls : list):
        phase = PHASE(instruction.phase)
        op = self.make_operation([], [], prev_mem, controls, phase=phase)
        return self.obligation_operation(op, self.quantum_memory_to_literals(prev_mem))
        
    # TODO: Fix bug with if x {...}
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
    
    def make_control_vector(self, prev_mem : QuantumMemory, controls : list):
        size = prev_mem.get_total_size()
        states = 2**size
        if controls == []: return ID_N(states)

        vars, control_ops = self.get_control_variables_and_ops(controls)
        control_locs = [prev_mem.get_loc_from_VarRef(var) for var in vars]
        control_sizes = [var.index if var.index else prev_mem.get_size(var.variable) for var in vars]

        F = [0]*states
        for state in range(states):
            bitstate = bin(state)[2:].zfill(size)
            control_states = [int(bitstate[size-l-s:size-l], 2) for l, s in zip(control_locs, control_sizes)]
            control_term = [op(s) for s, op in zip(control_states, control_ops)]
            F[state] = z3.simplify(If(And([c for c in control_term]), RealVal(1), RealVal(0)))
        return F

    def get_control_variables_and_ops(self, controls : list):
        vars = []
        ops = []
        for control in controls:
            if isinstance(control, QOP):
                vars.append(control.arg)
                ops.append(lambda t: control.operation(t) == 1)
            if isinstance(control, BOOLOP):
                v, f = self.get_control_variable_and_function(control.left)
                if v : ops.append(lambda x: control.comparitor(f(x), control.right))
                else:
                    v, f = self.get_control_variable_and_function(control.right)
                    ops.append(lambda x: control.comparitor(control.left, f(x)))
                vars.append(v)
        return vars, ops

    def get_control_variable_and_function(self, control):
        if isinstance(control, QOP): return control.arg, lambda t: control.operation(t)
        if isinstance(control, VarRef): return control, lambda t: t
        raise Exception("Unable to handle " + str(control))

    def obligation_quantum_assignment(self, lhs, rhs):
        if len(lhs) != len(rhs): raise Exception("LengthError: lengths of lists don't match")
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
        meas_obligations = []
        if RAND in measure_option: pass
        if HIGH_PROB in measure_option:
            meas_obligations += self.obligation_qmeas_with_high_prob(variable, probs_z3_vars, classical_value, prob_bound=self.__config[MEASURE_BOUND])
        if CERTAINTY in measure_option:
            meas_obligations += self.obligation_qmeas_with_certainty(variable, probs_z3_vars, classical_value)
        if SPECIFIC_VALUE in measure_option:
            meas_obligations += self.obligation_qmeas_with_specific_value(variable, probs_z3_vars, classical_value, self.__config[MEASURE_MARK])
        for meas_value in range(2**size): meas_obligations.append(Implies(probs_z3_vars[meas_value] == 0, classical_value != meas_value))

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
                post_prev_eq0 = And([And(Implies(prev_var.r == 0, post_var.r == 0), Implies(prev_var.i == 0, post_var.i == 0))
                                 for (post_var, prev_var) in zip(post_z3_vars, prev_mem_locs)])
                post_prev_eq1 = And([norm * post_var.r == prev_var.r for (post_var, prev_var) in zip(post_z3_vars, prev_mem_locs)])
                post_prev_eq2 = And([norm * post_var.i == prev_var.i for (post_var, prev_var) in zip(post_z3_vars, prev_mem_locs)])
                meas_possibilities.append(And(classical_value == meas_value, post_prev_eq0, post_prev_eq1, post_prev_eq2))
            post_state_obligations += [simplify(Or(post_state_obligations))]
        else: post_state_obligations.append(True)

        return obligations + meas_obligations + post_state_obligations
    
    def obligation_qmeas_with_specific_value(self, var, probs_z3_vars, classical_value, mark):
        max_prob = Real('hprob_' + var)
        obligations = [And([max_prob >= p for p in probs_z3_vars])]
        obligations += [Equiv(max_prob == probs_z3_vars[i], mark == i)
                        for i in range(len(probs_z3_vars))]
        obligations.append(classical_value == mark)
        return obligations

    def obligation_qmeas_with_certainty(self, var, probs_z3_vars, value):
        meas_cert = Bool('meas_cert')
        obligations = [Equiv(Or([p == 1 for p in probs_z3_vars]), meas_cert == True)]
        obligations += [Equiv(1 == probs_z3_vars[i], value == i)
                        for i in range(len(probs_z3_vars))]
        return obligations
    
    def obligation_qmeas_with_high_prob(self, var, probs_z3_vars, value, prob_bound=1/2):
        obligations = [Implies(value == i, prob_bound <= probs_z3_vars[i])
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
        # Z3 BUG: Summation is causing major slow down
        # forget_sum = Real("forget_" + instruction.variable.variable)
        # obligations = [s == forget_sum, forget_sum == 1]
        
        # Set new state based on prev. variables
        if new_vars != []: obligations += [new == prev for (new, prev) in zip(new_vars, prev_vars_at_value)]
        return obligations
    
    def obligation_operation(self, operation, obligations):
        out_obligations = []
        for row in operation:
            out_obligations.append(Sum([to_complex(row[col]) * obligations[col] for col in range(len(row))]))
        return out_obligations
    
    def matrix_from_string(self, op):
        if op == 'X': return X
        if op == 'Y': return Y
        if op == 'Z\'': return Z
        if op == 'H': return H
        raise Exception("ConversionError: no matrix for " + op)