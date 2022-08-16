from tests.check import check
import z3

# Verification of Grover's Algorithm
# 1 Call
# 2 qubits - uses certainty
check("grover_fixed2.slq", "grover_fixed", z3.unsat)

# 2 Calls
# 3 qubits
# Verifications is fast but finding instance is v. slow
# TODO: Allow multiple flags (for this prob. bound)
check("grover_fixed3.slq", "grover_fixed", z3.unsat)
check("grover_fixed4.slq", "grover_fixed", z3.unsat)
check("grover_fixed5.slq", "grover_fixed", z3.unsat)
check("grover_fixed6.slq", "grover_fixed", z3.unsat)

# 3 Calls - 7-14
check("grover_fixed7.slq", "grover_fixed", z3.unsat)

# 4 Calls - 15- 24