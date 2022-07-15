from tests.check import check
import z3

# Grover Reversed
check("grover_rev2.json", "grover_rev", z3.unsat)
check("grover_rev3.json", "grover_rev", z3.unsat)
check("grover_rev7.json", "grover_rev", z3.unsat)

# Verification of Grover's Algorithm
# 1 Call
# 2 qubits - uses certainty
check("grover_fixed.json", "grover_fixed", z3.unsat)

# 2 Calls
# 3 qubits - problems with measurement/probability
# Likely causing check to be unknown
# Setting WHP bound to be 1/2 ignores timeout and causes SilVer to take ~45s
check("grover_fixed2.json", "grover_fixed", z3.unsat)
# 4 qubits
# 5 qubits
# 6 qubits

# 3 Calls - 7-14
# 4 Calls - 15- 24