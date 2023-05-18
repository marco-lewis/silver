import logging
from tests.check import check, folder
import z3

# Verification of Grover's Algorithm
# 1 Call
# 2 qubits - uses certainty
check("grover_fixed2.slq", "grover_fixed", z3.unsat)
check("grover_fixed2.slq", "grover_fixed", z3.unsat, spq_file=folder + "grover_fixed2alt.spq")
check("grover_partial3.slq", "grover_partial", z3.unsat)

# 2 Calls
check("grover_fixed3.slq", "grover_fixed", z3.unsat)
# 3 Calls - 4-14?
check("grover_fixed4.slq", "grover_fixed", z3.unsat)
check("grover_fixed5.slq", "grover_fixed", z3.unsat)
check("grover_fixed6.slq", "grover_fixed", z3.unsat)
check("grover_fixed7.slq", "grover_fixed", z3.unsat)