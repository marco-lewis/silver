from tests.check import check
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
check("dj_fixed2.json", "fixed_dj", z3.unsat)
check("dj_fixed3.json", "fixed_dj", z3.unsat)
check("dj_fixed4.json", "fixed_dj", z3.unsat)
check("dj_fixed5.json", "fixed_dj", z3.unsat)
check("dj_fixed6.json", "fixed_dj", z3.unsat)
check("dj_fixed7.json", "fixed_dj", z3.unsat, timeout=60000)
# Returns Unkown < 180s
check("dj_fixed8.json", "fixed_dj", z3.unsat)