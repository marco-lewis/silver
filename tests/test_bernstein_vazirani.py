from tests.check import check
import z3

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
check("bv_fixed2.json", "fixed_bv", z3.unsat)