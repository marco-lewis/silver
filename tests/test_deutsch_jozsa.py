from tests.check import check
import z3

folder = "examples/Silq_Programs/"

# Verification of Deutsch-Jozsa
# Start thinking on BMC
# Give variable that is being BMC'd and check program with different sizes
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
check("dj_fixed2.slq", "fixed_dj", z3.unsat, spq_file=folder+"dj_fixed2const.spq")
check("dj_fixed2.slq", "fixed_dj", z3.unsat, spq_file=folder+"dj_fixed2bal.spq")
# BUG: Can check one assertion in post but not both
check("dj_fixed2.slq", "fixed_dj", z3.unsat)
check("dj_fixed3.slq", "fixed_dj", z3.unsat)
check("dj_fixed4.slq", "fixed_dj", z3.unsat)
check("dj_fixed5.slq", "fixed_dj", z3.unsat)
check("dj_fixed6.slq", "fixed_dj", z3.unsat)
check("dj_fixed7.slq", "fixed_dj", z3.unsat)
check("dj_fixed8.slq", "fixed_dj", z3.unsat)