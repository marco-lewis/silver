from tests.check import check
import z3

# Verification of Deutsch-Jozsa
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
check("dj_fixed2.json", "fixed_dj", z3.unsat)
check("dj_fixed3.json", "fixed_dj", z3.unsat)
check("dj_fixed4.json", "fixed_dj", z3.unsat)
check("dj_fixed5.json", "fixed_dj", z3.unsat)
check("dj_fixed6.json", "fixed_dj", z3.unsat)
# Quite slow - exponential? (18s)
check("dj_fixed7.json", "fixed_dj", z3.unsat, timeout=60000)
check("dj_fixed8.json", "fixed_dj", z3.unsat, timeout=60000)