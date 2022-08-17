from tests.check import check
import z3

# Verification of GHZ States
check("ghz2.slq", "ghz", z3.unsat, verbose=True, show_objects=True)