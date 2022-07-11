from tests.check import check
import z3

# Verification of Deutsch's algorithm
check("deutsch.json", "deutsch", z3.unsat)
check("deutsch_anc.json", "deutsch", z3.unsat)
# BUG: prog_obl not sat - related to measurement and forgetting
check("deutsch_anc2.json", "deutsch", z3.unsat)
# Verification fail on purpose - gives a model
# BUG: prog_obl not sat
check("deutsch_anc_fail.json", "deutsch", z3.unsat)