import logging
from tests.check import check
import z3

check("ctrl1.slq", "ctrl1", z3.unsat)
check("ctrl2.slq", "ctrl2", z3.unsat)
check("ctrl3.slq", "ctrl3", z3.unsat)
# TODO: ctrl_else1 returns unkown
check("ctrl_else1.slq", "ctrl_else1", z3.unsat)
check("ctrl_else2.slq", "ctrl_else2", z3.unsat)