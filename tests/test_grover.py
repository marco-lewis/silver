import logging
from tests.check import check, folder
from tests.log_settings import setup_logger
import z3

# Verification of Grover's Algorithm
logger = setup_logger("grover.log")
# 1 Call
# 2 qubits - uses certainty
avg_setup, avg_solve = check("grover_fixed2.slq", "grover_fixed", z3.unsat, runs=10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("grover_fixed2.slq", "grover_fixed", z3.unsat, spq_file=folder + "grover_fixed2alt.spq", runs=10)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
# avg_setup, avg_solve = check("grover_partial3.slq", "grover_partial", z3.unsat, runs=10)
# logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))

# 2 Calls
avg_setup, avg_solve = check("grover_fixed3.slq", "grover_fixed", z3.unsat)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
# 3 Calls - 4-14?
avg_setup, avg_solve = check("grover_fixed4.slq", "grover_fixed", z3.unsat)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("grover_fixed5.slq", "grover_fixed", z3.unsat)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("grover_fixed6.slq", "grover_fixed", z3.unsat)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))
avg_setup, avg_solve = check("grover_fixed7.slq", "grover_fixed", z3.unsat)
logger.info("Setup average: %s, Run average: %s", str(avg_setup), str(avg_solve))