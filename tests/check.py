import logging
import sys
sys.path.append('../silver')

from silver.silver.SilVer import SilVer
from silver.silver.utils import DREAL, Z3

import z3

folder = "examples/Silq_Programs/"
logger = logging.getLogger("check")
t = 3 * 60 * 60 * 1000

def check(json_file, func, expected, log_level=logging.INFO, spq_file=None, stats=False, timeout=t, seed=3, check_store=False, mode=Z3, runs=1):
    times = {"setup": [], "solve": []}
    logger.setLevel(log_level)
    logger.info("Starting check on %s in %s", func, json_file)

    silver = SilVer(timeout=timeout, seed=seed, check_store=check_store)

    for i in range(runs):
        sat, model = silver.verify_func(folder + json_file, func, log_level=log_level, spq_file=spq_file, mode=mode)
        if sat == expected: logger.info("Test passed as expected")
        else: logger.error("Expected %s but got %s", expected, sat)

        if mode == Z3:
            if sat == z3.sat:
                logger.debug("Model/CEX:\n%s", model)
                f = z3.Function('f', z3.IntSort(), z3.IntSort())
                if f in model: logger.debug('Function: %s', model[f])
            if sat == z3.unsat: logger.debug("Unsat core:\n%s", silver.solver.unsat_core())
            if sat == z3.unknown: logger.error('Reason: %s', silver.solver.reason_unknown())
            silver_stats = silver.solver.statistics()
            try: logger.info("Solver time to solve (s) %s", silver_stats.get_key_value('time'))
            except: logger.warn("Unable to get time (possibly 0)")
            if stats: logger.info("Stats:\n%s", silver_stats)
            time_dict = silver.get_times()
            times["setup"].append(time_dict["setup"])
            times["solve"].append(time_dict["solve"])
            
        if mode == DREAL:
            logger.error("No stats for dreal yet")
        
        logger.info("Done.\n")
        sys.stdout.flush()
    return sum(times["setup"])/runs, sum(times["solve"])/runs