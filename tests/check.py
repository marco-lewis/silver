import logging
import sys
sys.path.append('../silver')

from silver.silver.SilVer import SilVer
from silver.silver.utils import DREAL, DREAL_SAT, DREAL_UNSAT, Z3

from numpy import std
import z3

folder = "examples/Silq_Programs/"
logger = logging.getLogger("check")
THREE_HOURS = 3 * 60 * 60 * 1000

def check(json_file, func, expected, log_level=logging.INFO, silver_log_level=logging.ERROR, spq_file=None, stats=True, timeout=THREE_HOURS, seed=1, check_store=False, mode=Z3, delta=0.0001, runs=10):
    times = {"setup": [], "solve": []}
    logger.setLevel(log_level)
    logger.info("Starting check on %s in %s", func, json_file)

    silver = SilVer(timeout=timeout, seed=seed, check_store=check_store)

    for i in range(runs):
        logger.info("Run %s", i + 1)
        sat, model = silver.verify_func(folder + json_file, func, log_level=silver_log_level, spq_file=spq_file, mode=mode, delta=delta)
        if sat == expected: logger.info("Test passed as expected")
        else: logger.error("Expected %s but got %s", expected, sat)

        if mode == Z3:
            if sat == z3.sat: logger.debug("Model/CEX:\n%s", model)
            if sat == z3.unsat: logger.debug("Unsat core:\n%s", silver.solver.unsat_core())
            if sat == z3.unknown: logger.error('Reason: %s', silver.solver.reason_unknown())
            if stats: logger.info("Stats:\n%s", silver.solver.statistics())
            
        if mode == DREAL:
            if sat == DREAL_SAT: 
                logger.debug("delta:%s", silver.delta)
                logger.debug("Model/CEX:\n%s", model)
            if sat == DREAL_UNSAT: logger.debug("Unable to produce unsat core")
            if stats: logger.error("No stats for dreal")

        time_dict = silver.get_times(mode=mode)
        logger.info("Setup time: %s, Verification time: %s", time_dict["setup"], time_dict["solve"])
        times["setup"].append(time_dict["setup"])
        times["solve"].append(time_dict["solve"])
        logger.info("Done.")
        sys.stdout.flush()
    return times

def report_results(logger:logging.Logger, times, runs=10):
    logger.info("Setup average: %s, Run average: %s", str(sum(times["setup"])/runs), str(sum(times["solve"])/runs))
    logger.info("Setup standard deviation: %s, Run standard deviation: %s", str(std(times["setup"])), str(std(times["solve"])))