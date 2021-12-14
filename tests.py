from SilVer import SilVer

def check(json_file, func, model=False):
    silver = SilVer()
    sat = silver.verify_func(json_file, func)
    print(sat)
    if model:
        print(silver.solver.model())
    
check("test_singlevar.json", "main")
check("test_unitary.json", "main")
check("types.json", "main")
check("uint.json", "main")