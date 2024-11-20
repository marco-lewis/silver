from silver.silver.SilVer import SilVer

silver = SilVer()
obs = silver.get_speq_obs("examples/Silq_Programs/dj_general.spq", hyperparameters={'n': 2})

print(obs)