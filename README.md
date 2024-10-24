# SilVer: Silq Verification

SilVer (**Sil**q **Ver**ification) is an automated verification tool for Silq programs using the Z3 SMT solver. It allows users to specify behaviours they want their programs to follow and then verify that the program does meet the specification given.

## Installation

Requires Python 3.10.4

1. Preparing Silq
    1. Download/clone the following fork of Silq: https://github.com/marco-lewis/silq/tree/ast-file (make sure to be on the branch ast-file)
    2. Build Silq, following the instructions in the README
    3. Add the Silq folder to the path

2. Open a terminal in the `silver` directory.
3. Create the python environment: `python3.10 -m venv env`

4. Activate the environment: `source env/bin/activate`

5. Install requirements: `pip install -r requirements.txt`

### Running Tests

While within the directory `<path_to_project>/verif-silq/`:

```python -m tests.test_<test_to_run>```

## Docker
Alternatively, there is a Docker artifact available at https://zenodo.org/records/11395797

## Usage
Import SilVer into your python file:

`import silver`

Create a Python file that creates a `silver = silver.SilVer()` object and run:

`silver.verify_func(<path-to-silq-file>, <function-to-verify>)`
    
On the first run a spq file will be created which can be used to specify behaviour using SilSpeq. When ran again, SilVer will verify the function against the behaviour specified.

Full documentation to be released soon.

## Reference
If you use the tool in your research, please add a citation to the publication:
```
@INPROCEEDINGS{Lewis24,
  author={Lewis, Marco and Zuliani, Paolo and Soudjani, Sadegh},
  booktitle={2024 IEEE International Conference on Quantum Software (QSW)}, 
  title={Automated Verification of Silq Quantum Programs using SMT Solvers}, 
  year={2024},
  volume={},
  number={},
  pages={125-134},
  keywords={Silver;Computer languages;Adaptation models;Quantum computing;Quantum entanglement;Computational modeling;Programming;Quantum programs;Program verification;SMT Solvers;Silq;Intermediate representation},
  doi={10.1109/QSW62656.2024.00027}
}
```

## Credits

SilVer was developed by [Marco Lewis](https://github.com/marco-lewis).

SilVer makes use of a fork of [Silq](https://github.com/eth-sri/silq) and the [Z3](https://github.com/Z3Prover/z3) SMT solver.

Other packages used can be found in the [requirements.txt](requirements.txt).

## License
SilVer is publically available under the MIT License. See [LICENSE](LICENSE) for full details.