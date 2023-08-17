# SilVer: Silq Verification

SilVer (**Sil**q **Ver**ification) is an automated verification tool for Silq programs using the Z3 SMT solver. It allows users to specify behaviours they want their programs to follow and then verify that the program does meet the specification given.

## Installation

TBD

### Running Tests

While within the directory `<path_to_project>/verif-silq/`:

```python -m tests.test_<test_to_run>```

## Usage
Import SilVer into your python file:

`import silver`

Create a Python file that creates a `silver = silver.SilVer()` object and run:

`silver.verify_func(<path-to-silq-file>, <function-to-verify>)`
    
On the first run a spq file will be created which can be used to specify behaviour using SilSpeq. When ran again, SilVer will verify the function against the behaviour specified.

## Credits

SilVer was developed by [Marco Lewis](https://github.com/marco-lewis).

SilVer makes use of a fork of [Silq](https://github.com/eth-sri/silq) and the [Z3](https://github.com/Z3Prover/z3) SMT solver.

Other packages used can be found in the [requirements.txt](requirements.txt).

## License
SilVer is publically available under the MIT License. See [LICENSE](LICENSE) for full details.