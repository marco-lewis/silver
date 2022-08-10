# Z3 Notes

- Custom solvers (those made using tactics) cannot get a unsat core

- 'Axioms' are given using universal/existential quantifiers (Z3 probably views such statements as true and checks that any examples satisfy them)

- Solvers that use nlsat are reset and so do not benefit from incremental solving

- Non-linear real solver not integrated with other solvers yet? (https://stackoverflow.com/a/19662256)

- "arith-solver=6 uses a much more complete method for non-linear solving"

- grover_partial3 is incomplete but grover_fixed3 is fine (takes a long time to solve though me thinks). Need to use nlsat with smt tactic