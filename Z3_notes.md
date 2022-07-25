# Z3 Notes

- Custom solvers (those made using tactics) cannot get a unsat core

- 'Axioms' are given using universal/existential quantifiers (Z3 probably views such statements as true and checks that any examples satisfy them)

- Solvers that use nlsat are reset and so do not benefit from incremental solving

- Non-linear real solver not integrated with other solvers yet? (https://stackoverflow.com/a/19662256)