# Exercises and Experiments from Program Proofs

This repository contains execercise solutions and related experiments done
while reading through __Program Proofs__ by K. Rustan M. Leino.

## Setup

[Install Dafny](https://github.com/dafny-lang/dafny/wiki/INSTALL)

## Verifying

To check the proofs for every chapter:

```
$ make
...
Verifying ch10.dfy
dafny verify --solver-log ch10.log ch10.dfy

Dafny program verifier finished with 14 verified, 0 errors
Verified all
```

## References

* https://mitpress.mit.edu/9780262546232/program-proofs/
* https://dafny.org/
