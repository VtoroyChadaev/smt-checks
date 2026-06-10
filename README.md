# SMT experiments based on examples from the PIL doc

## Implemented checks
  - cyclic-missing-selector
     Encodes the CyclicExample scheme from the PIL doc; expected 
     to return unsat

  - cyclic-with-selector
     Adds SEL = [1,1,1,0]; expected to return sat

  - twobyteadd-underconstrained
     Encodes the TwoByteAdd scheme (only 2 rows) without range constraints for `carry` and `add`; expected to return sat

  - twobyteadd-constrained
     Encodes the TwoByteAdd scheme with proper range constraints; expected to return unsat (could return uknown if the scheme was large enough)

## Problems with specifications

### CyclicExample

```text
In PIL, constraints must be satisfied in every row transition, including last to first.
In CyclicExample it is handled using SEL polynomial. Without it, this scheme would be over-constrained.
It' s shown using cvc5 solver
```

### TwobyteADD

```text
There must be constraints in TwoByteAdd scheme, ensuring that all values are single bytes, but there aren't. So it's possible to cheat program restrictions. SMT solver is expected to find such values
```

## Usage examples:
you need cvc5 system-wide

`--show-model` is optional

run all tests

```bash
python3 manual-check.py --all [--show-model]
```

run cyclic-missing-selector

```bash
python3 manual-check.py --query cyclic-missing-selector [--show-model]
```

run cyclic-with-selector

```bash
python3 manual-check.py --query cyclic-with-selector [--show-model]
```

run twobyteadd-underconstrained

```bash
python3 manual-check.py --query twobyteadd-underconstrained [--show-model]
```

run twobyteadd-constrained
```bash
python3 manual-check.py --query twobyteadd-constrained [--show-model]
```

show help message

```bash
python3 manual-check.py --help
```
