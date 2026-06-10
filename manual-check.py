import argparse
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from collections.abc import Iterable

# chosen prime field order
P = 65537

QUERIES = [
        "cyclic-missing-selector",
        "cyclic-with-selector",
        "twobyteadd-underconstrained",
        "twobyteadd-constrained"
        ]
EXPECTED = {
        "cyclic-missing-selector": "unsat",
        "cyclic-with-selector": "sat",
        "twobyteadd-underconstrained": "sat",
        "twobyteadd-constrained": "unsat"
        }


@dataclass(frozen=True)
class Query:
    name: str
    description: str
    smt: str
    expected: str


# or several SMT conditions
def or_(*parts: str) -> str:
    # excluding empty lines from SMT query
    cleaned_parts = [part for part in parts if part != ""]
    if not cleaned_parts:
        return "false"
    if len(cleaned_parts) == 1:
        return cleaned_parts[0]
    return "(or\n  " + "\n  ".join(cleaned_parts) + "\n)"


# and several SMT conditions
def and_(*parts: str) -> str:
    # excluding empty lines from SMT query
    cleaned_parts = [part for part in parts if part != ""]

    if not cleaned_parts:
        return "true"
    if len(cleaned_parts) == 1:
        return cleaned_parts[0]

    return "(and\n  " + "\n  ".join(cleaned_parts) + "\n)"


# SMT condition that expr = 0 (mod P)
def field_zero(expr: str) -> str:
    return f"(= (mod {expr} {P}) 0)"


# SMT condition that x belongs to field
def in_field(x: str) -> str:
    return f"(and (<= 0 {x}) (< {x} {P}))"


# SMT condition that x is byte
def byte(x: str) -> str:
    return f"(and (<= 0 {x}) (< {x} 256))"


# build trace' column
def named_column(name: str, size: int) -> list[str]:
    return [f"{name}{i}" for i in range(size)]

# asign values to column
def fix_column(col: list[str], values: list[int]) -> list[str]:
    if len(col) != len(values):
        raise ValueError("column and values lengths must be equal")

    return [f"(= {var} {value})" for var, value in zip(col, values, strict=True)]


# declaring columns
def decl_columns(*cols: list[str]) -> str:
    names: list[str] = []
    
    for col in cols:
        # creating flat list of all variables names
        names.extend(col)

    return decl_int_vars(names)


# declaring variables
def decl_int_vars(names: Iterable[str]) -> str:
    return "\n".join(f"(declare-const {n} Int)" for n in names) + "\n"


def twobyteadd_row(a: str, b: str, reset: str, prev: str, carry: str, add: str) -> str:
    # (a + b + (1 - RESET) * prevCarry) - (carry * 2^8 + add) = 0  (mod p)

    expr = f"(- (+ {a} {b} (* (- 1 {reset}) {prev})) (+ (* {carry} 256) {add}))"
    return field_zero(expr)


# using nonlinear integer arithmetic; quantifer-free
def header(title: str) -> str:
    return f"""; {title}
; Encoding style: Int variables + modular field equalities over F_{P}.
(set-logic QF_NIA)
(set-option :produce-models true)
"""


def footer() -> str:
    return "\n(check-sat)\n(get-model)\n"


def make_cyclic(with_selector: bool) -> Query:
    # We have a valid execution trace for integer addition, encoded over F_p:
    # a = [1, 0, -1, 1], b = [1, 2, 2, 1]
    # transition logic is b' = a + b

    # Problem here is that b’ = b + a is satisfied for every row except for the last, because:
    # b’(g^4 ) = b(1) = 1  !=  2 = 1 + 1 = b(g^4) + a(g^4)
    # this means that scheme is over-constrained

    # trace' size
    N = 4
    a = named_column("a", N)
    b = named_column("b", N)

    # -1 is (p − 1) over F_p
    a_vals = [1, 0, P - 1, 1]
    b_vals = [1, 2, 2, 1]
    fixed = fix_column(a, a_vals) + fix_column(b, b_vals)

    constraints: list[str] = []

    for i in range(N):
        # p' operator
        nxt = (i + 1) % N

        # (a + 1) * a * (a - 1) = 0
        constraints.append(field_zero(f"(* (+ {a[i]} 1) {a[i]} (- {a[i]} 1))"))

        if with_selector:
            sel = 1 if i < 3 else 0

            # b' = SEL * (b+a) + (1-SEL)
            rhs = f"(+ (* {sel} (+ {b[i]} {a[i]})) (- 1 {sel}))"
            constraints.append(field_zero(f"(- {b[nxt]} {rhs})"))
        else:

            # b' = b + a
            constraints.append(field_zero(f"(- {b[nxt]} (+ {b[i]} {a[i]}))"))

    body = and_(*(fixed + constraints))
    title = "CyclicExample with SEL" if with_selector else "CyclicExample without SEL"

    smt = (
        header(title)
       + decl_columns(a, b)
       + f"(assert {body})\n"
       + footer()
    )

    name = "cyclic-with-selector" if with_selector else "cyclic-missing-selector"
    description_correct_constraints = "The trace is valid, and the constraints are correct. sat is expexcted"
    description_incorrect_constraints = "The trace is valid, but the constraints are incorrect. unsat is expexcted"

    description =  description_correct_constraints if with_selector else description_incorrect_constraints
    return Query(name, description, smt, EXPECTED[name])


def add_field_column_constraints(col: list[str]) -> list[str]:
    return [in_field(cell) for cell in col]


def add_byte_column_constraints(col: list[str]) -> list[str]:
    return [byte(cell) for cell in col]


def make_twobyteadd_underconstrained() -> Query:
    # Here we check if constraints admit two different outputs
    # for the same input.
    #
    # Modeled PIL constraints:
    #   prevCarry' = carry
    #   a + b + (1 - RESET) * prevCarry = carry * 2^8 + add
    # above PIL specification is underconstrained, because
    # no range checks performed;
    # thus, sat is expected

    N = 2
    constraints: list[str] = []
    fixed: list[str] = []

    a = named_column("a", N)
    b = named_column("b", N)
    reset = named_column("RESET", N)

    # First copy of output columns.
    prev_carry_1 = named_column("prevCarry_1_", N)
    carry_1 = named_column("carry_1_", N)
    add_1 = named_column("add_1_", N)

    # Second copy of output columns.
    prev_carry_2 = named_column("prevCarry_2_", N)
    carry_2 = named_column("carry_2_", N)
    add_2 = named_column("add_2_", N)

    fixed = fix_column(reset, [1, 0])

    # Inputs are bytes.
    constraints += add_byte_column_constraints(a)
    constraints += add_byte_column_constraints(b)

    # All output cells are field elements.
    for col in [prev_carry_1, carry_1, add_1, prev_carry_2, carry_2, add_2]:
        constraints += add_field_column_constraints(col)

    for i in range(N):
        nxt = (i + 1) % N

        # prevCarry' = carry
        constraints.append(field_zero(f"(- {prev_carry_1[nxt]} {carry_1[i]})"))

        # a + b + (1 - RESET) * prevCarry = carry * 2^8 + add
        constraints.append(
            twobyteadd_row(
                a[i],
                b[i],
                reset[i],
                prev_carry_1[i],
                carry_1[i],
                add_1[i],
            )
        )

        # Same for Copy 2:
        constraints.append(field_zero(f"(- {prev_carry_2[nxt]} {carry_2[i]})"))

        constraints.append(
            twobyteadd_row(
                a[i],
                b[i],
                reset[i],
                prev_carry_2[i],
                carry_2[i],
                add_2[i],
            )
        )

    different_outputs = []

    for i in range(N):
        different_outputs.append(f"(not (= {carry_1[i]} {carry_2[i]}))")
        different_outputs.append(f"(not (= {add_1[i]} {add_2[i]}))")

    constraints.append(or_(*different_outputs))

    body = and_(*(fixed + constraints))

    smt = (
        header("TwoByteAdd nondeterminism without range/inclusion checks")
        + decl_columns(
            a,
            b,
            reset,
            prev_carry_1,
            carry_1,
            add_1,
            prev_carry_2,
            carry_2,
            add_2,
        )
        + f"(assert {body})\n"
        + footer()
    )

    name = "twobyteadd-underconstrained"
    description = (
        "Check whether the weak TwoByteAdd model admits two different "
        "output traces for the same input trace"
    )

    return Query(
        name,
        description,
        smt,
        EXPECTED[name],
    )


def make_twobyteadd_constrained() -> Query:
    # Same check, but added constraints that  
    # a, b, carry, add are bytes
    # in PIL, such restrictions are enforced using an inclusion argument.
    # expected result is unsat

    N = 2
    constraints: list[str] = []
    fixed: list[str] = []

    # input columns.
    a = named_column("a", N)
    b = named_column("b", N)
    reset = named_column("RESET", N)

    prev_carry_1 = named_column("prevCarry_1_", N)
    carry_1 = named_column("carry_1_", N)
    add_1 = named_column("add_1_", N)

    # second copy of output columns.
    prev_carry_2 = named_column("prevCarry_2_", N)
    carry_2 = named_column("carry_2_", N)
    add_2 = named_column("add_2_", N)

    fixed += fix_column(reset, [1, 0])

    constraints += add_byte_column_constraints(a)
    constraints += add_byte_column_constraints(b)

    # Manual interpretation of missing inclusion checks
    # `carry`` and `add` must also be bytes in both copies of model
    constraints += add_byte_column_constraints(carry_1)
    constraints += add_byte_column_constraints(add_1)
    constraints += add_byte_column_constraints(carry_2)
    constraints += add_byte_column_constraints(add_2)

    constraints += add_field_column_constraints(prev_carry_1)
    constraints += add_field_column_constraints(prev_carry_2)

    for i in range(N):
        nxt = (i + 1) % N

        # prevCarry' = carry
        constraints.append(field_zero(f"(- {prev_carry_1[nxt]} {carry_1[i]})"))

        # a + b + (1 - RESET) * prevCarry = carry * 2^8 + add
        constraints.append(
            twobyteadd_row(
                a[i],
                b[i],
                reset[i],
                prev_carry_1[i],
                carry_1[i],
                add_1[i],
            )
        )

        # now for second copy
        constraints.append(field_zero(f"(- {prev_carry_2[nxt]} {carry_2[i]})"))

        constraints.append(
            twobyteadd_row(
                a[i],
                b[i],
                reset[i],
                prev_carry_2[i],
                carry_2[i],
                add_2[i],
            )
        )

    different_outputs: list[str] = []

    for i in range(N):
        different_outputs.append(f"(not (= {carry_1[i]} {carry_2[i]}))")
        different_outputs.append(f"(not (= {add_1[i]} {add_2[i]}))")

    constraints.append(or_(*different_outputs))
    body = and_(*(fixed + constraints))

    smt = (
        header("TwoByteAdd nondeterminism with abstracted range/inclusion checks")
        + decl_columns(
            a,
            b,
            reset,
            prev_carry_1,
            carry_1,
            add_1,
            prev_carry_2,
            carry_2,
            add_2,
        )
        + f"(assert {body})\n"
        + footer()
    )

    name = "twobyteadd-constrained"
    description = (
        "Check if the TwoByteAdd model still admits different "
        "output traces after adding byte-range constraints for carry and add."
    )

    return Query(
        name,
        description,
        smt,
        EXPECTED[name],
    )


def build_query(name: str) -> Query:
    if name == "cyclic-missing-selector":
        return make_cyclic(with_selector=False)

    if name == "cyclic-with-selector":
        return make_cyclic(with_selector=True)

    if name == "twobyteadd-underconstrained":
        return make_twobyteadd_underconstrained()
    
    if name == "twobyteadd-constrained":
        return make_twobyteadd_constrained()

    raise ValueError(f"unknown query: {name}")


def run_cvc5(query: Query, solver: str, keep_smt: bool, dir_to_save: Path, timeout: int) -> tuple[str | None, str, Path]:
    smt_query_path = Path("");

    if dir_to_save != Path("/tmp"):
        dir_to_save.mkdir(parents=True, exist_ok=True)
        smt_query_path = dir_to_save / f"{query.name}.smt2"
    else:
        tmp = tempfile.NamedTemporaryFile("w", suffix=f"_{query.name}.smt2", delete=False, encoding="utf-8")
        tmp.close()
        smt_query_path = Path(tmp.name)
    smt_query_path.write_text(query.smt, encoding="utf-8")

    solver_path = shutil.which(solver) if not Path(solver).exists() else solver
    if solver_path is None:
        return None, f"Solver '{solver}' was not found", smt_query_path

    try:
        proc = subprocess.run(
                [solver_path, "--lang=smt2", str(smt_query_path)],
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                )
    except subprocess.TimeoutExpired:
        return "timeout", f"timeout after {timeout}s", smt_query_path

    # cvc5 output
    out = proc.stdout.strip()
    err = proc.stderr.strip()
    # sat, unat or uknown
    first = out.splitlines()[0].strip() if out else None
    details = out

    if err:
        details += "\n[stderr]\n" + err
    if not keep_smt:
        smt_query_path.unlink(missing_ok=True)
        return first, details, Path("")

    return first, details, smt_query_path


def main() -> int:
    parser = argparse.ArgumentParser(description="Manual checks for PIL documentation examples using cvc5 SMT-solver")

    # `--querry` conflicts with `--all`
    group = parser.add_mutually_exclusive_group(required=True)

    group.add_argument("--query", choices=QUERIES, help="Run one query")
    group.add_argument("--all", action="store_true", help="Run all queries")

    parser.add_argument("--solver", default="cvc5", help="cvc5 executable name or path")
    parser.add_argument("--keep-smt", action="store_true", help="Save generated SMT-LIB files in /tmp. Use --dir to specify directory to save")
    parser.add_argument("--dir", type=Path, default=Path("/tmp"), help="Directory to save generated SMT-LIB files. Invalid without --keep-smt")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per query in seconds")
    parser.add_argument("--show-model", action="store_true", help="Print model")
    
    args = parser.parse_args()
    if args.dir != Path("/tmp") and (not args.keep_smt):
        parser.error("--dir can be used only together with --keep-smt")

    selected_tests = QUERIES if args.all else [args.query]
    exit_code = 0

    for test_name in selected_tests:
        query = build_query(test_name)

        result, details, smt_query_path = run_cvc5(query, args.solver, args.keep_smt, args.dir, args.timeout)
        status = result if result is not None else "not-run"

        expected_behaviour = (status == query.expected)
        if (not expected_behaviour) and (result is not None):
            exit_code = 1
        
        print_results(query, status, args.keep_smt, smt_query_path)

        if (result is None) or (args.show_model) or (not expected_behaviour):
            print("--- solver output ---")
            print(details)

    return exit_code


def print_results(query: Query, status: str, keep_smt: bool, smt_query_path: Path):
    expected_behaviour = (status == query.expected)
    smt_line = f"smt2: {smt_query_path}\n" if keep_smt else ""

    print(
        f"\n=== {query.name} ===\n"
        + f"{query.description}\n"
        + f"expected: {query.expected}\n"
        + f"actual:   {status}\n"
        + smt_line
        + f"result:   {'OK' if expected_behaviour else 'CHECK required'}"
    )


if __name__ == "__main__":
    # program exits with error if experiment behaviour differs from expected
    raise SystemExit(main())
