# Invariant subspaces of normal operators in Lean

A Lean 4 proof that every normal operator on a complex Hilbert space of dimension at least two has a nontrivial closed invariant subspace. It proves `Invariant_subspace_problem_normal_operator` from the invariant subspace problem file in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) against their own definitions.

## The result

The invariant subspace problem asks whether every bounded operator T on a Hilbert space has a closed subspace, other than 0 and the whole space, that T maps into itself. It is open in general. For normal operators, those that commute with their adjoint, the answer has long been known to be yes.

The proof here is the standard argument that Formal Conjectures' own docstring sketches. If the spectrum of T has at most one point c, then T is c times the identity, and any line is invariant. Otherwise pick two different points a and b of the spectrum, and two continuous bump functions, one around a and one around b, that are never both nonzero at the same place. Then f(T) g(T) = 0, but neither f(T) nor g(T) is zero. The kernel of f(T) is closed, it isn't everything, it contains the nonzero vectors g(T) produces, and T maps it into itself because T commutes with f(T).

This isn't the first formal proof. In September 2026 GitHub user baobingzhang proved the same statement in Lean, as part of a formalisation of Lomonosov's theorem ([jsp-000024-lomonosov-lean](https://github.com/baobingzhang/jsp-000024-lomonosov-lean)). This proof was written without reference to that one. The mathematics is textbook.

## The proof

- `ISPNormal/Normal.lean` has the whole argument, one lemma per step: the multiple-of-the-identity case, the bump functions, the fact that f(T) = 0 forces f to vanish on the spectrum (Mathlib's spectral mapping theorem), and the two-point case. It ends with `ISPNormal.invariant_subspace_problem_normal_operator`.
- `ISPNormal/Control.lean` checks the statement isn't empty. The theorem applies to the zero operator on ℂ², and on the line ℂ there's no such subspace at all, so the dimension condition is needed.

The statement is the same term as Formal Conjectures' `InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator`. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Building

It needs Lean v4.33.1 and depends on Formal Conjectures at commit `40a8592c`.

```
lake exe cache get
lake build
```

A fresh build first compiles the parts of Formal Conjectures it imports. On a machine with limited memory set `LEAN_NUM_THREADS` to a small number first.

To rerun the checks, one at a time:

```
lake env lean audit/Audit.lean
lake env lean audit/Vacuity.lean
python audit/lexical.py
lake exe runLinter ISPNormal
lake exe lint-style ISPNormal
```

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
