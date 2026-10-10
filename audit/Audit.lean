/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import ISPNormal

/-!
Audit: the headline statement is the same term as Formal Conjectures'
`Invariant_subspace_problem_normal_operator`, and the proofs use only the three standard axioms.
Any failure is an error, so `lake env lean` exits nonzero. As a control, Formal Conjectures' own
declaration must show `sorryAx`, which shows the axiom check can fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some ours := env.find? `ISPNormal.invariant_subspace_problem_normal_operator
    | throwError "ISPNormal.invariant_subspace_problem_normal_operator missing"
  let some theirs :=
      env.find? `InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator
    | throwError "InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator missing"
  unless ours.type == theirs.type do
    throwError m!"statements differ: {ours.type} vs {theirs.type}"
  unless ours.levelParams == theirs.levelParams do
    throwError m!"universe parameters differ: {ours.levelParams} vs {theirs.levelParams}"
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [`ISPNormal.invariant_subspace_problem_normal_operator,
      `ISPNormal.hypotheses_satisfiable, `ISPNormal.nonempty_closedInvariantSubspace_zero,
      `ISPNormal.isEmpty_closedInvariantSubspace_complex] do
    -- `collectAxioms` returns `[]` for a name that does not exist, so check existence first.
    if (env.find? n).isNone then throwError m!"{n} missing"
    let axs ← collectAxioms n
    let extra := axs.filter fun a ↦ !standard.contains a
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  let fc ← collectAxioms `InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator
  unless fc.contains ``sorryAx do
    throwError "control failed: Formal Conjectures' statement no longer shows sorryAx"
  logInfo m!"audit passed: statement identical ({ours.type}); standard axioms only; control ok"

/-- The statement, restated by hand, is proved by the headline theorem. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H) [IsStarNormal T] :
    Nonempty (InvariantSubspaceProblem.ClosedInvariantSubspace T) :=
  ISPNormal.invariant_subspace_problem_normal_operator hdim T
