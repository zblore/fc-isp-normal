/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import ISPNormal.Normal

/-!
# Controls: the statement is not vacuous

Two checks that the Formal Conjectures statement says something.

* Its hypotheses can all be met: the zero operator on `ℂ²` is normal, and `ℂ²` has dimension two.
  The theorem then applies to it.
* The dimension hypothesis is needed: on the one-dimensional space `ℂ` there is no closed invariant
  subspace other than `0` and `ℂ`, so `ClosedInvariantSubspace T` is empty for every `T`.
-/

namespace ISPNormal

open InvariantSubspaceProblem

/-- The hypotheses of the theorem hold for the zero operator on `ℂ²`. -/
theorem hypotheses_satisfiable :
    2 ≤ Module.rank ℂ (EuclideanSpace ℂ (Fin 2)) ∧
      IsStarNormal (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  refine ⟨?_, inferInstance⟩
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-- The theorem applies to the zero operator on `ℂ²`: the instances it needs are found and its
hypotheses hold. -/
theorem nonempty_closedInvariantSubspace_zero :
    Nonempty (ClosedInvariantSubspace
      (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) :=
  invariant_subspace_problem_normal_operator hypotheses_satisfiable.1 0

/-- On the line `ℂ` every subspace is `0` or everything, so no operator has a closed invariant
subspace in the sense of Formal Conjectures. The hypothesis `2 ≤ Module.rank ℂ H` cannot be
dropped. (`Ideal ℂ` is by definition `Submodule ℂ ℂ`, and a field has only two ideals.) -/
theorem isEmpty_closedInvariantSubspace_complex (T : ℂ →L[ℂ] ℂ) :
    IsEmpty (ClosedInvariantSubspace T) :=
  ⟨fun W ↦ (Ideal.eq_bot_or_top W.toSubspace).elim W.ne_bot W.ne_top⟩

end ISPNormal
