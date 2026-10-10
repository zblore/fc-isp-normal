/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.Wikipedia.InvariantSubspaceProblem

/-!
# Normal operators have nontrivial closed invariant subspaces

This file proves `InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator` from
Google DeepMind's Formal Conjectures: a normal operator `T` on a complex Hilbert space of dimension
at least two has a closed subspace, other than `0` and the whole space, that `T` maps into itself.

The argument is the one the Formal Conjectures docstring sketches: if `T` is a multiple of the
identity any nontrivial subspace works, and otherwise a nontrivial spectral subspace does. Here it
is made precise with Mathlib's continuous functional calculus.

* If the spectrum of `T` is contained in `{c}`, then `T = c • 1`, and any line is invariant.
* Otherwise pick two points `a ≠ b` of the spectrum and continuous functions `f`, `g` that are
  nonzero at `a` and `b` respectively but never nonzero at the same place. Then `f(T) g(T) = 0`
  while `f(T)` and `g(T)` are both nonzero, and the kernel of `f(T)` is the subspace we want.

The main result is `ISPNormal.invariant_subspace_problem_normal_operator`.
-/

namespace ISPNormal

open InvariantSubspaceProblem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A space of dimension at least two has a nonzero vector. -/
lemma nontrivial_of_two_le_rank (hdim : 2 ≤ Module.rank ℂ H) : Nontrivial H := by
  rw [← rank_pos_iff_nontrivial (R := ℂ)]
  exact lt_of_lt_of_le (by norm_num) hdim

/-- **Case 1: `T` is a multiple of the identity.** Then every subspace is invariant, and the line
through any nonzero vector is closed, nonzero, and (in dimension at least two) not everything. -/
lemma nonempty_closedInvariantSubspace_of_eq_smul (hdim : 2 ≤ Module.rank ℂ H)
    (T : H →L[ℂ] H) (c : ℂ) (hT : T = c • 1) : Nonempty (ClosedInvariantSubspace T) := by
  have := nontrivial_of_two_le_rank hdim
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  refine ⟨⟨ℂ ∙ v, ?_, ?_, Submodule.closed_of_finiteDimensional _, ?_⟩⟩
  · rwa [Ne, Submodule.span_singleton_eq_bot]
  · intro htop
    have h1 : Module.rank ℂ (ℂ ∙ v) = 1 := by
      rw [← Module.finrank_eq_rank, finrank_span_singleton hv, Nat.cast_one]
    rw [htop, rank_top] at h1
    rw [h1] at hdim
    norm_num at hdim
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff]
    change T v ∈ ℂ ∙ v
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

/-- A bump of height `r` at `a`: continuous, positive at `a` when `0 < r`, and zero at distance `r`
or more. -/
noncomputable def bump (a : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ((max 0 (r - dist z a) : ℝ) : ℂ)

/-- A bump is continuous. -/
lemma continuous_bump (a : ℂ) (r : ℝ) : Continuous (bump a r) := by
  unfold bump
  fun_prop

/-- A bump of positive radius is nonzero at its centre. -/
lemma bump_self {a : ℂ} {r : ℝ} (hr : 0 < r) : bump a r a ≠ 0 := by
  simp [bump, hr.le, hr.ne']

/-- Bumps of radius `dist a b / 3` around two points never overlap. -/
lemma bump_mul_bump {a b : ℂ} (z : ℂ) :
    bump a (dist a b / 3) z * bump b (dist a b / 3) z = 0 := by
  by_contra h
  rw [mul_eq_zero, not_or] at h
  have ha : dist z a < dist a b / 3 := by
    by_contra hz
    exact h.1 (by simp [bump, max_eq_left (sub_nonpos.2 (not_lt.1 hz))])
  have hb : dist z b < dist a b / 3 := by
    by_contra hz
    exact h.2 (by simp [bump, max_eq_left (sub_nonpos.2 (not_lt.1 hz))])
  have := dist_triangle_left a b z
  have := dist_nonneg (x := a) (y := b)
  linarith

/-- If `f(T) = 0` for a continuous `f`, then `f` vanishes on the spectrum of `T`: by the spectral
mapping theorem the spectrum of `f(T)` is `f` applied to the spectrum of `T`, and the spectrum of
`0` is `{0}`. -/
lemma apply_eq_zero_of_cfc_eq_zero [CompleteSpace H] [Nontrivial H] (T : H →L[ℂ] H)
    [IsStarNormal T] {f : ℂ → ℂ} (hf : Continuous f) (h : cfc f T = 0) {x : ℂ}
    (hx : x ∈ spectrum ℂ T) : f x = 0 := by
  have hmap := cfc_map_spectrum f T (hf := hf.continuousOn)
  rw [h, spectrum.zero_eq] at hmap
  have : f x ∈ f '' spectrum ℂ T := ⟨x, hx, rfl⟩
  rw [← hmap] at this
  simpa using this

/-- **Case 2: the spectrum has two distinct points `a` and `b`.** Take continuous bumps `f` at `a`
and `g` at `b` that never overlap. Then `f(T) g(T) = (f g)(T) = 0`, and neither `f(T)` nor `g(T)`
is zero. The kernel of `f(T)` is closed, is not everything (as `f(T) ≠ 0`), contains the nonzero
vectors in the range of `g(T)`, and is mapped into itself by `T`, because `T` commutes with
`f(T)`. This is the "spectral subspace" of the docstring. -/
lemma nonempty_closedInvariantSubspace_of_mem_spectrum [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℂ] H) [IsStarNormal T] {a b : ℂ} (ha : a ∈ spectrum ℂ T) (hb : b ∈ spectrum ℂ T)
    (hab : a ≠ b) :
    Nonempty (ClosedInvariantSubspace T) := by
  have hr : 0 < dist a b / 3 := div_pos (dist_pos.2 hab) (by norm_num)
  set f := bump a (dist a b / 3)
  set g := bump b (dist a b / 3)
  have hf : Continuous f := continuous_bump _ _
  have hg : Continuous g := continuous_bump _ _
  have hFG : cfc f T * cfc g T = 0 := by
    rw [← cfc_mul f g T hf.continuousOn hg.continuousOn]
    simp [f, g, bump_mul_bump]
  have hF : cfc f T ≠ 0 := fun h ↦ bump_self hr (apply_eq_zero_of_cfc_eq_zero T hf h ha)
  have hG : cfc g T ≠ 0 := fun h ↦ bump_self hr (apply_eq_zero_of_cfc_eq_zero T hg h hb)
  have hcomm : Commute (cfc f T) T := by
    simpa [cfc_id' ℂ T] using cfc_commute_cfc f (fun x ↦ x) T
  refine ⟨⟨LinearMap.ker ((cfc f T : H →L[ℂ] H) : H →ₗ[ℂ] H), ?_, ?_,
    ContinuousLinearMap.isClosed_ker _, ?_⟩⟩
  · obtain ⟨x, hx⟩ : ∃ x, cfc g T x ≠ 0 := by
      by_contra h
      push Not at h
      exact hG (ContinuousLinearMap.ext h)
    rw [Ne, Submodule.eq_bot_iff]
    push Not
    refine ⟨cfc g T x, ?_, hx⟩
    rw [LinearMap.mem_ker]
    simpa using congrArg (fun S : H →L[ℂ] H ↦ S x) hFG
  · intro htop
    apply hF
    ext x
    have hx : x ∈ LinearMap.ker ((cfc f T : H →L[ℂ] H) : H →ₗ[ℂ] H) := htop ▸ Submodule.mem_top
    simpa using hx
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : cfc f T x = 0 := by simpa using hx
    change cfc f T (T x) = 0
    rw [← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp, hx', map_zero]

/-- **Every normal operator on a Hilbert space of dimension at least two has a nontrivial closed
invariant subspace.** Either its spectrum is at most one point, and then `T` is a multiple of the
identity (case 1), or it has two distinct points (case 2). -/
theorem invariant_subspace_problem_normal_operator [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T : H →L[ℂ] H) [IsStarNormal T] : Nonempty (ClosedInvariantSubspace T) := by
  have := nontrivial_of_two_le_rank hdim
  by_cases htwo : ∃ a ∈ spectrum ℂ T, ∃ b ∈ spectrum ℂ T, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := htwo
    exact nonempty_closedInvariantSubspace_of_mem_spectrum T ha hb hab
  · push Not at htwo
    obtain ⟨c, hc⟩ : ∃ c, spectrum ℂ T ⊆ {c} := by
      by_cases hne : (spectrum ℂ T).Nonempty
      · obtain ⟨c, hc⟩ := hne
        exact ⟨c, fun x hx ↦ htwo x hx c hc⟩
      · exact ⟨0, by simp [Set.not_nonempty_iff_eq_empty.1 hne]⟩
    refine nonempty_closedInvariantSubspace_of_eq_smul hdim T c ?_
    rw [CFC.eq_algebraMap_of_spectrum_subset_singleton T c hc, Algebra.algebraMap_eq_smul_one]

end ISPNormal

