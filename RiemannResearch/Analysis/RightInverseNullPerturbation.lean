/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Rank-one head-null perturbations of a continuous linear right inverse

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 1.
Exact output energy is retained before estimating the norm. The construction
preserves the right-inverse equations but has arbitrarily large complete norm
whenever the free direction and one functional value are nonzero.
-/

noncomputable section
namespace RiemannResearch.Analysis.RightInverseNullPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def perturbation (R : E →L[ℝ] F) (ℓ : E →L[ℝ] ℝ) (h : F) (t : ℝ) : E →L[ℝ] F where
  toFun a := R a + (t * ℓ a) • h
  map_add' a b := by
    rw [map_add, map_add, mul_add, add_smul]
    abel
  map_smul' c a := by
    simp only [map_smul, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]
    congr 1
    congr 1
    ring
  cont := R.continuous.add ((continuous_const.mul ℓ.continuous).smul continuous_const)

@[simp] theorem perturbation_apply (R : E →L[ℝ] F) (ℓ : E →L[ℝ] ℝ)
    (h : F) (t : ℝ) (a : E) :
    perturbation R ℓ h t a = R a + (t * ℓ a) • h := rfl

/-- The full quadratic energy, including its signed linear term. -/
theorem perturbation_energy (R : E →L[ℝ] F) (ℓ : E →L[ℝ] ℝ)
    (h : F) (t : ℝ) (a : E) :
    ‖perturbation R ℓ h t a‖ ^ 2 = ‖R a‖ ^ 2 +
      2 * (t * ℓ a) * inner ℝ (R a) h + (t * ℓ a) ^ 2 * ‖h‖ ^ 2 :=
  RiemannResearch.LinearAlgebra.norm_add_smul_sq_exact _ _ _

theorem perturbation_rightInverse (H : F →L[ℝ] E) (R : E →L[ℝ] F)
    (ℓ : E →L[ℝ] ℝ) (h : F) (t : ℝ)
    (hR : Function.RightInverse R H) (hh : H h = 0) :
    Function.RightInverse (perturbation R ℓ h t) H := by
  intro a
  rw [perturbation_apply, map_add, map_smul, hh, smul_zero, add_zero]
  exact hR a

theorem perturbation_mem (V : Submodule ℝ F) (R : E →L[ℝ] F)
    (ℓ : E →L[ℝ] ℝ) (h : F) (t : ℝ)
    (hR : ∀ a, R a ∈ V) (hh : h ∈ V) (a : E) :
    perturbation R ℓ h t a ∈ V := V.add_mem (hR a) (V.smul_mem _ hh)

/-- A nonzero free direction gives unbounded norms for a single fixed nonzero head. -/
theorem perturbation_output_unbounded (R : E →L[ℝ] F) (ℓ : E →L[ℝ] ℝ)
    (h : F) (hh : h ≠ 0) (a : E) (ha : ℓ a ≠ 0) (C : ℝ) :
    ∃ t : ℝ, C < ‖perturbation R ℓ h t a‖ := by
  have hhnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  let s : ℝ := (|C| + ‖R a‖ + 1) / ‖h‖
  let t : ℝ := s / ℓ a
  have hs : 0 < s := by dsimp only [s]; positivity
  have ht : t * ℓ a = s := div_mul_cancel₀ _ ha
  have henergy : ‖(t * ℓ a) • h‖ = |C| + ‖R a‖ + 1 := by
    rw [ht, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact div_mul_cancel₀ _ hhnorm.ne'
  have htri := norm_sub_le (perturbation R ℓ h t a) (R a)
  rw [perturbation_apply] at htri
  have heq : R a + (t * ℓ a) • h - R a = (t * ℓ a) • h := by abel
  rw [heq, henergy] at htri
  refine ⟨t, ?_⟩
  change C < ‖R a + (t * ℓ a) • h‖
  linarith [le_abs_self C]

/-- The operator norms are unbounded as well, rather than just one output family. -/
theorem perturbation_opNorm_unbounded_of_value (R : E →L[ℝ] F)
    (ℓ : E →L[ℝ] ℝ) (h : F) (hh : h ≠ 0)
    (a : E) (ha : ℓ a ≠ 0) (C : ℝ) :
    ∃ t : ℝ, C < ‖perturbation R ℓ h t‖ := by
  obtain ⟨t, ht⟩ := perturbation_output_unbounded R ℓ h hh a ha (|C| * ‖a‖)
  refine ⟨t, ?_⟩
  by_contra hn
  have hop : ‖perturbation R ℓ h t‖ ≤ |C| := (le_of_not_gt hn).trans (le_abs_self C)
  have hbound := (perturbation R ℓ h t).le_opNorm a
  have hm := mul_le_mul_of_nonneg_right hop (norm_nonneg a)
  exact (not_le_of_gt ht) (hbound.trans hm)

theorem perturbation_opNorm_unbounded (R : E →L[ℝ] F)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (h : F) (hh : h ≠ 0) (C : ℝ) :
    ∃ t : ℝ, C < ‖perturbation R ℓ h t‖ := by
  have hex : ∃ a, ℓ a ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hℓ
    ext a
    exact hn a
  obtain ⟨a, ha⟩ := hex
  exact perturbation_opNorm_unbounded_of_value R ℓ h hh a ha C

end RiemannResearch.Analysis.RightInverseNullPerturbation
