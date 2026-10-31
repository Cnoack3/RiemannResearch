/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Exact Hermitian quadratic perturbation

Source: Signed_Quadratic_Correction_Research_Note.pdf, §3.2.
The signed linear term is retained; only an operator-kernel hypothesis
removes it for arbitrary perturbations.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Fourier

def kernelMixed {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a h : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, star (a i) * B i j * h j

def kernelQuadratic {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a : ι → ℂ) : ℝ := (kernelMixed s B a a).re

theorem kernelMixed_swap {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a h : ι → ℂ) (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    kernelMixed s B a h = star (kernelMixed s B h a) := by
  unfold kernelMixed
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB i hi j hj]
  ring

/-- Exact Hermitian perturbation identity, including the signed linear term. -/
theorem kernelQuadratic_perturbation {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    kernelQuadratic s B (fun i => a i + h i) =
      kernelQuadratic s B a + 2 * (kernelMixed s B h a).re + kernelQuadratic s B h := by
  have hexpand : kernelMixed s B (fun i => a i + h i) (fun i => a i + h i) =
      kernelMixed s B a a + kernelMixed s B a h +
        kernelMixed s B h a + kernelMixed s B h h := by
    unfold kernelMixed
    simp only [star_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  unfold kernelQuadratic
  rw [hexpand, kernelMixed_swap s B a h hB]
  simp only [Complex.add_re]
  have hconj (z : ℂ) : (star z).re = z.re := rfl
  rw [hconj]
  ring

/-- An operator kernel, unlike a mere quadratic zero, kills the linear term. -/
theorem kernelQuadratic_perturbation_of_kernel {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ∑ j ∈ s, B i j * a j = 0) :
    kernelQuadratic s B (fun i => a i + h i) = kernelQuadratic s B h := by
  have hmixed (u : ι → ℂ) : kernelMixed s B u a = 0 := by
    unfold kernelMixed
    apply Finset.sum_eq_zero
    intro i hi
    calc
      (∑ j ∈ s, star (u i) * B i j * a j) =
          star (u i) * (∑ j ∈ s, B i j * a j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [ha i hi, mul_zero]
  rw [kernelQuadratic_perturbation s B a h hB]
  simp [kernelQuadratic, hmixed]

theorem kernelMixed_norm_le_action {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (h a : ι → ℂ) (δ : ι → ℝ)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i) :
    ‖kernelMixed s B h a‖ ≤ ∑ i ∈ s, ‖h i‖ * δ i := by
  have heq : kernelMixed s B h a =
      ∑ i ∈ s, star (h i) * (∑ j ∈ s, B i j * a j) := by
    unfold kernelMixed
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mul_sum, mul_assoc]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ‖star (h i) * (∑ j ∈ s, B i j * a j)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (ha i hi) (norm_nonneg _)

theorem kernelQuadratic_linear_remainder_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ) (δ : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i) :
    |kernelQuadratic s B (fun i => a i + h i) -
      kernelQuadratic s B a - kernelQuadratic s B h| ≤
      2 * ∑ i ∈ s, ‖h i‖ * δ i := by
  rw [kernelQuadratic_perturbation s B a h hB]
  have heq : kernelQuadratic s B a + 2 * (kernelMixed s B h a).re +
      kernelQuadratic s B h - kernelQuadratic s B a - kernelQuadratic s B h =
      2 * (kernelMixed s B h a).re := by ring
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans (kernelMixed_norm_le_action s B h a δ ha))
    (by norm_num)

theorem kernelQuadratic_perturbation_abs_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ) (δ : ι → ℝ) (C : ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i)
    (hh : |kernelQuadratic s B h| ≤ C) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * ∑ i ∈ s, ‖h i‖ * δ i + C := by
  have hr := kernelQuadratic_linear_remainder_bound s B a h δ hB ha
  have ht := abs_add_le
    (kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a -
      kernelQuadratic s B h) (kernelQuadratic s B h)
  have heq : kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a -
      kernelQuadratic s B h + kernelQuadratic s B h =
      kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a := by ring
  rw [heq] at ht
  linarith

/-- Universal translation invariance characterizes the operator kernel exactly. -/
theorem kernelQuadratic_invariance_iff_kernel {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    (∀ h : ι → ℂ, kernelQuadratic s B (fun i => a i + h i) =
      kernelQuadratic s B h) ↔
      ∀ i ∈ s, ∑ j ∈ s, B i j * a j = 0 := by
  constructor
  · intro hinv
    have hzero : kernelQuadratic s B a = 0 := by
      simpa [kernelQuadratic, kernelMixed] using hinv (fun _ => 0)
    let v : ι → ℂ := fun i => ∑ j ∈ s, B i j * a j
    have hmixed : (kernelMixed s B v a).re = ∑ i ∈ s, ‖v i‖ ^ 2 := by
      unfold kernelMixed
      have heq : (∑ i ∈ s, ∑ j ∈ s, star (v i) * B i j * a j) =
          ∑ i ∈ s, star (v i) * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [v]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have hvzero : ∑ i ∈ s, ‖v i‖ ^ 2 = 0 := by
      have heq := kernelQuadratic_perturbation s B a v hB
      rw [hinv v, hzero, hmixed] at heq
      linarith
    intro i hi
    have hvi : ‖v i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖v j‖)).mp hvzero i hi
    have hv : v i = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hvi)
    exact hv
  · intro ha h
    exact kernelQuadratic_perturbation_of_kernel s B a h hB ha

/-!
Coefficient-sensitive continuation. Source for statements and elementary proof
strategy: RH/CoefficientSensitiveSignedCorrection20261030.md, sections 3 and 7.
Verification and applications: RH/CoefficientSensitiveFiniteVerification20261030.md.
The finite statements impose no RH or zero-density hypothesis.
-/

theorem symmetric_pairing_le_row_energy {ι : Type*} (s : Finset ι)
    (w : ι → ι → ℝ) (u : ι → ℝ)
    (hw : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ w i j)
    (hs : ∀ i ∈ s, ∀ j ∈ s, w i j = w j i) :
    (∑ i ∈ s, ∑ j ∈ s, w i j * u i * u j) ≤
      ∑ i ∈ s, (∑ j ∈ s, w i j) * u i ^ 2 := by
  have hyoung : 2 * (∑ i ∈ s, ∑ j ∈ s, w i j * u i * u j) ≤
      (∑ i ∈ s, ∑ j ∈ s, w i j * u i ^ 2) +
        ∑ i ∈ s, ∑ j ∈ s, w i j * u j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    nlinarith [mul_nonneg (hw i hi j hj) (sq_nonneg (u i - u j))]
  have hswap : (∑ i ∈ s, ∑ j ∈ s, w i j * u j ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i j * u i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j hj i hi]
  have hrow : (∑ i ∈ s, ∑ j ∈ s, w i j * u i ^ 2) =
      ∑ i ∈ s, (∑ j ∈ s, w i j) * u i ^ 2 := by
    simp only [Finset.sum_mul]
  rw [hswap, hrow] at hyoung
  linarith

theorem kernelQuadratic_abs_le_row_energy {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    |kernelQuadratic s B a| ≤
      ∑ i ∈ s, (∑ j ∈ s, ‖B i j‖) * ‖a i‖ ^ 2 := by
  have hact (i : ι) (hi : i ∈ s) :
      ‖∑ j ∈ s, B i j * a j‖ ≤ ∑ j ∈ s, ‖B i j‖ * ‖a j‖ := by
    calc
      _ ≤ ∑ j ∈ s, ‖B i j * a j‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  have hsym (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖B i j‖ = ‖B j i‖ := by rw [← hB i hi j hj, norm_star]
  have h := kernelMixed_norm_le_action s B a a
    (fun i => ∑ j ∈ s, ‖B i j‖ * ‖a j‖) hact
  have heq : (∑ i ∈ s, ‖a i‖ * ∑ j ∈ s, ‖B i j‖ * ‖a j‖) =
      ∑ i ∈ s, ∑ j ∈ s, ‖B i j‖ * ‖a i‖ * ‖a j‖ := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at h
  exact (Complex.abs_re_le_norm _).trans (h.trans
    (symmetric_pairing_le_row_energy s (fun i j => ‖B i j‖) (fun i => ‖a i‖)
      (fun i hi j hj => norm_nonneg _) hsym))

theorem kernelQuadratic_perturbation_row_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ) (δ : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * (∑ i ∈ s, ‖h i‖ * δ i) +
        ∑ i ∈ s, (∑ j ∈ s, ‖B i j‖) * ‖h i‖ ^ 2 :=
  kernelQuadratic_perturbation_abs_bound s B a h δ _ hB ha
    (kernelQuadratic_abs_le_row_energy s B h hB)
/-- A constraint-annihilator may be removed before measuring the action defect. -/
theorem kernelMixed_eq_action_sub_annihilator {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (h a z : ι → ℂ)
    (hz : (∑ i ∈ s, star (h i) * z i) = 0) :
    kernelMixed s B h a =
      ∑ i ∈ s, star (h i) * ((∑ j ∈ s, B i j * a j) - z i) := by
  have heq : kernelMixed s B h a =
      ∑ i ∈ s, star (h i) * (∑ j ∈ s, B i j * a j) := by
    simp only [kernelMixed, Finset.mul_sum, mul_assoc]
  rw [heq]
  simp only [mul_sub, Finset.sum_sub_distrib, hz, sub_zero]

theorem kernelMixed_norm_le_action_sub_annihilator {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (h a z : ι → ℂ) (δ : ι → ℝ)
    (hz : (∑ i ∈ s, star (h i) * z i) = 0)
    (ha : ∀ i ∈ s, ‖(∑ j ∈ s, B i j * a j) - z i‖ ≤ δ i) :
    ‖kernelMixed s B h a‖ ≤ ∑ i ∈ s, ‖h i‖ * δ i := by
  rw [kernelMixed_eq_action_sub_annihilator s B h a z hz]
  calc
    _ ≤ ∑ i ∈ s, ‖star (h i) * ((∑ j ∈ s, B i j * a j) - z i)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (ha i hi) (norm_nonneg _)

theorem kernelQuadratic_perturbation_annihilator_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h z : ι → ℂ) (δ : ι → ℝ) (C : ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (hz : (∑ i ∈ s, star (h i) * z i) = 0)
    (ha : ∀ i ∈ s, ‖(∑ j ∈ s, B i j * a j) - z i‖ ≤ δ i)
    (hh : |kernelQuadratic s B h| ≤ C) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * (∑ i ∈ s, ‖h i‖ * δ i) + C := by
  have hm := (Complex.abs_re_le_norm (kernelMixed s B h a)).trans
    (kernelMixed_norm_le_action_sub_annihilator s B h a z δ hz ha)
  rw [kernelQuadratic_perturbation s B a h hB]
  have heq : kernelQuadratic s B a + 2 * (kernelMixed s B h a).re +
      kernelQuadratic s B h - kernelQuadratic s B a =
      2 * (kernelMixed s B h a).re + kernelQuadratic s B h := by ring
  rw [heq]
  calc
    _ ≤ |2 * (kernelMixed s B h a).re| + |kernelQuadratic s B h| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; norm_num; linarith
/-- Exact finite adjoint pairing for the complete head map. -/
theorem finite_head_adjoint_pairing {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℂ) (h : ι → ℂ) (lam : κ → ℂ) :
    (∑ i ∈ s, star (h i) * (∑ k ∈ t, star (A k i) * lam k)) =
      ∑ k ∈ t, star (∑ i ∈ s, A k i * h i) * lam k := by
  simp only [Finset.mul_sum, star_sum, star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finite_head_adjoint_annihilates {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : κ → ι → ℂ) (h : ι → ℂ) (lam : κ → ℂ)
    (hh : ∀ k ∈ t, ∑ i ∈ s, A k i * h i = 0) :
    (∑ i ∈ s, star (h i) * (∑ k ∈ t, star (A k i) * lam k)) = 0 := by
  rw [finite_head_adjoint_pairing]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hh k hk, star_zero, zero_mul]

/-- Exact perturbation identity modulo all specified head constraints. -/
theorem kernelQuadratic_perturbation_head_constraints {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (B : ι → ι → ℂ) (A : κ → ι → ℂ)
    (a h : ι → ℂ) (lam : κ → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (hh : ∀ k ∈ t, ∑ i ∈ s, A k i * h i = 0) :
    kernelQuadratic s B (fun i => a i + h i) = kernelQuadratic s B a +
      2 * (∑ i ∈ s, star (h i) *
        ((∑ j ∈ s, B i j * a j) - (∑ k ∈ t, star (A k i) * lam k))).re +
      kernelQuadratic s B h := by
  rw [kernelQuadratic_perturbation s B a h hB,
    kernelMixed_eq_action_sub_annihilator s B h a
      (fun i => ∑ k ∈ t, star (A k i) * lam k)
      (finite_head_adjoint_annihilates s t A h lam hh)]

/-- Both the constrained action defect and the full row-energy remainder are kept. -/
theorem kernelQuadratic_perturbation_head_row_bound {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (B : ι → ι → ℂ) (A : κ → ι → ℂ)
    (a h : ι → ℂ) (lam : κ → ℂ) (delta : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (hh : ∀ k ∈ t, ∑ i ∈ s, A k i * h i = 0)
    (hdef : ∀ i ∈ s, ‖(∑ j ∈ s, B i j * a j) -
      (∑ k ∈ t, star (A k i) * lam k)‖ ≤ delta i) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * (∑ i ∈ s, ‖h i‖ * delta i) +
        ∑ i ∈ s, (∑ j ∈ s, ‖B i j‖) * ‖h i‖ ^ 2 := by
  exact kernelQuadratic_perturbation_annihilator_bound s B a h
    (fun i => ∑ k ∈ t, star (A k i) * lam k) delta _ hB
    (finite_head_adjoint_annihilates s t A h lam hh) hdef
    (kernelQuadratic_abs_le_row_energy s B h hB)

/-- Weighted row energy; no positivity assumption is needed on `u`. -/
theorem symmetric_pairing_le_weighted_row_energy {ι : Type*} (s : Finset ι)
    (w : ι → ι → ℝ) (u v : ι → ℝ)
    (hw : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ w i j)
    (hs : ∀ i ∈ s, ∀ j ∈ s, w i j = w j i)
    (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, ∑ j ∈ s, w i j * u i * u j) ≤
      ∑ i ∈ s, (∑ j ∈ s, w i j * v j / v i) * u i ^ 2 := by
  have ht := symmetric_pairing_le_row_energy s
    (fun i j => w i j * v i * v j) (fun i => u i / v i)
    (fun i hi j hj => mul_nonneg (mul_nonneg (hw i hi j hj) (hv i hi).le) (hv j hj).le)
    (fun i hi j hj => by rw [hs i hi j hj]; ring)
  have hl : (∑ i ∈ s, ∑ j ∈ s,
      (w i j * v i * v j) * (u i / v i) * (u j / v j)) =
      ∑ i ∈ s, ∑ j ∈ s, w i j * u i * u j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [(hv i hi).ne', (hv j hj).ne']
  have hr : (∑ i ∈ s, (∑ j ∈ s, w i j * v i * v j) * (u i / v i)^2) =
      ∑ i ∈ s, (∑ j ∈ s, w i j * v j / v i) * u i^2 := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [(hv i hi).ne']
  rw [hl, hr] at ht
  exact ht

theorem kernelQuadratic_abs_le_weighted_row_energy {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a : ι → ℂ) (v : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (hv : ∀ i ∈ s, 0 < v i) :
    |kernelQuadratic s B a| ≤
      ∑ i ∈ s, (∑ j ∈ s, ‖B i j‖ * v j / v i) * ‖a i‖ ^ 2 := by
  have hact (i : ι) (hi : i ∈ s) :
      ‖∑ j ∈ s, B i j * a j‖ ≤ ∑ j ∈ s, ‖B i j‖ * ‖a j‖ := by
    calc
      _ ≤ ∑ j ∈ s, ‖B i j * a j‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  have hsym (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖B i j‖ = ‖B j i‖ := by rw [← hB i hi j hj, norm_star]
  have h := kernelMixed_norm_le_action s B a a
    (fun i => ∑ j ∈ s, ‖B i j‖ * ‖a j‖) hact
  have heq : (∑ i ∈ s, ‖a i‖ * ∑ j ∈ s, ‖B i j‖ * ‖a j‖) =
      ∑ i ∈ s, ∑ j ∈ s, ‖B i j‖ * ‖a i‖ * ‖a j‖ := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at h
  exact (Complex.abs_re_le_norm _).trans (h.trans
    (symmetric_pairing_le_weighted_row_energy s (fun i j => ‖B i j‖)
      (fun i => ‖a i‖) v (fun i hi j hj => norm_nonneg _) hsym hv))

theorem kernelQuadratic_perturbation_head_weighted_row_bound {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (B : ι → ι → ℂ) (A : κ → ι → ℂ)
    (a h : ι → ℂ) (lam : κ → ℂ) (delta v : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (hh : ∀ k ∈ t, ∑ i ∈ s, A k i * h i = 0)
    (hdef : ∀ i ∈ s, ‖(∑ j ∈ s, B i j * a j) -
      (∑ k ∈ t, star (A k i) * lam k)‖ ≤ delta i)
    (hv : ∀ i ∈ s, 0 < v i) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * (∑ i ∈ s, ‖h i‖ * delta i) +
        ∑ i ∈ s, (∑ j ∈ s, ‖B i j‖ * v j / v i) * ‖h i‖ ^ 2 := by
  exact kernelQuadratic_perturbation_annihilator_bound s B a h
    (fun i => ∑ k ∈ t, star (A k i) * lam k) delta _ hB
    (finite_head_adjoint_annihilates s t A h lam hh) hdef
    (kernelQuadratic_abs_le_weighted_row_energy s B h v hB hv)


end RiemannResearch.Fourier
