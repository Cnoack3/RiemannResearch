import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite weighted profile energy
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, sections 4, 7 and agenda R3/R5. The exact Gram remainder and the
affine completion are generalized to arbitrary finite real weighted data.
-/
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProfileEnergy
noncomputable section
variable {ι : Type*}

def pairing (s : Finset ι) (w f g : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i * g i
def energy (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i ^ 2
def mass (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, w i

theorem energy_nonneg (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ energy s w f :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))

/-- Exact Cauchy--Schwarz identity, retaining every two - coordinate minor.
The equality also holds for signed weights. -/
theorem gram_identity (s : Finset ι) (w f g : ι → ℝ) :
    energy s w f * energy s w g - pairing s w f g ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g j - f j * g i) ^ 2)/2 := by
  have ht : ∀ i j, w i * w j * (f i * g j - f j * g i) ^ 2 =
      (w i * f i ^ 2) * (w j * g j ^ 2) + (w i * g i ^ 2) * (w j * f j ^ 2) -
        2 * (w i * f i * g i) * (w j * f j * g j) := by
    intro i j
    ring
  unfold energy pairing
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  ring

theorem pairing_sq_le (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    pairing s w f g ^ 2 ≤ energy s w f * energy s w g := by
  have h := gram_identity s w f g
  have hn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (f i * g j - f j * g i) ^ 2 := by
    exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)))
  linarith

/-- Signed profile error; no asymptotic squarefree - counting input is used. -/
theorem signed_profile_error_sq_le (s : Finset ι) (w sign b h : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsign : ∀ i ∈ s, sign i ^ 2 ≤ 1) :
    (pairing s w sign b - pairing s w sign h) ^ 2 ≤
      mass s w * energy s w (fun i => b i - h i) := by
  have heq : pairing s w sign b - pairing s w sign h =
      pairing s w (fun i => b i - h i) sign := by
    unfold pairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  have hc := pairing_sq_le s w (fun i => b i - h i) sign hw
  have hm : energy s w sign ≤ mass s w := by
    apply Finset.sum_le_sum
    intro i hi
    exact (mul_le_mul_of_nonneg_left (hsign i hi) (hw i hi)).trans_eq (mul_one _)
  nlinarith [mul_le_mul_of_nonneg_left hm
    (energy_nonneg s w (fun i => b i - h i) hw)]

def affineLoss (s : Finset ι) (w t b : ι → ℝ) (c0 c1 : ℝ) : ℝ :=
  energy s w (fun i => b i - c0 - c1 * t i)

/-- Normal equations remove the affine part before any estimate. -/
theorem affine_completion (s : Finset ι) (w t b : ι → ℝ) (c0 c1 a0 a1 : ℝ)
    (h0 : (∑ i ∈ s, w i * (b i - c0 - c1 * t i)) = 0)
    (h1 : (∑ i ∈ s, w i * t i * (b i - c0 - c1 * t i)) = 0) :
    affineLoss s w t b a0 a1 = affineLoss s w t b c0 c1 +
      energy s w (fun i => (a0 - c0) + (a1 - c1) * t i) := by
  unfold affineLoss energy
  calc
    _ = ∑ i ∈ s, (w i * (b i - c0 - c1 * t i) ^ 2 +
          w i * ((a0 - c0) + (a1 - c1) * t i) ^ 2 -
          (2 * (a0 - c0)) * (w i * (b i - c0 - c1 * t i)) -
          (2 * (a1 - c1)) * (w i * t i * (b i - c0 - c1 * t i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1]
      ring

theorem affine_minimizes (s : Finset ι) (w t b : ι → ℝ) (c0 c1 : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (h0 : (∑ i ∈ s, w i * (b i - c0 - c1 * t i)) = 0)
    (h1 : (∑ i ∈ s, w i * t i * (b i - c0 - c1 * t i)) = 0) (a0 a1 : ℝ) :
    affineLoss s w t b c0 c1 ≤ affineLoss s w t b a0 a1 := by
  rw [affine_completion s w t b c0 c1 a0 a1 h0 h1]
  exact le_add_of_nonneg_right (energy_nonneg _ _ _ hw)

/-- Two positive - weight distinct abscissae already give a nonsingular affine
normal matrix. There is no "sufficiently large cutoff" restriction. -/
theorem affine_determinant_pos (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (i j : ι) (hi : i ∈ s) (hj : j ∈ s)
    (hwi : 0 < w i) (hwj : 0 < w j) (ht : t i ≠ t j) :
    0 < mass s w * energy s w t - (∑ k ∈ s, w k * t k) ^ 2 := by
  have h := gram_identity s w (fun _ => 1) t
  have hn : 0 < ∑ k ∈ s, ∑ l ∈ s,
      w k * w l * ((1:ℝ) * t l - 1 * t k) ^ 2 := by
    apply Finset.sum_pos'
    · intro k hk
      exact Finset.sum_nonneg (fun l hl =>
        mul_nonneg (mul_nonneg (hw k hk) (hw l hl)) (sq_nonneg _))
    · refine ⟨i, hi, ?_⟩
      apply Finset.sum_pos'
      · intro l hl
        exact mul_nonneg (mul_nonneg (hw i hi) (hw l hl)) (sq_nonneg _)
      · refine ⟨j, hj, ?_⟩
        apply mul_pos (mul_pos hwi hwj)
        apply sq_pos_of_ne_zero
        simpa using sub_ne_zero.mpr ht.symm
  simpa [energy, pairing, mass] using (show 0 <
    energy s w (fun _ => 1) * energy s w t - pairing s w (fun _ => 1) t ^ 2 by linarith)

end
end RiemannResearch.Analysis.FiniteProfileEnergy
