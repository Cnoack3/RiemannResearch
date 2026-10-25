/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OffDiagonalGramBounds
import Mathlib.Tactic.Ring

/-!
# Stability of centered phase energies under finite sample changes

Source: finite algebra developed from the user's signed quadratic agenda,
item 7. These bounds explain why admissible growing-support phase asymptotics
alone do not detect a fixed finite exceptional set. They do not construct
alternative zeta zeros or assert that such sets obey the explicit formula.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Fourier
variable {ι κ : Type*} [DecidableEq ι]

def centeredPhaseEnergy (s : Finset ι) (a z : ι → ℂ) : ℂ :=
  star (∑ i ∈ s, a i * z i) * (∑ i ∈ s, a i * z i) -
    ∑ i ∈ s, star (a i) * a i

/-- The exact diagonal is removed before taking any absolute values. -/
theorem centeredPhaseEnergy_eq_pairing (s : Finset ι) (a z : ι → ℂ)
    (hz : ∀ i ∈ s, star (z i) * z i = 1) :
    centeredPhaseEnergy s a z =
      finiteGramErrorPairing s a
        (fun i j => if i = j then 0 else star (z i) * z j) := by
  classical
  have hdiag : (∑ i ∈ s, ∑ j ∈ s,
      if i = j then star (a i) * a j else 0) =
      ∑ i ∈ s, star (a i) * a i := by simp
  unfold centeredPhaseEnergy finiteGramErrorPairing
  simp only [star_sum, star_mul, Finset.sum_mul_sum]
  rw [← hdiag, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp only [if_true, mul_zero, zero_mul]
    calc
      _ = star (a i) * a i * (star (z i) * z i - 1) := by ring
      _ = 0 := by rw [hz i hi]; ring
  · simp only [if_neg hij, sub_zero]
    ring

theorem centeredPhaseEnergy_norm_le (s : Finset ι) (a z : ι → ℂ)
    (hz : ∀ i ∈ s, star (z i) * z i = 1)
    (hn : ∀ i ∈ s, ‖z i‖ = 1) :
    ‖centeredPhaseEnergy s a z‖ ≤
      (∑ i ∈ s, ‖a i‖) ^ 2 - ∑ i ∈ s, ‖a i‖ ^ 2 := by
  classical
  rw [centeredPhaseEnergy_eq_pairing s a z hz]
  simpa using finiteGramErrorPairing_norm_le_offDiagonal_mass s a
    (fun i j => if i = j then 0 else star (z i) * z j) 1
    (by intros; simp) (by
      intro i hi j hj hij
      simp [hij, norm_mul, norm_star, hn i hi, hn j hj])

theorem finitePhaseModification_norm_le
    (s : Finset ι) (a : ι → ℂ) (t : Finset κ) (z : κ → ι → ℂ)
    (hz : ∀ k ∈ t, ∀ i ∈ s, star (z k i) * z k i = 1)
    (hn : ∀ k ∈ t, ∀ i ∈ s, ‖z k i‖ = 1) :
    ‖∑ k ∈ t, centeredPhaseEnergy s a (z k)‖ ≤
      (t.card : ℝ) * ((∑ i ∈ s, ‖a i‖)^2 - ∑ i ∈ s, ‖a i‖^2) := by
  calc
    _ ≤ ∑ k ∈ t, ‖centeredPhaseEnergy s a (z k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ t, ((∑ i ∈ s, ‖a i‖)^2 - ∑ i ∈ s, ‖a i‖^2) :=
      Finset.sum_le_sum (fun k hk => centeredPhaseEnergy_norm_le s a (z k)
        (hz k hk) (hn k hk))
    _ = _ := by simp [nsmul_eq_mul]; ring

theorem finitePhaseModification_normalized_card_bound
    (s : Finset ι) (a : ι → ℂ) (t : Finset κ) (z : κ → ι → ℂ) (T : ℝ)
    (hT : 0 < T)
    (hz : ∀ k ∈ t, ∀ i ∈ s, star (z k i) * z k i = 1)
    (hn : ∀ k ∈ t, ∀ i ∈ s, ‖z k i‖ = 1) :
    ‖(∑ k ∈ t, centeredPhaseEnergy s a (z k)) / (T : ℂ)‖ ≤
      ((t.card : ℝ) * ((s.card : ℝ) - 1) / T) * ∑ i ∈ s, ‖a i‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖a i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply (div_le_iff₀ hT).mpr
  have hb := finitePhaseModification_norm_le s a t z hz hn
  have hc := mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg (α := ℝ) t.card)
  calc
    _ ≤ (t.card : ℝ) * ((s.card : ℝ) - 1) * (∑ i ∈ s, ‖a i‖^2) := by nlinarith
    _ = _ := by field_simp <;> ring

end RiemannResearch.Fourier
