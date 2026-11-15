/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite Fourier completion for Kloosterman sums

Source for the application: Baluyot (2017), Lemma 3.1.5 in *On the Zeros
of Riemann's Zeta-function*, where incomplete inverse sums are bounded by
Fourier completion and the complete Weil bound:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The completion uses the standard additive character on ZMod q. Translates,
frequencies, signs and repetitions in the interval all remain explicit.
The estimate from a complete-sum bound retains the full Fourier mass.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.Kloosterman

variable {q : ℕ} [NeZero q]

/-- The inverse phase on the units of the residue ring. -/
def inversePhase (m x : ZMod q) : ℂ := by
  classical
  exact if IsUnit x then ZMod.stdAddChar (m * x⁻¹) else 0

/-- The complete classical Kloosterman sum, with a positive linear frequency. -/
def completeSum (k m : ZMod q) : ℂ := by
  classical
  exact ∑ x : ZMod q, if IsUnit x then ZMod.stdAddChar (k * x + m * x⁻¹) else 0

theorem completeSum_eq_sum_phase (k m : ZMod q) :
    completeSum k m = ∑ x : ZMod q, ZMod.stdAddChar (k * x) * inversePhase m x := by
  classical
  unfold completeSum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x
  · simp [inversePhase, hx, AddChar.map_add_eq_mul]
  · simp [inversePhase, hx]

/-- The signed completion formula for any complex weight on the residue ring. -/
theorem weighted_sum_eq_complete (w : ZMod q → ℂ) (m : ZMod q) :
    (∑ x : ZMod q, w x * inversePhase m x) =
      (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.dft w k * completeSum k m := by
  classical
  have hw (x : ZMod q) :
      w x = (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.stdAddChar (k * x) * ZMod.dft w k := by
    simpa only [LinearEquiv.symm_apply_apply, smul_eq_mul] using
      (ZMod.invDFT_apply (ZMod.dft w) x)
  calc
    _ = (q : ℂ)⁻¹ * ∑ x : ZMod q, ∑ k : ZMod q,
          (ZMod.stdAddChar (k * x) * ZMod.dft w k) * inversePhase m x := by
      simp_rw [hw, mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [completeSum_eq_sum_phase, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- An interval is pushed onto the residue ring with its full multiplicity. -/
def intervalWeight (b : ZMod q) (L : ℕ) (x : ZMod q) : ℂ :=
  ∑ j ∈ Finset.range L, if x = b + (j : ZMod q) then 1 else 0

theorem interval_inverseSum_eq_weighted (b m : ZMod q) (L : ℕ) :
    (∑ j ∈ Finset.range L, inversePhase m (b + (j : ZMod q))) =
      ∑ x : ZMod q, intervalWeight b L x * inversePhase m x := by
  classical
  symm
  simp_rw [intervalWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- An interval coefficient is the original finite geometric progression,
with its translated phase. -/
theorem dft_intervalWeight (b k : ZMod q) (L : ℕ) :
    ZMod.dft (intervalWeight b L) k =
      ZMod.stdAddChar (-(b * k)) *
        ∑ j ∈ Finset.range L, ZMod.stdAddChar (-k) ^ j := by
  classical
  have hphase (j : ℕ) :
      ZMod.stdAddChar ((j : ZMod q) * (-k)) = ZMod.stdAddChar (-k) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ, add_mul, one_mul, AddChar.map_add_eq_mul, ih, pow_succ]
  rw [ZMod.dft_apply]
  simp_rw [smul_eq_mul, intervalWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [show -((b + (j : ZMod q)) * k) = -(b * k) + (j : ZMod q) * (-k) by ring,
    AddChar.map_add_eq_mul, hphase]

/-- The exact geometric numerator and denominator, valid at zero frequency
as an identity without division. -/
theorem dft_intervalWeight_mul_complement (b k : ZMod q) (L : ℕ) :
    (1 - ZMod.stdAddChar (-k)) * ZMod.dft (intervalWeight b L) k =
      ZMod.stdAddChar (-(b * k)) * (1 - ZMod.stdAddChar (-k) ^ L) := by
  have hgeom (z : ℂ) (n : ℕ) : (1 - z) * (∑ j ∈ Finset.range n, z ^ j) = 1 - z ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  rw [dft_intervalWeight, mul_left_comm, hgeom]

/-- For every nonzero frequency, the geometric denominator is positive
after taking its norm and the numerator has norm at most two. -/
theorem norm_dft_intervalWeight_le (b k : ZMod q) (L : ℕ) (hk : k ≠ 0) :
    ‖ZMod.dft (intervalWeight b L) k‖ ≤ 2 / ‖1 - ZMod.stdAddChar (-k)‖ := by
  have hnorm (x : ZMod q) : ‖ZMod.stdAddChar x‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hne : (1 : ℂ) - ZMod.stdAddChar (-k) ≠ 0 := by
    intro h
    have he : ZMod.stdAddChar (-k) = ZMod.stdAddChar (0 : ZMod q) := by
      simpa using (sub_eq_zero.mp h).symm
    exact hk (neg_eq_zero.mp (ZMod.injective_stdAddChar he))
  apply (le_div_iff₀ (norm_pos_iff.mpr hne)).2
  calc
    _ = ‖(1 - ZMod.stdAddChar (-k)) * ZMod.dft (intervalWeight b L) k‖ := by
      rw [norm_mul, mul_comm]
    _ = ‖1 - ZMod.stdAddChar (-k) ^ L‖ := by
      rw [dft_intervalWeight_mul_complement, norm_mul, hnorm, one_mul]
    _ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) (ZMod.stdAddChar (-k) ^ L)
      norm_num [norm_pow, hnorm] at h
      exact h

/-- The exact interval completion, including the zero frequency. -/
theorem interval_inverseSum_eq_complete (b m : ZMod q) (L : ℕ) :
    (∑ j ∈ Finset.range L, inversePhase m (b + (j : ZMod q))) =
      (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.dft (intervalWeight b L) k * completeSum k m :=
  (interval_inverseSum_eq_weighted b m L).trans (weighted_sum_eq_complete (intervalWeight b L) m)

/-- If one bound controls every complete sum, the interval sum is controlled
by the same bound times the normalized full Fourier mass. -/
theorem norm_interval_inverseSum_le_of_complete
    (b m : ZMod q) (L : ℕ) {B : ℝ} (hB : ∀ k, ‖completeSum k m‖ ≤ B) :
    ‖∑ j ∈ Finset.range L, inversePhase m (b + (j : ZMod q))‖ ≤
      B / q * ∑ k : ZMod q, ‖ZMod.dft (intervalWeight b L) k‖ := by
  rw [interval_inverseSum_eq_complete, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ k : ZMod q,
          ‖ZMod.dft (intervalWeight b L) k * completeSum k m‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (q : ℝ)⁻¹ * ∑ k : ZMod q, ‖ZMod.dft (intervalWeight b L) k‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end RiemannResearch.Analysis.Kloosterman
