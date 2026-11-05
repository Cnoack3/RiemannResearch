/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.SquareDifferenceRigidity
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.QSquarefreeDisplacementSignedTails
import RiemannResearch.RH.QCofinalDisplacementMoments
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # One-sided physical increments of the matched displacement

Source: the user's question about physical differences. A common sign at the
squarefree sites makes the displacement monotone starting at site one, so its
physical values have an eventual sign. Recurrence on powers allows an
asymptotic one-sided sign hypothesis instead. -/

noncomputable section
open Filter
open scoped Topology
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert SquarefreeRadicalDifference QSquarefreeDisplacementRegularity
open UniqueFactorizationMonoid

/-- No control of the size of the squarefree jumps is needed if they all
have the same sign. The boundary increment at one is unrestricted. -/
theorem riemannHypothesis_of_one_sided_squarefree_differences (ε : ℝ) (hε : |ε| = 1)
    (h : ∀ s : ℕ, 2 ≤ s → Squarefree s → 0 ≤ ε * qDifference displacement s) :
    RiemannHypothesis := by
  let v (n : ℕ) := ε * qSequence displacement (n + 1)
  have hv : Monotone v := monotone_nat_of_le_succ fun n => by
    have htwo : 2 ≤ n + 2 := by omega
    have hrad := h (radical (n + 2)) (Nat.two_le_radical_iff.mpr htwo) squarefree_radical
    rw [← displacement_difference_radical _ htwo] at hrad
    unfold qDifference at hrad
    rw [show n + 2 - 1 = n + 1 by omega, mul_sub] at hrad
    exact sub_nonneg.mp hrad
  by_cases hex : ∃ k : ℕ, 0 ≤ v k
  · obtain ⟨k, hk⟩ := hex
    apply riemannHypothesis_of_eventual_displacement_sign (-ε) (by simpa only [abs_neg] using hε)
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    have hh := hk.trans (hv (show k ≤ n - 1 by omega))
    change 0 ≤ ε * qSequence displacement (n - 1 + 1) at hh
    rw [show n - 1 + 1 = n by omega] at hh
    simpa only [neg_mul] using neg_nonpos.mpr hh
  · apply riemannHypothesis_of_eventual_displacement_sign ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hh : v (n - 1) ≤ 0 := le_of_lt (lt_of_not_ge (fun hn' => hex ⟨_, hn'⟩))
    change ε * qSequence displacement (n - 1 + 1) ≤ 0 at hh
    simpa only [show n - 1 + 1 = n by omega] using hh

private theorem exponent_add_one_le_pow (s : ℕ) (hs : 2 ≤ s) (k : ℕ) : k + 1 ≤ s ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hh := Nat.mul_le_mul_left (s ^ k) hs
    omega

/-- An asymptotic lower bound of zero for either sign of the differences
suffices, including when the differences have no two-sided limit. -/
theorem riemannHypothesis_of_asymptotic_one_sided_differences (ε : ℝ) (hε : |ε| = 1)
    (h : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop, -a ≤ ε * qDifference displacement n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_one_sided_squarefree_differences ε hε
  intro s hs hsf
  by_contra! hneg
  have ha : 0 < -(ε * qDifference displacement s) / 2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h _ ha)
  have hn : N ≤ s ^ (N + 1) := by
    have := exponent_add_one_le_pow s hs (N + 1)
    omega
  have hh := hN _ hn
  rw [displacement_difference_squarefree_power hs hsf (by omega : N + 1 ≠ 0)] at hh
  linarith

/-- A uniform bound on one side of the matched displacement gives a harmonic
prefix of at most C times the harmonic number. The opposite side is unrestricted. -/
theorem riemannHypothesis_of_one_sided_bounded_displacement (ε C : ℝ)
    (hε : |ε| = 1) (hC : 0 ≤ C) (hb : ∀ n, ε * qSequence displacement n ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_harmonic_polylog 1 (2 * C) zero_le_one (by positivity)
  apply Filter.Eventually.frequently
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X hX
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide ε X := by
    rcases le_total 0 ε with h | h
    · have he : ε = 1 := (abs_of_nonneg h).symm.trans hε
      rw [he]
      exact min_le_left _ _
    · rw [abs_of_nonpos h] at hε
      have he : ε = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  have hh : (∑ n ∈ Finset.range (X + 1), C / (n : ℝ)) = C * (harmonic X : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero, harmonic, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, Finset.mul_sum, div_eq_mul_inv, inv_zero, mul_zero]
  calc
    minimumHarmonicPrefix X ≤ harmonicSide ε X := hmin
    _ ≤ ∑ n ∈ Finset.range (X + 1), C / (n : ℝ) :=
      Finset.sum_le_sum (fun n _ => div_le_div_of_nonneg_right (max_le (hb n) hC) (Nat.cast_nonneg n))
    _ = C * (harmonic X : ℝ) := hh
    _ ≤ C * (1 + Real.log (X : ℝ)) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) hC
    _ ≤ _ := by
      rw [Real.rpow_one]
      calc
        _ ≤ C * (2 * Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
        _ = _ := by ring

/-- The anchor at zero matters. Flat physical values on the positive integers
give a Möbius profile, including the charge at one. -/
theorem charges_of_constant_on_positives (f : ℕ → ℝ) (hf : f 0 = 0)
    (hflat : ∀ n, 1 ≤ n → f n = f 1) (m : ℕ) (hm : 0 < m) :
    Pareto.mobiusDifference m f = f 1 * (ArithmeticFunction.moebius m : ℝ) := by
  have hfun : f = fun k : ℕ => f 1 * (if k = 0 then 0 else 1) := by
    funext k
    cases k with
    | zero => simp [hf]
    | succ k => simpa using hflat (k + 1) (by omega)
  calc
    _ = Pareto.mobiusDifference m (fun k : ℕ => f 1 * (if k = 0 then 0 else 1)) :=
      congrArg (Pareto.mobiusDifference m) hfun
    _ = _ := by rw [Pareto.mobiusDifference_const_mul_fn, Pareto.mobiusDifference_one m hm]

/-- Every possible finite limit of the ordinary increments of a physical
sublinear square-recurrent sequence equals zero. -/
theorem zero_limit_of_recurrent_differences (f : ℕ → ℝ) (ℓ : ℝ)
    (hsub : Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0))
    (hsq : ∀ n, 2 ≤ n → f (n ^ 2) - f (n ^ 2 - 1) = f n - f (n - 1))
    (hl : Tendsto (fun n : ℕ => f n - f (n - 1)) atTop (𝓝 ℓ)) : ℓ = 0 := by
  let g (n : ℕ) := f n - (n : ℝ) * ℓ
  have hstep (n : ℕ) (hn : 1 ≤ n) :
      g n - g (n - 1) = (f n - f (n - 1)) - ℓ := by
    dsimp only [g]
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  have hg := RiemannResearch.NumberTheory.SquareDifferenceRigidity.constant_of_difference_tendsto_zero g
    (fun n hn => by rw [hstep _ (by have : 0 < n ^ 2 := pow_pos (by omega) 2; omega),
      hstep _ (by omega), hsq n hn]) (by
      have hc := hl.sub_const ℓ
      rw [sub_self] at hc
      exact hc.congr' ((eventually_ge_atTop (1 : ℕ)).mono fun n hn => (hstep n hn).symm))
  have hc : Tendsto (fun n : ℕ => g 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have he : (fun n : ℕ => g 1 / (n : ℝ) + ℓ) =ᶠ[atTop] (fun n : ℕ => f n / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [← hg n hn]
    dsimp only [g]
    field_simp [hn0]
    <;> ring
  have ht := (hc.add_const ℓ).congr' he
  rw [zero_add] at ht
  exact tendsto_nhds_unique ht hsub

/-- The ordinary difference limit is equivalent to vanishing of the actual
matched displacement, independently of the subcritical approximation input. -/
theorem finite_difference_limit_iff_displacement_zero :
    (∃ ℓ : ℝ, Tendsto (fun n : ℕ => qDifference displacement n) atTop (𝓝 ℓ)) ↔
      displacement = 0 := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have hs := fun n hn => QSquarefreeMultiplierRigidity.closure_difference_square
      displacement_mem n hn
    have hl := zero_limit_of_recurrent_differences (qSequence displacement) ℓ
      (qSequence_div_nat_tendsto_zero displacement) hs hℓ
    rw [hl] at hℓ
    have hc := RiemannResearch.NumberTheory.SquareDifferenceRigidity.constant_of_difference_tendsto_zero
      _ hs hℓ
    apply displacement_eq_zero_of_residual_eq_zero
    apply residual_eq_zero_of_displacement_physically_bounded |qSequence displacement 1|
    intro n
    cases n with
    | zero => simpa only [qSequence_zero, abs_zero] using abs_nonneg (qSequence displacement 1)
    | succ k => rw [hc (k + 1) (by omega)]
  · intro hz
    refine ⟨0, ?_⟩
    simp only [hz, qDifference]
    have hzero (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
      cases n <;> simp [qSequence]
    simp only [hzero, sub_zero]
    exact tendsto_const_nhds

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
