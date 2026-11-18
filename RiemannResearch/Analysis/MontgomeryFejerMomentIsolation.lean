/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerPower
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Exact collision recovery from finitely many Fejér moments

A finite mixture of power sequences can be tested by a polynomial in the shift.
We normalize the polynomial to be one at the equal-ordinate mode, and use all
other modes as roots. This gives an exact signed test in any positive frequency
band at each finite cutoff. The factors depend on the nonzero gaps, and become
ill-conditioned when their Fejér responses approach one.
-/

noncomputable section

open Set Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor

open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson

/-- Apply the polynomial with the stated roots, normalized to be one at 1,
to the forward shift of a sequence. -/
def isolateFejerMoment : List ℝ → (ℕ → ℝ) → ℕ → ℝ
  | [], f, n => f n
  | r :: rs, f, n =>
    isolateFejerMoment rs (fun k => (f (k + 1) - r * f k) / (1 - r)) n

private def isolationMultiplier (roots : List ℝ) (x : ℝ) : ℝ :=
  (roots.map fun r => (x - r) / (1 - r)).prod

private theorem isolationMultiplier_one (roots : List ℝ) (h : ∀ r ∈ roots, r ≠ 1) :
    isolationMultiplier roots 1 = 1 := by
  induction roots with
  | nil => simp [isolationMultiplier]
  | cons r rs ih =>
    have hr : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm (h r (by simp)))
    have ht := ih (fun x hx => h x (by simp [hx]))
    change (1 - r) / (1 - r) * isolationMultiplier rs 1 = 1
    rw [div_self hr, ht, one_mul]

private theorem isolationMultiplier_eq_zero {roots : List ℝ} {x : ℝ} (h : x ∈ roots) :
    isolationMultiplier roots x = 0 := by
  induction roots with
  | nil => simp at h
  | cons r rs ih =>
    rcases List.mem_cons.mp h with he | ht
    · change (x - r) / (1 - r) * isolationMultiplier rs x = 0
      simp [he]
    · change (x - r) / (1 - r) * isolationMultiplier rs x = 0
      rw [ih ht, mul_zero]

private theorem isolateFejerMoment_sum_powers {ι : Type*} [Fintype ι]
    (roots : List ℝ) (a x : ι → ℝ) (n : ℕ) :
    isolateFejerMoment roots (fun k => ∑ i, a i * (x i) ^ k) n =
      ∑ i, a i * (x i) ^ n * isolationMultiplier roots (x i) := by
  classical
  induction roots generalizing a with
  | nil => simp [isolateFejerMoment, isolationMultiplier]
  | cons r rs ih =>
    have hstep :
        (fun k : ℕ =>
          ((∑ i, a i * (x i) ^ (k + 1)) - r * (∑ i, a i * (x i) ^ k)) / (1 - r)) =
          fun k => ∑ i, (a i * ((x i - r) / (1 - r))) * (x i) ^ k := by
      funext k
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [isolateFejerMoment, hstep, ih]
    apply Finset.sum_congr rfl
    intro i _
    simp only [isolationMultiplier, List.map_cons, List.prod_cons]
    ring

theorem isolateFejerMoment_eq_of_agree (roots : List ℝ) (f g : ℕ → ℝ) (n : ℕ)
    (h : ∀ k ≤ n + roots.length, f k = g k) :
    isolateFejerMoment roots f n = isolateFejerMoment roots g n := by
  induction roots generalizing f g with
  | nil => exact h n (by simp)
  | cons r rs ih =>
    simp only [isolateFejerMoment]
    apply ih
    intro k hk
    rw [h (k + 1) (by simpa only [List.length_cons] using (show
      k + 1 ≤ n + (rs.length + 1) by omega)),
      h k (by simpa only [List.length_cons] using (show
        k ≤ n + (rs.length + 1) by omega))]

private theorem sincSquared_lt_one_of_ne_zero {R v : ℝ} (hR : 0 < R) (hv : v ≠ 0) :
    sincSquared R v < 1 := by
  let y := R * v / 2
  have hy : y ≠ 0 := div_ne_zero (mul_ne_zero hR.ne' hv) (by norm_num)
  have hs : |Real.sinc y| < 1 := by
    rw [Real.sinc_of_ne_zero hy, abs_div, div_lt_one (abs_pos.mpr hy)]
    exact Real.abs_sin_lt_abs hy
  have hsq := (sq_lt_sq₀ (abs_nonneg _) zero_le_one).2 hs
  rw [sq_abs, one_pow] at hsq
  exact hsq

/-- Nonzero Fejér responses at a finite cutoff, enumerated with repetition. -/
def nonzeroFejerModes (T R : ℝ) : List ℝ := by
  classical
  exact (((Finset.univ : Finset (Copies T × Copies T)).filter fun p =>
    copyOrdinate T p.1 ≠ copyOrdinate T p.2).toList).map fun p =>
      sincSquared R (Real.log T * (copyOrdinate T p.1 - copyOrdinate T p.2))

private theorem one_not_mem_nonzeroFejerModes {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    {r : ℝ} (hr : r ∈ nonzeroFejerModes T R) : r ≠ 1 := by
  classical
  unfold nonzeroFejerModes at hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have hp' := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
  exact (sincSquared_lt_one_of_ne_zero hR
    (mul_ne_zero (Real.log_pos hT).ne' (sub_ne_zero.mpr hp'))).ne

private theorem mem_nonzeroFejerModes {T R : ℝ} (p : Copies T × Copies T)
    (hp : copyOrdinate T p.1 ≠ copyOrdinate T p.2) :
    sincSquared R (Real.log T * (copyOrdinate T p.1 - copyOrdinate T p.2)) ∈
      nonzeroFejerModes T R := by
  classical
  unfold nonzeroFejerModes
  exact List.mem_map.mpr ⟨p, Finset.mem_toList.mpr (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hp⟩), rfl⟩

/-- The exact signed Fejér test equals the distinct-zero collision count. -/
theorem normalized_isolatedFejerMoment_sub_analytic_eq {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) :
    isolateFejerMoment (nonzeroFejerModes T R)
      (fun n => (T * Real.log T / (2 * Real.pi)) * fejerPowerFormFactor T R n) 0 -
      (analyticPairCount T : ℝ) = (distinctZeroCollision T : ℝ) := by
  classical
  let D := T * Real.log T / (2 * Real.pi)
  have hD : D ≠ 0 :=
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
  let d (p : Copies T × Copies T) := copyOrdinate T p.1 - copyOrdinate T p.2
  have hf : (fun n => D * fejerPowerFormFactor T R n) =
      fun n => ∑ p : Copies T × Copies T, cauchyWeight (d p) *
        sincSquared R (Real.log T * d p) ^ n := by
    funext n
    rw [fejerPowerFormFactor_eq_kernelEnergy T hR]
    change D * (_ / D) = _
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hD]
    exact (Fintype.sum_prod_type (fun p : Copies T × Copies T => cauchyWeight (d p) *
      sincSquared R (Real.log T * d p) ^ n)).symm
  have hc : isolateFejerMoment (nonzeroFejerModes T R)
      (fun n => D * fejerPowerFormFactor T R n) 0 = (actualCollision T : ℝ) := by
    rw [hf, isolateFejerMoment_sum_powers, Fintype.sum_prod_type]
    unfold actualCollision occurrenceCollision
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : copyOrdinate T i = copyOrdinate T j
    · have hd : d (i, j) = 0 := sub_eq_zero.mpr h
      simp [hd, h, sincSquared, cauchyWeight, isolationMultiplier_one _ (fun _ =>
        one_not_mem_nonzeroFejerModes hT hR)]
    · simp [d, h, isolationMultiplier_eq_zero (mem_nonzeroFejerModes (i, j) h)]
  change _ - (analyticPairCount T : ℝ) = _
  rw [hc, collision_eq_analytic_add_distinctZeroCollision]
  push_cast
  ring

/-- At most the square of the occurrence count many modes are used. -/
theorem nonzeroFejerModes_length_le (T R : ℝ) :
    (nonzeroFejerModes T R).length ≤ (Ncount 0 T) ^ 2 := by
  classical
  unfold nonzeroFejerModes
  simp only [List.length_map, Finset.length_toList]
  apply (Finset.card_filter_le _ _).trans
  simp only [Finset.card_univ, Fintype.card_prod, card_copies, pow_two, le_refl]

/-- A width (B) can be allotted before looking at the gaps. Only the coefficients
of the signed test, through its list of roots, use the ordinates. -/
def isolationStepRadius (T B : ℝ) : ℝ := B / ((Ncount 0 T : ℝ) ^ 2 + 1)

theorem isolatedFejerMoment_eq_of_eqOn {T B : ℝ} (hB : 0 < B) {f g : ℝ → ℝ}
    (h : EqOn f g (Icc (-B) B)) :
    let R := isolationStepRadius T B
    isolateFejerMoment (nonzeroFejerModes T R)
      (fun n => iteratedFejerTriangle R f n 0) 0 =
    isolateFejerMoment (nonzeroFejerModes T R)
      (fun n => iteratedFejerTriangle R g n 0) 0 := by
  dsimp only
  let R := isolationStepRadius T B
  have hR : 0 < R := div_pos hB (by positivity)
  apply isolateFejerMoment_eq_of_agree
  intro n hn
  have hn' : n ≤ (Ncount 0 T) ^ 2 :=
    (by simpa only [zero_add] using hn : n ≤ (nonzeroFejerModes T R).length).trans
      (nonzeroFejerModes_length_le T R)
  have hcast : (n : ℝ) ≤ (Ncount 0 T : ℝ) ^ 2 := by exact_mod_cast hn'
  have hb : (n : ℝ) * R ≤ B := by
    change (n : ℝ) * (B / ((Ncount 0 T : ℝ) ^ 2 + 1)) ≤ B
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (Ncount 0 T : ℝ) ^ 2 + 1)).2
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_right (hcast.trans (le_add_of_nonneg_right zero_le_one)) hB.le
  apply iteratedFejerTriangle_eq_of_eqOn hR.le
  intro x hx
  simp only [mem_Icc, zero_sub, zero_add] at hx
  exact h ⟨(neg_le_neg hb).trans hx.1, hx.2.trans hb⟩

/-- For every positive band width, the corresponding finite signed Fourier test
recovers the exact RH certificate at cofinal cutoffs. -/
theorem cofinal_isolatedFejerMoment_lt_two_iff_RH {B : ℝ} (hB : 0 < B) :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧
      isolateFejerMoment (nonzeroFejerModes T (isolationStepRadius T B))
        (fun n => (T * Real.log T / (2 * Real.pi)) *
          fejerPowerFormFactor T (isolationStepRadius T B) n) 0 -
        (analyticPairCount T : ℝ) < 2) ↔ RiemannHypothesis := by
  have hcut {T : ℝ} (hT : 1 < T) :
      isolateFejerMoment (nonzeroFejerModes T (isolationStepRadius T B))
        (fun n => (T * Real.log T / (2 * Real.pi)) *
          fejerPowerFormFactor T (isolationStepRadius T B) n) 0 -
        (analyticPairCount T : ℝ) < 2 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
    have hR : 0 < isolationStepRadius T B := div_pos hB (by positivity)
    rw [normalized_isolatedFejerMoment_sub_analytic_eq hT hR]
    constructor
    · intro h ρ hρ
      by_contra hoff
      have hc : (2 : ℝ) ≤ distinctZeroCollision T := by
        exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
      exact (not_lt_of_ge hc) h
    · intro h
      have he := (collision_eq_analyticPairCount_iff T).mpr h
      rw [collision_eq_analytic_add_distinctZeroCollision] at he
      have hz : distinctZeroCollision T = 0 := by omega
      simp [hz]
  rw [← cofinal_fejer_critical_line_iff_RH, cofinal_fejer_critical_line_iff]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hHT, hT, hs⟩ := h H
    obtain ⟨hz, hi, hheight⟩ := mem_cutoff.mp hρ
    exact (hcut hT).mp hs ρ (mem_cutoff.mpr ⟨hz, hi, hheight.trans hHT⟩)
  · intro h H
    let T := max H 2
    have hT : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_right H 2)
    exact ⟨T, le_max_left H 2, hT, (hcut hT).mpr (h T)⟩

end RiemannResearch.Analysis.MontgomeryFormFactor
