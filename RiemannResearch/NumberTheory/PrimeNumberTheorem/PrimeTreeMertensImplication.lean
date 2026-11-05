/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMobiusSubtree
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeOrderedMobius
import RiemannResearch.RH.TreeEulerCriterion
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # From square-root cancellation in any fixed prime cylinder to RH
The Abel integral for the ordinary Möbius partial sums supplies an analytic
extension of the signed Euler tree. This proves the sufficient direction of
Titchmarsh's Theorem 14.25(C) without a published theorem as a hypothesis.
The finite arithmetic transfer then gives the same implication for each
fixed cylinder of Section 9 of *Prime trees, fractional parts, and zeta zeros*. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

private def mertensStep : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x => (M (⌊x⌋₊ : ℝ) : ℂ))

private theorem mertensStep_measurable : Measurable mertensStep := by
  have h : Measurable (fun x : ℝ => M (⌊x⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => M (n : ℝ))).comp Nat.measurable_floor
  exact (Complex.continuous_ofReal.measurable.comp h).indicator measurableSet_Ioi

private theorem mertensStep_locallyIntegrable :
    LocallyIntegrableOn mertensStep (Ioi (0 : ℝ)) := by
  have hi : LocallyIntegrableOn (fun x : ℝ => x) (Ioi (0 : ℝ)) :=
    continuous_id.locallyIntegrable.locallyIntegrableOn _
  apply hi.mono mertensStep_measurable.aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (le_of_lt hx)
    simp only [mertensStep, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx0]
    exact (M_nat_abs_le_self ⌊x⌋₊).trans (Nat.floor_le hx0)
  · simp [mertensStep, hx]

private theorem mertensStep_bigO {a : ℝ} (ha : 0 ≤ a)
    (h : PowerBound a (fun n => M (n : ℝ))) :
    mertensStep =O[atTop] (fun x : ℝ => x^a) := by
  obtain ⟨C, hC, hb⟩ := h
  apply IsBigO.of_bound C
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hm : x ∈ Ioi (1:ℝ) := hx
  have hx0 := (show 0 ≤ x by linarith)
  simp only [mertensStep, Set.indicator_of_mem hm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 a)]
  exact (hb ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    (Nat.cast_nonneg _) (Nat.floor_le hx0) ha) hC)

private theorem mertensStep_bigO_zero (b : ℝ) :
    mertensStep =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
  apply IsBigO.of_bound 0
  have hnear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hnear] with x hx
  change x < 1 at hx
  have hx' : x ∉ Ioi (1:ℝ) := by change ¬ 1 < x; exact not_lt.mpr hx.le
  simp [mertensStep, hx']

private theorem mertensStep_mellin_eq (s : ℂ) :
    mellin mertensStep (-s) =
      ∫ x in Ioi (1:ℝ), (M (⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ)^(-(s+1)) := by
  unfold mellin
  calc
    _ = ∫ x in Ioi (0:ℝ), (Ioi (1:ℝ)).indicator
        (fun t : ℝ => (M (⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ)^(-(s+1))) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      by_cases hx : x ∈ Ioi (1:ℝ)
      · simp only [mertensStep, Set.indicator_of_mem hx, smul_eq_mul,
          show -s - 1 = -(s+1) by ring, mul_comm]
      · simp [mertensStep,hx]
    _ = _ := by rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr
                  (Ioi_subset_Ioi (show (0:ℝ) ≤ 1 by norm_num))]

private theorem sum_moebius_eq_mertens (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ)) = (M (n : ℝ) : ℂ) := by
  simp only [M, Nat.floor_natCast, Complex.ofReal_sum, Complex.ofReal_intCast]
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hk).2
  · intro k hk hk'
    have he : k = 0 := by simp only [Finset.mem_Icc, Finset.mem_Iic] at *; omega
    simp [he]

private theorem mertens_rhs {s : ℂ} (hs : 1 < s.re) :
    s * mellin mertensStep (-s) = (riemannZeta s)⁻¹ := by
  have ho : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      fun n : ℕ => (n:ℝ)^(1:ℝ) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
    simp only [sum_moebius_eq_mertens, Complex.norm_real, Real.norm_eq_abs,
      Real.rpow_one, abs_of_nonneg hn, one_mul]
    exact M_nat_abs_le_self n
  have h := LSeries_eq_mul_integral (fun n => (ArithmeticFunction.moebius n : ℂ))
    (by norm_num : (0:ℝ) ≤ 1) hs (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs) ho
  simp_rw [sum_moebius_eq_mertens] at h
  rw [mertensStep_mellin_eq, ← h]
  have hid := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hid
  apply mul_left_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le)
  simpa only [mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le)] using hid

/-- Square-root-plus-epsilon Mertens cancellation implies Mathlib's RH.
The extension is the actual Mellin integral of the summatory Möbius function. -/
theorem riemannHypothesis_of_mertens_power_forall
    (h : ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (fun n => M (n : ℝ))) : RiemannHypothesis := by
  apply RiemannResearch.RH.PrimeTreeEuler.riemannHypothesis_iff_rootExtends.mpr
  refine ⟨fun s => s * mellin mertensStep (-s), ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun s => s * mellin mertensStep (-s))
        {s : ℂ | (1/2:ℝ) < s.re} := by
      intro s hs
      change (1/2:ℝ) < s.re at hs
      let ε := (s.re - 1/2)/2
      have he : 0 < ε := by dsimp [ε]; linarith
      have htop := mertensStep_bigO (a := 1/2+ε) (by linarith) (h ε he)
      have htop' : mertensStep =O[atTop] (fun x : ℝ => x^(-(-(1/2+ε)))) := by simpa using htop
      have hm := mellin_differentiableAt_of_isBigO_rpow mertensStep_locallyIntegrable htop'
        (s := -s) (by change -s.re < -(1/2+ε); dsimp [ε]; linarith)
        (mertensStep_bigO_zero (-s.re-1)) (by simp only [Complex.neg_re]; linarith)
      exact (differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)).differentiableWithinAt
    exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  · intro s hs
    change Tendsto _ atTop (𝓝 (s * mellin mertensStep (-s)))
    rw [mertens_rhs hs]
    exact RiemannResearch.RH.PrimeTreeEuler.tendsto_treeRoot hs

/-- One fixed squarefree cylinder suffices. No Littlewood or RH-equivalence
hypothesis is required for this direction. -/
theorem riemannHypothesis_of_cylinder_power_forall {r : ℕ} (hr : Squarefree r)
    (hr0 : 0 < r) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ r → p ∈ B)
    (h : ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (cylinder r B)) : RiemannHypothesis :=
  riemannHypothesis_of_mertens_power_forall fun ε hε =>
    (mertens_iff_cylinder hr hr0 B hB hcover (show 0 < 1/2+ε by linarith)).mpr (h ε hε)

theorem riemannHypothesis_of_orderedSubtree_power_forall {r : ℕ} (hr : Squarefree r)
    (h : ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (orderedSubtree r)) : RiemannHypothesis :=
  riemannHypothesis_of_mertens_power_forall fun ε hε =>
    (mertens_iff_orderedSubtree hr (show 0 < 1/2+ε by linarith)).mpr (h ε hε)

/-- This is the two-sided statement of (34) on the recursive ordered tree.
Only the implication from RH to the ordinary Mertens bounds is supplied by
the published Littlewood theorem. The direction to RH is internal. -/
theorem riemannHypothesis_iff_orderedSubtree_of_littlewood_upper {r : ℕ} (hr : Squarefree r)
    (hLittlewood : RiemannHypothesis →
      ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (fun n => M (n : ℝ))) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
        |orderedSubtree r ⌊X⌋₊| ≤ C * X^(1/2+ε) := by
  constructor
  · intro hRH ε hε
    have hpos : 0 < 1/2+ε := by linarith
    exact (ordered_powerBound_iff_real_cutoffs r hpos).mp
      ((mertens_iff_orderedSubtree hr hpos).mp (hLittlewood hRH ε hε))
  · intro h
    exact riemannHypothesis_of_orderedSubtree_power_forall hr fun ε hε =>
      (ordered_powerBound_iff_real_cutoffs r (show 0 < 1/2+ε by linarith)).mpr (h ε hε)

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
