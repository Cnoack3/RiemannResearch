/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.CombinedAuditedCore
import RiemannResearch.RH.CombinedAuditedInventory
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.CompleteLattice.Basic

/-!
# Deterministic combined-gain certificates

This module formalizes the order and scalar inequalities used by the
combined-gain reduction in Sections G.69--G.80 of the user-provided
continuation. It does not assert the arithmetic sampling, legal-conductor
realization, Jacquet return-covariance, G3, or Riemann hypothesis inputs.

Source: user-provided argument. The source supports the statements and proof
strategy; the analytic and arithmetic hypotheses needed for RH remain open.
-/

namespace RiemannResearch.RH.CombinedGain

open scoped BigOperators

/-- Supremal score over a family of admissible dual witnesses. -/
def dualCapture {ι α : Type*} [CompleteLattice α]
    (S : Set ι) (score : ι → α) : α :=
  ⨆ i ∈ S, score i

/-- Compressing to a smaller legal witness family cannot increase capture. -/
theorem dualCapture_mono {ι α : Type*} [CompleteLattice α]
    {S T : Set ι} {score : ι → α} (hST : S ⊆ T) :
    dualCapture S score ≤ dualCapture T score :=
  iSup_le_iSup_of_subset hST

/-- The scalar division step in the inverse-free dual Gram certificate. -/
theorem inverseFree_of_cauchy
    {numerator denominator gain : ℝ}
    (hden : 0 < denominator)
    (hcauchy : numerator ^ 2 ≤ denominator * gain) :
    numerator ^ 2 / denominator ≤ gain := by
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hcauchy)

/-- An actual-direction overlap bound yields the standardized inverse-free
lower bound once the concrete Gram Cauchy premise is supplied. -/
theorem gain_lowerBound_of_actualDirectionOverlap
    {signal overlap ε gain : ℝ}
    (hsignal : 0 < signal)
    (hε : -1 < ε)
    (hden : 0 < signal + overlap)
    (hoverlap : overlap ≤ ε * signal)
    (hcauchy : signal ^ 2 ≤ (signal + overlap) * gain) :
    signal / (1 + ε) ≤ gain := by
  have hεden : 0 < 1 + ε := by linarith
  have hscaled :
      signal * (signal + overlap) ≤ signal ^ 2 * (1 + ε) := by
    have hmul := mul_le_mul_of_nonneg_left hoverlap hsignal.le
    nlinarith
  have hquot :
      signal / (1 + ε) ≤ signal ^ 2 / (signal + overlap) :=
    (div_le_div_iff₀ hεden hden).2 hscaled
  exact hquot.trans (inverseFree_of_cauchy hden hcauchy)

/-- Finite-set Cauchy in the classwise second-moment form. -/
theorem classwiseSecondMoment
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (x i) ^ 2 := by
  simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := x))

/-- Divide classwise Cauchy by a positive class cardinality. -/
theorem averageSq_le_sumSq
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (x : ι → ℝ) :
    (∑ i ∈ s, x i) ^ 2 / (s.card : ℝ) ≤
      ∑ i ∈ s, (x i) ^ 2 := by
  have hcardNat : 0 < s.card := Finset.card_pos.mpr hs
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hcardNat
  apply (div_le_iff₀ hcard).2
  simpa [mul_comm] using classwiseSecondMoment s x

/-- The global second-moment participation comparison. -/
theorem participation_of_secondMoment
    {A B E N : ℝ}
    (hA : 0 < A) (hE : 0 < E) (hN : 0 < N)
    (hmoment : A ^ 2 ≤ N * B) :
    A / (E * N) ≤ B / (E * A) := by
  apply (div_le_div_iff₀ (mul_pos hE hN) (mul_pos hE hA)).2
  have hscaled := mul_le_mul_of_nonneg_left hmoment hE.le
  nlinarith

/-- Legal residual factors are bounded by the exponential of negative
cumulative participation. -/
theorem productOneSub_le_expNegSum
    {ι : Type*} (s : Finset ι) (κ : ι → ℝ)
    (hκone : ∀ i ∈ s, κ i ≤ 1) :
    (∏ i ∈ s, (1 - κ i)) ≤
      Real.exp (-(∑ i ∈ s, κ i)) := by
  calc
    (∏ i ∈ s, (1 - κ i)) ≤
        ∏ i ∈ s, Real.exp (-κ i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hκone i hi)
      · intro i hi
        exact Real.one_sub_le_exp_neg (κ i)
    _ = Real.exp (∑ i ∈ s, -κ i) := by
      symm
      simpa using Real.exp_sum s (fun i => -κ i)
    _ = Real.exp (-(∑ i ∈ s, κ i)) := by
      congr 1
      simp

/-- The exact greedy product ledger dominates exponential accumulation. -/
theorem exponentialAccumulation_le_exactProductGain
    {ι : Type*} (s : Finset ι) (κ ω : ι → ℝ)
    (hωone : ∀ i ∈ s, ω i ≤ 1)
    (hκω : ∀ i ∈ s, κ i ≤ ω i) :
    1 - Real.exp (-(∑ i ∈ s, κ i)) ≤
      1 - ∏ i ∈ s, (1 - ω i) := by
  have hprod :
      (∏ i ∈ s, (1 - ω i)) ≤
        ∏ i ∈ s, (1 - κ i) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact sub_nonneg.mpr (hωone i hi)
    · intro i hi
      linarith [hκω i hi]
  have hexp :
      (∏ i ∈ s, (1 - κ i)) ≤
        Real.exp (-(∑ i ∈ s, κ i)) :=
    productOneSub_le_expNegSum s κ fun i hi =>
      (hκω i hi).trans (hωone i hi)
  linarith

/-- Global rational lower bound `x/(1+x) ≤ 1-exp(-x)` for `x ≥ 0`. -/
theorem ratio_le_oneSubExpNeg (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : 1 / Real.exp x ≤ 1 / (1 + x) :=
    one_div_le_one_div_of_le hden hexp
  have hrewrite : x / (1 + x) = 1 - 1 / (1 + x) := by
    field_simp [ne_of_gt hden]
    <;> ring
  rw [hrewrite, Real.exp_neg]
  have hinv' : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by
    simpa [one_div] using hinv
  simpa [one_div] using (sub_le_sub_left hinv' 1)

/-- Pointwise exponential capture implies threshold-free weighted rational
capture. -/
theorem weightedCapture_of_exponential
    {ι : Type*} (s : Finset ι)
    (weight cumulative capture : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hcumulative : ∀ i ∈ s, 0 ≤ cumulative i)
    (hcapture : ∀ i ∈ s,
      1 - Real.exp (-cumulative i) ≤ capture i) :
    (∑ i ∈ s, weight i * (cumulative i / (1 + cumulative i))) ≤
      ∑ i ∈ s, weight i * capture i := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hweight i hi)
  exact (ratio_le_oneSubExpNeg (cumulative i) (hcumulative i hi)).trans
    (hcapture i hi)

/-- Certified capture times certified absolute cross-flux bounds the full
factorized observable. -/
theorem jointProduct_closure
    {c certifiedCapture capture certifiedFlux riccati scale : ℝ}
    (hscale : 0 < scale)
    (hcertifiedCapture : 0 ≤ certifiedCapture)
    (hflux : 0 ≤ certifiedFlux)
    (hcapture : certifiedCapture ≤ capture)
    (hriccati : certifiedFlux / scale ≤ riccati)
    (hcertificate :
      c ≤ certifiedCapture * (certifiedFlux / scale)) :
    c ≤ capture * riccati := by
  have hratio : 0 ≤ certifiedFlux / scale :=
    div_nonneg hflux hscale.le
  have hriccatiNonneg : 0 ≤ riccati := hratio.trans hriccati
  calc
    c ≤ certifiedCapture * (certifiedFlux / scale) := hcertificate
    _ ≤ certifiedCapture * riccati :=
      mul_le_mul_of_nonneg_left hriccati hcertifiedCapture
    _ ≤ capture * riccati :=
      mul_le_mul_of_nonneg_right hcapture hriccatiNonneg

/-- A joint product certificate with capture at most one still forces the
absolute cross-flux scale. -/
theorem jointProduct_forces_absoluteScale
    {c capture flux scale : ℝ}
    (hscale : 0 < scale)
    (hflux : 0 ≤ flux)
    (hcapture : capture ≤ 1)
    (hjoint : c ≤ capture * (flux / scale)) :
    c * scale ≤ flux := by
  have hratio : 0 ≤ flux / scale := div_nonneg hflux hscale.le
  have hupper :
      capture * (flux / scale) ≤ 1 * (flux / scale) :=
    mul_le_mul_of_nonneg_right hcapture hratio
  have hcRatio : c ≤ flux / scale := by
    simpa using hjoint.trans hupper
  exact (le_div_iff₀ hscale).mp hcRatio

end RiemannResearch.RH.CombinedGain
