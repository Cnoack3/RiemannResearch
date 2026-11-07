/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QValuationConditionalLegality
import RiemannResearch.Analysis.ConductorLogEnvelope
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual canonical growth at prime cutoffs

At a prime p the legal divisor span has only one nonzero generator, g_p.
Its canonical collocation lift is therefore an explicit scalar multiple of g_p.
The already-checked complete-Q conductor mean and norm estimates give an
unconditional lower growth bound for this actual canonical family.

This does not concern the full LCM tower. A sequence of prime cutoffs does
not exhaust the divisors, so this result does not contradict or establish
the divisor-exhausting canonical subpolynomial-growth criterion for RH.
The derivation is elementary from the user's CRT construction; no historical
novelty or published estimate for this new canonical sequence is asserted.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTPrimeCutoffGrowth
open ZetaTwoHilbert ZetaTwoProbability QCRTFiniteCollocation
open RiemannResearch.Analysis.ConductorLogEnvelope

/-- At a prime conductor the full divisor trial space is one dimensional. -/
theorem prime_trial_scalar (p : ℕ) (hp : p.Prime) (f : QHilbert)
    (hf : f ∈ trialSpace p) : ∃ c : ℝ, f = c • qResidue p := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨d, hd, rfl⟩
      rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mem_divisors hd) with h | h
      · subst d
        exact ⟨0, by simp⟩
      · subst d
        exact ⟨1, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, rfl⟩ := ihx
      obtain ⟨b, rfl⟩ := ihy
      exact ⟨a+b, by rw [add_smul]⟩
  | smul c x hx ih =>
      obtain ⟨a, rfl⟩ := ih
      exact ⟨c*a, by rw [mul_smul]⟩

/-- Exact actual canonical lift at a prime cutoff, using its complete Q mean. -/
theorem canonical_prime_eq_smul (p : ℕ) (hp : p.Prime) :
    (canonical p hp.two_le : QHilbert) =
      ((1 - 1/(p : ℝ)^2) / inner ℝ qOne (qResidue p)) • qResidue p := by
  obtain ⟨c, hc⟩ := prime_trial_scalar p hp (canonical p hp.two_le)
    (canonical p hp.two_le).property
  have hm := canonical_mean p hp.two_le
  rw [hc, real_inner_smul_left] at hm
  have hm' : c * inner ℝ qOne (qResidue p) = 1 - 1/(p : ℝ)^2 := by
    simpa only [real_inner_comm] using hm
  have hpos := QValuationConditionalLegality.qResidue_mean_pos p hp.two_le
  have he : c = (1 - 1/(p : ℝ)^2) / inner ℝ qOne (qResidue p) :=
    (eq_div_iff hpos.ne').mpr hm'
  rw [hc, he]

/-- Prime cutoffs exhibit genuine target-specific growth, not merely a large
operator norm: the lower bound is of order p/(log p)^2 for the squared norm. -/
theorem canonical_prime_norm_sq_lower (p : ℕ) (hp : p.Prime) :
    zetaTwo * ((p : ℝ)-1) * (1 - 1/(p : ℝ)^2)^2 /
      (2 + Real.log (p : ℝ))^2 ≤ ‖(canonical p hp.two_le : QHilbert)‖^2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p := by linarith
  have hpminus : 0 ≤ (p : ℝ)-1 := by linarith
  have hz := zetaTwo_pos
  have hm := QValuationConditionalLegality.qResidue_mean_pos p hp.two_le
  have hmup := qResidue_mean_le_log_div p hp.two_le
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ p by linarith)
  have hA : 0 < 2 + Real.log (p : ℝ) := by linarith
  have hp2 : (1 : ℝ) ≤ (p : ℝ)^2 := by nlinarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp2
  have hinv' : 1/(p : ℝ)^2 ≤ (1 : ℝ) := by
    simpa only [one_div, inv_one] using hinv
  have ht : 0 ≤ 1 - 1/(p : ℝ)^2 := sub_nonneg.mpr hinv'
  have hmean_scaled : (zetaTwo * (p : ℝ)) * inner ℝ qOne (qResidue p) ≤
      2 + Real.log (p : ℝ) := by
    have h := (le_div_iff₀ (by positivity : 0 < zetaTwo * (p : ℝ))).mp hmup
    nlinarith
  have hcoef : ((1 - 1/(p : ℝ)^2) * zetaTwo * (p : ℝ)) /
      (2 + Real.log (p : ℝ)) ≤
      (1 - 1/(p : ℝ)^2) / inner ℝ qOne (qResidue p) := by
    apply (div_le_div_iff₀ hA hm).mpr
    have h := mul_le_mul_of_nonneg_left hmean_scaled ht
    nlinarith
  have hcoef0 : 0 ≤ ((1 - 1/(p : ℝ)^2) * zetaTwo * (p : ℝ)) /
      (2 + Real.log (p : ℝ)) := by positivity
  have hcoef1 : 0 ≤ (1 - 1/(p : ℝ)^2) / inner ℝ qOne (qResidue p) := by positivity
  have hcoefsq := (sq_le_sq₀ hcoef0 hcoef1).mpr hcoef
  have hnorm := qResidue_norm_sq_ge_head p hp.pos
  calc
    _ = (((1 - 1/(p : ℝ)^2) * zetaTwo * (p : ℝ)) /
        (2 + Real.log (p : ℝ)))^2 *
        (((p : ℝ)-1) / (zetaTwo * (p : ℝ)^2)) := by
      field_simp
      <;> ring
    _ ≤ ((1 - 1/(p : ℝ)^2) / inner ℝ qOne (qResidue p))^2 * ‖qResidue p‖^2 :=
      mul_le_mul hcoefsq hnorm (by positivity) (sq_nonneg _)
    _ = _ := by
      rw [canonical_prime_eq_smul p hp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- A simpler uniform numerical factor valid already from p=2. -/
theorem canonical_prime_norm_sq_lower_uniform (p : ℕ) (hp : p.Prime) :
    (9*zetaTwo/16) * ((p : ℝ)-1) / (2 + Real.log (p : ℝ))^2 ≤
      ‖(canonical p hp.two_le : QHilbert)‖^2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpminus : 0 ≤ (p : ℝ)-1 := by linarith
  have hz := zetaTwo_pos
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ (p : ℝ)^2 by nlinarith)
  have hinv' : 1/(p : ℝ)^2 ≤ (1/4 : ℝ) := by
    simpa only [one_div] using hinv
  have ht : (3/4 : ℝ) ≤ 1 - 1/(p : ℝ)^2 := by linarith [hinv']
  have hsq : (9/16 : ℝ) ≤ (1 - 1/(p : ℝ)^2)^2 := by nlinarith
  calc
    _ = (zetaTwo * ((p : ℝ)-1) / (2 + Real.log (p : ℝ))^2) * (9/16) := by ring
    _ ≤ (zetaTwo * ((p : ℝ)-1) / (2 + Real.log (p : ℝ))^2) *
        (1 - 1/(p : ℝ)^2)^2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = zetaTwo * ((p : ℝ)-1) * (1 - 1/(p : ℝ)^2)^2 /
        (2 + Real.log (p : ℝ))^2 := by ring
    _ ≤ _ := canonical_prime_norm_sq_lower p hp

/-- Every fixed norm threshold is eventually exceeded along any sequence of
prime cutoffs tending to infinity. Such cutoffs are not divisor-exhausting. -/
theorem eventually_prime_canonical_norm_gt (p : ℕ → ℕ)
    (hp : ∀ n, (p n).Prime) (hptop : Tendsto p atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, C < ‖(canonical (p n) (hp n).two_le : QHilbert)‖ := by
  have hz := zetaTwo_pos
  have hsmall : Tendsto (fun n => C^2 *
      ((6 + Real.log ((p n : ℝ)+1))^2 / Real.sqrt (p n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((shifted_log_power_div_sqrt_tendsto_zero 2).comp hptop).const_mul (C^2)
  filter_upwards [hsmall.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 9*zetaTwo/32))] with n hn
  by_contra h
  have hnormle : ‖(canonical (p n) (hp n).two_le : QHilbert)‖ ≤ C := le_of_not_gt h
  have hnormsq := (sq_le_sq₀ (norm_nonneg _) hC).mpr hnormle
  have hpR : (2 : ℝ) ≤ p n := by exact_mod_cast (hp n).two_le
  have hpp : (0 : ℝ) < p n := by linarith
  have hspos : 0 < Real.sqrt (p n : ℝ) := Real.sqrt_pos.mpr hpp
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ p n by linarith)
  have hlog' : Real.log (p n : ℝ) ≤ Real.log ((p n : ℝ)+1) :=
    Real.log_le_log hpp (by linarith)
  have hA : 0 < (2 + Real.log (p n : ℝ))^2 := by positivity
  have hlower := (canonical_prime_norm_sq_lower_uniform (p n) (hp n)).trans hnormsq
  have hbound := (div_le_iff₀ hA).mp hlower
  have hsqrt : Real.sqrt (p n : ℝ) ≤ (p n : ℝ) := by
    nlinarith [Real.sq_sqrt hpp.le, Real.sqrt_nonneg (p n : ℝ)]
  have hhalf : Real.sqrt (p n : ℝ) / 2 ≤ (p n : ℝ)-1 := by linarith
  have hsq : (2 + Real.log (p n : ℝ))^2 ≤
      (6 + Real.log ((p n : ℝ)+1))^2 := by nlinarith
  have hbase : (9*zetaTwo/32) * Real.sqrt (p n : ℝ) ≤
      C^2 * (6 + Real.log ((p n : ℝ)+1))^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 9*zetaTwo/16)
    have h₂ := mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
    nlinarith
  have hfinal : 9*zetaTwo/32 ≤ C^2 *
      ((6 + Real.log ((p n : ℝ)+1))^2 / Real.sqrt (p n : ℝ)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hspos).mpr hbase
  exact (not_lt_of_ge hfinal) hn

end RiemannResearch.RH.QCRTPrimeCutoffGrowth
