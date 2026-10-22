/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicHarmonicTail
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.NonlinearZeroDensityRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
/-!
# Actual signed hyperbolic tails from an explicit nonlinear count budget

Reflection and the complete harmonic cap retain the full count normalizer and
additive remainder. The scalar inverse rate comes from `NonlinearZeroDensityRate`.
The count shape is motivated by Chourasiya--Simonic, arXiv:2507.15184v2,
Theorem 1 and Table 1, https://arxiv.org/html/2507.15184v2.
That reference supplies a published analytic statement, not a Lean assumption:
the substantive actual count bound appears explicitly in each consumer's type.
-/
noncomputable section
open scoped InnerProductSpace
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
open CenteredHyperbolicFrames
theorem actualSignedTailBudget_le_of_inclusiveCount (T : ℝ) (d : ℕ) (δ F : ℝ)
    (hδ : 0 ≤ δ)
    (hcount : rightInclusiveCount T (1/2+δ) ≤ F) :
    actualSignedTailBudget T d δ ≤
      (2*F/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  have hc : strictTail T δ ≤ 2*F :=
    (strictTail_le_twice_inclusive T δ hδ).trans
      (mul_le_mul_of_nonneg_left hcount (by norm_num))
  exact (actualSignedTailBudget_le_harmonic T d δ).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _))
      (harmonicHyperbolicCap_nonneg d))

/-- Exact inverse-rate cutoff using the full harmonic cap, with the source
additive count remainder retained after reflection and normalization. -/
theorem actualSignedTailBudget_le_at_countCutoff
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (M K E ω : ℝ)
    (hM : 0 < M) (hK : 0 < K) (hN : 0 < (Ncount 0 T : ℝ))
    (hS : 0 ≤ Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)
    (hcount : rightInclusiveCount T
        (1/2+countCutoff M
          (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)) ≤
      K*Real.exp (-M*inghamRate (countCutoff M
        (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)))+E) :
    actualSignedTailBudget T d (countCutoff M
      (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)) ≤
      Real.exp (-ω)+(2*E/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  let A : ℝ := 2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hW : 0 < harmonicHyperbolicCap d :=
    hdR.trans_le (harmonicHyperbolicCap_ge_card d)
  have hA : 0 < A := by dsimp [A]; positivity
  have hb := actualSignedTailBudget_le_of_inclusiveCount T d
    (countCutoff M (Real.log A+ω))
    (K*Real.exp (-M*inghamRate (countCutoff M (Real.log A+ω)))+E)
    (countCutoff_nonneg hM hS) hcount
  have he : (2*(K*Real.exp (-M*inghamRate
      (countCutoff M (Real.log A+ω)))+E)/(Ncount 0 T : ℝ))*
      harmonicHyperbolicCap d =
      A*Real.exp (-M*inghamRate (countCutoff M (Real.log A+ω)))+
        (2*E/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
    dsimp [A]
    simp only [div_eq_mul_inv]
    ring
  rw [he, countCutoff_exp_cancellation hM hA hS] at hb
  exact hb

theorem signedBadHyperbolic_norm_le_at_countCutoff
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (M K E ω : ℝ)
    (hM : 0 < M) (hK : 0 < K) (hN : 0 < (Ncount 0 T : ℝ))
    (hS : 0 ≤ Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)
    (hcount : rightInclusiveCount T
        (1/2+countCutoff M
          (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)) ≤
      K*Real.exp (-M*inghamRate (countCutoff M
        (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω)))+E) :
    ‖signedBadHyperbolic T d (countCutoff M
      (Real.log (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ))+ω))‖ ≤
      Real.exp (-ω)+(2*E/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d :=
  (signedBadHyperbolic_norm_le_budget _ _ _).trans
    (actualSignedTailBudget_le_at_countCutoff T d hd M K E ω hM hK hN hS hcount)
end RiemannResearch.Analysis.ActualZeroPhaseMoments
