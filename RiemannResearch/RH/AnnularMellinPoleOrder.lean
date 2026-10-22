import RiemannResearch.RH.AnnularMellinRH

/-!
# Exact pole order of the defined annular Mellin expression

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This strengthens failure of analyticity to meromorphic order exactly -1,
at every positive-real-part zeta zero, including multiple zeros. The
ActualAnnularMellin companion identifies the actual arithmetic integral with
this expression on Re(s)>1. Local continuation to a zero remains separate.
-/

set_option autoImplicit false
noncomputable section
namespace RiemannResearch.RH.AnnularMellin
open RiemannResearch.Analysis.AnnularMellin
open RiemannResearch.RH.ChebyshevMellin

theorem expression_order_at_zero {z : ℂ}
    (hz : 0 < z.re) (hz1 : z ≠ 1) (hzeta : riemannZeta z = 0) :
    meromorphicOrderAt meromorphicExpression z = -1 := by
  have hH : AnalyticAt ℂ (fun w : ℂ => -multiplier w) z :=
    (multiplier_analyticAt hz).neg
  have hmain : meromorphicOrderAt
      ((fun w : ℂ => -multiplier w) * logDeriv riemannZeta) z = -1 := by
    rw [meromorphicOrderAt_mul_of_ne_zero hH
      (neg_ne_zero.mpr (multiplier_ne_zero hz))]
    exact logDeriv_order_at_zero hz1 hzeta
  have hreg : AnalyticAt ℂ
      (fun w : ℂ => -((7 / 64 : ℂ) / (w - 1))) z :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hz1)).neg
  have he : meromorphicExpression =
      ((fun w : ℂ => -multiplier w) * logDeriv riemannZeta) +
        (fun w : ℂ => -((7 / 64 : ℂ) / (w - 1))) := by
    funext w
    simp [meromorphicExpression, sub_eq_add_neg]
  rw [he, meromorphicOrderAt_add_eq_left_of_lt hreg.meromorphicAt, hmain]
  rw [hmain]
  exact lt_of_lt_of_le (by decide : (-1 : WithTop ℤ) < 0)
    hreg.meromorphicOrderAt_nonneg

end RiemannResearch.RH.AnnularMellin
