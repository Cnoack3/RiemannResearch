import RiemannResearch.Analysis.AnnularMellinMultiplier
import RiemannResearch.RH.ChebyshevMellinRH
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Full-zero obstruction for the annular meromorphic expression

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This proves an equivalence for the specified meromorphic expression.
The ActualAnnularMellin companion supplies the actual prime-signal identity
on Re(s)>1. Continuation from that initial half-plane and quantitative
arithmetic energy estimates remain separate.

Source: the October 9 report, Section 15; the local proof uses the existing
ChebyshevMellinRH log-derivative order theorem and strip-zero criterion.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.AnnularMellin
open RiemannResearch.Analysis.AnnularMellin
open RiemannResearch.RH.ChebyshevMellin

def meromorphicExpression (z : ℂ) : ℂ :=
  -multiplier z * logDeriv riemannZeta z - (7 / 64 : ℂ) / (z - 1)

theorem analyticAt_expression_iff_zeta_ne_zero {z : ℂ}
    (hz : 0 < z.re) (hz1 : z ≠ 1) :
    AnalyticAt ℂ meromorphicExpression z ↔ riemannZeta z ≠ 0 := by
  have hH := multiplier_analyticAt hz
  have hHne := multiplier_ne_zero hz
  have ha := Zeta23.riemannZeta_analyticOnNhd_compl_one z hz1
  have hregular : AnalyticAt ℂ
      (fun w : ℂ => (7 / 64 : ℂ) / (w - 1)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz1)
  constructor
  · intro h hzeta
    have hg : AnalyticAt ℂ
        (fun w : ℂ =>
          -(meromorphicExpression w + (7 / 64 : ℂ) / (w - 1)) / multiplier w) z :=
      (h.add hregular).neg.div hH hHne
    have he :
        (fun w : ℂ =>
          -(meromorphicExpression w + (7 / 64 : ℂ) / (w - 1)) / multiplier w)
        =ᶠ[𝓝 z] logDeriv riemannZeta := by
      filter_upwards [hH.continuousAt.eventually_ne hHne] with w hw
      have hnum :
          -(meromorphicExpression w + (7 / 64 : ℂ) / (w - 1)) =
            multiplier w * logDeriv riemannZeta w := by
        unfold meromorphicExpression
        ring
      rw [hnum]
      apply (div_eq_iff hw).mpr
      ring
    have hp := (hg.congr he).meromorphicOrderAt_nonneg
    rw [logDeriv_order_at_zero hz1 hzeta] at hp
    have hn : ¬ (0 : WithTop ℤ) ≤ -1 := by decide
    exact hn hp
  · intro hnonzero
    have hlog : AnalyticAt ℂ (logDeriv riemannZeta) z := by
      have heq : logDeriv riemannZeta =
          (fun w : ℂ => deriv riemannZeta w / riemannZeta w) := by
        funext w
        simp only [logDeriv_apply]
      rw [heq]
      exact ha.deriv.div ha hnonzero
    exact (hH.neg.mul hlog).sub hregular

/-- This is an analytic criterion for the defined expression, not a proof of RH
and not an assertion of the unproved arithmetic energy bound. -/
theorem riemannHypothesis_iff_expression_analytic :
    RiemannHypothesis ↔
      ∀ z : ℂ, (1 / 2 : ℝ) < z.re → z.re < 1 →
        AnalyticAt ℂ meromorphicExpression z := by
  rw [riemannHypothesis_iff_error_analytic]
  constructor
  · intro h z hhalf hone
    have hz0 : z ≠ 0 := by intro he; norm_num [he] at hhalf
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hone
    exact (analyticAt_expression_iff_zeta_ne_zero (by linarith) hz1).mpr
      ((analyticAt_meromorphicError_iff hz0 hz1).mp (h z hhalf hone))
  · intro h z hhalf hone
    have hz0 : z ≠ 0 := by intro he; norm_num [he] at hhalf
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hone
    exact (analyticAt_meromorphicError_iff hz0 hz1).mpr
      ((analyticAt_expression_iff_zeta_ne_zero (by linarith) hz1).mp (h z hhalf hone))

end RiemannResearch.RH.AnnularMellin
