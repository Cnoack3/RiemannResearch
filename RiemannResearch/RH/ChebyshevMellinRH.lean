import RiemannResearch.RH.ChebyshevMellin
import RiemannResearch.Analysis.LogDerivZeroOrder
import RiemannResearch.RH.WeilExplicitFormula.Statement.Seam
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import RiemannResearch.RH.RiemannHypothesisStrip
import Mathlib.Tactic.FieldSimp

/-!
# The Chebyshev Mellin expression, zeta zeros, and RH

The expression meromorphicError agrees with the convergent Chebyshev-error
Mellin integral on Re(s) > 1. It is meromorphic away from 1. Away from 0 and 1,
it is analytic exactly where zeta is nonzero, and has order -1 at every
zeta zero, including multiple zeros.

Consequently Mathlib's RiemannHypothesis is equivalent to its analyticity
throughout 1/2 < Re(s) < 1. This is an equivalence, not a proof of RH.

Source: user-provided V_Zeta_Vector_Spaces_Research_2026-09-16.md,
Sections 12-19, for the requested Mellin/zero/RH link. The proof uses the
classical local order calculation and zeta reflection, already formalized
in the imported modules. It does not prove Hardy estimates, a signed
arithmetic energy bound, a residue coefficient, or pole cancellation at 1.
-/

set_option autoImplicit false

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.ChebyshevMellin

theorem logDeriv_order_at_zero {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s = 0) :
    meromorphicOrderAt (logDeriv riemannZeta) s = -1 :=
  (Zeta23.riemannZeta_analyticOnNhd_compl_one s hs).meromorphicOrderAt_logDeriv_of_zero
    (Zeta23.analyticOrderAt_riemannZeta_ne_top hs) hz

theorem analyticAt_meromorphicError_iff {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ meromorphicError s ↔ riemannZeta s ≠ 0 := by
  have ha := Zeta23.riemannZeta_analyticOnNhd_compl_one s hs1
  constructor
  · intro h hz
    have hg : AnalyticAt ℂ
        (fun z : ℂ => -z * (meromorphicError z + 1 / (z - 1))) s :=
      analyticAt_id.neg.mul (h.add
        (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1)))
    have he : (fun z : ℂ => -z * (meromorphicError z + 1 / (z - 1))) =ᶠ[𝓝 s]
        logDeriv riemannZeta := by
      filter_upwards [eventually_ne_nhds hs0] with z hz0
      by_cases hzeta : riemannZeta z = 0
      · simp [meromorphicError, logDeriv_apply, hzeta]
      · unfold meromorphicError
        rw [logDeriv_apply]
        field_simp
        ring
    have hp := (hg.congr he).meromorphicOrderAt_nonneg
    rw [logDeriv_order_at_zero hs1 hz] at hp
    have hn : ¬ (0 : WithTop ℤ) ≤ -1 := by decide
    exact hn hp
  · intro hz
    exact (ha.deriv.neg.div (analyticAt_id.mul ha) (mul_ne_zero hs0 hz)).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))

theorem riemannHypothesis_iff_error_analytic :
    RiemannHypothesis ↔
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 →
        AnalyticAt ℂ meromorphicError s := by
  constructor
  · intro hRH s hhalf hone
    have hs0 : s ≠ 0 := by intro h; norm_num [h] at hhalf
    have hs1 : s ≠ 1 := by intro h; norm_num [h] at hone
    apply (analyticAt_meromorphicError_iff hs0 hs1).mpr
    intro hz
    have he := (RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mp hRH)
      s hz (by linarith) hone
    linarith
  · intro h
    apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro s hz h0 h1
    have hright (z : ℂ) (hzero : riemannZeta z = 0)
        (_h0 : 0 < z.re) (h1 : z.re < 1) : z.re ≤ 1 / 2 := by
      by_contra hn
      have hh : 1 / 2 < z.re := lt_of_not_ge hn
      have hz0 : z ≠ 0 := by intro he; norm_num [he] at hh
      have hz1 : z ≠ 1 := by intro he; norm_num [he] at h1
      exact (analyticAt_meromorphicError_iff hz0 hz1).mp (h z hh h1) hzero
    have hb := hright s hz h0 h1
    have hr := Zeta23.zeta_reflect_zero s ⟨hz, h0, h1⟩
    have hrb := hright (Zeta23.reflect s) hr.1 hr.2.1 hr.2.2
    simp [Zeta23.reflect] at hrb
    linarith

theorem meromorphicAt_meromorphicError {s : ℂ} (hs : s ≠ 1) :
    MeromorphicAt meromorphicError s := by
  have ha := Zeta23.riemannZeta_analyticOnNhd_compl_one s hs
  exact (ha.deriv.neg.meromorphicAt.div
    (analyticAt_id.mul ha).meromorphicAt).sub
      (analyticAt_const.meromorphicAt.div
        (analyticAt_id.sub analyticAt_const).meromorphicAt)


theorem meromorphicError_order_at_zero {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    meromorphicOrderAt meromorphicError s = -1 := by
  have ha := Zeta23.riemannZeta_analyticOnNhd_compl_one s hs1
  have hden : meromorphicOrderAt (fun z : ℂ => -z) s = 0 := by
    have had : AnalyticAt ℂ (fun z : ℂ => -z) s := analyticAt_id.neg
    rw [had.meromorphicOrderAt_eq]
    have he : analyticOrderAt (fun z : ℂ => -z) s = 0 := by
      simp [analyticOrderAt_eq_zero, hs0]
    rw [he]
    rfl
  have hquot : meromorphicOrderAt
      (logDeriv riemannZeta / (fun z : ℂ => -z)) s = -1 := by
    have hl : MeromorphicAt (logDeriv riemannZeta) s :=
      ha.deriv.meromorphicAt.div ha.meromorphicAt
    have hn : MeromorphicAt (fun z : ℂ => -z) s := analyticAt_id.neg.meromorphicAt
    rw [meromorphicOrderAt_div hl hn, logDeriv_order_at_zero hs1 hz, hden, sub_zero]
  have hreg : AnalyticAt ℂ (fun z : ℂ => -(1 / (z - 1))) s :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hs1)).neg
  have he : meromorphicError =
      (logDeriv riemannZeta / (fun z : ℂ => -z)) +
        (fun z : ℂ => -(1 / (z - 1))) := by
    funext z
    simp [meromorphicError, logDeriv_apply, div_div, mul_comm, sub_eq_add_neg, div_neg, neg_div]
  rw [he, meromorphicOrderAt_add_eq_left_of_lt hreg.meromorphicAt, hquot]
  rw [hquot]
  exact lt_of_lt_of_le (by decide : (-1 : WithTop ℤ) < 0)
    hreg.meromorphicOrderAt_nonneg



end RiemannResearch.RH.ChebyshevMellin
