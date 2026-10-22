/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.ArithmeticConductorCommonZeros
import RiemannResearch.RH.RealZetaNonvanishing
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The two-prime logarithmic-target Mellin criterion

Source: user-provided `PrimePowerTargetsResearch20261020.md`, Section 2.
The actual Q targets, their square-summability and exact Mellin transforms
are imported from `PrimePowerTargetMellin`. The imaginary part of the
normalized continuous Mellin functional annihilates the squarefree closed
span plus real constants at an actual zeta zero.

The final theorem is a conditional research reduction. Membership of both
F_2 and F_3 in the displayed complete-Q closure remains Open. Neither
membership, nor RH, is assumed anywhere as an established provider.
-/

noncomputable section
open scoped ComplexConjugate
namespace RiemannResearch.RH.PrimePowerTarget
open Pareto Pareto.CoefficientStabilization ZetaTwoHilbert ZetaTwoParetoTransfer
open QMellinTransfer

/-- Closure of the squarefree legal closed span plus the real constants. -/
def closureWithConstants : Submodule ℝ QHilbert :=
  (ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).topologicalClosure

/-- Imaginary part of the normalized, continuous physical Mellin functional. -/
def normalizedMellinImag (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) : QHilbert →L[ℝ] ℝ :=
  Complex.imCLM.comp (s • qMellinContinuous s hs)

@[simp] theorem normalizedMellinImag_apply (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (f : QHilbert) : normalizedMellinImag s hs f = (s * qMellin f s).im := rfl

theorem normalizedMellinImag_zero_on_closureWithConstants
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {f : QHilbert} (hf : f ∈ closureWithConstants) :
    (s * qMellin f s).im = 0 := by
  let L := normalizedMellinImag s hs
  have hH : ZetaTwoOptimizerStage.closure ≤ L.ker := by
    intro g hg
    have hm : qMellin g s = 0 :=
      paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
        (fun _ hn => hn) s hs hs1 hz
        (closedSpace_le_legalClosure (toPareto_mem_closedSpace hg))
    change (s * qMellin g s).im = 0
    rw [hm, mul_zero, Complex.zero_im]
  have hOne : qOne ∈ L.ker := by
    change (s * qMellin qOne s).im = 0
    rw [qMellin_one s hs]
    have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
    simp [hs0]
  have hbase : ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne} ≤ L.ker :=
    sup_le hH ((Submodule.span_singleton_le_iff_mem qOne L.ker).2 hOne)
  exact ((ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).topologicalClosure_minimal
    hbase L.isClosed_ker) hf

theorem cpow_real_of_qTarget_mem_closureWithConstants (p : ℕ) (hp : 1 < p)
    (hmem : qTarget p hp ∈ closureWithConstants)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : ((p : ℂ) ^ s).im = 0 := by
  have hi := normalizedMellinImag_zero_on_closureWithConstants s hs hs1 hz hmem
  change (s * paretoMellin (toPareto (qTarget p hp)) s).im = 0 at hi
  rw [toPareto_qTarget, paretoTarget_mellin_exact p hp s hs] at hi
  have hc := Complex.conj_eq_iff_im.mpr hi
  have hd : conj ((p : ℂ) ^ s - 1) = (p : ℂ) ^ s - 1 := by
    apply inv_injective
    simpa only [one_div, map_inv₀] using hc
  have hpow : conj ((p : ℂ) ^ s) = (p : ℂ) ^ s := by
    simpa only [map_sub, map_one, sub_left_inj] using hd
  exact Complex.conj_eq_iff_im.mp hpow

/-- Reuses the existing conductor-pair injectivity. -/
theorem im_eq_zero_of_two_three_cpow_real (s : ℂ)
    (h2 : ((2 : ℂ) ^ s).im = 0) (h3 : ((3 : ℂ) ^ s).im = 0) :
    s.im = 0 := by
  have hpower (p : ℝ) (hp : 0 < p) (h : ((p : ℂ) ^ s).im = 0) :
      (p : ℂ) ^ (-s) = (p : ℂ) ^ (-conj s) := by
    have hc : conj ((p : ℂ) ^ (-s)) = (p : ℂ) ^ (-s) := by
      rw [Complex.cpow_neg, map_inv₀, Complex.conj_eq_iff_im.mpr h]
    have ha : Complex.arg (p : ℂ) ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hp.le]
      exact Real.pi_pos.ne
    have he : (p : ℂ) ^ (-conj s) = conj ((p : ℂ) ^ (-s)) := by
      simpa only [map_neg, Complex.conj_ofReal] using
        Complex.cpow_conj (p : ℂ) (-s) ha
    exact hc.symm.trans he.symm
  have hsconj : s = conj s :=
    ArithmeticConductorCommonZeros.two_three_cpow_neg_injective
      (Prod.ext (by simpa using hpower 2 (by norm_num) h2)
        (by simpa using hpower 3 (by norm_num) h3))
  exact Complex.conj_eq_iff_im.mp hsconj.symm

/-- Conditional research reduction. Both complete-Q closure memberships remain Open. -/
theorem riemannHypothesis_of_two_targets_mem_closureWithConstants
    (h2 : qTarget 2 (by norm_num) ∈ closureWithConstants)
    (h3 : qTarget 3 (by norm_num) ∈ closureWithConstants) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have him := im_eq_zero_of_two_three_cpow_real s
    (cpow_real_of_qTarget_mem_closureWithConstants 2 (by norm_num) h2 s hs hs1 hz)
    (cpow_real_of_qTarget_mem_closureWithConstants 3 (by norm_num) h3 s hs hs1 hz)
  have he : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [he] at hz
  exact RiemannResearch.RH.riemannZeta_ofReal_ne_zero s.re (by linarith) (by linarith) hz

end RiemannResearch.RH.PrimePowerTarget
