/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMomentEndpoints
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
/-!
# Continuity of the actual second moment in its evaluation line

The source's mollifier parameters remain fixed. Joint continuity above the
real axis gives continuity of the finite interval integral. Thus a moment
on one prescribed line transfers to a selectable neighborhood with arbitrary
positive slack and a protected counting denominator.

Source: the evaluation-line mismatch in the user-provided right-boundary
continuation. No uniform modulus in T or the mollifier length is asserted.
-/
noncomputable section
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis.ConreyBaluyot

theorem continuous_mollifiedSecondMoment_line (σ y ε : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    Continuous (fun l => mollifiedSecondMoment σ y ε l u v) := by
  let F : ℝ → ℝ → ℝ := fun l t =>
    ‖mollifiedZeta σ y ε ((l : ℂ) + (max u t : ℝ)*I)‖ ^ 2
  have hF : Continuous (Function.uncurry F) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        mollifiedZeta σ y ε ((p.1 : ℂ) + (max u p.2 : ℝ)*I)) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      have hs : (p.1 : ℂ) + (max u p.2 : ℝ)*I ≠ 1 := by
        intro he
        have hi := congrArg Complex.im he
        simp at hi
        linarith [le_max_left u p.2]
      exact ContinuousAt.comp (g := mollifiedZeta σ y ε)
        (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (max u p.2 : ℝ)*I)
        (analyticAt_mollifiedZeta σ y ε hs).continuousAt (by fun_prop)
    exact hc.norm.pow 2
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hF u v
  have he : (fun l => ∫ t in u..v, F l t) =
      (fun l => mollifiedSecondMoment σ y ε l u v) := by
    funext l
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : u ≤ t := (by simpa only [uIcc_of_le huv] using ht : t ∈ Icc u v).1
    simp only [F, max_eq_right ht']
  rw [he] at h
  exact h

/-- A bound on a prescribed line transfers to a neighborhood with any
positive slack; the mollifier parameters stay fixed. -/
theorem exists_mollifiedSecondMoment_line_neighborhood (σ y ε l : ℝ) {u v κ : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hκ : 0 < κ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-l| < r →
      mollifiedSecondMoment σ y ε x u v < mollifiedSecondMoment σ y ε l u v + κ := by
  obtain ⟨r, hr, hb⟩ := Metric.continuousAt_iff.mp
    (continuous_mollifiedSecondMoment_line σ y ε hu huv).continuousAt κ hκ
  refine ⟨r, hr, ?_⟩
  intro x hx
  have hh := hb (show dist x l < r by simpa only [Real.dist_eq] using hx)
  rw [Real.dist_eq] at hh
  have hupper := (abs_lt.mp hh).2
  linarith

/-- A prescribed central moment line strictly between 1/2 and alpha yields
a selectable open interval with a protected positive denominator. -/
theorem exists_mollifiedSecondMoment_admissible_interval (σ y ε : ℝ)
    {l α u v E κ : ℝ} (hl : 1/2 < l) (hlα : l < α)
    (hu : 0 < u) (huv : u ≤ v) (hκ : 0 < κ)
    (hm : mollifiedSecondMoment σ y ε l u v ≤ v-u+E) :
    ∃ a c : ℝ, 1/2 < a ∧ a < l ∧ l < c ∧ c < α ∧
      (α-l)/2 ≤ α-c ∧
      ∀ x ∈ Ioo a c, mollifiedSecondMoment σ y ε x u v ≤ v-u+E+κ := by
  obtain ⟨r, hr, hb⟩ := exists_mollifiedSecondMoment_line_neighborhood σ y ε l hu huv hκ
  let d := min (r/2) (min ((l-1/2)/2) ((α-l)/2))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hdr : d < r := (min_le_left _ _).trans_lt (by linarith)
  have hdl : d ≤ (l-1/2)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hda : d ≤ (α-l)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l-d, l+d, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_⟩
  intro x hx
  have hx' : |x-l| < r := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hh := hb x hx'
  linarith
end RiemannResearch.Analysis.ConreyBaluyot
