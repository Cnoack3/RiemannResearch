/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ZetaSquareMellinRepresentation
import RiemannResearch.Analysis.ActualZetaSquareMovingResidue
import RiemannResearch.Analysis.ConreyBaluyotEstermannActualGrowth
import RiemannResearch.Analysis.RectanglePoleSubtraction

/-!
# The actual zeta-square Mellin contour shift

For every positive real smoothing scale and every real ordinate, the Mellin
integral on any line to the right of 1/2 shifts to any line in (-1,0).
The residues are the actual zeta square at zero and the explicit moving
double-pole contribution at 1/2-it. The horizontal limits use the proved
Estermann strip-growth provider, with no supplied growth hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis
open ConreyBaluyot

/-- Subtract the leading double-pole term, retaining its simple Laurent coefficient. -/
def zetaSquareMellinRegularized (Y t : ℝ) (z : ℂ) : ℂ :=
  zetaSquareMellinKernel Y t z -
    (Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t) /
      (z - zetaSquareMovingPole t) ^ 2

theorem zetaSquareMovingPole_ne_zero (t : ℝ) : zetaSquareMovingPole t ≠ 0 := by
  intro he
  have hh := congrArg Complex.re he
  norm_num [zetaSquareMovingPole] at hh

theorem analyticAt_zetaSquareMellinKernel {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0)
    (hzp : z ≠ zetaSquareMovingPole t) :
    AnalyticAt ℂ (zetaSquareMellinKernel Y t) z := by
  have he : zetaSquareMellinKernel Y t =
      estermannMellinKernel (0 : ZMod 1) ((1 / 2 : ℂ) + I * t)
        ((1 / 2 : ℂ) + I * t) (Y : ℂ)⁻¹ :=
    funext (zetaSquareMellinKernel_eq_estermannMellinKernel hY t)
  rw [he]
  have hp : 1 - ((1 / 2 : ℂ) + I * t) = zetaSquareMovingPole t := by
    dsimp [zetaSquareMovingPole]; ring
  exact analyticAt_estermannMellinKernel_off_poles _ _ _
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')) hz hz0
    (by simpa only [hp] using hzp) (by simpa only [hp] using hzp)

theorem meromorphicAt_zetaSquareMellinKernel {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (zetaSquareMellinKernel Y t) z := by
  have he : zetaSquareMellinKernel Y t =
      estermannMellinKernel (0 : ZMod 1) ((1 / 2 : ℂ) + I * t)
        ((1 / 2 : ℂ) + I * t) (Y : ℂ)⁻¹ :=
    funext (zetaSquareMellinKernel_eq_estermannMellinKernel hY t)
  rw [he]
  exact meromorphicAt_estermannMellinKernel _ _ _
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')) hz

theorem analyticAt_zetaSquareMellinRegularized {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0)
    (hzp : z ≠ zetaSquareMovingPole t) :
    AnalyticAt ℂ (zetaSquareMellinRegularized Y t) z := by
  exact (analyticAt_zetaSquareMellinKernel hY t hz hz0 hzp).sub
    (analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hzp)))

theorem meromorphicAt_zetaSquareMellinRegularized {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (zetaSquareMellinRegularized Y t) z := by
  exact (meromorphicAt_zetaSquareMellinKernel hY t hz).sub
    (analyticAt_const.meromorphicAt.div
      (((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt))

theorem zetaSquareMellinKernel_residue_zero {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Tendsto (fun z : ℂ => z * zetaSquareMellinKernel Y t z)
      (𝓝[≠] 0) (𝓝 (riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2)) := by
  have hs : (1 / 2 : ℂ) + I * t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  have hh := estermannMellinKernel_residue_zero (0 : ZMod 1)
    hs hs (inv_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'))
  simpa only [← zetaSquareMellinKernel_eq_estermannMellinKernel hY t,
    estermann_mod_one_eq_zeta_product, ← pow_two] using hh

theorem zetaSquareMellinRegularized_residue_zero {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Tendsto (fun z : ℂ => z * zetaSquareMellinRegularized Y t z)
      (𝓝[≠] 0) (𝓝 (riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2)) := by
  have hp : ContinuousAt (fun z : ℂ => z *
      ((Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t) /
        (z - zetaSquareMovingPole t) ^ 2)) 0 :=
    continuousAt_id.mul (continuousAt_const.div
      ((continuousAt_id.sub continuousAt_const).pow 2)
      (pow_ne_zero 2 (by simpa using neg_ne_zero.mpr (zetaSquareMovingPole_ne_zero t))))
  have hh := (zetaSquareMellinKernel_residue_zero hY t).sub hp.continuousWithinAt.tendsto
  have hh' : Tendsto (fun z : ℂ => z * zetaSquareMellinKernel Y t z -
      z * ((Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t) /
        (z - zetaSquareMovingPole t) ^ 2))
      (𝓝[≠] 0) (𝓝 (riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2)) := by
    simpa using hh
  exact hh'.congr' (Eventually.of_forall fun z => by
    dsimp [zetaSquareMellinRegularized]; ring)

/-- Exact finite rectangle identity through both actual poles. -/
theorem rectangleIntegral_zetaSquareMellinKernel {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {a b T : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hb : 1 / 2 < b) (hT : |t| < T) :
    RectangleIntegral' (zetaSquareMellinKernel Y t)
      ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
      riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + zetaSquareMovingResidue Y t := by
  classical
  let z : ℂ := (a : ℂ) - T * I
  let w : ℂ := (b : ℂ) + T * I
  let p := zetaSquareMovingPole t
  let f := zetaSquareMellinRegularized Y t
  let A : ℂ := Gamma p * (Y : ℂ) ^ p
  let q : ℂ → ℂ := fun s => A / (s - p) ^ 2
  have hT0 : 0 < T := (abs_nonneg t).trans_lt hT
  have htlo := (abs_lt.mp hT).1
  have hthi := (abs_lt.mp hT).2
  have hp0 : p ≠ 0 := zetaSquareMovingPole_ne_zero t
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simp [z, w]; linarith
  have hRre {s : ℂ} (hs : s ∈ Rectangle z w) : -1 < s.re := by
    have hh := (mem_Rect hre him s).mp hs
    have hh0 := hh.1
    simp [z] at hh0
    linarith
  have h0in : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z, w] <;> linarith
  have hpin : Rectangle z w ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z, w, p, zetaSquareMovingPole] <;> linarith
  have hrect : RectangleIntegral' f z w =
      riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + zetaSquareMovingResidue Y t := by
    have hh := Complex.rectangleIntegral'_eq_sum_of_residue_limits f hre him
      ({0, p} : Finset ℂ)
      (fun s => if s = 0 then riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2
        else zetaSquareMovingResidue Y t)
      (fun s hs => meromorphicAt_zetaSquareMellinRegularized hY t (hRre hs))
      (by
        intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact h0in
        · exact hpin)
      (by
        intro s hs hns
        have hns' : s ≠ 0 ∧ s ≠ p := by simpa using hns
        exact analyticAt_zetaSquareMellinRegularized hY t
          (hRre hs) hns'.1 hns'.2)
      (by
        intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · simpa [f] using zetaSquareMellinRegularized_residue_zero hY t
        · simpa [f, p, hp0, zetaSquareMellinRegularized,
            zetaSquareMovingPole_ne_zero] using zetaSquareMellinKernel_moving_residue hY t)
    simpa [hp0, Ne.symm hp0] using hh
  have hn0 {s : ℂ} (hs : s ∈ RectangleBorder z w) : s ≠ 0 := by
    intro he
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds h0in (he ▸ hs)
  have hnp {s : ℂ} (hs : s ∈ RectangleBorder z w) : s ≠ p := by
    intro he
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds hpin (he ▸ hs)
  have hc : ContinuousOn f (RectangleBorder z w) := by
    intro s hs
    exact (analyticAt_zetaSquareMellinRegularized hY t
      (hRre (rectangleBorder_subset_rectangle z w hs))
      (hn0 hs) (hnp hs)).continuousAt.continuousWithinAt
  have hq : ContinuousOn q (RectangleBorder z w) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr (hnp hs)))
  have hadd := hc.rectangleBorder_integrable.add hq.rectangleBorder_integrable
  have heq : f + q = zetaSquareMellinKernel Y t := by
    funext s
    dsimp [f, q, A, p, zetaSquareMellinRegularized]
    ring
  have hqzero : RectangleIntegral q z w = 0 :=
    Complex.rectangleIntegral_div_sub_sq_eq_zero A p
      (not_mem_rectangleBorder_of_rectangle_mem_nhds hpin)
  rw [heq, hqzero, add_zero] at hadd
  change (1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral _ z w = _
  rw [hadd]
  exact hrect

/-- The actual kernel has an integrable quadratic tail on every closed strip
in Re z > -1, with the critical ordinate and positive smoothing scale fixed. -/
theorem exists_zetaSquareMellinKernel_strip_tail {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {a b : ℝ} (ha : -1 < a) :
    ∃ B T₀ : ℝ, 0 ≤ B ∧ 1 ≤ T₀ ∧ ∀ r ∈ Icc a b, ∀ v : ℝ,
      T₀ ≤ |v| → ‖zetaSquareMellinKernel Y t ((r : ℂ) + v * I)‖ ≤
        B * (1 + v ^ 2)⁻¹ := by
  have hlam : 0 < ((Y : ℂ)⁻¹).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  obtain ⟨B, T₀, hB, hT, hbound⟩ := exists_estermannMellinKernel_tail_bound
    (0 : ZMod 1) ((1 / 2 : ℂ) + I * t) ((1 / 2 : ℂ) + I * t)
    hlam ha (by simp; linarith) (by simp; linarith)
  refine ⟨B, T₀, hB, hT, ?_⟩
  intro r hr v hv
  rw [zetaSquareMellinKernel_eq_estermannMellinKernel hY t]
  exact hbound r hr v hv

/-- Absolute integrability on every left line between the first two Gamma poles. -/
theorem integrable_zetaSquareMellinKernel_negative {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {a : ℝ} (ha : -1 < a) (ha0 : a < 0) :
    Integrable (fun v : ℝ => zetaSquareMellinKernel Y t ((a : ℂ) + v * I)) := by
  obtain ⟨B, T₀, _, _, hbound⟩ :=
    exists_zetaSquareMellinKernel_strip_tail hY t ha (b := a)
  have he : zetaSquareMellinKernel Y t =
      estermannMellinKernel (0 : ZMod 1) ((1 / 2 : ℂ) + I * t)
        ((1 / 2 : ℂ) + I * t) (Y : ℂ)⁻¹ :=
    funext (zetaSquareMellinKernel_eq_estermannMellinKernel hY t)
  rw [he]
  simpa only [mul_comm I] using
    integrable_estermannMellinKernel_negative_of_tail_bound (0 : ZMod 1)
      ((1 / 2 : ℂ) + I * t) ((1 / 2 : ℂ) + I * t)
      (by norm_num) (by norm_num)
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')) ha ha0
      (fun v hv => by
        simpa only [he, mul_comm I] using hbound a ⟨le_rfl, le_rfl⟩ v hv)

/-- Unconditional shift of the full vertical Mellin integral. -/
theorem zetaSquareMellinIntegral_eq_residues_add_leftIntegral {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {a b : ℝ}
    (ha : -1 < a) (ha0 : a < 0) (hb : 1 / 2 < b) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ v : ℝ, zetaSquareMellinKernel Y t ((b : ℂ) + v * I)) =
      riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + zetaSquareMovingResidue Y t +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ v : ℝ, zetaSquareMellinKernel Y t ((a : ℂ) + v * I) := by
  obtain ⟨B, T₀, _, _, hbound⟩ := exists_zetaSquareMellinKernel_strip_tail hY t ha (b := b)
  have hab : a ≤ b := by linarith
  have hlam : 0 < ((Y : ℂ)⁻¹).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have he : zetaSquareMellinKernel Y t =
      estermannMellinKernel (0 : ZMod 1) ((1 / 2 : ℂ) + I * t)
        ((1 / 2 : ℂ) + I * t) (Y : ℂ)⁻¹ :=
    funext (zetaSquareMellinKernel_eq_estermannMellinKernel hY t)
  have hintLeft := integrable_zetaSquareMellinKernel_negative hY t ha ha0
  have hintRight : Integrable (fun v : ℝ =>
      zetaSquareMellinKernel Y t ((b : ℂ) + v * I)) := by
    rw [he]
    simpa only [mul_comm I] using
      integrable_estermannMellinKernel_vertical (0 : ZMod 1)
        ((1 / 2 : ℂ) + I * t) ((1 / 2 : ℂ) + I * t)
        hlam (by linarith) (by simp; linarith) (by simp; linarith)
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' (zetaSquareMellinKernel Y t)
        ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
        riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + zetaSquareMovingResidue Y t := by
    filter_upwards [eventually_gt_atTop |t|] with T hT
    exact rectangleIntegral_zetaSquareMellinKernel hY t ha ha0 hb hT
  exact Complex.mellin_vertical_eq_of_rectangle_of_cauchy_tail
    hab hintLeft hintRight hbound hrect

end RiemannResearch.Analysis
