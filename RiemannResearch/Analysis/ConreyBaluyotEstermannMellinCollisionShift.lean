/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinCollision
import RiemannResearch.Analysis.RectanglePoleSubtraction
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# The Estermann Mellin shift at the colliding poles

Subtract the explicit leading double-pole term. The remainder has the actual
simple residue computed in ConreyBaluyotEstermannMellinCollision. Its finite
rectangle integral is obtained from those residue limits. The subtracted term
has primitive -A/(s-1), so its boundary contribution is zero.

Source: Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.3, pp. 96–97 (contour strategy and setting):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
Global identities below retain the stated growth hypothesis. Its actual
fixed-damping provider and the unconditional specialization are supplied in
ConreyBaluyotEstermannActualGrowth.
-/

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Remove only the leading double-pole term, retaining its simple Laurent coefficient. -/
def estermannMellinCollisionRegularized {K : ℕ} [NeZero K]
    (h : ZMod K) (lam s : ℂ) : ℂ :=
  estermannMellinKernel h 0 0 lam s - (lam⁻¹ * (K : ℂ)⁻¹) / (s - 1) ^ 2

/-- Exact collision residue sum; all logarithms are principal. -/
def estermannMellinCollisionResidueSum {K : ℕ} [NeZero K]
    (h : ZMod K) (lam : ℂ) : ℂ :=
  estermann h 0 0 + lam⁻¹ * (K : ℂ)⁻¹ *
    ((Real.eulerMascheroniConstant : ℂ) - log lam - 2 * log (K : ℂ))

theorem analyticAt_estermannMellinCollisionRegularized {K : ℕ} [NeZero K]
    (h : ZMod K) {lam s : ℂ} (hlam : lam ≠ 0)
    (hs : -1 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (estermannMellinCollisionRegularized h lam) s := by
  have hf := analyticAt_estermannMellinKernel_off_poles h 0 0 hlam hs hs0
    (by simpa using hs1) (by simpa using hs1)
  exact hf.sub (analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hs1)))

theorem meromorphicAt_estermannMellinCollisionRegularized {K : ℕ} [NeZero K]
    (h : ZMod K) {lam s : ℂ} (hlam : lam ≠ 0) (hs : -1 < s.re) :
    MeromorphicAt (estermannMellinCollisionRegularized h lam) s := by
  exact (meromorphicAt_estermannMellinKernel h 0 0 hlam hs).sub
    (analyticAt_const.meromorphicAt.div
      (((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt))

theorem estermannMellinCollisionRegularized_residue_zero {K : ℕ} [NeZero K]
    (h : ZMod K) {lam : ℂ} (hlam : lam ≠ 0) :
    Tendsto (fun s : ℂ => s * estermannMellinCollisionRegularized h lam s)
      (𝓝[≠] 0) (𝓝 (estermann h 0 0)) := by
  have hp : ContinuousAt (fun s : ℂ => s * ((lam⁻¹ * (K : ℂ)⁻¹) / (s - 1) ^ 2)) 0 :=
    continuousAt_id.mul (continuousAt_const.div
      ((continuousAt_id.sub continuousAt_const).pow 2) (by norm_num))
  have hh := (estermannMellinKernel_residue_zero h (α := 0) (β := 0) (by norm_num) (by norm_num) hlam).sub
    hp.continuousWithinAt.tendsto
  have hh' : Tendsto (fun s : ℂ => s * estermannMellinKernel h 0 0 lam s -
      s * ((lam⁻¹ * (K : ℂ)⁻¹) / (s - 1) ^ 2)) (𝓝[≠] 0) (𝓝 (estermann h 0 0)) := by
    simpa using hh
  exact hh'.congr' (Eventually.of_forall fun s => by
    dsimp [estermannMellinCollisionRegularized]
    ring)

/-- Unconditional finite contour identity for the diagonal double pole. -/
theorem rectangleIntegral_estermannMellinKernel_diagonal {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {lam : ℂ} (hlam : lam ≠ 0) {a b T : ℝ}
    (ha : -1 < a) (ha0 : a < 0) (hb : 1 < b) (hT : 0 < T) :
    RectangleIntegral' (estermannMellinKernel (h : ZMod K) 0 0 lam)
      ((a : ℂ)-T * I) ((b : ℂ) + T * I) =
        estermannMellinCollisionResidueSum (h : ZMod K) lam := by
  classical
  let z : ℂ := (a : ℂ)-T * I
  let w : ℂ := (b : ℂ) + T * I
  let f := estermannMellinCollisionRegularized (h : ZMod K) lam
  let A : ℂ := lam⁻¹ * (K : ℂ)⁻¹
  let B : ℂ := A * ((Real.eulerMascheroniConstant : ℂ)-log lam-2 * log (K : ℂ))
  let q : ℂ → ℂ := fun s => A / (s - 1) ^ 2
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
  have h1in : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z, w] <;> linarith
  have hrect : RectangleIntegral' f z w = estermann (h : ZMod K) 0 0 + B := by
    have hh := Complex.rectangleIntegral'_eq_sum_of_residue_limits f hre him
      ({0,1} : Finset ℂ) (fun p => if p = 0 then estermann (h:ZMod K) 0 0 else B)
      (fun s hs => meromorphicAt_estermannMellinCollisionRegularized (h:ZMod K) hlam (hRre hs))
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact h0in
        · exact h1in)
      (by
        intro s hs hns
        have hns' : s ≠ 0 ∧ s ≠ 1 := by simpa using hns
        exact analyticAt_estermannMellinCollisionRegularized (h:ZMod K) hlam
          (hRre hs) hns'.1 hns'.2)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · simpa [f] using estermannMellinCollisionRegularized_residue_zero (h:ZMod K) hlam
        · simpa [f, B, A, estermannMellinCollisionRegularized] using
            estermannMellinKernel_diagonal_residue_explicit h hlam)
    simpa using hh
  have hn0 {s : ℂ} (hs : s ∈ RectangleBorder z w) : s ≠ 0 := by
    intro he
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds h0in (he ▸ hs)
  have hn1 {s : ℂ} (hs : s ∈ RectangleBorder z w) : s ≠ 1 := by
    intro he
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds h1in (he ▸ hs)
  have hc : ContinuousOn f (RectangleBorder z w) := by
    intro s hs
    exact (analyticAt_estermannMellinCollisionRegularized (h:ZMod K) hlam
      (hRre (rectangleBorder_subset_rectangle z w hs)) (hn0 hs) (hn1 hs)).continuousAt.continuousWithinAt
  have hq : ContinuousOn q (RectangleBorder z w) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr (hn1 hs)))
  have hadd := hc.rectangleBorder_integrable.add hq.rectangleBorder_integrable
  have heq : f + q = estermannMellinKernel (h:ZMod K) 0 0 lam := by
    funext s
    dsimp [f, q, A,estermannMellinCollisionRegularized]
    ring
  have hqzero : RectangleIntegral q z w = 0 :=
    Complex.rectangleIntegral_div_sub_sq_eq_zero A 1
      (not_mem_rectangleBorder_of_rectangle_mem_nhds h1in)
  rw [heq, hqzero, add_zero] at hadd
  change (1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral _ z w = _
  rw [hadd]
  exact hrect


/-- Conditional global collision shift. One closed-strip tail bound supplies
vertical integrability and both vanishing horizontal sides. -/
theorem estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {w : ℂ} (hw : 0 < w.im)
    {a b B T₀ : ℝ} (ha : -1 < a) (ha0 : a < 0) (hb : 1 < b)
    (hbound : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermannMellinKernel (h : ZMod K) 0 0 (-2 * (Real.pi : ℂ) * I * w)
        ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹) :
    estermannDampedSeries (h : ZMod K) 0 0 w =
      estermannMellinCollisionResidueSum (h : ZMod K) (-2 * (Real.pi : ℂ) * I * w) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) 0 0
            (-2 * (Real.pi : ℂ) * I * w) ((a : ℂ) + I * t) := by
  let lam : ℂ := -2 * (Real.pi : ℂ) * I * w
  let f := estermannMellinKernel (h : ZMod K) 0 0 lam
  have hlam : 0 < lam.re := by
    have he : lam.re = 2 * Real.pi * w.im := by simp [lam, Complex.mul_re, Complex.mul_im]
    rw [he]
    positivity
  have hlam0 : lam ≠ 0 := by intro he; simp [he] at hlam
  have hb0 : 0 < b := by linarith
  have hab : a ≤ b := by linarith
  have hintLeft : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)) := by
    simpa only [mul_comm I] using
      integrable_estermannMellinKernel_negative_of_tail_bound (h : ZMod K) 0 0
        (by norm_num) (by norm_num) hlam0 ha ha0
        (fun t ht => by
          simpa only [mul_comm I] using hbound a ⟨le_rfl, hab⟩ t ht)
  have hintRight : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)) := by
    simpa only [mul_comm I] using
      integrable_estermannMellinKernel_vertical (h : ZMod K) 0 0 hlam hb0
        (by simpa using hb) (by simpa using hb)
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
        estermannMellinCollisionResidueSum (h : ZMod K) lam := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rectangleIntegral_estermannMellinKernel_diagonal h hlam0 ha ha0 hb hT
  have he := Complex.mellin_vertical_eq_of_rectangle_of_cauchy_tail
    hab hintLeft hintRight hbound hrect
  rw [estermannDampedSeries_eq_mellinIntegral (h : ZMod K) 0 0 hw hb0
    (by simpa using hb) (by simpa using hb)]
  simpa only [f, lam, mul_comm I] using he

/-- Conditional collision shift with the same sole analytic provider as the
distinct-pole shift: polynomial growth of the actual Estermann continuation. -/
theorem estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_polynomial_growth
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {w : ℂ} (hw : 0 < w.im)
    {a b C T₀ : ℝ} (ha : -1 < a) (ha0 : a < 0) (hb : 1 < b)
    (n : ℕ) (hC : 0 ≤ C)
    (hgrowth : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermann (h : ZMod K) ((r : ℂ) + t * I) ((r : ℂ) + t * I)‖ ≤ C * |t| ^ n) :
    estermannDampedSeries (h : ZMod K) 0 0 w =
      estermannMellinCollisionResidueSum (h : ZMod K) (-2 * (Real.pi : ℂ) * I * w) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) 0 0
            (-2 * (Real.pi : ℂ) * I * w) ((a : ℂ) + I * t) := by
  have hlam : 0 < (-2 * (Real.pi : ℂ) * I * w).re := by
    have he : (-2 * (Real.pi : ℂ) * I * w).re = 2 * Real.pi * w.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    positivity
  obtain ⟨B, _, hB⟩ := exists_estermannMellinKernel_tail_bound_of_polynomial_growth
    (h : ZMod K) 0 0 hlam ha n hC (by simpa using hgrowth)
  exact estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound
    h hw ha ha0 hb hB

end RiemannResearch.Analysis.ConreyBaluyot
