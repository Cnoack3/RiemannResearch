/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinResidues
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellin
import RiemannResearch.Analysis.VerticalResidueShift
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite Estermann Mellin shifts and the remaining global tail obligation

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the contour strategy and residue formula.

The finite rectangle theorem is unconditional for distinct complex shifts
with real parts below one, a unit residue class, and nonzero damping.
It encloses all three candidate poles in Re s > -1, allowing removable ones.
The diagonal alpha = beta = 0 is treated separately in the sibling
ConreyBaluyotEstermannMellinCollision module and is excluded from this formula.

The global identity is a **conditional research reduction**: the uniform
closed-strip tail estimate remains an explicit hypothesis. The new vertical
integrability and both horizontal limits are derived from that estimate;
they are not additional providers. No global growth estimate, collision
residue, uniform mollified-moment estimate, or density bound is claimed.
-/

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Holomorphy of the actual kernel away from the three candidate poles in Re s > -1. -/
theorem analyticAt_estermannMellinKernel_off_poles {K : ℕ} [NeZero K]
    (h : ZMod K) (α β : ℂ) {lam z : ℂ} (hlam : lam ≠ 0)
    (hz : -1 < z.re) (hz0 : z ≠ 0) (hzα : z ≠ 1 - α) (hzβ : z ≠ 1 - β) :
    AnalyticAt ℂ (estermannMellinKernel h α β lam) z := by
  have hgreg (w : ℂ) (hw : -1 < w.re) (hw0 : w ≠ 0) :
      DifferentiableAt ℂ Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    cases n with
    | zero => exact hw0 (by simpa using hn)
    | succ n =>
      have he := congrArg Complex.re hn
      simp at he
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hg : AnalyticAt ℂ Gamma z := by
    let U : Set ℂ := {w | -1 < w.re} ∩ {0}ᶜ
    have hU : IsOpen U :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
    have hd : DifferentiableOn ℂ Gamma U :=
      fun w hw => (hgreg w hw.1 hw.2).differentiableWithinAt
    exact hd.analyticAt (hU.mem_nhds ⟨hz, hz0⟩)
  have hp : AnalyticAt ℂ (fun s : ℂ => lam ^ (-s)) z := by
    simp only [Complex.cpow_def_of_ne_zero hlam]
    fun_prop
  exact (hg.mul hp).mul (analyticAt_estermann_shifted h α β
    (fun he => hzα (eq_sub_of_add_eq he)) (fun he => hzβ (eq_sub_of_add_eq he)))

/-- Meromorphy includes the three candidate poles and also coincident shifted poles. -/
theorem meromorphicAt_estermannMellinKernel {K : ℕ} [NeZero K]
    (h : ZMod K) (α β : ℂ) {lam z : ℂ} (hlam : lam ≠ 0) (hz : -1 < z.re) :
    MeromorphicAt (estermannMellinKernel h α β lam) z := by
  have hg : AnalyticAt ℂ (fun s : ℂ => Gamma (s + 1)) z := by
    have hd : DifferentiableOn ℂ (fun s : ℂ => Gamma (s + 1)) {s | -1 < s.re} := by
      intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply (Complex.differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.add_const 1)
      intro n hn
      have he := congrArg Complex.re hn
      simp at he
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      change -1 < s.re at hs
      linarith
    exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have hGamma : MeromorphicAt Gamma z := by
    have he : Gamma = fun s : ℂ => Gamma (s + 1) / s := by
      funext s
      by_cases hs : s = 0
      · simp [hs]
      · rw [Complex.Gamma_add_one s hs]
        field_simp
    rw [he]
    exact hg.meromorphicAt.div analyticAt_id.meromorphicAt
  have hp : AnalyticAt ℂ (fun s : ℂ => lam ^ (-s)) z := by
    simp only [Complex.cpow_def_of_ne_zero hlam]
    fun_prop
  exact (hGamma.mul hp.meromorphicAt).mul (meromorphic_estermann_shifted h α β z)

private theorem order_ge_neg_one_of_limit {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p)
    (hc : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  have hs : MeromorphicAt (fun z : ℂ => z - p) p :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hs.mul hf)).mp ⟨c, hc⟩
  rw [meromorphicOrderAt_mul hs hf, meromorphicOrderAt_id_sub_const] at ho
  apply (WithTop.add_le_add_iff_left (show (1 : WithTop ℤ) ≠ ⊤ by simp)).mp
  simpa using ho

/-- Distinct shifts below one give at most simple poles on the whole strip. -/
theorem hasSimplePolesOn_estermannMellinKernel {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {α β lam : ℂ} (hα : α.re < 1) (hβ : β.re < 1)
    (hne : α ≠ β) (hlam : lam ≠ 0) :
    HasSimplePolesOn (estermannMellinKernel (h : ZMod K) α β lam) {z | -1 < z.re} := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have ha : α ≠ 1 := by intro he; simp [he] at hα
    have hb : β ≠ 1 := by intro he; simp [he] at hβ
    exact order_ge_neg_one_of_limit
      (f := estermannMellinKernel (h : ZMod K) α β lam)
      (meromorphicAt_estermannMellinKernel (h : ZMod K) α β hlam hz)
      (by simpa only [sub_zero] using
        estermannMellinKernel_residue_zero (h : ZMod K) ha hb hlam)
  by_cases hzα : z = 1 - α
  · subst z
    exact order_ge_neg_one_of_limit
      (f := estermannMellinKernel (h : ZMod K) α β lam)
      (meromorphicAt_estermannMellinKernel (h : ZMod K) α β hlam hz)
      (estermannMellinKernel_residue_left h hα hne hlam)
  by_cases hzβ : z = 1 - β
  · subst z
    exact order_ge_neg_one_of_limit
      (f := estermannMellinKernel (h : ZMod K) α β lam)
      (meromorphicAt_estermannMellinKernel (h : ZMod K) α β hlam hz)
      (estermannMellinKernel_residue_right h hβ hne hlam)
  exact le_trans (show ((-1 : ℤ) : WithTop ℤ) ≤ 0 from by decide)
    (analyticAt_estermannMellinKernel_off_poles (h : ZMod K) α β hlam
      hz hz0 hzα hzβ).meromorphicOrderAt_nonneg

/-- Sum of the three candidate residues, with their original complex signs. -/
def estermannMellinResidueSum {K : ℕ} [NeZero K] (h : ZMod K) (α β lam : ℂ) : ℂ :=
  estermann h α β +
    Gamma (1 - α) * lam ^ (α - 1) *
      (K : ℂ) ^ (-(1 - α + β)) * riemannZeta (1 - α + β) +
    Gamma (1 - β) * lam ^ (β - 1) *
      (K : ℂ) ^ (-(1 - β + α)) * riemannZeta (1 - β + α)

/-- Exact finite rectangle shift across zero and the two distinct shifted poles.
The shifts and damping may be complex; the height encloses both imaginary parts. -/
theorem rectangleIntegral_estermannMellinKernel {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {α β lam : ℂ} (hα : α.re < 1) (hβ : β.re < 1)
    (hne : α ≠ β) (hlam : lam ≠ 0) {a b T : ℝ}
    (ha : -1 < a) (ha0 : a < 0) (hbα : 1 - α.re < b) (hbβ : 1 - β.re < b)
    (hT : 0 < T) (hTα : |α.im| < T) (hTβ : |β.im| < T) :
    RectangleIntegral' (estermannMellinKernel (h : ZMod K) α β lam)
      ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
        estermannMellinResidueSum (h : ZMod K) α β lam := by
  classical
  let z₀ : ℂ := (a : ℂ) - T * I
  let z₁ : ℂ := (b : ℂ) + T * I
  let p : ℂ := 1 - α
  let q : ℂ := 1 - β
  let S : Finset ℂ := {0, p, q}
  let f := estermannMellinKernel (h : ZMod K) α β lam
  let R : Set ℂ := Rectangle z₀ z₁
  let P : Set ℂ := {z | meromorphicOrderAt f z < 0}
  have hab : z₀.re ≤ z₁.re := by simp [z₀, z₁]; linarith
  have habi : z₀.im ≤ z₁.im := by simp [z₀, z₁]; linarith
  have hRre {z : ℂ} (hz : z ∈ R) : -1 < z.re := by
    have hh := (mem_Rect hab habi z).mp hz
    have hh0 := hh.1
    simp [z₀] at hh0
    linarith
  have h0in : R ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hab, uIoo_of_le habi]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z₀, z₁] <;> linarith
  have hpin : R ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hab, uIoo_of_le habi]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z₀, z₁, p] <;>
      linarith [neg_abs_le α.im, le_abs_self α.im]
  have hqin : R ∈ 𝓝 q := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hab, uIoo_of_le habi]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z₀, z₁, q] <;>
      linarith [neg_abs_le β.im, le_abs_self β.im]
  have hSIn {z : ℂ} (hz : z ∈ (S : Set ℂ)) : z ∈ R := by
    simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact mem_of_mem_nhds h0in
    · exact mem_of_mem_nhds hpin
    · exact mem_of_mem_nhds hqin
  have hmero : MeromorphicOn f R :=
    fun z hz => meromorphicAt_estermannMellinKernel (h : ZMod K) α β hlam (hRre hz)
  have hsub : R ∩ P ⊆ (S : Set ℂ) := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [S, hz0]
    by_cases hzp : z = p
    · simp [S, hzp]
    by_cases hzq : z = q
    · simp [S, hzq]
    exact False.elim (not_lt_of_ge
      (analyticAt_estermannMellinKernel_off_poles (h : ZMod K) α β hlam (hRre hz.1)
        hz0 hzp hzq).meromorphicOrderAt_nonneg hz.2)
  have hnobd : Disjoint (RectangleBorder z₀ z₁) P := by
    apply Set.disjoint_left.mpr
    intro z hzb hzP
    have hzR := rectangleBorder_subset_rectangle z₀ z₁ hzb
    have hzS := hsub ⟨hzR, hzP⟩
    simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl | rfl
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds h0in hzb
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds hpin hzb
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds hqin hzb
  have hfinite : (R ∩ P).Finite := S.finite_toSet.subset hsub
  have hsimple : HasSimplePolesOn f R :=
    (hasSimplePolesOn_estermannMellinKernel h hα hβ hne hlam).mono
      (fun z hz => hRre hz)
  have hrect := RectangleIntegral'_eq_sumResiduesIn (f := f) (z := z₀) (w := z₁) hab habi hmero hnobd hfinite hsimple
  have hset : R ∩ P = (S : Set ℂ) ∩ P :=
    Set.Subset.antisymm (fun z hz => ⟨hsub hz, hz.2⟩)
      (fun z hz => ⟨hSIn hz.1, hz.2⟩)
  have hsum := sumResiduesIn_inter_eq_of_set_eq (F := f) hset
    (fun z hz hzp => residue_eq_zero_of_not_pole_of_meromorphicAt
      (hmero z (hSIn hz)) (le_of_not_gt hzp))
  have h0p : (0 : ℂ) ≠ p := by
    intro he
    have hh := congrArg Complex.re he
    simp [p] at hh
    linarith
  have h0q : (0 : ℂ) ≠ q := by
    intro he
    have hh := congrArg Complex.re he
    simp [q] at hh
    linarith
  have hpq : p ≠ q := by
    intro he
    apply hne
    dsimp [p, q] at he
    linear_combination -he
  have hval : sumResiduesIn f (S : Set ℂ) =
      residue f 0 + residue f p + residue f q := by
    unfold sumResiduesIn
    calc
      _ = ∑ z ∈ S, residue f z := by
        exact (tsum_fintype _).trans
          (Finset.sum_subtype (p := fun z : ℂ => z ∈ (S : Set ℂ))
            S (fun z => Iff.rfl) (residue f)).symm
      _ = _ := by simp [S, h0p, h0q, hpq, add_assoc]
  have ha1 : α ≠ 1 := by intro he; simp [he] at hα
  have hb1 : β ≠ 1 := by intro he; simp [he] at hβ
  rw [hsum, hval] at hrect
  simpa only [f, p, q, residue_estermannMellinKernel_zero (h : ZMod K) ha1 hb1 hlam,
    residue_estermannMellinKernel_left h hα hne hlam,
    residue_estermannMellinKernel_right h hβ hne hlam, estermannMellinResidueSum] using hrect


/-- The negative line is absolutely integrable once its quadratic tail is supplied.
Holomorphy proves continuity on its compact middle, with no convergence provider there. -/
theorem integrable_estermannMellinKernel_negative_of_tail_bound
    {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ) {lam : ℂ}
    (hα : α.re < 1) (hβ : β.re < 1) (hlam : lam ≠ 0)
    {a B T₀ : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hbound : ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermannMellinKernel h α β lam ((a : ℂ) + I * t)‖ ≤
        B * (1 + t ^ 2)⁻¹) :
    Integrable (fun t : ℝ => estermannMellinKernel h α β lam ((a : ℂ) + I * t)) := by
  have hc : Continuous (fun t : ℝ =>
      estermannMellinKernel h α β lam ((a : ℂ) + I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd : AnalyticAt ℂ (estermannMellinKernel h α β lam) ((a : ℂ) + I * t) := by
      apply analyticAt_estermannMellinKernel_off_poles h α β hlam
      · simpa using ha
      · intro he; have hh := congrArg Complex.re he; simp at hh; linarith
      · intro he; have hh := congrArg Complex.re he; simp at hh; linarith
      · intro he; have hh := congrArg Complex.re he; simp at hh; linarith
    exact hd.continuousAt.comp (f := fun t : ℝ => (a : ℂ) + I * t) (by fun_prop)
  exact MeasureTheory.integrable_of_continuous_of_cauchy_tail hc hbound

/-- Conditional research reduction: a single closed-strip tail estimate discharges
both vertical convergence and both remote sides of the actual three-pole Mellin shift. -/
theorem estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {α β w : ℂ}
    (hα : α.re < 1) (hβ : β.re < 1) (hne : α ≠ β) (hw : 0 < w.im)
    {a b B T₀ : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hbα : 1 < b + α.re) (hbβ : 1 < b + β.re)
    (hbound : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermannMellinKernel (h : ZMod K) α β (-2 * (Real.pi : ℂ) * I * w)
        ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹) :
    estermannDampedSeries (h : ZMod K) α β w =
      estermannMellinResidueSum (h : ZMod K) α β (-2 * (Real.pi : ℂ) * I * w) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) α β
            (-2 * (Real.pi : ℂ) * I * w) ((a : ℂ) + I * t) := by
  let lam : ℂ := -2 * (Real.pi : ℂ) * I * w
  let f := estermannMellinKernel (h : ZMod K) α β lam
  have hlam : 0 < lam.re := by
    have he : lam.re = 2 * Real.pi * w.im := by simp [lam, Complex.mul_re, Complex.mul_im]
    rw [he]
    positivity
  have hlam0 : lam ≠ 0 := by intro he; simp [he] at hlam
  have hb : 0 < b := by linarith
  have hab : a ≤ b := by linarith
  have hintLeft : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)) := by
    simpa only [mul_comm I] using
      integrable_estermannMellinKernel_negative_of_tail_bound (h : ZMod K) α β
        hα hβ hlam0 ha ha0
        (fun t ht => by
          simpa only [mul_comm I] using hbound a ⟨le_rfl, hab⟩ t ht)
  have hintRight : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)) := by
    simpa only [mul_comm I] using
      integrable_estermannMellinKernel_vertical (h : ZMod K) α β hlam hb hbα hbβ
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
        estermannMellinResidueSum (h : ZMod K) α β lam := by
    filter_upwards [eventually_gt_atTop (max 0 (max |α.im| |β.im|))] with T hT
    exact rectangleIntegral_estermannMellinKernel h hα hβ hne hlam0 ha ha0
      (by linarith) (by linarith)
      ((le_max_left 0 _).trans_lt hT)
      ((le_max_left |α.im| |β.im|).trans (le_max_right 0 _ ) |>.trans_lt hT)
      ((le_max_right |α.im| |β.im|).trans (le_max_right 0 _ ) |>.trans_lt hT)
  have he := Complex.mellin_vertical_eq_of_rectangle_of_cauchy_tail
    hab hintLeft hintRight hbound hrect
  rw [estermannDampedSeries_eq_mellinIntegral (h : ZMod K) α β hw hb hbα hbβ]
  simpa only [f, lam, mul_comm I] using he

end RiemannResearch.Analysis.ConreyBaluyot
