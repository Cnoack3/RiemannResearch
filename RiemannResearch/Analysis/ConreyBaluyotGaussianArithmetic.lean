/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianMoment
import RiemannResearch.Analysis.ConreyBaluyotGaussianReflection
import RiemannResearch.Analysis.ConreyBaluyotGaussianShift
import RiemannResearch.Analysis.ConreyBaluyotEstermann
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinKernel
import RiemannResearch.Analysis.ConreyBaluyotMellinWeight
import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import RiemannResearch.Analysis.GammaMellinBounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# The actual Gaussian-to-arithmetic bridge

Source for the functional-equation and Dirichlet-series strategy:
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, between (3.3.6) and (3.3.7), pp. 116–117:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

The actual shifted Gaussian moment is an absolutely convergent double
series of integrals. The final theorem expands the exact finite mollifier
into its coefficients and the scalar kernel at m * n * h/k. The original signed
residue at 1 is retained, together with the exact normalization and cutoff.

The bridge holds for every c > max(1, 2 * l); no upper restriction c < 2 is
needed. The evaluation line l and mollifier parameter sigma stay separate.
All real centers u and cutoff parameters epsilon are allowed.

Integrability of the Gaussian–Gamma factor, each summand, and the
integral–series exchange are proved. The Estermann connection here is the
untwisted modulus-one specialization. Identifying the scalar transform
with the rotated, damped Estermann integrals is the next analytic step.
This module supplies no uniform growing-height moment or density provider.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The Gaussian multiplied by the exact functional-equation factor chi(2 * l-s). -/
def gaussianArithmeticKernel (l Δ u : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2) *
    (2 * (2 * Real.pi : ℂ) ^ (-(1 - (2 * l : ℝ) + s)) *
      Gamma (1 - (2 * l : ℝ) + s) *
      Complex.cos ((Real.pi : ℂ) * (1 - (2 * l : ℝ) + s) / 2))

/-- Continuity on every line where the reflected Gamma argument has positive real part. -/
theorem gaussianArithmeticKernel_continuous (l Δ u c : ℝ)
    (hc : 0 < 1 - 2 * l + c) :
    Continuous (fun t : ℝ => gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t)) := by
  have hw : Continuous (fun t : ℝ => 1 - ((2 * l : ℝ) : ℂ) + ((c : ℂ) + I * t)) := by fun_prop
  have hg : Continuous (fun t : ℝ =>
      Gamma (1 - ((2 * l : ℝ) : ℂ) + ((c : ℂ) + I * t))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g := Gamma) _ hw.continuousAt
    apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : Continuous (fun t : ℝ =>
      (2 * Real.pi : ℂ) ^ (-(1 - (2 * l : ℝ) + ((c : ℂ) + I * t)))) :=
    hw.neg.const_cpow (.inl (by exact_mod_cast (ne_of_gt (show (0:ℝ) < 2 * Real.pi by positivity))))
  unfold gaussianArithmeticKernel
  have he : Continuous (fun t : ℝ =>
      Complex.exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2)) := by fun_prop
  exact he.mul (((continuous_const.mul hp).mul hg).mul (by fun_prop))

/-- An explicit Gaussian times exponential bound, for fixed parameters. -/
theorem norm_gaussianArithmeticKernel_le (l Δ u c : ℝ)
    (hc : 0 < 1 - 2 * l + c) (t : ℝ) :
    ‖gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t)‖ ≤
      (2 * |Real.Gamma (1 - 2 * l + c)|) *
        Real.exp ((((c - l)^2-(t - u)^2)/Δ ^ 2) + (Real.pi / 2)*|t|) := by
  let w : ℂ := 1 - (2 * l : ℝ) + ((c : ℂ) + I * t)
  have hw : w.re = 1 - 2 * l + c := by simp [w]
  have hi : w.im = t := by simp [w]
  have hp : ‖(2 * Real.pi : ℂ) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hw]
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
      (show -(1 - 2 * l + c) ≤ 0 by linarith)
  have hg : ‖Gamma w‖ ≤ |Real.Gamma (1 - 2 * l + c)| := by
    exact (Complex.gamma_norm_le_real_part (hw ▸ hc)).trans
      (hw ▸ le_abs_self (Real.Gamma w.re))
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
      Real.exp ((Real.pi / 2) * |t|) := by
    have he : (((Real.pi : ℂ) * w / 2)).im = (Real.pi / 2) * t := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im, Complex.mul_im]
      simp [hi]
      ring
    simpa only [he, abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)] using
      norm_cos_le_exp_abs_im ((Real.pi : ℂ) * w / 2)
  unfold gaussianArithmeticKernel
  change ‖Complex.exp _ * (2 * (2 * Real.pi : ℂ) ^ (-w) * Gamma w * _)‖ ≤ _
  simp only [norm_mul, Complex.norm_ofNat]
  rw [show ‖Complex.exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ:ℂ)^2)‖ =
      Real.exp (((c - l)^2-(t - u)^2)/Δ ^ 2) by
        simpa only [mul_comm I (t : ℂ)] using norm_gaussianContourFactor l Δ u c t]
  calc
    _ ≤ Real.exp (((c - l)^2-(t - u)^2)/Δ ^ 2) *
        (2 * 1 * |Real.Gamma (1 - 2 * l + c)| * Real.exp ((Real.pi / 2)*|t|)) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- The Gaussian absorbs the Gamma/cosine growth; no c < 2 or l ≤ c premise is needed. -/
theorem integrable_gaussianArithmeticKernel (l u : ℝ) {c Δ : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) :
    Integrable (fun t : ℝ => gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t)) := by
  let q : ℝ := 1 / Δ ^ 2
  let k : ℝ := Real.pi / 2
  let E : ℝ := q * (c - l)^2 + (2 * q * |u| + k)^2/(2 * q)
  have hq : 0 < q := by dsimp [q]; positivity
  have hint := (integrable_exp_neg_mul_sq (show 0 < q / 2 by positivity)).const_mul
    (2 * |Real.Gamma (1 - 2 * l + c)| * Real.exp E)
  apply hint.mono' (gaussianArithmeticKernel_continuous l Δ u c hc).aestronglyMeasurable
  filter_upwards [] with t
  have he : ((c - l)^2-(t - u)^2)/Δ ^ 2 + k * |t| ≤ E - (q / 2)*t ^ 2 := by
    have h := gaussian_strip_absorption (x := 0) (l := 0) (c := 0)
      (k := k) (u := u) (t := t) hq (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl, le_rfl⟩)
    convert add_le_add_left h (q * (c - l)^2) using 1 <;> dsimp [E, q] <;> ring
  calc
    _ ≤ (2 * |Real.Gamma (1 - 2 * l + c)|) *
        Real.exp ((((c - l)^2-(t - u)^2)/Δ ^ 2) + k * |t|) :=
      norm_gaussianArithmeticKernel_le l Δ u c hc t
    _ ≤ (2 * |Real.Gamma (1 - 2 * l + c)|) * Real.exp (E-(q / 2)*t ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by rw [show E-(q / 2)*t ^ 2 = E + (-(q / 2)*t ^ 2) by ring, Real.exp_add]; ring

/-- Actual functional-equation substitution and the untwisted Estermann identification. -/
theorem mollifiedGaussianContourKernel_eq_arithmetic (σ y ε l Δ u : ℝ)
    {s : ℂ} (hs : 2 * l < s.re) :
    mollifiedGaussianContourKernel σ y ε l Δ u s =
      (gaussianArithmeticKernel l Δ u s *
        nonstandardMollifier σ y ε s * nonstandardMollifier σ y ε ((2 * l:ℝ)-s)) *
        estermann (0 : ZMod 1) s (s + (1 - (2 * l:ℝ))) := by
  let w : ℂ := 1 - (2 * l:ℝ) + s
  have hw : 1 < w.re := by simp [w]; linarith
  have hne : ∀ n : ℕ, w ≠ -n := by
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne1 : w ≠ 1 := by
    intro he
    rw [he] at hw
    norm_num at hw
  have hfe := riemannZeta_one_sub hne hne1
  have harg : 1-w = ((2 * l:ℝ):ℂ)-s := by dsimp [w]; ring
  rw [harg] at hfe
  rw [mollifiedGaussianContourKernel, mollifiedZeta, mollifiedZeta, hfe,
    estermann_mod_one_eq_zeta_product, gaussianArithmeticKernel]
  dsimp [w]
  rw [show s + (1 - ((2 * l:ℝ):ℂ)) = 1 - ((2 * l:ℝ):ℂ) + s by ring]
  ring

/-- The scalar Gaussian kernel with the two actual finite mollifier factors. -/
def mollifiedGaussianArithmeticKernel (σ y ε l Δ u : ℝ) (s : ℂ) : ℂ :=
  gaussianArithmeticKernel l Δ u s *
    nonstandardMollifier σ y ε s * nonstandardMollifier σ y ε ((2 * l : ℝ) - s)

/-- The actual double-series summand, with zero terms at either zero index. -/
def mollifiedGaussianArithmeticTerm (σ y ε l Δ u : ℝ) (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  mollifiedGaussianArithmeticKernel σ y ε l Δ u s *
    estermannTerm (0 : ZMod 1) s (s + (1 - (2 * l : ℝ))) p

/-- The finite mollifiers preserve absolute integrability for arbitrary real parameters. -/
theorem integrable_mollifiedGaussianArithmeticKernel (σ y ε l u : ℝ) {c Δ : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) :
    Integrable (fun t : ℝ => mollifiedGaussianArithmeticKernel σ y ε l Δ u
      ((c : ℂ) + I * t)) := by
  let B₁ := ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
    ‖mollifierCoefficient σ y n‖ / (n : ℝ) ^ c
  let B₂ := ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
    ‖mollifierCoefficient σ y n‖ / (n : ℝ) ^ (2 * l - c)
  have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; positivity
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  have hM : Continuous (nonstandardMollifier σ y ε) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_nonstandardMollifier σ y ε z).continuousAt
  have hcont : Continuous (fun t : ℝ => mollifiedGaussianArithmeticKernel σ y ε l Δ u
      ((c : ℂ) + I * t)) := by
    unfold mollifiedGaussianArithmeticKernel
    exact ((gaussianArithmeticKernel_continuous l Δ u c hc).mul
      (hM.comp (by fun_prop))).mul (hM.comp (by fun_prop))
  apply (((integrable_gaussianArithmeticKernel l u hc hΔ).norm.mul_const B₁).mul_const B₂).mono'
    hcont.aestronglyMeasurable
  filter_upwards [] with t
  have h₁ : ‖nonstandardMollifier σ y ε ((c : ℂ) + I * t)‖ ≤ B₁ :=
    norm_mollifier_le_of_re_ge σ y ε c (by simp)
  have h₂ : ‖nonstandardMollifier σ y ε ((2 * l : ℝ) - ((c : ℂ) + I * t))‖ ≤ B₂ :=
    norm_mollifier_le_of_re_ge σ y ε (2 * l - c) (by simp)
  simp only [mollifiedGaussianArithmeticKernel, norm_mul]
  gcongr

/-- Each arithmetic summand is genuinely integrable when Delta is positive. -/
theorem integrable_mollifiedGaussianArithmeticTerm (σ y ε l u : ℝ) {c Δ : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (p : ℕ × ℕ) :
    Integrable (fun t : ℝ => mollifiedGaussianArithmeticTerm σ y ε l Δ u
      ((c : ℂ) + I * t) p) := by
  simpa only [mollifiedGaussianArithmeticTerm, add_zero] using
    integrable_mul_estermannTerm_vertical (0 : ZMod 1) 0 (1 - (2 * l : ℝ)) c p
      (integrable_mollifiedGaussianArithmeticKernel σ y ε l u hc hΔ)

/-- The termwise norm integrals form a summable double series. -/
theorem summable_integral_norm_mollifiedGaussianArithmeticTerm
    (σ y ε l Δ u : ℝ) {c : ℝ} (hc : 1 < c) (hlc : 2 * l < c) :
    Summable (fun p : ℕ × ℕ => ∫ t : ℝ,
      ‖mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p‖) := by
  have ha : 1 < ((c : ℂ) + (0 : ℂ)).re := by simpa using hc
  have hb : 1 < ((c : ℂ) + (1 - (2 * l : ℝ))).re := by simp; linarith
  have hnorm (t : ℝ) (p : ℕ × ℕ) :
      ‖estermannTerm (0 : ZMod 1) ((c : ℂ) + I * t)
        ((c : ℂ) + I * t + (1 - (2 * l : ℝ))) p‖ =
      ‖estermannTerm (0 : ZMod 1) (c : ℂ) ((c : ℂ) + (1 - (2 * l : ℝ))) p‖ := by
    simpa only [add_zero] using norm_estermannTerm_vertical (0 : ZMod 1) 0
      (1 - (2 * l : ℝ)) c t p
  simp_rw [mollifiedGaussianArithmeticTerm, norm_mul, hnorm, integral_mul_const]
  have hs := (summable_norm_estermannTerm (0 : ZMod 1) ha hb).mul_left
    (∫ t : ℝ, ‖mollifiedGaussianArithmeticKernel σ y ε l Δ u ((c : ℂ) + I * t)‖)
  simpa only [add_zero] using hs

/-- The actual shifted integral equals its arithmetic series, with Fubini proved. -/
theorem integral_mollifiedGaussianContourKernel_eq_tsum (σ y ε l u : ℝ) {c Δ : ℝ}
    (hc : 1 < c) (hlc : 2 * l < c) (hΔ : 0 < Δ) :
    (∫ t : ℝ, mollifiedGaussianContourKernel σ y ε l Δ u ((c : ℂ) + I * t)) =
      ∑' p : ℕ × ℕ, ∫ t : ℝ,
        mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p := by
  have hf := integrable_mollifiedGaussianArithmeticKernel σ y ε l u (c := c) (by linarith) hΔ
  calc
    _ = ∫ t : ℝ, mollifiedGaussianArithmeticKernel σ y ε l Δ u ((c : ℂ) + I * t) *
        estermann (0 : ZMod 1) ((c : ℂ) + I * t)
          ((c : ℂ) + I * t + (1 - (2 * l : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact mollifiedGaussianContourKernel_eq_arithmetic σ y ε l Δ u (by simpa using hlc)
    _ = _ := by
      simpa only [mollifiedGaussianArithmeticTerm, add_zero] using
        integral_mul_estermann_eq_tsum_integral (0 : ZMod 1) 0 (1 - (2 * l : ℝ))
          (by simpa using hc) (by simp; linarith) hf

/-- Exact normalized arithmetic identity, retaining the signed Gaussian residue. -/
theorem mollifiedGaussianMoment_eq_arithmetic_series (σ ε u : ℝ) {y l c Δ : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hl' : l < 1)
    (hc : 1 < c) (hlc : 2 * l < c) (hΔ : 0 < Δ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ((∑' p : ℕ × ℕ, ∫ t : ℝ,
          mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p) -
          (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u) := by
  rw [mollifiedGaussianMoment_eq_right_shift σ ε u hy hl hl' hc hΔ]
  have hi := integral_mollifiedGaussianContourKernel_eq_tsum σ y ε l u hc hlc hΔ
  simpa only [mul_comm I] using congrArg
    (fun z : ℂ => ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
      (z - (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u)) hi

/-- Absolute convergence of the double series of integrated arithmetic terms. -/
theorem summable_norm_integral_mollifiedGaussianArithmeticTerm
    (σ y ε l Δ u : ℝ) {c : ℝ} (hc : 1 < c) (hlc : 2 * l < c) :
    Summable (fun p : ℕ × ℕ => ‖∫ t : ℝ,
      mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_integral_le_integral_norm _)
    (summable_integral_norm_mollifiedGaussianArithmeticTerm σ y ε l Δ u hc hlc)

/-- The source's explicit m * n * h/k expansion at positive Dirichlet indices. -/
theorem mollifiedGaussianArithmeticTerm_eq_finite_sum
    (σ y ε l Δ u : ℝ) (s : ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    mollifiedGaussianArithmeticTerm σ y ε l Δ u s (m, n) =
      ∑ h ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        (mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
          (n : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ) *
          gaussianArithmeticKernel l Δ u s * (((m * n * h : ℕ) : ℂ) / (k : ℂ)) ^ (-s) := by
  classical
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold mollifiedGaussianArithmeticTerm mollifiedGaussianArithmeticKernel nonstandardMollifier
  simp only [estermannTerm, zero_mul, LSeries.term_def, hm, hn, if_false]
  rw [show ZMod.stdAddChar (0 : ZMod 1) = 1 by simp, one_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hh' : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1))
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1))
  have hpow : (((m * n * h : ℕ) : ℂ) / (k : ℂ)) ^ (-s) =
      (k : ℂ) ^ s / ((m : ℂ) ^ s * (n : ℂ) ^ s * (h : ℂ) ^ s) := by
    have hd := Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg (m * n * h))
      (Nat.cast_nonneg k) (-s)
    simp only [Complex.ofReal_natCast] at hd
    have hprod : ((m * n * h : ℕ) : ℂ) ^ s =
        (m : ℂ) ^ s * (n : ℂ) ^ s * (h : ℂ) ^ s := by
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rw [hd, Complex.cpow_neg, hprod, Complex.cpow_neg]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [hpow, show s + (1 - ((2 * l:ℝ):ℂ)) = s - (((2 * l:ℝ):ℂ)-1) by ring,
    Complex.cpow_sub _ _ hn', Complex.cpow_sub _ _ hk']
  have hp (z : ℂ) (hz : z ≠ 0) (a : ℂ) : z ^ a ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hz]
    exact Complex.exp_ne_zero _
  field_simp [hp _ hm', hp _ hn', hp _ hh', hp _ hk']
  <;> ring

/-- The scalar Gaussian–chi Mellin transform in the dt parameterization. -/
def gaussianArithmeticTransform (l Δ u c ω : ℝ) : ℂ :=
  ∫ t : ℝ, gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t) *
    (ω : ℂ) ^ (-((c : ℂ) + I * t))

/-- Absolute integrability of the scalar transform at every positive frequency. -/
theorem integrable_gaussianArithmeticTransform (l u : ℝ) {c Δ ω : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (hω : 0 < ω) :
    Integrable (fun t : ℝ => gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t) *
      (ω : ℂ) ^ (-((c : ℂ) + I * t))) := by
  have hp : Continuous (fun t : ℝ => (ω : ℂ) ^ (-((c : ℂ) + I * t))) :=
    (by fun_prop : Continuous (fun t : ℝ => -((c : ℂ) + I * t))).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hω.ne'))
  refine ((integrable_gaussianArithmeticKernel l u hc hΔ).norm.mul_const (ω ^ (-c))).mono'
    ((gaussianArithmeticKernel_continuous l Δ u c hc).mul hp).aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hω]
  simp

/-- The explicit expansion also respects both zero-index conventions on Re s > 0. -/
theorem mollifiedGaussianArithmeticTerm_eq_finite_sum_of_re_pos
    (σ y ε l Δ u : ℝ) {s : ℂ} (hs : 0 < s.re) (m n : ℕ) :
    mollifiedGaussianArithmeticTerm σ y ε l Δ u s (m, n) =
      ∑ h ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        (mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
          (n : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ) *
          gaussianArithmeticKernel l Δ u s * (((m * n * h : ℕ) : ℂ) / (k : ℂ)) ^ (-s) := by
  have hs0 : -s ≠ 0 := by
    intro he
    have hz : s = 0 := neg_eq_zero.mp he
    simp [hz] at hs
  by_cases hm : m = 0
  · simp [mollifiedGaussianArithmeticTerm, estermannTerm, LSeries.term_def, hm,
      Complex.zero_cpow hs0]
  by_cases hn : n = 0
  · simp [mollifiedGaussianArithmeticTerm, estermannTerm, LSeries.term_def, hn,
      Complex.zero_cpow hs0]
  exact mollifiedGaussianArithmeticTerm_eq_finite_sum σ y ε l Δ u s hm hn

/-- At zero frequency the scalar integrand vanishes on c > 0. -/
theorem integrable_gaussianArithmeticTransform_of_nonneg (l u : ℝ) {c Δ ω : ℝ}
    (hc0 : 0 < c) (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (hω : 0 ≤ ω) :
    Integrable (fun t : ℝ => gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t) *
      (ω : ℂ) ^ (-((c : ℂ) + I * t))) := by
  rcases hω.eq_or_lt with h | h
  · subst ω
    have hz (t : ℝ) : -((c : ℂ) + I * t) ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    simp only [Complex.ofReal_zero, Complex.zero_cpow (hz _), mul_zero]
    exact integrable_zero _ _ _
  · exact integrable_gaussianArithmeticTransform l u hc hΔ h

/-- Finite mollifier sums and their exact coefficients pass through the scalar integral. -/
theorem integral_mollifiedGaussianArithmeticTerm_eq_finite_sum
    (σ y ε l u : ℝ) {c Δ : ℝ} (hc0 : 0 < c)
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (m n : ℕ) :
    (∫ t : ℝ, mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) (m, n)) =
      ∑ h ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
          (n : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ)) *
          gaussianArithmeticTransform l Δ u c (((m * n * h : ℕ) : ℝ) / (k : ℝ)) := by
  classical
  let S := Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊
  let A (h k : ℕ) : ℂ := (mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
    (n : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ)
  let ω (h k : ℕ) : ℝ := ((m * n * h : ℕ) : ℝ) / (k : ℝ)
  let F (h k : ℕ) (t : ℝ) : ℂ := A h k *
    (gaussianArithmeticKernel l Δ u ((c : ℂ) + I * t) *
      (ω h k : ℂ) ^ (-((c : ℂ) + I * t)))
  have hint (h k : ℕ) : Integrable (F h k) := by
    exact (integrable_gaussianArithmeticTransform_of_nonneg l u hc0 hc hΔ
      (show 0 ≤ ω h k by dsimp [ω]; positivity)).const_mul (A h k)
  have he : (fun t : ℝ => mollifiedGaussianArithmeticTerm σ y ε l Δ u
      ((c : ℂ) + I * t) (m, n)) = fun t => ∑ h ∈ S, ∑ k ∈ S, F h k t := by
    funext t
    simpa only [S, F, A, ω, Complex.ofReal_div, Complex.ofReal_natCast, mul_assoc] using
      mollifiedGaussianArithmeticTerm_eq_finite_sum_of_re_pos σ y ε l Δ u
        (by simpa using hc0 : 0 < ((c : ℂ) + I * t).re) m n
  rw [he, integral_finset_sum S (fun h _ => integrable_finset_sum S (fun k _ => hint h k))]
  apply Finset.sum_congr rfl
  intro h hh
  rw [integral_finset_sum S (fun k _ => hint h k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_const_mul (A h k) _

/-- The complete expanded arithmetic identity for the actual Gaussian moment.
The hypotheses contain only parameter inequalities; no moment or summability provider is assumed. -/
theorem mollifiedGaussianMoment_eq_expanded_arithmetic_series (σ ε u : ℝ)
    {y l c Δ : ℝ} (hy : 0 < y) (hl : 0 < l) (hl' : l < 1)
    (hc : 1 < c) (hlc : 2 * l < c) (hΔ : 0 < Δ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ((∑' p : ℕ × ℕ,
          ∑ h ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
          ∑ k ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
            ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
              (p.2 : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ)) *
              gaussianArithmeticTransform l Δ u c (((p.1 * p.2 * h : ℕ) : ℝ) / (k : ℝ))) -
          (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u) := by
  rw [mollifiedGaussianMoment_eq_arithmetic_series σ ε u hy hl hl' hc hlc hΔ]
  simp_rw [integral_mollifiedGaussianArithmeticTerm_eq_finite_sum σ y ε l u
    (by linarith : 0 < c) (by linarith : 0 < 1 - 2 * l + c) hΔ]

end RiemannResearch.Analysis.ConreyBaluyot
