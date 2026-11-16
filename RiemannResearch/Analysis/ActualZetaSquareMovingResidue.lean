/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaSquareMellinTail
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.DigammaGrowthWide
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-!
# The moving double pole in the actual zeta-square Mellin kernel

The pole is p(t) = 1/2 - i t. Its exact Laurent coefficient is
Gamma(p) Y^p (digamma(p) + log Y + 2 gamma), with principal logarithms.

For every natural m, its norm times |t|^m is bounded by
C_m sqrt(Y) (1 + |log Y|), uniformly for Y > 0 and |t| >= 1.
For 1 <= Y <= U <= |t| this strengthens to uniform decay of every
inverse-power order in U. The same statement holds for dyadic square
moments. The constants are independent of Y, U, and t.

Source for the moving-pole contribution: Chourasiya--Simonic,
arXiv:2507.15184v2, Section 5.1:
https://arxiv.org/html/2507.15184v2
The local coefficient and all estimates below are proved unconditionally.
The global shifted-contour identity and the complete actual residual
bound are separate obligations; this module does not assume or prove I1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis

def zetaSquareMovingPole (t : ℝ) : ℂ := (1 / 2 : ℂ) - I * t

def zetaSquareMellinNumerator (Y t : ℝ) (z : ℂ) : ℂ :=
  Gamma z * (Y : ℂ) ^ z *
    riemannZeta₁ ((1 / 2 : ℂ) + I * t + z) ^ 2

def zetaSquareMovingResidue (Y t : ℝ) : ℂ :=
  Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t *
    (digamma (zetaSquareMovingPole t) + Complex.log (Y : ℂ) +
      2 * (Real.eulerMascheroniConstant : ℂ))

theorem zetaSquareMellinNumerator_at_pole (Y t : ℝ) :
    zetaSquareMellinNumerator Y t (zetaSquareMovingPole t) =
      Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t := by
  have h : (1 / 2 : ℂ) + I * t + zetaSquareMovingPole t = 1 := by
    dsimp [zetaSquareMovingPole]
    ring
  simp only [zetaSquareMellinNumerator, h, riemannZeta₁_one, one_pow, mul_one]

theorem zetaSquareMellinKernel_eq_numerator (Y t : ℝ) {z : ℂ}
    (hz : z ≠ zetaSquareMovingPole t) :
    zetaSquareMellinKernel Y t z =
      zetaSquareMellinNumerator Y t z / (z - zetaSquareMovingPole t) ^ 2 := by
  have he : (1 / 2 : ℂ) + I * t + z - 1 = z - zetaSquareMovingPole t := by
    dsimp [zetaSquareMovingPole]
    ring
  have hs : (1 / 2 : ℂ) + I * t + z ≠ 1 := by
    intro hh
    apply hz
    apply sub_eq_zero.mp
    rw [← he, hh, sub_self]
  rw [zetaSquareMellinKernel, riemannZeta_eq_inv_sub_mul hs,
    zetaSquareMellinNumerator, he]
  field_simp [sub_ne_zero.mpr hz]

theorem hasDerivAt_zetaSquareMellinNumerator_pole {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) :
    HasDerivAt (zetaSquareMellinNumerator Y t)
      (zetaSquareMovingResidue Y t) (zetaSquareMovingPole t) := by
  let p := zetaSquareMovingPole t
  have hp : 0 < p.re := by norm_num [p, zetaSquareMovingPole]
  have hΓ : DifferentiableAt ℂ Gamma p := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have he := congrArg Complex.re hn
    norm_num [p, zetaSquareMovingPole] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΓ0 : Gamma p ≠ 0 := Gamma_ne_zero_of_re_pos hp
  have hY0 : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hY)
  have hy := (hasDerivAt_id p).const_cpow (c := (Y : ℂ)) (Or.inl hY0)
  have hs : (1 / 2 : ℂ) + I * t + p = 1 := by
    dsimp [p, zetaSquareMovingPole]
    ring
  have hz : HasDerivAt (fun z : ℂ => riemannZeta₁ ((1 / 2 : ℂ) + I * t + z))
      (Real.eulerMascheroniConstant : ℂ) p := by
    have hz1 : HasDerivAt riemannZeta₁ (Real.eulerMascheroniConstant : ℂ) 1 := by
      simpa using (differentiable_riemannZeta₁ (1 : ℂ)).hasDerivAt
    have hz1' : HasDerivAt riemannZeta₁ (Real.eulerMascheroniConstant : ℂ)
        ((1 / 2 : ℂ) + I * t + p) := by rw [hs]; exact hz1
    simpa only [mul_one] using!
      hz1'.comp p ((hasDerivAt_id p).const_add ((1 / 2 : ℂ) + I * t))
  have hd := (hΓ.hasDerivAt.mul hy).mul (hz.pow 2)
  convert! hd using 1
  change Gamma p * (Y : ℂ) ^ p *
    (digamma p + Complex.log (Y : ℂ) + 2 * (Real.eulerMascheroniConstant : ℂ)) = _
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, hs, riemannZeta₁_one, one_pow,
    mul_one, Nat.cast_ofNat]
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp [hΓ0]

/-- Exact pole-subtracted Laurent limit of the actual kernel at the moving double pole. -/
theorem zetaSquareMellinKernel_moving_residue {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Tendsto (fun z : ℂ => (z - zetaSquareMovingPole t) *
      (zetaSquareMellinKernel Y t z -
        (Gamma (zetaSquareMovingPole t) * (Y : ℂ) ^ zetaSquareMovingPole t) /
          (z - zetaSquareMovingPole t) ^ 2))
      (𝓝[≠] zetaSquareMovingPole t) (𝓝 (zetaSquareMovingResidue Y t)) := by
  apply (hasDerivAt_iff_tendsto_slope.mp
    (hasDerivAt_zetaSquareMellinNumerator_pole hY t)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ zetaSquareMovingPole t at hz
  rw [zetaSquareMellinKernel_eq_numerator Y t hz,
    ← zetaSquareMellinNumerator_at_pole Y t]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hz]

/-- Arbitrary inverse-power decay of the actual moving residue, with its complete
smoothing-scale dependence explicit. -/
theorem exists_zetaSquareMovingResidue_pow_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t : ℝ, 0 < Y → 1 ≤ |t| →
      ‖zetaSquareMovingResidue Y t‖ * |t| ^ m ≤
        C * Y ^ (1 / 2 : ℝ) * (1 + |Real.log Y|) := by
  obtain ⟨D, hD, hDb⟩ := Zeta23.ThmE.digamma_growth_wide
  obtain ⟨G, hG, hGb⟩ :=
    Complex.exists_gamma_mul_cpow_neg_strip_pow_bound
      (lam := 1) (by norm_num) (a := 1 / 2) (b := 1 / 2) (m+1)
      (by positivity)
  let E : ℝ := |Real.eulerMascheroniConstant|
  refine ⟨G * (2 * D + 1 + 2 * E), by positivity, ?_⟩
  intro Y t hY ht
  let p := zetaSquareMovingPole t
  have ht0 : 0 < |t| := by linarith
  have htne : -t ≠ 0 := neg_ne_zero.mpr (abs_pos.mp ht0)
  have hgb : ‖Gamma p‖ * |t| ^ (m+1) ≤ G := by
    have hh := hGb (1/2) ⟨le_rfl, le_rfl⟩ (-t) htne
    simpa [p, zetaSquareMovingPole, sub_eq_add_neg, mul_comm] using hh
  have hgb0 : ‖Gamma p‖ * |t| ^ m ≤ G := by
    apply le_trans _ hgb
    rw [pow_succ]
    nlinarith [mul_nonneg (norm_nonneg (Gamma p)) (pow_nonneg (abs_nonneg t) m)]
  have hpsi : ‖digamma p‖ ≤ 2 * D * |t| := by
    have hh := hDb p (by norm_num [p, zetaSquareMovingPole])
      (by norm_num [p, zetaSquareMovingPole])
    have hl : Real.log (2 + |t|) ≤ 2 * |t| := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |t|)
      linarith
    have hh' : ‖digamma p‖ ≤ D * Real.log (2 + |t|) := by
      simpa [p, zetaSquareMovingPole] using hh
    exact hh'.trans (by nlinarith [mul_le_mul_of_nonneg_left hl hD.le])
  have hy : ‖(Y : ℂ) ^ p‖ = Y ^ (1/2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    congr 1
    norm_num [p, zetaSquareMovingPole]
  have hlog : ‖Complex.log (Y : ℂ)‖ = |Real.log Y| := by
    rw [← Complex.ofReal_log hY.le, Complex.norm_real, Real.norm_eq_abs]
  have hbr : ‖digamma p + Complex.log (Y : ℂ) +
      2 * (Real.eulerMascheroniConstant : ℂ)‖ ≤
      2 * D * |t| + |Real.log Y| + 2 * E := by
    calc
      _ ≤ ‖digamma p‖ + ‖Complex.log (Y : ℂ)‖ +
          ‖2 * (Real.eulerMascheroniConstant : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [hlog, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
        dsimp [E]
        linarith
  have hnon : 0 ≤ Y ^ (1/2 : ℝ) := Real.rpow_nonneg hY.le _
  calc
    _ = Y ^ (1/2 : ℝ) * ((‖Gamma p‖ * |t| ^ m) *
        ‖digamma p + Complex.log (Y : ℂ) + 2 * (Real.eulerMascheroniConstant : ℂ)‖) := by
      change ‖Gamma p * (Y : ℂ) ^ p *
        (digamma p + Complex.log (Y : ℂ) + 2 * (Real.eulerMascheroniConstant : ℂ))‖ *
          |t| ^ m = _
      rw [norm_mul, norm_mul, hy]
      ring
    _ ≤ Y ^ (1/2 : ℝ) * ((‖Gamma p‖ * |t| ^ m) *
        (2 * D * |t| + |Real.log Y| + 2 * E)) := by gcongr
    _ = Y ^ (1/2 : ℝ) * (2 * D * (‖Gamma p‖ * |t| ^ (m+1)) +
        (|Real.log Y| + 2 * E) * (‖Gamma p‖ * |t| ^ m)) := by
      rw [pow_succ]
      ring
    _ ≤ Y ^ (1/2 : ℝ) * (2 * D * G + (|Real.log Y| + 2 * E) * G) := by
      gcongr
    _ ≤ G * (2 * D + 1 + 2 * E) * Y ^ (1/2 : ℝ) * (1 + |Real.log Y|) := by
      have he : 0 ≤ E := abs_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hG (by positivity : 0 ≤ 2 * D + 2 * E))
        (mul_nonneg hnon (abs_nonneg (Real.log Y)))]


/-- Rapid decay uniform over every smoothing scale between one and the height.
No residue-bound hypothesis is supplied by the caller. -/
theorem exists_zetaSquareMovingResidue_uniform_pow_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U Y t : ℝ,
      1 ≤ U → 1 ≤ Y → Y ≤ U → U ≤ |t| →
      ‖zetaSquareMovingResidue Y t‖ * U ^ m ≤ C := by
  obtain ⟨C, hC, hCb⟩ := exists_zetaSquareMovingResidue_pow_bound (m+2)
  refine ⟨C, hC, ?_⟩
  intro U Y t hU hY hYU hUt
  have hU0 : 0 < U := by linarith
  have hY0 : 0 < Y := by linarith
  have hYs : Y ^ (1/2 : ℝ) ≤ U := by
    calc
      _ ≤ U ^ (1/2 : ℝ) := Real.rpow_le_rpow hY0.le hYU (by norm_num)
      _ ≤ U ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by norm_num)
      _ = U := Real.rpow_one U
  have hYl : 1 + |Real.log Y| ≤ U := by
    rw [abs_of_nonneg (Real.log_nonneg hY)]
    have := Real.log_le_sub_one_of_pos hY0
    linarith
  have hb : (‖zetaSquareMovingResidue Y t‖ * U ^ m) * U ^ 2 ≤ C * U ^ 2 := by
    calc
      _ = ‖zetaSquareMovingResidue Y t‖ * U ^ (m+2) := by rw [pow_add]; ring
      _ ≤ ‖zetaSquareMovingResidue Y t‖ * |t| ^ (m+2) := by gcongr
      _ ≤ C * Y ^ (1/2 : ℝ) * (1 + |Real.log Y|) :=
        hCb Y t hY0 (hU.trans hUt)
      _ ≤ C * U * U := by gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (show 0 < U ^ 2 by positivity)).mp
    (by simpa only [mul_comm] using hb)

theorem continuous_zetaSquareMovingResidue {Y : ℝ} (hY : 0 < Y) :
    Continuous (zetaSquareMovingResidue Y) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let p := zetaSquareMovingPole t
  have hp : 0 < p.re := by norm_num [p, zetaSquareMovingPole]
  have hΓ : AnalyticAt ℂ Gamma p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [ho.mem_nhds hp] with z hz
    apply differentiableAt_Gamma
    intro n hn
    have he := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpsi : ContinuousAt digamma p := by
    convert! hΓ.deriv.continuousAt.div hΓ.continuousAt (Gamma_ne_zero_of_re_pos hp) using 1
  have hpc : Continuous (fun u : ℝ => zetaSquareMovingPole u) := by
    unfold zetaSquareMovingPole
    fun_prop
  have hy : Continuous (fun u : ℝ => (Y : ℂ) ^ zetaSquareMovingPole u) :=
    hpc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hY)))
  exact ((hΓ.continuousAt.comp (f := zetaSquareMovingPole) (x := t) hpc.continuousAt).mul
    hy.continuousAt).mul
    (((hpsi.comp (f := zetaSquareMovingPole) (x := t) hpc.continuousAt).add
      continuousAt_const).add continuousAt_const)

/-- Every polynomially weighted dyadic square moment of the moving residue
is bounded, uniformly for all 1 ≤ Y ≤ U. -/
theorem exists_zetaSquareMovingResidue_uniform_second_moment (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U Y : ℝ, 1 ≤ U → 1 ≤ Y → Y ≤ U →
      (∫ t in U..2*U, ‖zetaSquareMovingResidue Y t‖ ^ 2) * U ^ (2*m) ≤ C * U := by
  obtain ⟨C, hC, hCb⟩ := exists_zetaSquareMovingResidue_uniform_pow_bound m
  refine ⟨C^2, sq_nonneg _, ?_⟩
  intro U Y hU hY hYU
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  have hcont := (continuous_zetaSquareMovingResidue hY0).norm.pow 2
  calc
    _ = ∫ t in U..2*U, ‖zetaSquareMovingResidue Y t‖ ^ 2 * U ^ (2*m) := by
      rw [intervalIntegral.integral_mul_const]
    _ ≤ ∫ _t in U..2*U, C^2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hcont.mul continuous_const).intervalIntegrable _ _)
        intervalIntegrable_const
      intro t ht
      have hUt : U ≤ |t| := ht.1.trans (le_abs_self t)
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ‖zetaSquareMovingResidue Y t‖ * U^m)
        (hCb U Y t hU hY hYU hUt) 2
      simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow, ← pow_mul, Nat.mul_comm] using! hh
    _ = C^2 * U := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

end RiemannResearch.Analysis
