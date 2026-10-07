import RiemannResearch.RH.ParetoProgressionDigamma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Tactic

/-!
# Actual positive-real digamma: sharp first two Bernoulli terms

The input is the existing proved reciprocal-difference series for the literal
`Complex.digamma`. No asymptotic or Binet formula is assumed. The positive
trapezoidal error is identified by telescoping, and two alternating bounds
are proved by exact derivatives of elementary real functions.

This module proves the first two Bernoulli terms on every positive real
argument. It does not claim the arbitrary-order Bernoulli expansion.

Source for the classical asymptotic statement: NIST DLMF 5.11.2
(https://dlmf.nist.gov/5.11.E2). The formal proof uses the actual digamma
partial-fraction series and Bernoulli integration by parts.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaAsymptotic

/-- The actual Gamma logarithmic derivative has zero imaginary part on the
real axis.  This includes the entire positive axis. -/
theorem digamma_ofReal_im_eq_zero (x : ℝ) :
    (Complex.digamma (x : ℂ)).im = 0 := by
  have h : (Complex.digamma (x : ℂ)).im = -(Complex.digamma (x : ℂ)).im := by
    simpa using congrArg Complex.im (Zeta23.digamma_conj (x : ℂ))
  linarith

/-- The real-part formulas are formulas for digamma itself at real inputs. -/
theorem digamma_ofReal_eq_re (x : ℝ) :
    Complex.digamma (x : ℂ) = ((Complex.digamma (x : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [digamma_ofReal_im_eq_zero]


def cellError (x : ℝ) : ℝ :=
  (x⁻¹ + (x + 1)⁻¹) / 2 - (Real.log (x + 1) - Real.log x)

def inversePowerDifference (x : ℝ) (k : ℕ) : ℝ :=
  (x⁻¹) ^ k - ((x + 1)⁻¹) ^ k

def firstCellRemainder (x : ℝ) : ℝ :=
  inversePowerDifference x 2 / 12 - cellError x

def secondCellRemainder (x : ℝ) : ℝ :=
  cellError x - inversePowerDifference x 2 / 12 +
    inversePowerDifference x 4 / 120

private theorem hasDerivAt_log_gap {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (y + 1) - Real.log y)
      ((x + 1)⁻¹ - x⁻¹) x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h := (((hasDerivAt_id x).add_const 1).log hx1).sub
    (Real.hasDerivAt_log (ne_of_gt hx))
  convert h using 1 <;> first | rfl | simp only [id_eq, one_div, one_mul]

private theorem hasDerivAt_inverse_power_difference {x : ℝ}
    (hx : 0 < x) (k : ℕ) :
    HasDerivAt (fun y => inversePowerDifference y k)
      ((k : ℝ) * (x⁻¹) ^ (k - 1) * (-1 / x ^ 2) -
        (k : ℝ) * ((x + 1)⁻¹) ^ (k - 1) * (-1 / (x + 1) ^ 2)) x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  exact (((hasDerivAt_id x).fun_inv (ne_of_gt hx)).fun_pow k).sub
    ((((hasDerivAt_id x).add_const 1).fun_inv hx1).fun_pow k)

theorem hasDerivAt_cellError {x : ℝ} (hx : 0 < x) :
    HasDerivAt cellError (-1 / (2 * x ^ 2 * (x + 1) ^ 2)) x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h := ((((hasDerivAt_id x).fun_inv (ne_of_gt hx)).add
    (((hasDerivAt_id x).add_const 1).fun_inv hx1)).div_const 2).sub
      (hasDerivAt_log_gap hx)
  convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [ne_of_gt hx, hx1] <;> ring)

theorem hasDerivAt_firstCellRemainder {x : ℝ} (hx : 0 < x) :
    HasDerivAt firstCellRemainder
      (-1 / (6 * x ^ 3 * (x + 1) ^ 3)) x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h := ((hasDerivAt_inverse_power_difference hx 2).div_const 12).sub
    (hasDerivAt_cellError hx)
  convert h using 1 <;> first | rfl | (norm_num only [Nat.cast_ofNat, Nat.reduceSub, id_eq]; field_simp [ne_of_gt hx, hx1] <;> ring)

theorem hasDerivAt_secondCellRemainder {x : ℝ} (hx : 0 < x) :
    HasDerivAt secondCellRemainder
      (-(5 * x ^ 2 + 5 * x + 1) / (30 * x ^ 5 * (x + 1) ^ 5)) x := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h := ((hasDerivAt_cellError hx).sub
    ((hasDerivAt_inverse_power_difference hx 2).div_const 12)).add
      ((hasDerivAt_inverse_power_difference hx 4).div_const 120)
  convert h using 1 <;> first | rfl | (norm_num only [Nat.cast_ofNat, Nat.reduceSub, id_eq]; field_simp [ne_of_gt hx, hx1] <;> ring)

private theorem log_gap_eq {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x = Real.log (1 + x⁻¹) := by
  rw [← Real.log_div (by positivity : x + 1 ≠ 0) (ne_of_gt hx)]
  congr 1
  field_simp [ne_of_gt hx]
  <;> ring

private theorem tendsto_inverse_shift :
    Tendsto (fun x : ℝ => (x + 1)⁻¹) atTop (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_mono (fun x => by change x ≤ x + 1; linarith)
      (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  exact htop.inv_tendsto_atTop

private theorem tendsto_log_gap :
    Tendsto (fun x : ℝ => Real.log (x + 1) - Real.log x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) :=
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).inv_tendsto_atTop
  have hadd : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using hinv.const_add 1
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hadd
  have hzero : Tendsto (fun x : ℝ => Real.log (1 + x⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using hlog
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (log_gap_eq hx).symm

theorem tendsto_cellError : Tendsto cellError atTop (𝓝 0) := by
  change Tendsto (fun x : ℝ => (x⁻¹ + (x + 1)⁻¹) / 2 -
    (Real.log (x + 1) - Real.log x)) atTop (𝓝 0)
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) :=
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).inv_tendsto_atTop
  simpa only [cellError, zero_add, zero_div, sub_zero] using
    ((hinv.add tendsto_inverse_shift).div_const 2).sub tendsto_log_gap

private theorem tendsto_inversePowerDifference (k : ℕ) (hk : 0 < k) :
    Tendsto (fun x => inversePowerDifference x k) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) :=
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).inv_tendsto_atTop
  simpa only [inversePowerDifference, zero_pow (ne_of_gt hk), sub_zero] using
    (hinv.pow k).sub (tendsto_inverse_shift.pow k)

theorem tendsto_firstCellRemainder :
    Tendsto firstCellRemainder atTop (𝓝 0) := by
  change Tendsto (fun x => inversePowerDifference x 2 / 12 - cellError x) atTop (𝓝 0)
  simpa only [zero_div, sub_zero] using
    ((tendsto_inversePowerDifference 2 (by omega)).div_const 12).sub tendsto_cellError

theorem tendsto_secondCellRemainder :
    Tendsto secondCellRemainder atTop (𝓝 0) := by
  change Tendsto (fun x => cellError x - inversePowerDifference x 2 / 12 +
    inversePowerDifference x 4 / 120) atTop (𝓝 0)
  simpa only [zero_div, sub_zero, zero_add] using
    (tendsto_cellError.sub
      ((tendsto_inversePowerDifference 2 (by omega)).div_const 12)).add
        ((tendsto_inversePowerDifference 4 (by omega)).div_const 120)

private theorem nonneg_of_derivative_nonpos_of_tendsto_zero
    (f f' : ℝ → ℝ)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hsign : ∀ x ∈ Ioi (0 : ℝ), f' x ≤ 0)
    (htop : Tendsto f atTop (𝓝 0)) {x : ℝ} (hx : 0 < x) :
    0 ≤ f x := by
  have hanti : AntitoneOn f (Ioi (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    · intro y hy
      exact (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy' : y ∈ Ioi (0 : ℝ) := by simpa only [interior_Ioi] using hy
      exact (hderiv y hy').hasDerivWithinAt
    · intro y hy
      exact hsign y (by simpa only [interior_Ioi] using hy)
  apply le_of_tendsto htop
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hanti hx (by linarith : 0 < y) hy

theorem cellError_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ cellError x := by
  apply nonneg_of_derivative_nonpos_of_tendsto_zero cellError
    (fun y => -1 / (2 * y ^ 2 * (y + 1) ^ 2))
    (fun y hy => hasDerivAt_cellError hy) _ tendsto_cellError hx
  intro y hy
  have hy0 : 0 < y := hy
  have hden : 0 < 2 * y ^ 2 * (y + 1) ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le

theorem firstCellRemainder_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ firstCellRemainder x := by
  apply nonneg_of_derivative_nonpos_of_tendsto_zero firstCellRemainder
    (fun y => -1 / (6 * y ^ 3 * (y + 1) ^ 3))
    (fun y hy => hasDerivAt_firstCellRemainder hy) _ tendsto_firstCellRemainder hx
  intro y hy
  have hy0 : 0 < y := hy
  have hden : 0 < 6 * y ^ 3 * (y + 1) ^ 3 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le

theorem secondCellRemainder_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ secondCellRemainder x := by
  apply nonneg_of_derivative_nonpos_of_tendsto_zero secondCellRemainder
    (fun y => -(5 * y ^ 2 + 5 * y + 1) / (30 * y ^ 5 * (y + 1) ^ 5))
    (fun y hy => hasDerivAt_secondCellRemainder hy) _ tendsto_secondCellRemainder hx
  intro y hy
  have hy0 : 0 < y := hy
  have hden : 0 < 30 * y ^ 5 * (y + 1) ^ 5 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg _ hden.le
  nlinarith [sq_nonneg y]

theorem cellError_bernoulli_bounds {x : ℝ} (hx : 0 < x) :
    inversePowerDifference x 2 / 12 - inversePowerDifference x 4 / 120 ≤
      cellError x ∧
    cellError x ≤ inversePowerDifference x 2 / 12 := by
  have hfirst := firstCellRemainder_nonneg hx
  have hsecond := secondCellRemainder_nonneg hx
  dsimp [firstCellRemainder, secondCellRemainder] at hfirst hsecond
  constructor <;> linarith

private theorem tendsto_harmonic_sub_log_shift {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) - Real.log ((N : ℝ) + x))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hbase : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) - Real.log ((N : ℝ) + 1))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [Zeta23.DigammaSeries.harmonic_cast_eq, one_div] using
      Real.tendsto_harmonic_sub_log_add_one
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have htop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun N => by change (N : ℝ) ≤ (N : ℝ) + 1; linarith)
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    exact htop.inv_tendsto_atTop
  have hratio : Tendsto (fun N : ℕ => 1 + (x - 1) * ((N : ℝ) + 1)⁻¹)
      atTop (𝓝 1) := by
    have htemp : Tendsto (fun N : ℕ => (x - 1) * ((N : ℝ) + 1)⁻¹)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hinv.const_mul (x - 1)
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add htemp
  have hlog : Tendsto (fun N : ℕ => Real.log
      (1 + (x - 1) * ((N : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hdecomp (N : ℕ) :
      Real.log ((N : ℝ) + x) = Real.log ((N : ℝ) + 1) +
        Real.log (1 + (x - 1) * ((N : ℝ) + 1)⁻¹) := by
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    have hNx : ((N : ℝ) + x) ≠ 0 := by positivity
    have he : 1 + (x - 1) * ((N : ℝ) + 1)⁻¹ =
        ((N : ℝ) + x) / ((N : ℝ) + 1) := by
      field_simp [hN]
      <;> ring
    rw [he, Real.log_div hNx hN]
    ring
  have heq (N : ℕ) :
      (∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) - Real.log ((N : ℝ) + x) =
        ((∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) - Real.log ((N : ℝ) + 1)) -
          Real.log (1 + (x - 1) * ((N : ℝ) + 1)⁻¹) := by
    rw [hdecomp]
    ring
  simpa only [heq, sub_zero] using hbase.sub hlog

private theorem tendsto_nat_shift_inverse {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ((N : ℝ) + x)⁻¹) atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) + x) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  exact htop.inv_tendsto_atTop

theorem cellError_sum_range (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, cellError ((n : ℝ) + x) =
      (∑ n ∈ Finset.range N, (((n : ℝ) + x)⁻¹ - ((n : ℝ) + 1)⁻¹)) +
        ((∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) - Real.log ((N : ℝ) + x)) +
        Real.log x - x⁻¹ / 2 + ((N : ℝ) + x)⁻¹ / 2 := by
  have he (n : ℕ) : cellError ((n : ℝ) + x) =
      ((n : ℝ) + x)⁻¹ -
        (((n : ℝ) + x)⁻¹ - (((n + 1 : ℕ) : ℝ) + x)⁻¹) / 2 -
        (Real.log (((n + 1 : ℕ) : ℝ) + x) - Real.log ((n : ℝ) + x)) := by
    simp only [cellError, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_range_sub' (fun n : ℕ => ((n : ℝ) + x)⁻¹) N,
    Finset.sum_range_sub (fun n : ℕ => Real.log ((n : ℝ) + x)) N,
    Finset.sum_sub_distrib]
  simp only [Nat.cast_zero, zero_add]
  ring

/-- The actual positive-axis digamma is the complete positive trapezoidal
series. This discharges the analytic identification rather than assuming it. -/
theorem hasSum_cellError {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => cellError ((n : ℝ) + x))
      (Real.log x - 1 / (2 * x) - (Complex.digamma (x : ℂ)).re) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => cellError_nonneg (by positivity)) _).mpr
  have hrecip :=
    (RiemannResearch.RH.Pareto.hasSum_reciprocal_difference_positive hx).tendsto_sum_nat
  simp only [one_div] at hrecip
  have hlimit := (((hrecip.add (tendsto_harmonic_sub_log_shift hx)).add_const
    (Real.log x)).sub_const (x⁻¹ / 2)).add
      ((tendsto_nat_shift_inverse hx).div_const 2)
  convert hlimit using 1
  · funext N
    exact cellError_sum_range x N
  · simp only [zero_div]
    field_simp [ne_of_gt hx]
    <;> ring

theorem hasSum_inversePowerDifference {x : ℝ} (hx : 0 < x)
    (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => inversePowerDifference ((n : ℝ) + x) k) (x⁻¹ ^ k) := by
  have hpos (n : ℕ) : 0 ≤ inversePowerDifference ((n : ℝ) + x) k := by
    have hbase : (((n : ℝ) + x + 1)⁻¹) ≤ ((n : ℝ) + x)⁻¹ := by
      exact inv_anti₀ (by positivity) (by linarith)
    exact sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) hbase k)
  apply (hasSum_iff_tendsto_nat_of_nonneg hpos _).mpr
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, inversePowerDifference ((n : ℝ) + x) k) =
        x⁻¹ ^ k - (((N : ℝ) + x)⁻¹) ^ k := by
    simpa only [inversePowerDifference, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_add, add_zero, add_assoc, add_left_comm, add_comm] using
        Finset.sum_range_sub' (fun n : ℕ => (((n : ℝ) + x)⁻¹) ^ k) N
  simpa only [he, zero_pow (ne_of_gt hk), sub_zero] using
    tendsto_const_nhds.sub ((tendsto_nat_shift_inverse hx).pow k)

/-- Sharp first-two-Bernoulli enclosure for the literal positive-real
digamma. The constants are not abstract supplied bounds. -/
theorem re_digamma_bernoulli_bounds {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) ≤
      (Complex.digamma (x : ℂ)).re ∧
    (Complex.digamma (x : ℂ)).re ≤
      Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) := by
  have htau := hasSum_cellError hx
  have htwo := (hasSum_inversePowerDifference hx 2 (by omega)).div_const 12
  have hfour := (hasSum_inversePowerDifference hx 4 (by omega)).div_const 120
  have hu := Summable.tsum_le_tsum
    (fun n : ℕ => (cellError_bernoulli_bounds (by positivity : 0 < (n : ℝ) + x)).2)
      htau.summable htwo.summable
  have hl := Summable.tsum_le_tsum
    (fun n : ℕ => (cellError_bernoulli_bounds (by positivity : 0 < (n : ℝ) + x)).1)
      (htwo.sub hfour).summable htau.summable
  rw [htau.tsum_eq, htwo.tsum_eq] at hu
  rw [(htwo.sub hfour).tsum_eq, htau.tsum_eq] at hl
  have he₂ : (x⁻¹ ^ 2) / 12 = 1 / (12 * x ^ 2) := by
    field_simp [ne_of_gt hx]
    <;> ring
  have he₄ : (x⁻¹ ^ 4) / 120 = 1 / (120 * x ^ 4) := by
    field_simp [ne_of_gt hx]
    <;> ring
  rw [he₂] at hu
  rw [he₂, he₄] at hl
  constructor <;> linarith

/-- Actual Gamma derivatives at natural arguments identify the literal
digamma with the harmonic number; no harmonic asymptotic is assumed. -/
theorem digamma_nat_add_one (n : ℕ) :
    Complex.digamma ((n : ℂ) + 1) =
      -(Real.eulerMascheroniConstant : ℂ) + ((harmonic n : ℚ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply,
    (Complex.hasDerivAt_Gamma_nat n).deriv, Complex.Gamma_nat_eq_factorial]
  have hfact : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hfact]

theorem re_digamma_nat_add_one (n : ℕ) :
    (Complex.digamma ((n : ℂ) + 1)).re =
      ((harmonic n : ℚ) : ℝ) - Real.eulerMascheroniConstant := by
  rw [digamma_nat_add_one]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ratCast_re]
  ring

/-- The actual harmonic lower bound needed by the complete norm consumer,
together with the matching next-term upper bound. -/
theorem harmonic_bernoulli_bounds (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
        1 / (12 * (n : ℝ) ^ 2) ≤ ((harmonic n : ℚ) : ℝ) ∧
      ((harmonic n : ℚ) : ℝ) ≤
        Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
          1 / (12 * (n : ℝ) ^ 2) + 1 / (120 * (n : ℝ) ^ 4) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrec := RiemannResearch.RH.Pareto.re_digamma_add_one hnR
  have hnat : (Complex.digamma (((n : ℝ) + 1 : ℝ) : ℂ)).re =
      ((harmonic n : ℚ) : ℝ) - Real.eulerMascheroniConstant := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using
      re_digamma_nat_add_one n
  have hidentity : (Complex.digamma ((n : ℝ) : ℂ)).re =
      ((harmonic n : ℚ) : ℝ) - Real.eulerMascheroniConstant - 1 / (n : ℝ) := by
    linarith
  have hb := re_digamma_bernoulli_bounds hnR
  rw [hidentity] at hb
  have hhalf : 1 / (n : ℝ) = 2 * (1 / (2 * (n : ℝ))) := by
    field_simp [ne_of_gt hnR]
  constructor <;> linarith [hb.1, hb.2]

theorem harmonic_bernoulli_lower (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
      1 / (12 * (n : ℝ) ^ 2) ≤ ((harmonic n : ℚ) : ℝ) :=
  (harmonic_bernoulli_bounds n hn).1

end RiemannResearch.RH.DigammaAsymptotic
