import RiemannResearch.Analysis.ContractiveLogBudget
import RiemannResearch.RH.RamanujanMellinProduct
import RiemannResearch.RH.RamanujanUnitMean
import RiemannResearch.RH.RamanujanSaturationCriteria
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative logarithmic and Blaschke budgets from actual packet mass

Source: user-requested fourth Ramanujan continuation, 23 October 2026.
The product terminology is motivated by J.-F. Burnol,
https://arxiv.org/abs/math/9910055. The deductions here use the verified finite
Ramanujan certificates and positive product limit, not an identification of
the entire residual with the zero product. All nonlinear logarithmic slack
is retained in the exact budget. The estimates do not assert that any of
these nonnegative charges vanish.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

def zeroFactor (z : ℂ) : ℝ := ‖(z - 1) / z‖ ^ 2
def zeroCharge (z : ℂ) : ℝ := (2 * z.re - 1) / ‖z‖ ^ 2

theorem zeroCharge_eq_defect (z : ℂ) (hz : z ≠ 0) :
    zeroCharge z = 1 - zeroFactor z := by
  unfold zeroCharge zeroFactor
  rw [norm_div, div_pow]
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div, div_eq_one_iff_eq hn]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

theorem zeroFactor_pos (z : ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1) :
    0 < zeroFactor z := sq_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr hz1) hz))

theorem zeroCharge_pos (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) : 0 < zeroCharge z := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr h0))

theorem zeroFactor_lt_one (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) : zeroFactor z < 1 := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have h := zeroCharge_pos z hz
  rw [zeroCharge_eq_defect z h0] at h
  linarith

theorem zeroFactor_partialProduct (z : ℕ → ℂ) (n : ℕ) :
    Real.partialProduct (fun i => zeroFactor (z i)) n =
      mellinZeroProduct (fun i : Fin n => z i.val) := by
  unfold Real.partialProduct mellinZeroProduct zeroFactor
  exact (Fin.prod_univ_eq_prod_range _ n).symm

end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ContractiveLogBudget
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual packet mass yields an exact finite logarithmic budget with both remainders. -/
theorem zero_log_budget_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hz1 : ∀ i, z i ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    -Real.log (packetMass n) = (∑ i, zeroCharge (z i)) +
      (∑ i, slack (zeroFactor (z i))) +
      Real.log (mellinZeroProduct z / packetMass n) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef, mellinZeroProduct, zeroFactor] using
    finite_budget_exact Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) (packetMass_pos n hn)

/-- Every finite family of distinct actual right zeros has a packet-controlled Blaschke budget. -/
theorem zero_charge_sum_le_packet_log (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (n : ℕ) (hn : 0 < n) : ∑ i, zeroCharge (z i) ≤ -Real.log (packetMass n) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef, mellinZeroProduct, zeroFactor] using
    finite_defect_bound Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) (packetMass_pos n hn)
      (packetMass_le_zeroProduct z hzre hinj hz1 hzero n)

/-- The finite zero-family budget also has the stronger limiting captured mass. -/
theorem zero_log_limit_budget_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hz1 : ∀ i, z i ≠ 1) :
    -Real.log (1 - limitEnergy) = (∑ i, zeroCharge (z i)) +
      (∑ i, slack (zeroFactor (z i))) +
      Real.log (mellinZeroProduct z / (1 - limitEnergy)) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef, mellinZeroProduct, zeroFactor] using
    finite_budget_exact Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) packetLimitMass_pos

theorem zero_charge_sum_le_limit_packet_log (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    ∑ i, zeroCharge (z i) ≤ -Real.log (1 - limitEnergy) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  have hmass : 1 - limitEnergy ≤ mellinZeroProduct z := by
    linarith [zeroProduct_limitEnergy_lower_bound z hzre hinj hz1 hzero]
  simpa only [hdef, mellinZeroProduct, zeroFactor] using
    finite_defect_bound Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) packetLimitMass_pos hmass

/-- Summability is a conclusion of the actual zero certificates and positive packet mass. -/
theorem zero_log_hasSum (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    HasSum (fun i => -Real.log (zeroFactor (z i))) (-Real.log (mellinZeroProductLimit z)) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  apply hasSum_neg_log _ (fun i => zeroFactor_pos (z i) (hz0 i) (hz1 i))
    (fun i => (zeroFactor_lt_one (z i) (hzre i)).le)
    (zeroProductLimit_pos z hzre hinj hz1 hzero)
  simpa only [← zeroFactor_partialProduct] using mellinZeroProduct_prefix_tendsto z hzre hinj

theorem zero_charge_summable (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    Summable (fun i => zeroCharge (z i)) := by
  apply Summable.of_nonneg_of_le (fun i => (zeroCharge_pos (z i) (hzre i)).le)
    (fun i => ?_) (zero_log_hasSum z hzre hinj hz1 hzero).summable
  have hz0 : z i ≠ 0 := by intro h; have := hzre i; simp [h] at this; linarith
  rw [zeroCharge_eq_defect _ hz0]
  have h := slack_nonneg (zeroFactor_pos (z i) hz0 (hz1 i))
  unfold slack at h
  linarith

/-- All first-order zero charges and all nonlinear slack exhaust the logarithmic budget. -/
theorem zero_infinite_log_budget (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    Summable (fun i => slack (zeroFactor (z i))) ∧
      -Real.log (mellinZeroProductLimit z) =
        (∑' i, zeroCharge (z i)) + ∑' i, slack (zeroFactor (z i)) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have ht : Tendsto (Real.partialProduct (fun i => zeroFactor (z i))) atTop
      (𝓝 (mellinZeroProductLimit z)) := by
    simpa only [← zeroFactor_partialProduct] using mellinZeroProduct_prefix_tendsto z hzre hinj
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef] using
    infinite_budget_exact _ (fun i => zeroFactor_pos (z i) (hz0 i) (hz1 i))
      (fun i => (zeroFactor_lt_one (z i) (hzre i)).le)
      (zeroProductLimit_pos z hzre hinj hz1 hzero) ht

/-- The strongest captured-mass ceiling uses the positive limiting packet mass;
every positive finite packet mass gives a further, weaker ceiling. -/
theorem zero_infinite_charge_bounds (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    (∑' i, zeroCharge (z i)) ≤ -Real.log (mellinZeroProductLimit z) ∧
      (-Real.log (mellinZeroProductLimit z) ≤ -Real.log (1 - limitEnergy) ∧
        ∀ n : ℕ, 0 < n → -Real.log (1 - limitEnergy) ≤ -Real.log (packetMass n)) := by
  constructor
  · have he := (zero_infinite_log_budget z hzre hinj hz1 hzero).2
    have hs : 0 ≤ ∑' i, slack (zeroFactor (z i)) := by
      apply tsum_nonneg
      intro i
      have hz0 : z i ≠ 0 := by
        intro h
        have hh := hzre i
        simp [h] at hh
        linarith
      exact slack_nonneg (zeroFactor_pos (z i) hz0 (hz1 i))
    linarith
  · constructor
    · have hmL : 1 - limitEnergy ≤ mellinZeroProductLimit z := by
        linarith [zeroProductLimit_limitEnergy_lower_bound z hzre hinj hz1 hzero]
      exact neg_le_neg (Real.log_le_log packetLimitMass_pos hmL)
    · intro n hn
      have hnm : packetMass n ≤ 1 - limitEnergy := by
        apply ge_of_tendsto packetMass_tendsto
        filter_upwards [eventually_ge_atTop n] with k hk
        exact packetMass_monotone hk
      exact neg_le_neg (Real.log_le_log (packetMass_pos n hn) hnm)

/-- Exact budget at the limiting packet mass, which is positive without RH.
The remaining logarithm measures the unresolved gap between that captured
mass and the full actual zero-product limit. -/
theorem zero_limit_packet_log_budget (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    -Real.log (1 - limitEnergy) = (∑' i, zeroCharge (z i)) +
      (∑' i, slack (zeroFactor (z i))) +
      Real.log (mellinZeroProductLimit z / (1 - limitEnergy)) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have ht : Tendsto (Real.partialProduct (fun i => zeroFactor (z i))) atTop
      (𝓝 (mellinZeroProductLimit z)) := by
    simpa only [← zeroFactor_partialProduct] using mellinZeroProduct_prefix_tendsto z hzre hinj
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef] using
    infinite_budget_with_mass _ (fun i => zeroFactor_pos (z i) (hz0 i) (hz1 i))
      (fun i => (zeroFactor_lt_one (z i) (hzre i)).le)
      (zeroProductLimit_pos z hzre hinj hz1 hzero) ht packetLimitMass_pos

/-- The infinite packet budget retains all nonlinear slack and the unused
mass between the actual zero-product limit and the finite packet mass. -/
theorem zero_infinite_packet_log_budget (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (n : ℕ) (hn : 0 < n) :
    -Real.log (packetMass n) = (∑' i, zeroCharge (z i)) +
      (∑' i, slack (zeroFactor (z i))) +
      Real.log (mellinZeroProductLimit z / packetMass n) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have ht : Tendsto (Real.partialProduct (fun i => zeroFactor (z i))) atTop
      (𝓝 (mellinZeroProductLimit z)) := by
    simpa only [← zeroFactor_partialProduct] using mellinZeroProduct_prefix_tendsto z hzre hinj
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef] using
    infinite_budget_with_mass _ (fun i => zeroFactor_pos (z i) (hz0 i) (hz1 i))
      (fun i => (zeroFactor_lt_one (z i) (hzre i)).le)
      (zeroProductLimit_pos z hzre hinj hz1 hzero) ht (packetMass_pos n hn)

/-- Every cutoff has an exact residual logarithmic budget consisting of the
remaining zero charges and their complete nonlinear slack. -/
theorem zero_tail_log_budget (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (N : ℕ) :
    Real.log (mellinZeroProduct (fun i : Fin N => z i.val) / mellinZeroProductLimit z) =
      (∑' i, zeroCharge (z (i + N))) + ∑' i, slack (zeroFactor (z (i + N))) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have ht : Tendsto (Real.partialProduct (fun i => zeroFactor (z i))) atTop
      (𝓝 (mellinZeroProductLimit z)) := by
    simpa only [← zeroFactor_partialProduct] using mellinZeroProduct_prefix_tendsto z hzre hinj
  have hdef : ∀ i, zeroCharge (z i) = 1 - zeroFactor (z i) :=
    fun i => zeroCharge_eq_defect (z i) (hz0 i)
  simpa only [hdef, zeroFactor_partialProduct] using
    tail_budget_exact _ (fun i => zeroFactor_pos (z i) (hz0 i) (hz1 i))
      (fun i => (zeroFactor_lt_one (z i) (hzre i)).le)
      (zeroProductLimit_pos z hzre hinj hz1 hzero) ht N

theorem zero_tail_charge_bound (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (N : ℕ) :
    (∑' i, zeroCharge (z (i + N))) ≤
      Real.log (mellinZeroProduct (fun i : Fin N => z i.val) / mellinZeroProductLimit z) := by
  rw [zero_tail_log_budget z hzre hinj hz1 hzero N]
  apply le_add_of_nonneg_right
  apply tsum_nonneg
  intro i
  have hz0 : z (i + N) ≠ 0 := by
    intro h
    have hh := hzre (i + N)
    simp [h] at hh
    linarith
  exact slack_nonneg (zeroFactor_pos (z (i + N)) hz0 (hz1 (i + N)))

end RiemannResearch.RH.RamanujanZeroCertificates
