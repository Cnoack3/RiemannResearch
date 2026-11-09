import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Psi-normalized screened Ramanujan families

The prime-power source on [2,N] is exactly Chebyshev.psi N. Normalizing
all screened coefficients by this source produces a legal mean-one family.
Its squared error is exactly the complete centered covariance mass / psi(N)^2.
The repository's unconditional PNT converts subquadratic covariance mass
into the previously proved screened-covariance RH criterion.
No covariance decay estimate is assumed proved here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur

def window (N : ℕ) : Finset ℕ := Finset.Icc 2 N

theorem prime_source_eq_psi (N : ℕ) :
    (∑ q : primeConductors (window N), ArithmeticFunction.vonMangoldt q.val) =
      Chebyshev.psi (N : ℝ) := by
  classical
  rw [Finset.sum_coe_sort]
  unfold primeConductors
  rw [Finset.sum_filter]
  have ht (q : ℕ) :
      (if IsPrimePow q then ArithmeticFunction.vonMangoldt q else 0) =
        ArithmeticFunction.vonMangoldt q := by
    by_cases h : IsPrimePow q
    · simp only [if_pos h]
    · simp only [ArithmeticFunction.vonMangoldt_apply, if_neg h]
  simp_rw [ht]
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  apply Finset.sum_subset
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hq).2⟩
  · intro q hq hn
    have hsmall : q = 0 ∨ q = 1 := by
      simp only [window, Finset.mem_Icc] at hq hn
      omega
    rcases hsmall with rfl | rfl <;> simp

theorem psi_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Chebyshev.psi (N : ℝ) := by
  have hn : Chebyshev.psi (N : ℝ) ≠ 0 := by
    intro he
    have h := Chebyshev.psi_eq_zero_iff.mp he
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact lt_of_le_of_ne (Chebyshev.psi_nonneg _) (Ne.symm hn)

def coefficients (N : ℕ) : primeConductors (window N) → ℝ :=
  fun _ => (Chebyshev.psi (N : ℝ))⁻¹

def approximant (N : ℕ) : ThresholdHilbert :=
  screenedCombination (window N) (coefficients N)

def covarianceMass (N : ℕ) : ℝ :=
  screenedCovariance (window N) (fun _ => 1)

theorem constant_source (N : ℕ) (c : ℝ) :
    screenedSource (window N) (fun _ => c) = c * Chebyshev.psi (N : ℝ) := by
  unfold screenedSource
  rw [← Finset.mul_sum, prime_source_eq_psi]

theorem constant_covariance (s : Finset ℕ) (c : ℝ) :
    screenedCovariance s (fun _ => c) = c ^ 2 * screenedCovariance s (fun _ => 1) := by
  simp only [screenedCovariance, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem source_eq_one {N : ℕ} (hN : 2 ≤ N) :
    screenedSource (window N) (coefficients N) = 1 := by
  unfold coefficients
  rw [constant_source, inv_mul_cancel₀ (psi_pos hN).ne']

theorem approximant_mean_one {N : ℕ} (hN : 2 ≤ N) :
    inner ℝ (approximant N) hilbertOne = 1 :=
  (screenedCombination_inner_one _ _).trans (source_eq_one hN)

theorem approximant_mem_closedSpace (N : ℕ) :
    approximant N ∈ CoefficientStabilization.closedSpace := by
  apply screenedCombination_mem_closedSpace
  intro q hq
  have h := (Finset.mem_Icc.mp hq).1
  omega

theorem covarianceMass_nonneg (N : ℕ) : 0 ≤ covarianceMass N :=
  screenedCovariance_nonneg _ _

theorem normalized_covariance (N : ℕ) :
    screenedCovariance (window N) (coefficients N) =
      covarianceMass N / (Chebyshev.psi (N : ℝ)) ^ 2 := by
  unfold coefficients
  rw [constant_covariance]
  simp only [covarianceMass, div_eq_mul_inv, inv_pow, mul_comm]

theorem error_exact {N : ℕ} (hN : 2 ≤ N) :
    ‖hilbertOne - approximant N‖ ^ 2 =
      covarianceMass N / (Chebyshev.psi (N : ℝ)) ^ 2 := by
  rw [approximant, screened_error_mean_covariance, source_eq_one hN,
    sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_add, normalized_covariance]


theorem psi_div_nat_tendsto :
    Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  convert RiemannResearch.NumberTheory.PrimeNumberTheorem.WeakPNT' using 1
  funext N
  congr 1
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rfl

theorem riemannHypothesis_of_covarianceMass_subquadratic
    (h : Tendsto (fun N => covarianceMass N / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_screened_covariance window coefficients
  · intro N q hq
    have hq' := (Finset.mem_Icc.mp hq).1
    omega
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (source_eq_one hN).symm
  · simp only [normalized_covariance]
    have ht : Tendsto (fun N => (covarianceMass N / (N : ℝ) ^ 2) /
        (Chebyshev.psi (N : ℝ) / (N : ℝ)) ^ 2) atTop (𝓝 0) := by
      convert! h.div (psi_div_nat_tendsto.pow 2) (by norm_num) using 1
      simp only [one_pow, zero_div]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp

theorem normalizedMass_tendsto_iff_subquadratic :
    Tendsto (fun N => covarianceMass N / (Chebyshev.psi (N:ℝ))^2) atTop (𝓝 0) ↔
      Tendsto (fun N => covarianceMass N / (N:ℝ)^2) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht : Tendsto (fun N => (covarianceMass N/(Chebyshev.psi (N:ℝ))^2) *
        (Chebyshev.psi (N:ℝ)/(N:ℝ))^2) atTop (𝓝 0) := by
      convert! h.mul (psi_div_nat_tendsto.pow 2) using 1
      simp only [one_pow, zero_mul]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hp := (psi_pos hN).ne'
    have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  · intro h
    have ht : Tendsto (fun N => (covarianceMass N/(N:ℝ)^2) /
        (Chebyshev.psi (N:ℝ)/(N:ℝ))^2) atTop (𝓝 0) := by
      convert! h.div (psi_div_nat_tendsto.pow 2) (by norm_num) using 1
      simp only [one_pow, zero_div]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp

theorem approximant_tendsto_iff_normalizedMass :
    Tendsto approximant atTop (𝓝 hilbertOne) ↔
      Tendsto (fun N => covarianceMass N/(Chebyshev.psi (N:ℝ))^2) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht : Tendsto (fun N => ‖hilbertOne-approximant N‖^2) atTop (𝓝 0) := by
      simpa only [norm_sub_rev, zero_pow (by norm_num : 2 ≠ 0)] using
        (tendsto_iff_norm_sub_tendsto_zero.mp h).pow 2
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact error_exact hN
  · intro h
    have ht : Tendsto (fun N => ‖hilbertOne-approximant N‖^2) atTop (𝓝 0) := by
      apply h.congr'
      filter_upwards [eventually_ge_atTop 2] with N hN
      exact (error_exact hN).symm
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    convert! ht.sqrt using 1
    · funext N
      rw [Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
    · norm_num

theorem approximant_tendsto_iff_subquadratic :
    Tendsto approximant atTop (𝓝 hilbertOne) ↔
      Tendsto (fun N => covarianceMass N/(N:ℝ)^2) atTop (𝓝 0) :=
  approximant_tendsto_iff_normalizedMass.trans normalizedMass_tendsto_iff_subquadratic

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
