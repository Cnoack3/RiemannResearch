import RiemannResearch.RH.RamanujanMeanOptimizer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exact covariance signal-to-noise identity for genuine Ramanujan packets

Source: user-provided `signal_to_noise_RH_program (2)(1).pdf`, Theorem 4.2.
The arithmetic matrix and solution below use the full Pareto law. The previously
constructed genuine Gram inverse supplies the normal equations; finite common
periods prove every denominator nonzero. No inverse witness or RH-level estimate
is assumed.

-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanOptimizer
open FiniteSchur
noncomputable section

theorem mass_nonneg (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    0 ≤ mass s hs := by
  rw [← projection_energy]
  exact paretoInner_self_nonneg _

/-- The actual full centered covariance entries. -/
def covariance (s : Finset ℕ) (i j : s) : ℝ :=
  paretoInner (family s i) (family s j) - meanVector s i * meanVector s j

def covarianceAction (s : Finset ℕ) (v : s → ℝ) (i : s) : ℝ :=
  ∑ j : s, covariance s i j * v j

def covarianceCoefficients (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : s → ℝ :=
  fun i => (1 - mass s hs)⁻¹ * coefficients s hs i

def covarianceSNR (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : ℝ :=
  ∑ i : s, meanVector s i * covarianceCoefficients s hs i

theorem covariance_symm (s : Finset ℕ) (i j : s) :
    covariance s i j = covariance s j i := by
  unfold covariance
  rw [paretoInner_comm]
  ring

theorem covarianceAction_eq_gram (s : Finset ℕ) (v : s → ℝ) (i : s) :
    covarianceAction s v i = ramanujanGramAction s v i -
      meanVector s i * ∑ j : s, meanVector s j * v j := by
  simp only [covarianceAction, covariance, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  rfl

theorem covarianceAction_scale (s : Finset ℕ) (v : s → ℝ) (t : ℝ) (i : s) :
    covarianceAction s (fun j => t * v j) i = t * covarianceAction s v i := by
  unfold covarianceAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem covarianceAction_coefficients (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (i : s) :
    covarianceAction s (coefficients s hs) i = meanVector s i * (1 - mass s hs) := by
  rw [covarianceAction_eq_gram]
  have hnormal : ramanujanGramAction s (coefficients s hs) i = meanVector s i := by
    exact congrFun (ramanujanGramSolve_normal_equations s hs (meanVector s)) i
  have hm : (∑ j : s, meanVector s j * coefficients s hs j) = mass s hs := by
    rw [mass_eq_inverse_mean_quadratic]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hnormal, hm]
  ring

/-- An explicit solution of the actual centered covariance normal equations. -/
theorem covarianceCoefficients_normal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    covarianceAction s (covarianceCoefficients s hs) = meanVector s := by
  funext i
  unfold covarianceCoefficients
  rw [covarianceAction_scale, covarianceAction_coefficients]
  have hd : 1 - mass s hs ≠ 0 := ne_of_gt (sub_pos.mpr (mass_lt_one_general s hs))
  field_simp [hd]

theorem covarianceSNR_eq_mass_ratio (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    covarianceSNR s hs = mass s hs / (1 - mass s hs) := by
  have hm : (∑ i : s, meanVector s i * coefficients s hs i) = mass s hs := by
    rw [mass_eq_inverse_mean_quadratic]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold covarianceSNR covarianceCoefficients
  calc
    _ = (1 - mass s hs)⁻¹ * ∑ i : s, meanVector s i * coefficients s hs i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hm]; ring

theorem covarianceSNR_nonneg (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    0 ≤ covarianceSNR s hs := by
  rw [covarianceSNR_eq_mass_ratio]
  exact div_nonneg (mass_nonneg s hs) (le_of_lt (sub_pos.mpr (mass_lt_one_general s hs)))

/-- The exact SNR formula for the true optimal full Pareto error. -/
theorem projection_error_eq_covarianceSNR (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    paretoError (projection s hs) = 1 / (1 + covarianceSNR s hs) := by
  rw [projection_error, covarianceSNR_eq_mass_ratio]
  have hd : 1 - mass s hs ≠ 0 := ne_of_gt (sub_pos.mpr (mass_lt_one_general s hs))
  have hden : 1 + mass s hs / (1 - mass s hs) ≠ 0 := by
    have hn := covarianceSNR_nonneg s hs
    rw [covarianceSNR_eq_mass_ratio] at hn
    linarith
  field_simp [hd, hden]
  ring

/-- The full Pareto approximation minimum, with the genuine centered SNR. -/
theorem covarianceSNR_minimum (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (b : s → ℝ) :
    1 / (1 + covarianceSNR s hs) ≤ paretoError (combination (family s) b) := by
  rw [← projection_error_eq_covarianceSNR]
  exact projection_minimizes s hs b

/-- C^{-1} lambda /(1+R) is exactly the independently constructed minimizer. -/
theorem covariance_optimal_coefficients (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (i : s) :
    covarianceCoefficients s hs i / (1 + covarianceSNR s hs) = coefficients s hs i := by
  rw [covarianceSNR_eq_mass_ratio]
  unfold covarianceCoefficients
  have hd : 1 - mass s hs ≠ 0 := ne_of_gt (sub_pos.mpr (mass_lt_one_general s hs))
  have hden : 1 + mass s hs / (1 - mass s hs) ≠ 0 := by
    have hn := covarianceSNR_nonneg s hs
    rw [covarianceSNR_eq_mass_ratio] at hn
    linarith
  field_simp [hd, hden]
  ring

/-- No nonzero coefficient vector lies in the actual centered covariance kernel. -/
theorem covarianceAction_kernel (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (v : s → ℝ) (hv : covarianceAction s v = 0) : v = 0 := by
  let t : ℝ := ∑ j : s, meanVector s j * v j
  have hcoeff : v = fun i => t * coefficients s hs i := by
    apply ramanujanGramAction_injective s hs
    ext i
    have hrow := congrFun hv i
    rw [covarianceAction_eq_gram] at hrow
    have hscale : ramanujanGramAction s (fun j => t * coefficients s hs j) i =
        t * meanVector s i := by
      change ramanujanGramAction s (t • coefficients s hs) i = _
      rw [map_smul]
      change t * ramanujanGramAction s (coefficients s hs) i = _
      rw [show ramanujanGramAction s (coefficients s hs) i = meanVector s i from
        congrFun (ramanujanGramSolve_normal_equations s hs (meanVector s)) i]
    rw [hscale]
    change ramanujanGramAction s v i - meanVector s i * t = 0 at hrow
    linarith
  have ht : t = t * mass s hs := by
    calc
      t = ∑ i : s, meanVector s i * (t * coefficients s hs i) := by
        change (∑ i : s, meanVector s i * v i) = _
        apply Finset.sum_congr rfl
        intro i _
        rw [congrFun hcoeff i]
      _ = t * mass s hs := by
        rw [mass_eq_inverse_mean_quadratic, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hd : 1 - mass s hs ≠ 0 := ne_of_gt (sub_pos.mpr (mass_lt_one_general s hs))
  have ht0 : t = 0 := by
    have hh : t * (1 - mass s hs) = 0 := by nlinarith only [ht]
    exact (mul_eq_zero.mp hh).resolve_right hd
  rw [hcoeff]
  funext i
  simp [ht0]

/-- Uniqueness of the actual centered covariance solution. -/
theorem covarianceAction_injective (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    Function.Injective (covarianceAction s) := by
  intro v w hvw
  have hz : covarianceAction s (v-w) = 0 := by
    ext i
    have hi := congrFun hvw i
    change (∑ j : s, covariance s i j * (v j - w j)) = 0
    rw [show (∑ j : s, covariance s i j * (v j - w j)) =
        covarianceAction s v i - covarianceAction s w i by
          simp [covarianceAction, mul_sub, Finset.sum_sub_distrib]]
    exact sub_eq_zero.mpr hi
  exact sub_eq_zero.mp (covarianceAction_kernel s hs (v-w) hz)

theorem covarianceCoefficients_unique (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (v : s → ℝ) (hv : covarianceAction s v = meanVector s) :
    v = covarianceCoefficients s hs :=
  covarianceAction_injective s hs (hv.trans (covarianceCoefficients_normal s hs).symm)

end
end RiemannResearch.RH.Pareto.RamanujanOptimizer
