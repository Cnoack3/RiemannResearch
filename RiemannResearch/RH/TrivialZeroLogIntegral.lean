import RiemannResearch.Analysis.DilogarithmSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integrated logarithmic trivial-zero correction

The real logarithm power series and a geometric majorant identify the
integrated trivial-zero series with its exact logarithmic integral,
retaining both finite endpoints. The dyadic specialization is expressed
through the real dilogarithm series on the unit interval.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Interval

namespace RiemannResearch.RH.TrivialZeroLogIntegral

def densityTerm (n : ℕ) (t : ℝ) : ℝ :=
  (t⁻¹) ^ (2 * (n + 1) + 1) / (2 * ((n + 1 : ℕ) : ℝ))

def integratedTerm (a b : ℝ) (n : ℕ) : ℝ :=
  ((a⁻¹) ^ (2 * (n + 1)) - (b⁻¹) ^ (2 * (n + 1))) /
    (4 * (((n + 1 : ℕ) : ℝ) ^ 2))

theorem densityTerm_hasSum {t : ℝ} (ht : 1 < t) :
    HasSum (fun n : ℕ => densityTerm n t)
      (-Real.log (1 - (t⁻¹) ^ 2) / (2 * t)) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hi1 : t⁻¹ < 1 := (inv_lt_one₀ ht0).2 ht
  have hq : |(t⁻¹) ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_lt_one₀ hi0 hi1 (by norm_num)
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hq).mul_right ((2 * t)⁻¹)
  have he (n : ℕ) : densityTerm n t =
      ((t⁻¹) ^ 2) ^ (n + 1) / ((n : ℝ) + 1) * ((2 * t)⁻¹) := by
    unfold densityTerm
    simp only [Nat.cast_add, Nat.cast_one, pow_add, pow_one, pow_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [div_eq_mul_inv] using hs.congr_fun he

theorem densityTerm_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ densityTerm n t := by
  unfold densityTerm
  positivity

theorem densityTerm_norm_le_geometric {a t : ℝ} (ha : 1 < a)
    (hat : a ≤ t) (n : ℕ) : ‖densityTerm n t‖ ≤ (a⁻¹) ^ n := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ht0 : 0 < t := lt_of_lt_of_le ha0 hat
  have hi0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hi1 : a⁻¹ ≤ 1 := ((inv_lt_one₀ ha0).2 ha).le
  have hit : t⁻¹ ≤ a⁻¹ := (inv_le_inv₀ ht0 ha0).2 hat
  have hd : (1 : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  rw [Real.norm_of_nonneg (densityTerm_nonneg ht0.le n)]
  calc
    densityTerm n t ≤ (t⁻¹) ^ (2 * (n + 1) + 1) :=
      div_le_self (pow_nonneg (inv_nonneg.mpr ht0.le) _) hd
    _ ≤ (a⁻¹) ^ (2 * (n + 1) + 1) :=
      pow_le_pow_left₀ (inv_nonneg.mpr ht0.le) hit _
    _ ≤ (a⁻¹) ^ n := by
      have he : 2 * (n + 1) + 1 = n + (n + 3) := by omega
      rw [he, pow_add]
      simpa using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (n := n + 3) hi0 hi1) (pow_nonneg hi0 n)

theorem integral_densityTerm {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (n : ℕ) :
    (∫ t in a..b, densityTerm n t) = integratedTerm a b n := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    exact (not_le_of_gt ha0) h.1
  have hneg : -(↑(2 * (n + 1) + 1) : ℤ) ≠ -1 := by omega
  have he : -(↑(2 * (n + 1) + 1) : ℤ) + 1 = -(↑(2 * (n + 1)) : ℤ) := by omega
  have hden : ((-(↑(2 * (n + 1) + 1) : ℤ) : ℤ) : ℝ) + 1 =
      -(2 * ((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast he
  unfold densityTerm integratedTerm
  rw [intervalIntegral.integral_div]
  have hfun : (fun t : ℝ => (t⁻¹) ^ (2 * (n + 1) + 1)) =
      (fun t : ℝ => t ^ (-(↑(2 * (n + 1) + 1) : ℤ))) := by
    funext t
    simp only [zpow_neg, zpow_natCast, inv_pow]
  rw [hfun, integral_zpow (Or.inr ⟨hneg, hzero⟩), he, hden]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

theorem densityTerm_intervalIntegrable {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) (n : ℕ) : IntervalIntegrable (densityTerm n) volume a b := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    exact (not_le_of_gt ha0) h.1
  have hpow : IntervalIntegrable
      (fun t : ℝ => t ^ (-(↑(2 * (n + 1) + 1) : ℤ))) volume a b :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  convert hpow.div_const (2 * ((n + 1 : ℕ) : ℝ)) using 1
  funext t
  simp only [densityTerm, zpow_neg, zpow_natCast, inv_pow]

theorem integral_finite_densityTerm {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (M : ℕ) :
    (∫ t in a..b, ∑ n ∈ Finset.range M, densityTerm n t) =
      ∑ n ∈ Finset.range M, integratedTerm a b n := by
  rw [intervalIntegral.integral_finsetSum
    (fun n _ => densityTerm_intervalIntegrable ha hab n)]
  exact Finset.sum_congr rfl (fun n _ => integral_densityTerm ha hab n)

theorem integratedTerm_hasSum {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    HasSum (integratedTerm a b)
      (∫ t in a..b, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hr0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hr1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  have hg : Summable (fun n : ℕ => (a⁻¹) ^ n) :=
    (hasSum_geometric_of_lt_one hr0 hr1).summable
  have hs : HasSum (fun n : ℕ => ∫ t in a..b, densityTerm n t)
      (∫ t in a..b, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => (a⁻¹) ^ n)
    · intro n
      have hm : Measurable (densityTerm n) := by
        unfold densityTerm
        measurability
      exact hm.aestronglyMeasurable
    · intro n
      exact ae_of_all _ (fun t ht => by
        rw [uIoc_of_le hab] at ht
        exact densityTerm_norm_le_geometric ha ht.1.le n)
    · exact ae_of_all _ (fun _ _ => hg)
    · exact intervalIntegrable_const
    · exact ae_of_all _ (fun t ht => by
        rw [uIoc_of_le hab] at ht
        exact densityTerm_hasSum (lt_of_lt_of_le ha ht.1.le))
  exact hs.congr_fun (fun n => (integral_densityTerm ha hab n).symm)

theorem integratedTerm_tsum_eq_log_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑' n : ℕ, integratedTerm a b n) =
      ∫ t in a..b, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) :=
  (integratedTerm_hasSum ha hab).tsum_eq

theorem dyadic_trivial_zero_series_eq_log_integral {x : ℝ} (hx : 2 < x) :
    (∑' n : ℕ, integratedTerm (x / 2) x n) =
      ∫ t in (x / 2)..x, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) := by
  apply integratedTerm_tsum_eq_log_integral <;> linarith

open RiemannResearch.Analysis.DilogarithmSeries

theorem dilog_difference_eq_log_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (1 / 4 : ℝ) * (value ((a⁻¹) ^ 2) - value ((b⁻¹) ^ 2)) =
      ∫ t in a..b, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hqa : (a⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ (inv_nonneg.mpr ha0.le) ((inv_lt_one₀ ha0).2 ha) (by norm_num)
  have hqb : (b⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ (inv_nonneg.mpr hb0.le) ((inv_lt_one₀ hb0).2 hb) (by norm_num)
  have hs := ((summable_term (sq_nonneg _) hqa).hasSum.sub
    (summable_term (sq_nonneg _) hqb).hasSum).mul_left (1 / 4 : ℝ)
  have hs' : HasSum (integratedTerm a b)
      ((1 / 4 : ℝ) * (value ((a⁻¹) ^ 2) - value ((b⁻¹) ^ 2))) := by
    apply hs.congr_fun
    intro n
    unfold integratedTerm term
    rw [pow_mul, pow_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hs'.unique (integratedTerm_hasSum ha hab)

theorem dyadic_dilog_eq_log_integral {x : ℝ} (hx : 2 < x) :
    (1 / 4 : ℝ) * (value (4 / x ^ 2) - value (1 / x ^ 2)) =
      ∫ t in (x / 2)..x, -Real.log (1 - (t⁻¹) ^ 2) / (2 * t) := by
  have hx0 : x ≠ 0 := by linarith
  have ha : 1 < x / 2 := by linarith
  have hab : x / 2 ≤ x := by linarith
  have hqa : ((x / 2)⁻¹) ^ 2 = 4 / x ^ 2 := by
    field_simp [hx0]
    ring
  have hqb : (x⁻¹) ^ 2 = 1 / x ^ 2 := by
    simp [inv_pow, one_div]
  simpa only [hqa, hqb] using dilog_difference_eq_log_integral ha hab

end RiemannResearch.RH.TrivialZeroLogIntegral
