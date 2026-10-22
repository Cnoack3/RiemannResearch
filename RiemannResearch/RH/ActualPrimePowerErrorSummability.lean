import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MediumPNT
import RiemannResearch.Analysis.LogPowerSummability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual square-root prime-power correction

The providers are the existing unconditional MediumPNT theorem and the pinned
Mathlib Costa-Pereira inequalities. The primary function is the actual Chebyshev
prime-power remainder, sampled at natural arguments. No RH hypothesis appears.
Source: user-provided Prime_Phases_Agenda_Proof_Attempts.tex, square-root correction;
the quantitative input is the existing proved MediumPNT adaptation.
-/

noncomputable section
open Filter

namespace RiemannResearch.RH.ActualPrimePowerError

/-- The square-root PNT error plus the remaining higher prime-power count. -/
def error (n : ℕ) : ℝ :=
  Chebyshev.psi n - Chebyshev.theta n - Real.sqrt n

/-- The higher-power remainder after subtracting the full square-root psi count. -/
def rootRemainder (x : ℝ) : ℝ :=
  Chebyshev.psi x - Chebyshev.theta x - Chebyshev.psi (Real.sqrt x)

/-- The exact square-root decomposition preserves every prime power. -/
theorem error_eq (n : ℕ) :
    error n = (Chebyshev.psi (Real.sqrt n) - Real.sqrt n) + rootRemainder n := by
  unfold error rootRemainder
  ring

/-- Costa-Pereira gives an actual cubic-root bound for all remaining prime powers. -/
theorem rootRemainder_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ rootRemainder x ∧
      rootRemainder x ≤ 2 * (Real.log 4 + 4) * x ^ ((1 : ℝ) / 3) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hlow := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0
  have hupp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hsqrt : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hsqrt] at hlow hupp
  have h3 := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹))
  have h5 := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx0 ((5 : ℝ)⁻¹))
  have h53 : x ^ (5 : ℝ)⁻¹ ≤ x ^ (3 : ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hC : 0 ≤ Real.log 4 + 4 := by positivity
  have h5' := mul_le_mul_of_nonneg_left h53 hC
  have hn3 := Chebyshev.psi_nonneg (x ^ (3 : ℝ)⁻¹)
  have hn7 := Chebyshev.psi_nonneg (x ^ (7 : ℝ)⁻¹)
  unfold rootRemainder
  constructor
  · linarith
  · have hi : (3 : ℝ)⁻¹ = (1 : ℝ) / 3 := by norm_num
    rw [← hi]
    linarith

/-- A completely explicit polynomial majorant for the stretched exponential.
Ten Taylor terms suffice for the MediumPNT exponent 1/10. -/
theorem log_mul_decay_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    t * Real.exp (-c * t ^ ((1 : ℝ) / 10)) ≤ (Nat.factorial 10 : ℝ) / c ^ 10 := by
  let u : ℝ := c * t ^ ((1 : ℝ) / 10)
  have hu : 0 ≤ u := mul_nonneg hc.le (Real.rpow_nonneg ht _)
  have hp := Real.pow_div_factorial_le_exp u hu 10
  have hut : u ^ 10 = c ^ 10 * t := by
    dsimp [u]
    rw [mul_pow]
    have ht10 : (t ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      norm_num
    rw [ht10]
  rw [hut] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (-u))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hf : 0 < (Nat.factorial 10 : ℝ) := by positivity
  have hcp : 0 < c ^ 10 := pow_pos hc _
  have hmdiv : (c ^ 10 * t * Real.exp (-u)) / (Nat.factorial 10 : ℝ) ≤ 1 := by
    simpa only [div_mul_eq_mul_div] using hm
  have hm' : c ^ 10 * t * Real.exp (-u) ≤ (Nat.factorial 10 : ℝ) := by
    simpa only [one_mul] using (div_le_iff₀ hf).mp hmdiv
  apply (le_div_iff₀ hcp).2
  dsimp [u] at hm'
  have hexp : -(c * t ^ ((1 : ℝ) / 10)) = -c * t ^ ((1 : ℝ) / 10) := by ring
  rw [hexp] at hm'
  nlinarith [hm']

/-- Actual quantitative PNT implies an eventual inverse-log bound.
The implicit constant is obtained from MediumPNT; its existence is unconditional. -/
theorem psi_inverse_log_bound : ∃ A > 0, ∀ᶠ x : ℝ in atTop,
    |Chebyshev.psi x - x| ≤ A * x / Real.log x := by
  obtain ⟨c, hc, hpnt⟩ :=
    RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MediumPNT
  obtain ⟨C, hC, hbound⟩ := hpnt.exists_pos
  let M : ℝ := (Nat.factorial 10 : ℝ) / c ^ 10
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  filter_upwards [hbound.bound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hdec := log_mul_decay_le hc hlog.le
  have hdec' : Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤ M / Real.log x := by
    apply (le_div_iff₀ hlog).2
    dsimp [M]
    nlinarith [hdec]
  have hb : |Chebyshev.psi x - x| ≤
      C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
      abs_of_pos (mul_pos hx0 (Real.exp_pos _))] using hx
  calc
    _ ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hb
    _ ≤ C * (x * (M / Real.log x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec' hx0.le) hC.le
    _ = _ := by ring

/-- The actual square-root PNT error has the logarithmic envelope needed in Pareto energy. -/
theorem sqrt_psi_bound : ∃ A > 0, ∀ᶠ n : ℕ in atTop,
    |Chebyshev.psi (Real.sqrt n) - Real.sqrt n| ≤
      A * Real.sqrt n / Real.log (2 * (n : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := psi_inverse_log_bound
  refine ⟨4 * A, by positivity, ?_⟩
  have hsample := (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually hbound
  filter_upwards [hsample, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : 0 < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hL : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by nlinarith)
  have hlog2 : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnR
  have hL4 : Real.log (2 * (n : ℝ)) ≤ 4 * Real.log (Real.sqrt n) := by
    rw [Real.log_mul (by norm_num) hn0.ne', Real.log_sqrt hn0.le]
    linarith
  have ht : 0 < Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0.le]
    positivity
  calc
    _ ≤ A * Real.sqrt n / Real.log (Real.sqrt n) := hn
    _ ≤ (4 * A) * Real.sqrt n / Real.log (2 * (n : ℝ)) := by
      apply (div_le_div_iff₀ ht hL).2
      have hmul := mul_le_mul_of_nonneg_left hL4
        (mul_nonneg hA.le (Real.sqrt_nonneg (n : ℝ)))
      nlinarith

end RiemannResearch.RH.ActualPrimePowerError
