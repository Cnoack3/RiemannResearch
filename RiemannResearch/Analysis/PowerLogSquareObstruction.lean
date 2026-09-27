import Mathlib.Analysis.PSeries
import RiemannResearch.Analysis.LogPowerSummability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The power/logarithm obstruction for pointwise-square energy bounds

These are statements about candidate majorants, not lower bounds for any
arithmetic discrepancy. In particular a nonsummable upper bound does not
imply that the bounded sequence has divergent energy.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- Every fixed logarithmic power is too weak to make a power with exponent
strictly smaller than one summable. The logarithmic exponent may be any real
number, including negative numbers. -/
theorem not_summable_power_log_of_lt_one {a : ℝ} (ha : a < 1) (p : ℝ) :
    ¬ Summable (fun n : ℕ =>
      1 / ((n : ℝ) ^ a * Real.log (n : ℝ) ^ p)) := by
  intro hs
  apply Real.not_summable_one_div_natCast
  apply hs.of_norm_bounded_eventually_nat
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop p (show 0 < 1 - a by linarith)).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hnat : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ p‖ ≤ 1 * ‖(n : ℝ) ^ (1 - a)‖ :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      hsmall
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hpnonneg := (Real.rpow_pos_of_pos hlpos p).le
  have hapnonneg := (Real.rpow_pos_of_pos hnpos (1 - a)).le
  rw [Real.norm_of_nonneg hpnonneg, Real.norm_of_nonneg hapnonneg, one_mul] at hn
  have hden : (n : ℝ) ^ a * Real.log (n : ℝ) ^ p ≤ n := by
    calc
      _ ≤ (n : ℝ) ^ a * (n : ℝ) ^ (1 - a) :=
        mul_le_mul_of_nonneg_left hn (Real.rpow_pos_of_pos hnpos a).le
      _ = n := by
        rw [← Real.rpow_add hnpos, show a + (1 - a) = 1 by ring, Real.rpow_one]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  exact one_div_le_one_div_of_le
    (mul_pos (Real.rpow_pos_of_pos hnpos a) (Real.rpow_pos_of_pos hlpos p)) hden

/-- Shifting removes the irrelevant exceptional indices where the real
logarithm is zero. -/
theorem not_summable_shifted_power_log_of_lt_one {a : ℝ} (ha : a < 1) (p : ℝ) :
    ¬ Summable (fun n : ℕ =>
      1 / (((n + 2 : ℕ) : ℝ) ^ a * Real.log ((n + 2 : ℕ) : ℝ) ^ p)) := by
  intro hs
  exact not_summable_power_log_of_lt_one ha p
    ((summable_nat_add_iff 2).mp hs)

/-- The exact claimed subcritical majorant diverges for every fixed real
logarithmic saving. This does not assert divergence of the actual energy. -/
theorem not_summable_subcritical_square_majorant
    {ε : ℝ} (hε : ε < (1 / 2 : ℝ)) (q : ℝ) :
    ¬ Summable (fun n : ℕ =>
      ((n + 2 : ℕ) : ℝ) ^ (-(2 * ε)) /
        Real.log ((n + 2 : ℕ) : ℝ) ^ (2 * q)) := by
  intro hs
  apply not_summable_shifted_power_log_of_lt_one (a := 2 * ε) (by linarith) (2 * q)
  apply hs.congr
  intro n
  rw [Real.rpow_neg (by positivity)]
  simp [div_eq_mul_inv, mul_comm]

/-- Exact conversion of the pointwise-square Pareto majorant. The factor
`x / (x + 1)` must be retained if an equality, rather than an asymptotic
comparison, is wanted. -/
theorem pareto_power_log_square_eq (x ε q : ℝ) (hx : 1 < x) :
    1 / (x * (x + 1)) * (x ^ (1 - ε) / Real.log x ^ q) ^ 2 =
      x / (x + 1) * (x ^ (-(2 * ε)) / Real.log x ^ (2 * q)) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hnum : (x ^ (1 - ε)) ^ 2 = x ^ 2 * x ^ (-(2 * ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      ← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    ring
  have hden : (Real.log x ^ q) ^ 2 = Real.log x ^ (2 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    congr 1
    ring
  rw [div_pow, hnum, hden]
  field_simp

/-- Even with the exact Pareto weight, rather than a power-equivalent
weight, the pointwise-square majorant is nonsummable below half damping. -/
theorem not_summable_subcritical_exact_pareto_majorant
    {ε : ℝ} (hε : ε < (1 / 2 : ℝ)) (q : ℝ) :
    ¬ Summable (fun n : ℕ =>
      1 / (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 1)) *
        (((n + 2 : ℕ) : ℝ) ^ (1 - ε) /
          Real.log ((n + 2 : ℕ) : ℝ) ^ q) ^ 2) := by
  intro hs
  apply not_summable_subcritical_square_majorant hε q
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hx : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < n + 2 by omega)
    rw [pareto_power_log_square_eq _ ε q hx]
    have hfac : (1 / 2 : ℝ) ≤
        ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) + 1) := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    have hm : 0 ≤ ((n + 2 : ℕ) : ℝ) ^ (-(2 * ε)) /
        Real.log ((n + 2 : ℕ) : ℝ) ^ (2 * q) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hfac hm]


/-- The logarithmic harmonic series is divergent. This is an analytic
majorant statement, independent of the completed arithmetic endpoint. -/
theorem not_summable_log_harmonic_majorant :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log (2 * (n : ℝ)))) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (2 * (n : ℝ)))
  have hl (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ)) := by
    rcases n with _ | n
    · simp
    · apply Real.log_nonneg
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hf (n : ℕ) : 0 ≤ f n := by
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (hl n))
  have hm : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm0 hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hmR : 0 < (m : ℝ) := by linarith
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hnR : 0 < (n : ℝ) := lt_of_lt_of_le hmR hmnR
    have hlm : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by linarith)
    have hln : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
    have hlogs : Real.log (2 * (m : ℝ)) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    exact one_div_le_one_div_of_le (mul_pos hmR hlm)
      (mul_le_mul hmnR hlogs hlm.le hnR.le)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro hs
  have hc : Summable (fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) :=
    (summable_condensed_iff_of_nonneg hf hm).mpr hs
  have hh : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    apply (hc.mul_left (Real.log 2)).congr
    intro k
    have hlog : Real.log (2 * ((2 ^ k : ℕ) : ℝ)) =
        ((k : ℝ) + 1) * Real.log 2 := by
      calc
        _ = Real.log ((2 : ℝ) ^ (k + 1)) := by
          congr 1
          simp only [Nat.cast_pow, Nat.cast_ofNat, pow_succ']
        _ = _ := by rw [Real.log_pow]; push_cast; ring
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    dsimp [f]
    rw [hlog]
    push_cast
    field_simp [h2k, hk, hl2.ne']
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- Completes the sharp threshold for the logarithmic p-series already
used by the half-damping endpoint. It reuses the existing convergence
theorem and adds the missing divergence direction. -/
theorem summable_log_power_majorant_iff (p : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ p)) ↔ 1 < p := by
  constructor
  · intro hs
    by_contra h
    have hp : p ≤ 1 := le_of_not_gt h
    apply not_summable_log_harmonic_majorant
    apply hs.of_norm_bounded_eventually_nat
    have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (2 * (n : ℝ)) :=
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop
          (show (0 : ℝ) < 2 by norm_num))).eventually_ge_atTop 1
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlpos : 0 < Real.log (2 * (n : ℝ)) := by linarith
    have hpow : Real.log (2 * (n : ℝ)) ^ p ≤ Real.log (2 * (n : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn hp
    rw [Real.norm_of_nonneg (by positivity :
      0 ≤ 1 / ((n : ℝ) * Real.log (2 * (n : ℝ))))]
    exact one_div_le_one_div_of_le
      (mul_pos hnpos (Real.rpow_pos_of_pos hlpos p))
      (mul_le_mul_of_nonneg_left hpow hnpos.le)
  · exact summable_log_power_majorant

/-- At the power threshold `2 ε = 1`, the pointwise-square majorant is
summable exactly for logarithmic saving `q > 1/2`. -/
theorem summable_half_square_log_majorant_iff (q : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ (2 * q))) ↔
      (1 / 2 : ℝ) < q := by
  rw [summable_log_power_majorant_iff]
  constructor <;> intro h <;> linarith

end RiemannResearch.Analysis
