import RiemannResearch.RH.ParetoRepairModulus
import RiemannResearch.RH.PrimeLogSummability
import RiemannResearch.RH.SmallGapLogBound
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Analytic completion of the summable-prime-repair argument

The discrete Pareto modulus and the unconditional Chebyshev summation theorem
are combined here. The final theorem explicitly retains only the quantitative
gap estimate as an arithmetic hypothesis. It does not assert that the
published smooth-number gap theorem has itself been formalized.
-/

namespace RiemannResearch.RH.Pareto
open Filter
noncomputable section

/-- An explicit square-root modulus for the actual full repair variance. -/
theorem arithmeticRepair_binary_variance_sqrt_bound (n h : ℕ)
    (hh0 : 0 < h) (hh : h ≤ n) :
    paretoVariance (arithmeticRepair 2 n (n + h)) ≤
      16 * Real.sqrt ((h : ℝ) / n) / n := by
  have hn : 0 < n := lt_of_lt_of_le hh0 hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh0
  have hδ : 0 < (h : ℝ) / n := div_pos hhR hnR
  have hδ1 : (h : ℝ) / n ≤ 1 := by
    apply (div_le_one hnR).2
    exact_mod_cast hh
  have hm := small_gap_log_modulus_le_sqrt ((h : ℝ) / n) hδ hδ1
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 / (n : ℝ) by positivity)
  have heq : (8 / (n : ℝ)) *
      (((h : ℝ) / n) * (1 + Real.log (((h : ℝ) / n)⁻¹))) =
      8 * ((h : ℝ) / (n : ℝ)^2) * (1 + Real.log ((n : ℝ) / h)) := by
    rw [inv_div]
    ring
  rw [heq] at hm'
  calc
    _ ≤ 8 * ((h : ℝ) / (n : ℝ)^2) * (1 + Real.log ((n : ℝ) / h)) :=
      arithmeticRepair_binary_variance_log_bound n h hh0 hh
    _ ≤ (8 / (n : ℝ)) * (2 * Real.sqrt ((h : ℝ) / n)) := hm'
    _ = _ := by ring

/-- Concrete quantitative repair estimate after substituting a logarithmic
gap bound. The exponent loss is harmless for summability over primes. -/
theorem arithmeticRepair_binary_variance_le_log_weight
    (n h : ℕ) (hn1 : 1 < n) (hh0 : 0 < h) (hh : h ≤ n)
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hgap : (h : ℝ) / n ≤ C / (Real.log (n : ℝ))^η) :
    paretoVariance (arithmeticRepair 2 n (n + h)) ≤
      (16 * Real.sqrt C) * (1 / ((n : ℝ) * (Real.log (n : ℝ))^(η/2))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hs := Real.sqrt_le_sqrt hgap
  have hpow : Real.sqrt ((Real.log (n : ℝ))^η) =
      (Real.log (n : ℝ))^(η/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hl.le]
    congr 1
    ring
  rw [Real.sqrt_div hC, hpow] at hs
  calc
    _ ≤ 16 * Real.sqrt ((h : ℝ) / n) / n :=
      arithmeticRepair_binary_variance_sqrt_bound n h hh0 hh
    _ ≤ 16 * (Real.sqrt C / (Real.log (n : ℝ))^(η/2)) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hnR.le
    _ = _ := by ring

/-- With a quantitative gap estimate supplied, summability of the actual
prime repairs now follows from proved results. This is a conditional arithmetic
reduction, not a proof of the missing smooth-number gap theorem. -/
theorem summable_arithmeticRepair_of_prime_log_gap
    (h : Nat.Primes → ℕ) (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hh : ∀ p, 0 < h p ∧ h p ≤ p.val)
    (hgap : ∀ p : Nat.Primes,
      (h p : ℝ) / p.val ≤ C / (Real.log (p.val : ℝ))^η) :
    Summable (fun p : Nat.Primes =>
      paretoVariance (arithmeticRepair 2 p.val (p.val + h p))) := by
  have hs := (summable_prime_inv_mul_log_rpow (η/2) (by linarith)).mul_left
    (16 * Real.sqrt C)
  apply Summable.of_nonneg_of_le (fun p => paretoVariance_nonneg _) _ hs
  intro p
  exact arithmeticRepair_binary_variance_le_log_weight p.val (h p)
    p.property.one_lt (hh p).1 (hh p).2 C η hC hη (hgap p)

/-- The same conclusion only needs the quantitative estimate away from
finitely many primes, exactly as in a published asymptotic gap theorem. -/
theorem summable_arithmeticRepair_of_eventually_prime_log_gap
    (h : Nat.Primes → ℕ) (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hgap : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      0 < h p ∧ h p ≤ p.val ∧
      (h p : ℝ) / p.val ≤ C / (Real.log (p.val : ℝ))^η) :
    Summable (fun p : Nat.Primes =>
      paretoVariance (arithmeticRepair 2 p.val (p.val + h p))) := by
  have hs := (summable_prime_inv_mul_log_rpow (η/2) (by linarith)).mul_left
    (16 * Real.sqrt C)
  apply hs.of_norm_bounded_eventually
  filter_upwards [hgap] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (paretoVariance_nonneg _)]
  exact arithmeticRepair_binary_variance_le_log_weight p.val (h p)
    p.property.one_lt hp.1 hp.2.1 C η hC hη hp.2.2

/-- A logarithmic-power gap estimate gives an actual ratio limit, with no
quantitative distribution theorem beyond the displayed bound. -/
theorem prime_relative_gap_tendsto_zero (h : Nat.Primes → ℕ)
    (C η : ℝ) (hη : 0 < η)
    (hgap : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      (h p : ℝ) / p.val ≤ C / (Real.log (p.val : ℝ))^η) :
    Filter.Tendsto (fun p : Nat.Primes => (h p : ℝ) / p.val)
      Filter.cofinite (nhds 0) := by
  have hi : Function.Injective (fun p : Nat.Primes => p.val) :=
    fun _ _ he => Subtype.ext he
  have hv : Filter.Tendsto (fun p : Nat.Primes => p.val)
      Filter.cofinite Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hi.tendsto_cofinite
  have hr : Filter.Tendsto (fun p : Nat.Primes => (p.val : ℝ))
      Filter.cofinite Filter.atTop := tendsto_natCast_atTop_atTop.comp hv
  have hlog := Real.tendsto_log_atTop.comp hr
  have hmajor := ((tendsto_rpow_atTop hη).comp hlog).const_div_atTop C
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) hgap hmajor

/-- Complete analytic conclusion of the smooth-prime repair argument: both
the conductor ratio and the sum of actual variances follow from the single
remaining quantitative arithmetic input. -/
theorem prime_repairs_limit_and_summable_of_log_gap
    (h : Nat.Primes → ℕ) (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hgap : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      0 < h p ∧ (h p : ℝ) / p.val ≤ C / (Real.log (p.val : ℝ))^η) :
    Filter.Tendsto (fun p : Nat.Primes => ((p.val + h p : ℕ) : ℝ) / p.val)
      Filter.cofinite (nhds 1) ∧
    Summable (fun p : Nat.Primes =>
      paretoVariance (arithmeticRepair 2 p.val (p.val + h p))) := by
  have hz := prime_relative_gap_tendsto_zero h C η hη (hgap.mono (fun _ hp => hp.2))
  have hsmall : ∀ᶠ p : Nat.Primes in Filter.cofinite, h p ≤ p.val := by
    have he := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [he] with p hp
    have hpR : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
    have hlt : (h p : ℝ) < p.val := (div_lt_one hpR).1 hp
    exact_mod_cast hlt.le
  constructor
  · have hr : Filter.Tendsto (fun p : Nat.Primes => 1 + (h p : ℝ) / p.val)
        Filter.cofinite (nhds 1) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hz)
    apply hr.congr' (Filter.Eventually.of_forall (fun p => ?_))
    have hpR : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    simp [Nat.cast_add, add_div, hpR]
  · apply summable_arithmeticRepair_of_eventually_prime_log_gap h C η hC hη
    filter_upwards [hgap, hsmall] with p hp hs
    exact ⟨hp.1, hs, hp.2⟩

end
end RiemannResearch.RH.Pareto
