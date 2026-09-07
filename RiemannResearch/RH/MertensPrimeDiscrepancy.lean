import RiemannResearch.RH.MertensElementary
import RiemannResearch.RH.PrimeSquarePartialSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual bounded prime-square discrepancy

Source: user-provided argument, §6.6. The proof removes higher prime powers
from the Mangoldt Mertens estimate using the unconditional Chebyshev bound
`psi - theta = O(sqrt x)` and Abel summation.
-/

open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH

private noncomputable def nonprimeMangoldt (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

private theorem nonprimeMangoldt_nonneg (n : ℕ) : 0 ≤ nonprimeMangoldt n := by
  unfold nonprimeMangoldt
  split_ifs <;> simp only [le_refl, ArithmeticFunction.vonMangoldt_nonneg]

private theorem sum_nonprimeMangoldt (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, nonprimeMangoldt n) =
      Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [nonprimeMangoldt, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [nonprimeMangoldt, hp]

private theorem nonprimeMangoldt_prefix_identity (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, nonprimeMangoldt n / n) =
      mangoldtReciprocalPrefix N - primeReciprocalLogSum N := by
  have hrange : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [mangoldtReciprocalPrefix, primeReciprocalLogSum, Nat.floor_natCast, hrange]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [nonprimeMangoldt, primeSquareWeight, hp,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [nonprimeMangoldt, primeSquareWeight, hp]

private theorem continuousOn_inverse_sq (b : ℝ) :
    ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Icc 1 b) := by
  apply (continuousOn_id.pow 2).inv₀
  intro x hx
  exact pow_ne_zero 2 (by change x ≠ 0; linarith [hx.1])

private theorem deriv_inverse_eq {x : ℝ} (hx : x ≠ 0) :
    deriv (fun y : ℝ => y⁻¹) x = -(x ^ 2)⁻¹ := by
  exact (hasDerivAt_inv hx).deriv

private theorem nonprimeMangoldt_prefix_abel {N : ℕ} (hN : N ≠ 0) :
    (∑ n ∈ Finset.Icc 0 N, nonprimeMangoldt n / n) =
      (Chebyshev.psi N - Chebyshev.theta N) / N +
      ∫ x in Ioc 1 (N : ℝ), (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2 := by
  have hd (x : ℝ) (hx : x ∈ Icc 1 (N : ℝ)) :
      DifferentiableAt ℝ (fun y : ℝ => y⁻¹) x :=
    (hasDerivAt_inv (by linarith [hx.1])).differentiableAt
  have hc : ContinuousOn (deriv (fun y : ℝ => y⁻¹)) (Icc 1 (N : ℝ)) := by
    apply (continuousOn_inverse_sq N).neg.congr
    intro x hx
    exact deriv_inverse_eq (by linarith [hx.1])
  have ha := sum_mul_eq_sub_integral_mul₀ nonprimeMangoldt
    (by simp [nonprimeMangoldt]) (N : ℝ) hd hc.integrableOn_Icc
  have hi :
      (∫ x in Ioc 1 (N : ℝ), deriv (fun y : ℝ => y⁻¹) x *
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, nonprimeMangoldt n) =
      -(∫ x in Ioc 1 (N : ℝ), (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [deriv_inverse_eq (by linarith [hx.1]), sum_nonprimeMangoldt]
    ring
  rw [hi, sum_nonprimeMangoldt, sub_neg_eq_add] at ha
  simpa only [Nat.floor_natCast, div_eq_mul_inv, mul_comm] using ha

/-- Higher prime powers contribute a bounded amount at exponent one.
The bound is obtained from the actual Chebyshev functions. -/
theorem exists_nonprimeMangoldt_prefix_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, N ≠ 0 →
      0 ≤ mangoldtReciprocalPrefix N - primeReciprocalLogSum N ∧
      mangoldtReciprocalPrefix N - primeReciprocalLogSum N ≤ 3 * C := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hC0 : 0 ≤ C := by simpa using hC 1
  refine ⟨C, hC0, ?_⟩
  intro N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : 0 < (N : ℝ) := by linarith
  rw [← nonprimeMangoldt_prefix_identity]
  constructor
  · exact Finset.sum_nonneg (fun n hn =>
      div_nonneg (nonprimeMangoldt_nonneg n) (Nat.cast_nonneg n))
  · rw [nonprimeMangoldt_prefix_abel hN]
    have hboundary : (Chebyshev.psi N - Chebyshev.theta N) / N ≤ C := by
      apply (div_le_iff₀ hN0).mpr
      have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := Real.sqrt_le_iff.mpr
        ⟨hN0.le, by nlinarith [sq_nonneg ((N : ℝ) - 1)]⟩
      exact (hC N).trans (mul_le_mul_of_nonneg_left hsqrt hC0)
    have hr : IntegrableOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    have hint : (∫ x in Ioc 1 (N : ℝ), x ^ (-3 / 2 : ℝ)) ≤ 2 := by
      calc
        _ ≤ ∫ x in Ioi (1 : ℝ), x ^ (-3 / 2 : ℝ) := by
          apply setIntegral_mono_set hr
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            change 1 < x at hx
            exact Real.rpow_nonneg (by linarith) _
          · exact Filter.Eventually.of_forall (fun x hx => hx.1)
        _ = 2 := by
          rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
          norm_num
    have hmeas : IntegrableOn
        (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2) (Ioc 1 (N : ℝ)) := by
      have h := integrableOn_mul_sum_Icc nonprimeMangoldt (m := 0)
        (by norm_num : (0 : ℝ) ≤ 1) (continuousOn_inverse_sq N).integrableOn_Icc
      have he :
          (fun x => (x ^ 2)⁻¹ * ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, nonprimeMangoldt n) =
          (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2) := by
        ext x
        rw [sum_nonprimeMangoldt]
        ring
      rw [he] at h
      exact h.mono_set Ioc_subset_Icc_self
    have hpoint (x : ℝ) (hx : x ∈ Ioc 1 (N : ℝ)) :
        (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2 ≤ C * x ^ (-3 / 2 : ℝ) := by
      have hx0 : 0 < x := by linarith [hx.1]
      calc
        _ ≤ C * Real.sqrt x / x ^ 2 := div_le_div_of_nonneg_right (hC x) (sq_nonneg _)
        _ = _ := by
          rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_two,
            ← Real.rpow_neg hx0.le, mul_assoc, ← Real.rpow_add hx0]
          norm_num
    have hmain :
        (∫ x in Ioc 1 (N : ℝ), (Chebyshev.psi x - Chebyshev.theta x) / x ^ 2) ≤ 2 * C := by
      calc
        _ ≤ ∫ x in Ioc 1 (N : ℝ), C * x ^ (-3 / 2 : ℝ) := by
          apply integral_mono_ae hmeas ((hr.mono_set (fun x hx => hx.1)).const_mul C)
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hpoint x hx
        _ = C * ∫ x in Ioc 1 (N : ℝ), x ^ (-3 / 2 : ℝ) := integral_const_mul _ _
        _ ≤ 2 * C := by nlinarith
    linarith

/-- Mertens's bounded discrepancy for the actual prime-only prefix at integers. -/
theorem exists_primeReciprocalLogSum_discrepancy_bound_nat :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, N ≠ 0 →
      |primeReciprocalLogSum N - Real.log N| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_nonprimeMangoldt_prefix_bound
  refine ⟨Real.log 4 + 5 + 3 * C, by positivity, ?_⟩
  intro N hN
  have hm := mangoldtReciprocalPrefix_discrepancy_bound hN
  obtain ⟨hp0, hp1⟩ := hC N hN
  have hm' := abs_le.mp hm
  apply abs_le.mpr
  constructor <;> linarith

/-- The exact discrepancy used by the prime-square Abel formula is bounded
on its full real domain, with no unverified Mertens hypothesis. -/
theorem exists_primeSquareDiscrepancy_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → |primeSquareDiscrepancy x| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_primeReciprocalLogSum_discrepancy_bound_nat
  refine ⟨B + 1, by linarith, ?_⟩
  intro x hx
  let N := ⌊x⌋₊
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN1
  have hx0 : 0 < x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog0 : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
  have hratio : x / (N : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hN0).mpr
    have hN1' : 1 ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hlog1 : Real.log x - Real.log N ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hN0)
    rw [Real.log_div hx0.ne' hN0.ne'] at h
    linarith
  have hprefix : primeReciprocalLogSum x = primeReciprocalLogSum N := by
    simp only [primeReciprocalLogSum, Nat.floor_natCast, N]
  have hb := abs_le.mp (hB N (by omega))
  unfold primeSquareDiscrepancy
  rw [hprefix]
  apply abs_le.mpr
  constructor <;> linarith

/-- The logarithmic discrepancy E(t) in §6.6 is uniformly bounded for t ≥ 0. -/
theorem exists_logarithmic_primeSquareDiscrepancy_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |primeReciprocalLogSum (Real.exp t) - t| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_primeSquareDiscrepancy_bound
  refine ⟨B, hB0, ?_⟩
  intro t ht
  simpa only [primeSquareDiscrepancy, Real.log_exp] using
    hB (Real.exp t) (Real.one_le_exp_iff.mpr ht)

/-- The pre-existing compact prime-square remainder now has a checked
arithmetic provider in place of its former Mertens-bound hypothesis. -/
theorem exists_uniform_primeSquareSector_remainder_bound
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hsupp : ∀ s, 1 ≤ s → c s = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 < R →
      |primeSquareSector c R + R * (∫ s in (0 : ℝ)..1, c s)| ≤
        2 * B * ∫ s in (0 : ℝ)..1, |deriv c s| := by
  obtain ⟨B, hB0, hB⟩ := exists_primeSquareDiscrepancy_bound
  refine ⟨B, hB0, ?_⟩
  intro R hR
  apply abs_primeSquareSector_remainder_le c hc hc' hsupp hR
  intro x hx
  exact hB x hx.1.le

end RiemannResearch.RH
