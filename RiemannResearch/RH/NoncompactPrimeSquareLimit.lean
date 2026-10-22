import RiemannResearch.RH.MertensPrimeDiscrepancy
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual noncompact prime-square Abel limit

The arithmetic hypotheses are discharged: the prime discrepancy is bounded
by the elementary Mertens proof, and the infinite prime series is summable
by an ordinary p-series comparison. The profile assumptions below are
explicit C¹ and inverse-square decay assumptions in the x coordinate.
No full-return profile provider or Weil explicit formula is assumed proved.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH

/-- The actual arithmetic discrepancy is measurable, including its jumps. -/
theorem measurable_primeSquareDiscrepancy : Measurable primeSquareDiscrepancy := by
  have hp : Measurable primeReciprocalLogSum :=
    (measurable_of_countable (fun N : ℕ =>
      ∑ p ∈ Finset.Icc 0 N, primeSquareWeight p)).comp Nat.measurable_floor
  exact hp.sub Real.measurable_log

private theorem primeSquareWeight_nonneg_le_one (p : ℕ) :
    0 ≤ primeSquareWeight p ∧ primeSquareWeight p ≤ 1 := by
  by_cases hp : p.Prime
  · have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    have hp0 : 0 < (p : ℝ) := by linarith
    simp only [primeSquareWeight, if_pos hp]
    constructor
    · exact div_nonneg (Real.log_nonneg hp1) hp0.le
    · apply (div_le_iff₀ hp0).mpr
      have h := Real.log_le_sub_one_of_pos hp0
      linarith
  · simp [primeSquareWeight, hp]

private theorem integrableOn_inverse_square :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  apply hi.mono' ((measurable_id.pow_const 2).inv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := by change 1 < x at hx; linarith
  change ‖(x ^ 2)⁻¹‖ ≤ x ^ (-2 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x)),
    Real.rpow_neg hx0, Real.rpow_two]

/-- Noncompact profiles with a concrete x⁻² bound give an absolutely convergent
actual prime-square series. No summability hypothesis is hidden here. -/
theorem summable_primeSquare_of_profile_decay (c : ℝ → ℝ) (R A : ℝ)
    (hA : 0 ≤ A)
    (hdecay : ∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2) :
    Summable (fun p : ℕ => primeSquareWeight p * c (2 * Real.log p / R)) := by
  have hs : Summable (fun p : ℕ => A * (1 / (p : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left A
  apply hs.of_norm_bounded
  intro p
  by_cases hp : p.Prime
  · obtain ⟨hw0, hw1⟩ := primeSquareWeight_nonneg_le_one p
    have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    calc
      _ ≤ primeSquareWeight p * (A / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hdecay p hp1) hw0
      _ ≤ A / (p : ℝ) ^ 2 :=
        mul_le_of_le_one_left (div_nonneg hA (sq_nonneg _)) hw1
      _ = _ := by ring
  · simp only [primeSquareWeight, if_neg hp, zero_mul, norm_zero]
    positivity

/-- Concrete decay gives integrability of the main term, the profile derivative,
and the exact arithmetic-discrepancy integrand on the full half-line. -/
theorem integrable_noncompact_primeSquare_terms
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (R A D : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hdecay : ∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2)
    (hderiv : ∀ x : ℝ, 1 ≤ x →
      |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) :
    IntegrableOn (fun x => c (2 * Real.log x / R) / x) (Ioi 1) ∧
    IntegrableOn (deriv (fun x => c (2 * Real.log x / R))) (Ioi 1) ∧
    IntegrableOn (fun x => deriv (fun y => c (2 * Real.log y / R)) x *
      primeSquareDiscrepancy x) (Ioi 1) := by
  let g : ℝ → ℝ := fun x => c (2 * Real.log x / R)
  have hgm : Measurable g := hc.continuous.measurable.comp
    ((measurable_const.mul Real.measurable_log).div_const R)
  have hdm : Measurable (deriv g) := measurable_deriv g
  obtain ⟨B, hB0, hB⟩ := exists_primeSquareDiscrepancy_bound
  refine ⟨?_, ?_, ?_⟩
  · apply (integrableOn_inverse_square.const_mul A).mono'
      ((hgm.div measurable_id).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hx0 : 0 < x := by linarith
    change ‖g x / x‖ ≤ A * (x ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    calc
      |g x| / x ≤ |g x| := div_le_self (abs_nonneg _) hx1
      _ ≤ A / x ^ 2 := hdecay x hx1
      _ = A * (x ^ 2)⁻¹ := div_eq_mul_inv _ _
  · apply (integrableOn_inverse_square.const_mul D).mono' hdm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change ‖deriv g x‖ ≤ D * (x ^ 2)⁻¹
    rw [Real.norm_eq_abs, ← div_eq_mul_inv]
    exact hderiv x (le_of_lt hx)
  · apply (integrableOn_inverse_square.const_mul (D * B)).mono'
      ((hdm.mul measurable_primeSquareDiscrepancy).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change ‖deriv g x * primeSquareDiscrepancy x‖ ≤ (D * B) * (x ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (D / x ^ 2) * B := mul_le_mul (hderiv x (le_of_lt hx))
        (hB x (le_of_lt hx)) (abs_nonneg _) (div_nonneg hD (sq_nonneg _))
      _ = (D * B) * (x ^ 2)⁻¹ := by ring

private theorem tendsto_primeSquareCutoff_of_summable
    (c : ℝ → ℝ) (R : ℝ)
    (hs : Summable (fun p : ℕ => primeSquareWeight p * c (2 * Real.log p / R))) :
    Tendsto (fun N : ℕ => primeSquareCutoff c R N) atTop
      (𝓝 (primeSquareSector c R)) := by
  have hnext : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b, by intro n hn; omega⟩
  have ht := (hs.hasSum.tendsto_sum_nat.comp hnext).const_mul (-2 : ℝ)
  apply ht.congr
  intro N
  have he : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  simp only [primeSquareCutoff, Nat.floor_natCast, he, Function.comp_apply]

private theorem tendsto_setIntegral_Ioc_nat {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 1)) :
    Tendsto (fun N : ℕ => ∫ x in Ioc 1 (N : ℝ), f x) atTop
      (𝓝 (∫ x in Ioi 1, f x)) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply (intervalIntegral_tendsto_integral_Ioi 1 hf hnat).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  exact intervalIntegral.integral_of_le hN1

/-- The bounded arithmetic discrepancy times the decaying profile really tends
to zero. The bound on the actual discrepancy is supplied by Mertens. -/
theorem tendsto_primeSquare_boundary_zero (c : ℝ → ℝ) (R A : ℝ)
    (hA : 0 ≤ A)
    (hdecay : ∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2) :
    Tendsto (fun N : ℕ => c (2 * Real.log N / R) * primeSquareDiscrepancy N)
      atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_primeSquareDiscrepancy_bound
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (A * B) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, inv_pow,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero.comp hnat).pow 2).const_mul (A * B)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (A / (N : ℝ) ^ 2) * B := mul_le_mul (hdecay N hN1)
      (hB N hN1) (abs_nonneg _) (div_nonneg hA (sq_nonneg _))
    _ = _ := by ring

/-- Exact noncompact Abel identity, including the entire signed discrepancy.
The prime series, improper integrals, and vanished boundary are all justified
by the preceding estimates; compact support is not a hypothesis. -/
theorem primeSquareSector_exact_noncompact_remainder
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (R A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hdecay : ∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2)
    (hderiv : ∀ x : ℝ, 1 ≤ x →
      |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) :
    primeSquareSector c R =
      -2 * (∫ x in Ioi 1, c (2 * Real.log x / R) / x) +
      2 * ∫ x in Ioi 1, deriv (fun y => c (2 * Real.log y / R)) x *
        primeSquareDiscrepancy x := by
  obtain ⟨hi, hd, he⟩ := integrable_noncompact_primeSquare_terms
    c hc R A D hA hD hdecay hderiv
  have hleft := tendsto_primeSquareCutoff_of_summable c R
    (summable_primeSquare_of_profile_decay c R A hA hdecay)
  have hboundary := (tendsto_primeSquare_boundary_zero c R A hA hdecay).const_mul (-2 : ℝ)
  have hmain := (tendsto_setIntegral_Ioc_nat hi).const_mul (2 : ℝ)
  have herror := (tendsto_setIntegral_Ioc_nat he).const_mul (2 : ℝ)
  have hright := (hboundary.sub hmain).add herror
  have heq :
      (fun N : ℕ => -2 * (c (2 * Real.log N / R) * primeSquareDiscrepancy N) -
        2 * (∫ x in Ioc 1 (N : ℝ), c (2 * Real.log x / R) / x) +
        2 * ∫ x in Ioc 1 (N : ℝ), deriv (fun y => c (2 * Real.log y / R)) x *
          primeSquareDiscrepancy x) =ᶠ[atTop]
      (fun N : ℕ => primeSquareCutoff c R N) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h := primeSquareCutoff_exact_remainder c R hN1
      (fun x hx => (hasDerivAt_primeSquareProfile c hc R
        (by linarith [hx.1])).differentiableAt)
      (continuousOn_deriv_primeSquareProfile c hc hc' R N)
    simpa only [mul_assoc] using h.symm
  have hright' := hright.congr' heq
  simpa only [mul_zero, zero_sub, neg_mul] using tendsto_nhds_unique hleft hright'

/-- A uniform Mertens constant bounds the retained full half-line discrepancy,
with no hypothesis about the sign of the prime sector or the Weil form. -/
theorem exists_noncompact_primeSquare_remainder_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ → ℝ), Differentiable ℝ c →
      Continuous (deriv c) → ∀ R A D : ℝ, 0 ≤ A → 0 ≤ D →
      (∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2) →
      (∀ x : ℝ, 1 ≤ x →
        |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) →
      |primeSquareSector c R +
        2 * (∫ x in Ioi 1, c (2 * Real.log x / R) / x)| ≤
        2 * B * ∫ x in Ioi 1, |deriv (fun y => c (2 * Real.log y / R)) x| := by
  obtain ⟨B, hB0, hB⟩ := exists_primeSquareDiscrepancy_bound
  refine ⟨B, hB0, ?_⟩
  intro c hc hc' R A D hA hD hdecay hderiv
  obtain ⟨hi, hd, he⟩ := integrable_noncompact_primeSquare_terms
    c hc R A D hA hD hdecay hderiv
  rw [primeSquareSector_exact_noncompact_remainder c hc hc' R A D hA hD hdecay hderiv]
  have hcancel (M E : ℝ) : (-2 * M + 2 * E) + 2 * M = 2 * E := by ring
  rw [hcancel, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbound :
      |∫ x in Ioi 1, deriv (fun y => c (2 * Real.log y / R)) x * primeSquareDiscrepancy x| ≤
      B * ∫ x in Ioi 1, |deriv (fun y => c (2 * Real.log y / R)) x| := by
    calc
      _ ≤ ∫ x in Ioi 1,
          |deriv (fun y => c (2 * Real.log y / R)) x * primeSquareDiscrepancy x| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => deriv (fun y => c (2 * Real.log y / R)) x * primeSquareDiscrepancy x)
      _ ≤ ∫ x in Ioi 1, B * |deriv (fun y => c (2 * Real.log y / R)) x| := by
        apply integral_mono_ae he.abs (hd.abs.const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [abs_mul]
        calc
          _ ≤ |deriv (fun y => c (2 * Real.log y / R)) x| * B :=
            mul_le_mul_of_nonneg_left (hB x (le_of_lt hx)) (abs_nonneg _)
          _ = _ := mul_comm _ _
      _ = _ := integral_const_mul _ _
  nlinarith

end RiemannResearch.RH
