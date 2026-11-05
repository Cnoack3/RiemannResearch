/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeOddLift
import RiemannResearch.RH.PrimeTreeCanonicalBounds
import RiemannResearch.RH.PrimeTreeGridLaw
import RiemannResearch.RH.ParetoResidueUniformCovariance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The Haar mean of the physical carry signal
Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, §3.2,
immediately after (9). Each prime coordinate has its normalized counting law.
The same readout agrees with the physical integer carries on the diagonal.
-/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.CanonicalPrimeCarry
open PrimeTreeHaarRows CRTCarryArithmetic

local instance primeAt_neZero (k : ℕ) : NeZero (primeAt k) := ⟨(primeAt_prime k).ne_zero⟩

abbrev PrimeGrid := (k : ℕ) → Fin (primeAt k)

def primeGridHaar : Measure PrimeGrid := Measure.infinitePi (fun k => gridLaw (primeAt k))

instance primeGridHaar_probability : IsProbabilityMeasure primeGridHaar := by unfold primeGridHaar; infer_instance

def rawDigit (k : ℕ) (ω : PrimeGrid) : ℝ := (ω k).val

private theorem rawDigit_measurable (k : ℕ) : Measurable (rawDigit k) :=
  (measurable_of_countable (fun i : Fin (primeAt k) => (i.val : ℝ))).comp (measurable_pi_apply k)

theorem rawDigit_norm (k : ℕ) (ω : PrimeGrid) : ‖rawDigit k ω‖ ≤ (primeAt k : ℝ) := by
  rw [rawDigit, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (ω k).isLt.le

private theorem rawDigit_integrable (k : ℕ) : Integrable (rawDigit k) primeGridHaar :=
  (integrable_const (primeAt k : ℝ)).mono' (rawDigit_measurable k).aestronglyMeasurable
    (ae_of_all _ (rawDigit_norm k))

theorem rawDigit_integral (k : ℕ) :
    (∫ ω, rawDigit k ω ∂primeGridHaar) = ((primeAt k : ℝ)-1)/2 := by
  let p := primeAt k
  let f := fun i : Fin p => (i.val : ℝ)
  have hm := integral_map (μ := primeGridHaar) (φ := Function.eval k) (f := f)
    (measurable_pi_apply k).aemeasurable (measurable_of_countable f).aestronglyMeasurable
  unfold primeGridHaar at hm
  rw [Measure.infinitePi_map_eval] at hm
  change (∫ ω : PrimeGrid, f (Function.eval k ω) ∂Measure.infinitePi (fun i => gridLaw (primeAt i))) = _
  rw [← hm, integral_fintype .of_finite]
  have hw (x : Fin p) : (gridLaw p).real {x} = (p : ℝ)⁻¹ := by
    simp [gridLaw, measureReal_def]
  change (∑ x : Fin p, (gridLaw p).real {x} • f x) = _
  simp only [hw, smul_eq_mul, ← Finset.mul_sum, f, Pareto.fin_real_sum]
  change (p : ℝ)⁻¹ * ((p : ℝ) * ((p : ℝ)-1)/2) = ((p : ℝ)-1)/2
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (primeAt_prime k).ne_zero
  field_simp [hp] <;> ring

/-- Formula (9) as a function on the product of the prime residue groups. -/
def haarCarryReadout (j : ℕ) (ω : PrimeGrid) : ℝ :=
  (rawDigit 0 ω - ∑' k, (oddChain j).edgeMass k * rawDigit (k+1) ω)/2

/-- This is the same signal as the weighted floors at every physical integer. -/
theorem haarCarryReadout_diagonal (j n : ℕ) :
    haarCarryReadout j (fun k => ⟨n % primeAt k, Nat.mod_lt _ (primeAt_prime k).pos⟩) =
      ∑' k, (oddChain j).carryTerm n k := by
  rw [(oddChain j).carrySum_eq_residue_average]
  change (((n % primeAt 0 : ℕ) : ℝ) - ∑' k, (oddChain j).edgeMass k *
      ((n % radix k : ℕ) : ℝ))/2 =
    (oddChain j).parentTerm n 0 - (1/2 : ℝ) * ∑' k, (oddChain j).edgeMass k * ((n % radix k : ℕ) : ℝ)
  have hp : (oddChain j).parentTerm n 0 = ((n % primeAt 0 : ℕ) : ℝ)/2 := by
    simp [NormalizedCarryChain.parentTerm, oddChain, oddWeight, firstChain, primorialAt, primeAt,
      ArithmeticCumulative.residueFraction]
  rw [hp]
  ring

/-- The actual prime law has a finite first moment at each positive odd lift. -/
theorem oddChain_firstMoment (j : ℕ) :
    Summable (fun k => (oddChain j).edgeMass k * (radix k : ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  have h (k : ℕ) : (oddChain j).edgeMass (k+1) * (radix (k+1) : ℝ) =
      (2/liftU j) * absPrimeCoefficient (k+1) := by
    rw [oddChain_edgeMass_succ]
    calc
      _ = (firstChain.edgeMass (k+1) * (radix (k+1) : ℝ))/liftU j := by ring
      _ = _ := by rw [edgeMass_mul_radix]; ring
  simpa only [h] using canonical_firstMoment.1.mul_left (2/liftU j)

/-- The Haar mean after (9), with the moment taken under the actual odd-lift law. -/
theorem oddChain_haarCarryReadout_mean (j : ℕ) :
    (∫ ω, haarCarryReadout j ω ∂primeGridHaar) =
      (2 - ∑' k, (oddChain j).edgeMass k * (radix k : ℝ))/4 := by
  let m := (oddChain j).edgeMass
  let Z (k : ℕ) (ω : PrimeGrid) := m k * rawDigit (k+1) ω
  have hm : HasSum m 1 := (oddChain_probability j).1
  have hm0 (k : ℕ) : 0 ≤ m k := ((oddChain_probability j).2 k).le
  have hmoment : Summable (fun k => m k * (radix k : ℝ)) := oddChain_firstMoment j
  have hbound (k : ℕ) (ω : PrimeGrid) : ‖Z k ω‖ ≤ m k * (radix k : ℝ) := by
    change ‖m k * rawDigit (k+1) ω‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hm0 k)]
    exact mul_le_mul_of_nonneg_left (rawDigit_norm (k+1) ω) (hm0 k)
  have hsite (ω : PrimeGrid) : Summable (fun k => Z k ω) :=
    Summable.of_norm_bounded hmoment (fun k => hbound k ω)
  have hmeas (k : ℕ) : Measurable (Z k) := measurable_const.mul (rawDigit_measurable (k+1))
  have hM : Measurable (fun ω => ∑' k, Z k ω) := by
    apply measurable_of_tendsto_metrizable (f := fun N ω => ∑ k ∈ Finset.range N, Z k ω)
    · exact fun N => Finset.measurable_sum _ (fun k _ => hmeas k)
    · exact tendsto_pi_nhds.mpr fun ω => (hsite ω).hasSum.tendsto_sum_nat
  have htotal : Integrable (fun ω => ∑' k, Z k ω) primeGridHaar :=
    (integrable_const (∑' k, m k * (radix k : ℝ))).mono' hM.aestronglyMeasurable
      (ae_of_all _ (fun ω => tsum_of_norm_bounded hmoment.hasSum (fun k => hbound k ω)))
  have hi (k : ℕ) : Integrable (Z k) primeGridHaar := (rawDigit_integrable (k+1)).const_mul _
  have he (k : ℕ) : (∫ ω, Z k ω ∂primeGridHaar) = m k * (((radix k : ℝ)-1)/2) := by
    simp only [Z, integral_const_mul, rawDigit_integral, radix]
  have hs : HasSum (fun k => m k * (((radix k : ℝ)-1)/2))
      (((∑' k, m k * (radix k : ℝ)) - 1)/2) :=
    ((hmoment.hasSum.sub hm).div_const 2).congr_fun (fun k => by ring)
  have hsn : Summable (fun k => ∫ ω, ‖Z k ω‖ ∂primeGridHaar) := by
    have hn (k : ℕ) (ω : PrimeGrid) : ‖Z k ω‖ = Z k ω :=
      Real.norm_of_nonneg (mul_nonneg (hm0 k) (Nat.cast_nonneg _))
    simpa only [hn, he] using hs.summable
  have h := hasSum_integral_of_summable_integral_norm hi hsn
  simp only [he] at h
  change (∫ ω, (rawDigit 0 ω - ∑' k, Z k ω)/2 ∂primeGridHaar) = _
  rw [integral_div, integral_sub (rawDigit_integrable 0) htotal, rawDigit_integral, h.unique hs,
    show primeAt 0 = 2 from Nat.nth_prime_zero_eq_two]
  change (((2 : ℝ)-1)/2 - ((∑' k, m k * (radix k : ℝ))-1)/2)/2 = _
  ring

end RiemannResearch.RH.CanonicalPrimeCarry
