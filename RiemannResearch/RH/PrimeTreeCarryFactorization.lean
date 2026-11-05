/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeEntireMultiplier
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! # Mellin factorization and the removable point for the actual floor series

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§5, equations (20) and (21). The value at one is treated separately from
multiplication by Mathlib's pointwise value of the meromorphic zeta function.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic PrimeTreeTwoCarry ArithmeticCumulative

private theorem law_coefficient (j k : ℕ) :
    (oddChain j).chainCoefficients (k+1) =
      -(((oddChain j).edgeMass k : ℂ) * (radix k : ℂ)) / 2 := by
  let t := oddChain j
  have hm : 1 % t.p k = 1 := Nat.mod_eq_of_lt (t.radix_ge k)
  have hp : (t.p k : ℝ) ≠ 0 := by exact_mod_cast (primeAt_prime (k+1)).ne_zero
  have hh := t.primeTerm_eq 1 k
  simp only [NormalizedCarryChain.primeTerm, residueFraction, hm, Nat.cast_one, one_mul] at hh
  have ht : t.w (k+1) * (t.b k : ℝ) = -(t.edgeMass k * (t.p k : ℝ))/2 := by
    have hh' := (div_eq_iff hp).mp (show t.w (k+1) * (t.b k : ℝ) / (t.p k : ℝ) = _ by
      simpa [div_eq_mul_inv] using hh)
    unfold NormalizedCarryChain.edgeMass
    simp only [div_eq_mul_inv] at *
    linear_combination hh'
  change ((t.w (k+1) * (t.b k : ℝ) : ℝ) : ℂ) = -((t.edgeMass k : ℂ) * (t.p k : ℂ)) / 2
  exact_mod_cast ht

private theorem full_positive (j k : ℕ) : 0 < (oddChain j).chainConductors k := by
  cases k with
  | zero => exact (oddChain j).start_pos
  | succ k => exact (primeAt_prime (k+1)).pos

private theorem full_summable (j : ℕ) :
    Summable (fun k => ‖(oddChain j).chainCoefficients k‖) :=
  (oddChain j).chainCoefficients_summable (fun k => (oddWeight_pos j k).le)
    (oddChain_inverse j) radix_le_prefix

private theorem oddMass_complex (j : ℕ) : HasSum (fun k => ((oddChain j).edgeMass k : ℂ)) 1 := by
  simpa using (Complex.hasSum_ofReal.mpr (oddChain_probability j).1)

theorem carry_readout_zeta (j : ℕ) (s : ℂ) (hs : 0 < s.re) (hone : s ≠ 1) :
    readout (oddChain j).chainSignal s = riemannZeta s / s * carryMultiplier j s := by
  let t := oddChain j
  let Z := riemannZeta s / s
  let b (k : ℕ) := t.chainCoefficients k * (Z * (1/(t.chainConductors k : ℂ) -
    (t.chainConductors k : ℂ)^(-s)))
  have h : HasSum b (readout (atomSeries t.chainConductors t.chainCoefficients) s) :=
    atomSeries_readout_hasSum _ (full_positive j) _ (full_summable j) s hs hone
  have hstep (k : ℕ) : b (k+1) = (Z/2) * (primeMomentTerm j k s - (t.edgeMass k : ℂ)) := by
    have hp : (radix k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (primeAt_prime _).ne_zero
    have hpow : (radix k : ℂ)^(1-s) = (radix k : ℂ) * (radix k : ℂ)^(-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hp, Complex.cpow_one]
    change t.chainCoefficients (k+1) * (Z * (1/(radix k : ℂ) - (radix k : ℂ)^(-s))) = _
    rw [law_coefficient, primeMomentTerm, hpow]
    change -((t.edgeMass k : ℂ) * (radix k : ℂ))/2 * _ =
      _ * ((t.edgeMass k : ℂ) * _ - _)
    field_simp [hp] <;> ring
  have ht := ((momentSeries_summable j s).hasSum.sub (oddMass_complex j)).mul_left (Z/2)
  have hs0 : b 0 = Z * (1/2 - (2 : ℂ)^(-s)) := by
    have hD : t.D 0 = 2 := by norm_num [t, oddChain, firstChain, primorialAt, primeAt]
    simp [b, NormalizedCarryChain.chainCoefficients, NormalizedCarryChain.chainConductors,
      hD, show t.w 0 = 1 by rfl]
  rw [(oddChain j).chainSignal_eq_atomSeries, ← h.tsum_eq, h.summable.tsum_eq_zero_add, hs0]
  simp_rw [hstep]
  rw [ht.tsum_eq]
  dsimp only [carryMultiplier, Z]
  ring

/-- Endpoint formula directly from the physical integral. -/
theorem carry_readout_one (j : ℕ) :
    readout (oddChain j).chainSignal 1 = deriv (carryMultiplier j) 1 := by
  let t := oddChain j
  let L (k : ℕ) := (t.edgeMass k : ℂ) * (Real.log (radix k) : ℂ)
  let b (k : ℕ) := t.chainCoefficients k * ((Real.log (t.chainConductors k) : ℂ) / (t.chainConductors k : ℂ))
  have h : HasSum b (readout (atomSeries t.chainConductors t.chainCoefficients) 1) := by
    have ha (k : ℕ) := atom_readout_one (t.chainConductors k) (full_positive j k)
    simpa only [b, ha] using
      atomSeries_readout_hasSum_atoms t.chainConductors t.chainCoefficients (full_summable j) 1 (by norm_num)
  have hstep (k : ℕ) : b (k+1) = (-1/2 : ℂ) * L k := by
    have hp : (radix k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (primeAt_prime _).ne_zero
    change t.chainCoefficients (k+1) * ((Real.log (radix k) : ℂ)/(radix k : ℂ)) = _
    rw [law_coefficient]
    dsimp [L, t]
    field_simp [hp] <;> ring
  have hs0 : b 0 = (Real.log 2 : ℂ)/2 := by
    have hD : t.D 0 = 2 := by norm_num [t, oddChain, firstChain, primorialAt, primeAt]
    simp [b, NormalizedCarryChain.chainCoefficients, NormalizedCarryChain.chainConductors,
      hD, show t.w 0 = 1 by rfl]
  rw [(oddChain j).chainSignal_eq_atomSeries, ← h.tsum_eq, h.summable.tsum_eq_zero_add, hs0,
    carryMultiplier_deriv_one]
  simp_rw [hstep]
  rw [tsum_mul_left]
  dsimp [L, t]
  ring

theorem carry_readout_one_re_neg (j : ℕ) : (readout (oddChain j).chainSignal 1).re < 0 := by
  let m (k : ℕ) := (oddChain j).edgeMass k
  have hsum : Summable (fun k => m k * Real.log (radix k)) := by
    apply Complex.summable_ofReal.mp
    simpa only [m, Complex.ofReal_mul, neg_neg] using (primeLogMoment_derivative j).summable.neg
  have hlog (k : ℕ) : Real.log 3 ≤ Real.log (radix k) := by
    have hmon : StrictMono primeAt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hh := hmon.monotone (show 1 ≤ k+1 by omega)
    have hb : primeAt 1 = 3 := Nat.nth_prime_one_eq_three
    rw [hb] at hh
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hh)
  have hm : Real.log 3 ≤ ∑' k, m k * Real.log (radix k) := by
    have ho := ((oddChain_probability j).1.mul_right (Real.log 3))
    have h := ho.summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hlog k) ((oddChain_probability j).2 k).le) hsum
    simpa only [ho.tsum_eq, one_mul] using h
  have hR : (∑' k, ((oddChain j).edgeMass k : ℂ) * (Real.log (radix k) : ℂ)) =
      ((∑' k, m k * Real.log (radix k) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    simp only [m, Complex.ofReal_mul]
  rw [carry_readout_one, carryMultiplier_deriv_one, hR]
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  have hcast : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [hcast, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith

end RiemannResearch.RH.CanonicalPrimeCarry
