/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QPrimeDerivativePrimitive
import RiemannResearch.RH.CesaroResidueMean

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QPrimeDerivativePeriodMean
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative
open ArithmeticCumulative.CesaroResidue
open FinitePrimeLikelihood FinitePrimeDerivativeProjection
open FinitePrimeDerivativeExpansion QPrimeDerivativePrimitive

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPeriod (p : ι → ℕ) : ℕ := ∏ i, p i

theorem baseRatio_sum_conductors (p : ι → ℝ) (hp1 : ∀ i, p i+1 ≠ 0) :
    baseRatio p*(∑ A : Finset ι, subsetConductor p A) = ∏ i, p i := by
  have h := likelihood_monomial_expansion p hp1 (fun _ => true)
  simpa [finiteMonomial, boolIndicator, finiteLikelihood, tensorFunction,
    primeLikelihood] using h

theorem sum_subsetMobius [Nonempty ι] : (∑ A : Finset ι, subsetMobius A) = 0 := by
  have h := mobius_monomial_expansion (fun _ : ι => true)
  simpa [finiteMonomial, boolIndicator, zeroIndicator, zeroConfiguration,
    funext_iff] using h

theorem sum_primitiveCoefficient [Nonempty ι] (p : ι → ℝ) (q : ℝ)
    (hp1 : ∀ i, p i+1 ≠ 0) :
    (∑ A : Finset ι, primitiveCoefficient p q A) =
      q*(∏ i, p i)/(2:ℝ)^(Fintype.card ι) := by
  calc
    _ = (q/(2:ℝ)^(Fintype.card ι)) *
        (baseRatio p*(∑ A : Finset ι, subsetConductor p A)) -
        (q/zeroMass p)*(∑ A : Finset ι, subsetMobius A) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro A _
      unfold primitiveCoefficient
      ring
    _ = _ := by
      rw [baseRatio_sum_conductors p hp1, sum_subsetMobius]
      ring

theorem coefficient_period_mean [Nonempty ι] (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i+1 ≠ 0)
    (ha : zeroMass p ≠ 0) :
    (∑ A : Finset ι, primitiveCoefficient p q A *
      ((subsetConductor p A-1)/(2*subsetConductor p A))) =
      q*(∏ i, p i)/(2*(2:ℝ)^(Fintype.card ι)) := by
  calc
    _ = ((∑ A : Finset ι, primitiveCoefficient p q A) -
        (∑ A : Finset ι, primitiveCoefficient p q A*(1/subsetConductor p A)))/2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro A _
      have hd : subsetConductor p A ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)
      field_simp [hd]
      <;> ring
    _ = _ := by
      rw [sum_primitiveCoefficient p q hp1, coefficient_constant_sum p q hp0 hp1 ha]
      ring

theorem conductor_dvd_fullPeriod (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (A : Finset ι) : conductor p A ∣ fullPeriod p := by
  have h := primePower_product_dvd_iff p hp hinj (fun _ => 1) A (fullPeriod p)
  simp only [pow_one] at h
  apply h.mpr
  intro i _
  exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)

theorem cumulative_residue_dvd_period {d L : ℕ} (hd : 0 < d) (hdiv : d ∣ L) :
    cumulative (residueFraction d) L =
      (L:ℝ)*((d:ℝ)-1)/(2*(d:ℝ)) := by
  obtain ⟨k, hk⟩ := hdiv
  have hL : k*d=L := by simpa [Nat.mul_comm] using hk.symm
  rw [← hL, cumulative_residue_complete_periods d k hd]
  have hdR : (d:ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [hdR]
  <;> ring

theorem residueCombination_sequence (p : ι → ℕ) (c : Finset ι → ℝ) (n : ℕ) :
    qSequence (residueCombination p c) n =
      ∑ A : Finset ι, c A*residueFraction (conductor p A) n := by
  change (qSequenceLinear (∑ A : Finset ι, c A • qResidue (conductor p A))) n = _
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  exact congrFun (qSequence_qResidue (conductor p A)) n

theorem cumulative_residueCombination (p : ι → ℕ) (c : Finset ι → ℝ) (L : ℕ) :
    cumulative (qSequence (residueCombination p c)) L =
      ∑ A : Finset ι, c A*cumulative (residueFraction (conductor p A)) L := by
  unfold cumulative
  simp_rw [residueCombination_sequence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  exact (Finset.mul_sum _ _ _).symm

theorem cumulative_primitive_period [Nonempty ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    cumulative (qSequence (primitive p)) (fullPeriod p) =
      (1/zetaTwo)*(fullPeriod p:ℝ)^2/(2*(2:ℝ)^(Fintype.card ι)) := by
  have hp0 (i : ι) : (p i:ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i:ℝ)+1 ≠ 0 := by positivity
  have ha := ne_of_gt (prime_zeroMass_pos p hp)
  rw [primitive, cumulative_residueCombination]
  simp_rw [cumulative_residue_dvd_period (conductor_pos p hp _)
    (conductor_dvd_fullPeriod p hp hinj _)]
  calc
    _ = (fullPeriod p:ℝ) *
        (∑ A : Finset ι, primitiveCoefficient (fun i => (p i:ℝ)) (1/zetaTwo) A *
          ((subsetConductor (fun i => (p i:ℝ)) A-1)/
            (2*subsetConductor (fun i => (p i:ℝ)) A))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      simp only [subsetConductor, conductor, Nat.cast_prod]
      ring
    _ = _ := by
      rw [coefficient_period_mean (fun i => (p i:ℝ)) (1/zetaTwo) hp0 hp1 ha]
      simp only [fullPeriod, Nat.cast_prod]
      ring

end RiemannResearch.RH.QPrimeDerivativePeriodMean
