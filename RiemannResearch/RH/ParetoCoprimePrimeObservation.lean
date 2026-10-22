/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoInfiniteRoughTailCertificates

/-!
# Exact prime observations of the infinite coprime certificate

Source: continuation of the user-provided Pareto capacity formalization
(2026-09-21). The actual infinite Hilbert sum is paired with each prime
residue atom. Removing the prime's multiples evaluates its full signed
divisibility contribution. At a fresh prime q the defect is
M_P / (q^2 * (M_P - 1)), with every Euler factor retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

theorem coprimePairMass_prime_refinement (P q j : ℕ) (hq : Nat.Prime q) :
    coprimePairMass (P * q) j =
      if q ∣ j then 0 else coprimePairMass P j := by
  have hc : Nat.Coprime j q ↔ ¬ q ∣ j := by
    rw [Nat.coprime_comm]
    exact hq.coprime_iff_not_dvd
  by_cases hd : q ∣ j <;>
    simp [coprimePairMass, coprimePairIndex, Nat.coprime_mul_iff_right, hc, hd]

theorem coprimeReciprocalSquareMass_mul_fresh_prime (P q : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hq : Nat.Prime q) (hqP : ¬ q ∣ P) :
    coprimeReciprocalSquareMass (P * q) =
      coprimeReciprocalSquareMass P * (1 - 1 / (q : ℝ) ^ 2) := by
  have hnot : q ∉ P.primeFactors := by
    intro h
    exact hqP (Nat.mem_primeFactors.mp h).2.1
  have hf : (P * q).primeFactors = insert q P.primeFactors := by
    rw [Nat.primeFactors_mul hP hq.ne_zero, hq.primeFactors]
    exact Finset.union_singleton q P.primeFactors
  rw [coprimeReciprocalSquareMass_eulerProduct (P * q) (mul_ne_zero hP hq.ne_zero)
      (dvd_mul_of_dvd_left h2 q),
    coprimeReciprocalSquareMass_eulerProduct P hP h2, hf, Finset.prod_insert hnot]
  ring

private theorem shiftedCoprimeMass_hasSum (P : ℕ) :
    HasSum (fun k => coprimePairMass P (k + 2))
      (coprimeReciprocalSquareMass P - 1) := by
  apply (hasSum_nat_add_iff 2).mpr
  have hz : (∑ k ∈ Finset.range 2, coprimePairMass P k) = 0 := by
    norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
  rw [hz, add_zero]
  simpa only [coprimeReciprocalSquareMass, add_sub_cancel_left] using
    (coprimePairMass_summable P).hasSum

theorem coprimeCertificateFamily_inner_tail (P k : ℕ)
    (j : CoprimeCertificateIndex P) :
    inner ℝ (tailAtom k) (coprimeCertificateFamily P j) =
      1 / ((k + 2 : ℕ) : ℝ) - divisorIndicator (k + 2) (j.val + 2) := by
  rw [real_inner_comm]
  change inner ℝ (differenceCertificate j.val)
    (residueAtom k -
      (anchoredEvaluationCLM 1 (residueAtom k)) • paretoPointHilbert 0) = _
  rw [inner_sub_right, inner_smul_right,
    differenceCertificate_inner_firstPoint j.val (by have h := j.property.1; omega),
    mul_zero, sub_zero]
  exact differenceCertificate_inner_residue j.val (k + 2) (by omega)

theorem infiniteCoprimeCertificate_prime_observation (P k : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hq : Nat.Prime (k + 2)) :
    inner ℝ (tailAtom k) (infiniteCoprimeCertificate P) =
      1 / ((k + 2 : ℕ) : ℝ) -
        (coprimeReciprocalSquareMass P -
          coprimeReciprocalSquareMass (P * (k + 2))) /
          (coprimeReciprocalSquareMass P - 1) := by
  let S := coprimeReciprocalSquareMass P - 1
  let T := coprimeReciprocalSquareMass (P * (k + 2)) - 1
  have hS : S ≠ 0 := by
    simpa only [S, coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos P hP h2)
  have hSdef : S = ∑' p, coprimePairMass P p := by
    simp only [S, coprimeReciprocalSquareMass, add_sub_cancel_left]
  let f : ℕ → ℝ := fun j =>
    (coprimePairMass P (j + 2) / ((k + 2 : ℕ) : ℝ) -
      (coprimePairMass P (j + 2) - coprimePairMass (P * (k + 2)) (j + 2))) / S
  have hf : HasSum f ((S / ((k + 2 : ℕ) : ℝ) - (S - T)) / S) :=
    (((shiftedCoprimeMass_hasSum P).div_const ((k + 2 : ℕ) : ℝ)).sub
      ((shiftedCoprimeMass_hasSum P).sub
        (shiftedCoprimeMass_hasSum (P * (k + 2))))).div_const S
  have hout : ∀ j ∉ Set.range (Subtype.val : CoprimeCertificateIndex P → ℕ),
      f j = 0 := by
    intro j hj
    have hj' : ¬ coprimePairIndex P (j + 2) := by
      intro h
      exact hj ⟨⟨j, h⟩, rfl⟩
    dsimp [f]
    rw [coprimePairMass_prime_refinement P (k + 2) (j + 2) hq]
    simp [coprimePairMass, hj']
  have hsub := (Subtype.val_injective.hasSum_iff hout).mpr hf
  have hterm (j : CoprimeCertificateIndex P) :
      f j.val =
        ((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
            (coprimeCertificateFamily P))⁻¹ *
          (‖coprimeCertificateFamily P j‖ ^ 2)⁻¹) *
        inner ℝ (tailAtom k) (coprimeCertificateFamily P j) := by
    rw [coprimeCertificateFamily_inner_tail,
      coprimeCertificate_reciprocalEnergyMass, ← hSdef]
    change f j.val = ((S / 2)⁻¹ * (‖differenceCertificate j.val‖ ^ 2)⁻¹) *
      (1 / ((k + 2 : ℕ) : ℝ) - divisorIndicator (k + 2) (j.val + 2))
    rw [differenceCertificate_norm_sq]
    have hj : ((j.val : ℝ) + 2) ≠ 0 := by positivity
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    dsimp [f]
    rw [coprimePairMass_prime_refinement P (k + 2) (j.val + 2) hq]
    simp only [coprimePairMass, if_pos j.property, divisorIndicator]
    split_ifs <;> push_cast <;> field_simp [hS, hj, hk] <;> ring
  have hi := (innerSL ℝ (tailAtom k)).hasSum (infiniteCoprimeCertificate_hasSum P)
  change HasSum (fun j : CoprimeCertificateIndex P =>
    inner ℝ (tailAtom k)
      (((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
          (coprimeCertificateFamily P))⁻¹ *
        (‖coprimeCertificateFamily P j‖ ^ 2)⁻¹) • coprimeCertificateFamily P j))
    (inner ℝ (tailAtom k) (infiniteCoprimeCertificate P)) at hi
  simp only [inner_smul_right] at hi
  have he : (f ∘ (Subtype.val : CoprimeCertificateIndex P → ℕ)) =
      (fun j : CoprimeCertificateIndex P =>
        ((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
            (coprimeCertificateFamily P))⁻¹ *
          (‖coprimeCertificateFamily P j‖ ^ 2)⁻¹) *
        inner ℝ (tailAtom k) (coprimeCertificateFamily P j)) := by
    funext j
    exact hterm j
  rw [he] at hsub
  rw [hi.unique hsub]
  have hk : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  change (S / _ - (S - T)) / S = 1 / _ - _ / S
  have hdiff : coprimeReciprocalSquareMass P -
      coprimeReciprocalSquareMass (P * (k + 2)) = S - T := by dsimp [S, T]; ring
  rw [hdiff]
  field_simp

/-- The explicit defect at a fresh prime q. -/
def coprimePrimeDefect (P q : ℕ) : ℝ :=
  coprimeReciprocalSquareMass P /
    ((q : ℝ) ^ 2 * (coprimeReciprocalSquareMass P - 1))

theorem coprimePrimeDefect_pos (P q : ℕ) (hP : P ≠ 0)
    (h2 : 2 ∣ P) (hq : 0 < q) : 0 < coprimePrimeDefect P q := by
  have hS : 0 < coprimeReciprocalSquareMass P - 1 := by
    simpa only [coprimeReciprocalSquareMass, add_sub_cancel_left] using
      coprimePairMass_tsum_pos P hP h2
  have hM : 0 < coprimeReciprocalSquareMass P := by linarith
  exact div_pos hM (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hq)) hS)

theorem infiniteCoprimeCertificate_fresh_prime_observation (P k : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hq : Nat.Prime (k + 2))
    (hqP : ¬ (k + 2) ∣ P) :
    inner ℝ (tailAtom k) (infiniteCoprimeCertificate P) =
      1 / ((k + 2 : ℕ) : ℝ) - coprimePrimeDefect P (k + 2) := by
  rw [infiniteCoprimeCertificate_prime_observation P k hP h2 hq,
    coprimeReciprocalSquareMass_mul_fresh_prime P (k + 2) hP h2 hq hqP]
  unfold coprimePrimeDefect
  simp only [div_mul_eq_div_div]
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
