/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimePrimeObservation

/-!
# All-modulus observations of the infinite coprime certificate

Source: continuation of the user-provided Pareto capacity handoff (2026-09-21).
The proof reindexes the actual convergent divisibility mass by multiplication
by an arbitrary modulus. It extends the prime observation to every modulus,
including composites, with the full signed divisor term retained.
-/

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

theorem coprimePairMass_divisible_hasSum (P q : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hq : 2 ≤ q) :
    HasSum (fun j => if q ∣ j then coprimePairMass P j else 0)
      (if Nat.Coprime q P then coprimeReciprocalSquareMass P / (q : ℝ)^2 else 0) := by
  let f : ℕ → ℝ := fun j => if Nat.Coprime j P then 1 / (j : ℝ)^2 else 0
  have hf : HasSum f (coprimeReciprocalSquareMass P) := by
    rw [coprimeReciprocalSquareMass_eulerProduct P hP h2]
    exact coprime_reciprocalSquare_hasSum P hP
  have hinj : Function.Injective (fun n : ℕ => q * n) := by
    intro n m h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hout : ∀ j ∉ Set.range (fun n : ℕ => q * n),
      (if q ∣ j then coprimePairMass P j else 0) = 0 := by
    intro j hj
    have hd : ¬ q ∣ j := by
      rintro ⟨m, hm⟩
      exact hj ⟨m, hm.symm⟩
    simp [hd]
  apply (hinj.hasSum_iff hout).mp
  have he : ((fun j => if q ∣ j then coprimePairMass P j else 0) ∘
      (fun n : ℕ => q * n)) =
      (fun n => if Nat.Coprime q P then f n / (q : ℝ)^2 else 0) := by
    funext n
    have hne : q * n ≠ 1 := by
      intro h
      have : q ∣ 1 := ⟨n, h.symm⟩
      have := Nat.dvd_one.mp this
      omega
    have hd := coprime_reciprocalSquare_decomposition_of_even P (q*n) h2
    simp only [hne, if_false, zero_add] at hd
    simp only [Function.comp_apply, dvd_mul_right, if_true, ← hd,
      Nat.coprime_mul_iff_left]
    dsimp only [f]
    by_cases hc : Nat.Coprime q P
    · rw [if_pos hc]
      by_cases hn : Nat.Coprime n P
      · rw [if_pos hn, if_pos ⟨hc, hn⟩]
        push_cast
        field_simp
      · rw [if_neg hn, if_neg (fun h => hn h.2), zero_div]
    · rw [if_neg hc, if_neg (fun h => hc h.1)]

  rw [he]
  split_ifs with hc
  · exact hf.div_const _
  · exact hasSum_zero

theorem shiftedCoprimeMass_divisible_hasSum (P k : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    HasSum (fun j => if k+2 ∣ j+2 then coprimePairMass P (j+2) else 0)
      (if Nat.Coprime (k+2) P then
        coprimeReciprocalSquareMass P / ((k+2 : ℕ) : ℝ)^2 else 0) := by
  apply (hasSum_nat_add_iff (f := fun j => if k+2 ∣ j then coprimePairMass P j else 0) 2).mpr
  have hz : (∑ j ∈ Finset.range 2,
      if k+2 ∣ j then coprimePairMass P j else 0) = 0 := by
    norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
  rw [hz, add_zero]
  exact coprimePairMass_divisible_hasSum P (k+2) hP h2 (by omega)

/-- Full divisibility defect, including composite moduli. -/
def coprimeObservationDefect (P q : ℕ) : ℝ :=
  if Nat.Coprime q P then coprimePrimeDefect P q else 0

theorem infiniteCoprimeCertificate_all_observations (P k : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    inner ℝ (tailAtom k) (infiniteCoprimeCertificate P) =
      1 / ((k+2 : ℕ) : ℝ) - coprimeObservationDefect P (k+2) := by
  let S := coprimeReciprocalSquareMass P - 1
  let U := if Nat.Coprime (k+2) P then
    coprimeReciprocalSquareMass P / ((k+2 : ℕ) : ℝ)^2 else 0
  have hS : S ≠ 0 := by
    simpa only [S, coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos P hP h2)
  have hSdef : S = ∑' p, coprimePairMass P p := by
    simp only [S, coprimeReciprocalSquareMass, add_sub_cancel_left]
  have hs : HasSum (fun j => coprimePairMass P (j+2)) S := by
    apply (hasSum_nat_add_iff 2).mpr
    have hz : (∑ j ∈ Finset.range 2, coprimePairMass P j) = 0 := by
      norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
    rw [hz, add_zero, hSdef]
    exact (coprimePairMass_summable P).hasSum
  let f : ℕ → ℝ := fun j =>
    (coprimePairMass P (j+2) / ((k+2 : ℕ) : ℝ) -
      (if k+2 ∣ j+2 then coprimePairMass P (j+2) else 0)) / S
  have hf : HasSum f ((S / ((k+2 : ℕ) : ℝ) - U) / S) :=
    ((hs.div_const _).sub (shiftedCoprimeMass_divisible_hasSum P k hP h2)).div_const S
  have hout : ∀ j ∉ Set.range (Subtype.val : CoprimeCertificateIndex P → ℕ),
      f j = 0 := by
    intro j hj
    have hj' : ¬ coprimePairIndex P (j+2) := by
      intro h
      exact hj ⟨⟨j,h⟩,rfl⟩
    simp [f, coprimePairMass, hj']
  have hsub := (Subtype.val_injective.hasSum_iff hout).mpr hf
  have hterm (j : CoprimeCertificateIndex P) :
      f j.val =
        ((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
            (coprimeCertificateFamily P))⁻¹ *
          (‖coprimeCertificateFamily P j‖ ^ 2)⁻¹) *
        inner ℝ (tailAtom k) (coprimeCertificateFamily P j) := by
    rw [coprimeCertificateFamily_inner_tail,
      coprimeCertificate_reciprocalEnergyMass, ← hSdef]
    change f j.val = ((S/2)⁻¹ * (‖differenceCertificate j.val‖^2)⁻¹) *
      (1 / ((k+2 : ℕ) : ℝ) - divisorIndicator (k+2) (j.val+2))
    rw [differenceCertificate_norm_sq]
    have hj : (j.val : ℝ)+2 ≠ 0 := by positivity
    have hk : (k : ℝ)+2 ≠ 0 := by positivity
    dsimp [f]
    simp only [coprimePairMass, if_pos j.property, divisorIndicator]
    split_ifs <;> push_cast <;> field_simp [hS, hj, hk] <;> ring
  have hi := (innerSL ℝ (tailAtom k)).hasSum (infiniteCoprimeCertificate_hasSum P)
  change HasSum (fun j : CoprimeCertificateIndex P =>
    inner ℝ (tailAtom k)
      (((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
          (coprimeCertificateFamily P))⁻¹ *
        (‖coprimeCertificateFamily P j‖^2)⁻¹) • coprimeCertificateFamily P j))
    (inner ℝ (tailAtom k) (infiniteCoprimeCertificate P)) at hi
  simp only [inner_smul_right] at hi
  have he : (f ∘ (Subtype.val : CoprimeCertificateIndex P → ℕ)) =
      (fun j : CoprimeCertificateIndex P =>
        ((RiemannResearch.Analysis.OrthogonalAffineSeries.reciprocalEnergyMass
            (coprimeCertificateFamily P))⁻¹ *
          (‖coprimeCertificateFamily P j‖^2)⁻¹) *
        inner ℝ (tailAtom k) (coprimeCertificateFamily P j)) := by
    funext j
    exact hterm j
  rw [he] at hsub
  rw [hi.unique hsub]
  dsimp [U, S]
  unfold coprimeObservationDefect coprimePrimeDefect
  split_ifs <;> field_simp [show coprimeReciprocalSquareMass P - 1 ≠ 0 from hS] <;> ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
