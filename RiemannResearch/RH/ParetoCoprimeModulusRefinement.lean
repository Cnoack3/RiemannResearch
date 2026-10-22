/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoInfiniteRoughTailCertificates

/-!
# Exact energy cost of enlarging a coprime certificate modulus

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21). The argument uses inclusion of the actual odd-coprime
families and the existing infinite Hilbert sums.
Enlarging a modulus with the dictionary fixed adds exactly an invisible
orthogonal increment. Arbitrary convergent signed mixtures of enlarged
moduli cannot reduce the energy below the original certificate.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.OrthogonalAffineSeries
open RiemannResearch.RH.ArithmeticCumulative

/-- A coprime index for a multiple is already an index for the divisor. -/
def coprimeCertificateIndexOfDvd {P Q : ℕ} (hPQ : P ∣ Q)
    (k : CoprimeCertificateIndex Q) : CoprimeCertificateIndex P :=
  ⟨k.val, k.property.1, k.property.2.1, k.property.2.2.of_dvd_right hPQ⟩

/-- The smaller-modulus certificate has a constant pairing with every member
of the refined family. -/
theorem infiniteCoprimeCertificate_inner_refined_member
    {P Q : ℕ} (hPQ : P ∣ Q) (k : CoprimeCertificateIndex Q) :
    inner ℝ (infiniteCoprimeCertificate P) (coprimeCertificateFamily Q k) =
      (reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹ := by
  exact affineMinimum_inner (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
    (coprimeCertificateIndexOfDvd hPQ k)

/-- Exact cross energy of certificates from nested moduli. -/
theorem infiniteCoprimeCertificate_inner_of_dvd {P Q : ℕ}
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hQ : Q ≠ 0) (hPQ : P ∣ Q) :
    inner ℝ (infiniteCoprimeCertificate P) (infiniteCoprimeCertificate Q) =
      ‖infiniteCoprimeCertificate P‖ ^ 2 := by
  have hQ2 : 2 ∣ Q := dvd_trans h2 hPQ
  have h := (innerSL ℝ (infiniteCoprimeCertificate P)).hasSum
    (infiniteCoprimeCertificate_hasSum Q)
  change HasSum (fun k : CoprimeCertificateIndex Q =>
    inner ℝ (infiniteCoprimeCertificate P)
      (((reciprocalEnergyMass (coprimeCertificateFamily Q))⁻¹ *
        (‖coprimeCertificateFamily Q k‖ ^ 2)⁻¹) • coprimeCertificateFamily Q k))
    (inner ℝ (infiniteCoprimeCertificate P) (infiniteCoprimeCertificate Q)) at h
  simp only [inner_smul_right, infiniteCoprimeCertificate_inner_refined_member hPQ] at h
  have hc := (infiniteCoprimeCertificate_coefficients_hasSum Q hQ hQ2).mul_right
    (reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹
  simp only [one_mul] at hc
  have hn := affineMinimum_norm_sq (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
    (ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2))
  change ‖infiniteCoprimeCertificate P‖ ^ 2 = _ at hn
  exact (h.unique hc).trans hn.symm

/-- All extra energy from modulus enlargement is a squared orthogonal increment. -/
theorem infiniteCoprimeCertificate_refinement_energy {P Q : ℕ}
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hQ : Q ≠ 0) (hPQ : P ∣ Q) :
    ‖infiniteCoprimeCertificate Q‖ ^ 2 =
      ‖infiniteCoprimeCertificate P‖ ^ 2 +
        ‖infiniteCoprimeCertificate Q - infiniteCoprimeCertificate P‖ ^ 2 := by
  have h := infiniteCoprimeCertificate_inner_of_dvd hP h2 hQ hPQ
  have hs := norm_sub_sq_real (infiniteCoprimeCertificate P) (infiniteCoprimeCertificate Q)
  rw [h, norm_sub_rev] at hs
  linarith

theorem infiniteCoprimeCertificate_energy_mono {P Q : ℕ}
    (hP : P ≠ 0) (h2 : 2 ∣ P) (hQ : Q ≠ 0) (hPQ : P ∣ Q) :
    ‖infiniteCoprimeCertificate P‖ ^ 2 ≤ ‖infiniteCoprimeCertificate Q‖ ^ 2 := by
  rw [infiniteCoprimeCertificate_refinement_energy hP h2 hQ hPQ]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The enlargement increment does not change any observation already supplied
by the smaller modulus. -/
theorem infiniteCoprimeCertificate_refinement_observation_zero
    (n : ℕ) {P Q : ℕ} (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hQ : Q ≠ 0) (hPQ : P ∣ Q)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) (i : Fin n) :
    inner ℝ (tailAtom i.val)
      (infiniteCoprimeCertificate Q - infiniteCoprimeCertificate P) = 0 := by
  rw [inner_sub_right,
    infiniteCoprimeCertificate_observation n Q hQ (dvd_trans h2 hPQ)
      (fun j => dvd_trans (hmod j) hPQ),
    infiniteCoprimeCertificate_observation n P hP h2 hmod, sub_self]

/-- With the dictionary fixed, the entire refinement cost goes into the gap. -/
theorem infiniteCoprimeCertificate_refinement_gap
    (n : ℕ) {P Q : ℕ} (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hQ : Q ≠ 0) (hPQ : P ∣ Q)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) :
    ‖infiniteCoprimeCertificate Q - tailMinimum n‖ ^ 2 =
      ‖infiniteCoprimeCertificate P - tailMinimum n‖ ^ 2 +
        ‖infiniteCoprimeCertificate Q - infiniteCoprimeCertificate P‖ ^ 2 := by
  have hp := finiteTailCertificate_energy_completion n (infiniteCoprimeCertificate P)
    (infiniteCoprimeCertificate_observation n P hP h2 hmod)
  have hq := finiteTailCertificate_energy_completion n (infiniteCoprimeCertificate Q)
    (infiniteCoprimeCertificate_observation n Q hQ (dvd_trans h2 hPQ)
      (fun j => dvd_trans (hmod j) hPQ))
  have h := infiniteCoprimeCertificate_refinement_energy hP h2 hQ hPQ
  linarith

/-- Signed averaging over any family of enlarged moduli cannot improve the
base certificate. The series need only converge in the Hilbert norm. -/
theorem infiniteCoprimeCertificate_mixture_energy_completion {ι : Type*}
    {P : ℕ} (hP : P ≠ 0) (h2 : 2 ∣ P)
    (Q : ι → ℕ) (hQ : ∀ i, Q i ≠ 0) (hPQ : ∀ i, P ∣ Q i)
    (a : ι → ℝ) (z : ThresholdHilbert)
    (hz : HasSum (fun i => a i • infiniteCoprimeCertificate (Q i)) z)
    (ha : HasSum a 1) :
    ‖z‖ ^ 2 = ‖infiniteCoprimeCertificate P‖ ^ 2 +
      ‖z - infiniteCoprimeCertificate P‖ ^ 2 := by
  have h := (innerSL ℝ (infiniteCoprimeCertificate P)).hasSum hz
  change HasSum (fun i => inner ℝ (infiniteCoprimeCertificate P)
    (a i • infiniteCoprimeCertificate (Q i)))
    (inner ℝ (infiniteCoprimeCertificate P) z) at h
  simp only [inner_smul_right] at h
  have hp (i : ι) : inner ℝ (infiniteCoprimeCertificate P)
      (infiniteCoprimeCertificate (Q i)) = ‖infiniteCoprimeCertificate P‖ ^ 2 :=
    infiniteCoprimeCertificate_inner_of_dvd hP h2 (hQ i) (hPQ i)
  simp only [hp] at h
  have hc := ha.mul_right (‖infiniteCoprimeCertificate P‖ ^ 2)
  simp only [one_mul] at hc
  have hi := h.unique hc
  have hs := norm_sub_sq_real (infiniteCoprimeCertificate P) z
  rw [hi, norm_sub_rev] at hs
  linarith

theorem infiniteCoprimeCertificate_mixture_energy_eq_iff {ι : Type*}
    {P : ℕ} (hP : P ≠ 0) (h2 : 2 ∣ P)
    (Q : ι → ℕ) (hQ : ∀ i, Q i ≠ 0) (hPQ : ∀ i, P ∣ Q i)
    (a : ι → ℝ) (z : ThresholdHilbert)
    (hz : HasSum (fun i => a i • infiniteCoprimeCertificate (Q i)) z)
    (ha : HasSum a 1) :
    ‖z‖ ^ 2 = ‖infiniteCoprimeCertificate P‖ ^ 2 ↔
      z = infiniteCoprimeCertificate P := by
  rw [infiniteCoprimeCertificate_mixture_energy_completion hP h2 Q hQ hPQ a z hz ha]
  constructor
  · intro h
    have hn : ‖z - infiniteCoprimeCertificate P‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro h
    rw [h, sub_self, norm_zero]
    ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
