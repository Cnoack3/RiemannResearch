/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoInfiniteRoughTailCertificates
import RiemannResearch.RH.ParetoTailCertificateEscape

/-!
# Actual factorial coprime certificates escape into the tail

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21). This specializes the proved support-escape obstruction to
the actual infinite coprime averages, then computes their gap at a fixed
dictionary. The dictionary size and modulus-growth parameter are kept
separate; no conclusion about the growing-dictionary capacity is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.OrthogonalAffineSeries
open RiemannResearch.RH.ArithmeticCumulative

/-- All pair indices surviving the factorial sieve lie beyond its head. -/
theorem coprimeCertificate_factorial_index_lower (m : ℕ)
    (k : CoprimeCertificateIndex (m + 2).factorial) : m < k.val := by
  by_contra h
  have hd : k.val + 2 ∣ (m + 2).factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  have hdone : k.val + 2 ∣ 1 := by
    simpa only [show Nat.gcd (k.val + 2) (m + 2).factorial = 1
      from k.property.2.2] using Nat.dvd_gcd (dvd_refl (k.val + 2)) hd
  have he := Nat.dvd_one.mp hdone
  omega

/-- The actual infinite sum has a vanishing physical head, not merely
summands whose individual supports escape. -/
theorem infiniteCoprimeCertificate_factorial_coordinate_zero (m j : ℕ)
    (hj : j ≤ m) :
    hilbertGibbsPhysical (infiniteCoprimeCertificate (m + 2).factorial) j = 0 := by
  have hi (k : CoprimeCertificateIndex (m + 2).factorial) :
      inner ℝ (paretoPointHilbert j)
        (coprimeCertificateFamily (m + 2).factorial k) = 0 := by
    have hk := coprimeCertificate_factorial_index_lower m k
    rw [real_inner_comm]
    change inner ℝ (differenceCertificate k.val) (paretoPointHilbert j) = 0
    rw [differenceCertificate_inner]
    simp [hilbertGibbsPhysical_paretoPoint,
      show k.val + 1 ≠ j by omega, show k.val ≠ j by omega]
  have h := (innerSL ℝ (paretoPointHilbert j)).hasSum
    (infiniteCoprimeCertificate_hasSum (m + 2).factorial)
  change HasSum (fun k : CoprimeCertificateIndex (m + 2).factorial =>
    inner ℝ (paretoPointHilbert j)
      (((reciprocalEnergyMass (coprimeCertificateFamily (m + 2).factorial))⁻¹ *
        (‖coprimeCertificateFamily (m + 2).factorial k‖ ^ 2)⁻¹) •
          coprimeCertificateFamily (m + 2).factorial k))
    (inner ℝ (paretoPointHilbert j)
      (infiniteCoprimeCertificate (m + 2).factorial)) at h
  simp only [inner_smul_right, hi, mul_zero] at h
  have hz := h.unique hasSum_zero
  rw [real_inner_comm, inner_paretoPoint] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (paretoWeight_pos j))

/-- The g₂ pairing used by the support-escape lower bound is actual and exact. -/
theorem infiniteCoprimeCertificate_residue_two_observation (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    inner ℝ (normalizedResidueHilbert 2 (by omega)) (infiniteCoprimeCertificate P) =
      1 / 2 := by
  have hpoint : inner ℝ (paretoPointHilbert 0) (infiniteCoprimeCertificate P) = 0 := by
    rw [real_inner_comm]
    exact infiniteCoprimeCertificate_inner_firstPoint P
  have hmod : ∀ i : Fin 1, i.val + 2 ∣ P := by
    intro i
    have hi : i.val = 0 := by omega
    simpa [hi] using h2
  have h := infiniteCoprimeCertificate_observation 1 P hP h2 hmod (0 : Fin 1)
  change inner ℝ (residueAtom 0 -
    (anchoredEvaluationCLM 1 (residueAtom 0)) • paretoPointHilbert 0)
      (infiniteCoprimeCertificate P) = _ at h
  rw [inner_sub_left, real_inner_smul_left, hpoint, mul_zero, sub_zero] at h
  exact h

/-- Linear lower bound on the norm squared of the explicit factorial certificate. -/
theorem infiniteCoprimeCertificate_factorial_energy_lower (m : ℕ) :
    (m : ℝ) + 2 ≤ ‖infiniteCoprimeCertificate (m + 2).factorial‖ ^ 2 := by
  have h2 : 2 ∣ (m + 2).factorial := Nat.dvd_factorial (by omega) (by omega)
  have h := normalized_certificate_head_vanishing_energy_lower (m + 1)
    (infiniteCoprimeCertificate (m + 2).factorial) ?_
    (infiniteCoprimeCertificate_residue_two_observation _ (Nat.factorial_ne_zero _) h2)
  · simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  · intro k hk hkM
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simpa only [hilbertGibbsPhysical_eq, Nat.succ_eq_add_one] using
      infiniteCoprimeCertificate_factorial_coordinate_zero m j (by omega)

theorem infiniteCoprimeCertificate_factorial_energy_tendsto :
    Tendsto (fun m : ℕ => ‖infiniteCoprimeCertificate (m + 2).factorial‖ ^ 2)
      atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
  have h := infiniteCoprimeCertificate_factorial_energy_lower m
  linarith

/-- A fixed dictionary is feasible at every stage of this explicitly growing
modulus family. -/
theorem infiniteCoprimeCertificate_factorial_observation (n m : ℕ) (i : Fin n) :
    inner ℝ (tailAtom i.val)
      (infiniteCoprimeCertificate (m + n + 2).factorial) = reciprocalSource n i := by
  apply infiniteCoprimeCertificate_observation
    n (m + n + 2).factorial (Nat.factorial_ne_zero _)
  · exact Nat.dvd_factorial (by omega) (by omega)
  · intro j
    exact Nat.dvd_factorial (by omega) (by omega)

/-- The exact certificate-capacity gap, with dictionary size n held fixed. -/
theorem infiniteCoprimeCertificate_factorial_fixed_gap (n m : ℕ) :
    ‖infiniteCoprimeCertificate (m + n + 2).factorial - tailMinimum n‖ ^ 2 =
      ‖infiniteCoprimeCertificate (m + n + 2).factorial‖ ^ 2 - tailCapacity n := by
  have h := finiteTailCertificate_energy_completion n
    (infiniteCoprimeCertificate (m + n + 2).factorial)
    (infiniteCoprimeCertificate_factorial_observation n m)
  linarith

/-- The entire gap can diverge while the capacity is held fixed. -/
theorem infiniteCoprimeCertificate_factorial_fixed_gap_tendsto (n : ℕ) :
    Tendsto (fun m : ℕ =>
      ‖infiniteCoprimeCertificate (m + n + 2).factorial - tailMinimum n‖ ^ 2)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hev : ∀ᶠ m : ℕ in atTop, b + tailCapacity n ≤ (m : ℝ) :=
    (tendsto_atTop.1 (tendsto_natCast_atTop_atTop :
      Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)) (b + tailCapacity n)
  filter_upwards [hev] with m hm
  rw [infiniteCoprimeCertificate_factorial_fixed_gap]
  have he := infiniteCoprimeCertificate_factorial_energy_lower (m + n)
  push_cast at he
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- At a fixed dictionary, asymptotically all energy of the growing factorial
certificate is the exact excess over the capacity. -/
theorem infiniteCoprimeCertificate_factorial_fixed_gap_ratio_tendsto (n : ℕ) :
    Tendsto (fun m : ℕ =>
      ‖infiniteCoprimeCertificate (m + n + 2).factorial - tailMinimum n‖ ^ 2 /
        ‖infiniteCoprimeCertificate (m + n + 2).factorial‖ ^ 2)
      atTop (𝓝 1) := by
  have hE : Tendsto (fun m : ℕ =>
      ‖infiniteCoprimeCertificate (m + n + 2).factorial‖ ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
    have he := infiniteCoprimeCertificate_factorial_energy_lower (m + n)
    push_cast at he
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hlim : Tendsto (fun m : ℕ =>
      1 - tailCapacity n * (‖infiniteCoprimeCertificate (m + n + 2).factorial‖ ^ 2)⁻¹)
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := tailCapacity n)).mul
          (tendsto_inv_atTop_zero.comp hE))
  convert hlim using 1
  ext m
  have he := infiniteCoprimeCertificate_factorial_energy_lower (m + n)
  have hn := Nat.cast_nonneg (α := ℝ) (m + n)
  have he0 : ‖infiniteCoprimeCertificate (m + n + 2).factorial‖ ^ 2 ≠ 0 := by
    intro hz
    rw [hz] at he
    linarith
  rw [infiniteCoprimeCertificate_factorial_fixed_gap, sub_div, div_self he0, div_eq_mul_inv]


end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
