/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimePrimeUpdates
import RiemannResearch.RH.ParetoGibbsTailBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Bertrand

/-!
# Exact finite-support certificates for the complete prime Schur pivot

Source: independently developed elementary residue-difference argument.
No mathematical priority is asserted. The prime-existence input is Mathlib's
formal Bertrand theorem Nat.exists_prime_lt_and_le_two_mul:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html

Two physical sites give the exact old-source observations and a signed
capacity estimate. Subtracting certificates at two distinct odd primes gives
a four-site dual orthogonal to every old row, including composites. Its exact
norm-square completion retains the full inverse-Gram screening. Bertrand then
proves an unconditional lower bound 1/(10*p^2) for the actual prime pivot.
The physical dictionary is never truncated; the dual vector has finite support.
The concrete consumer is ParetoPrimeRawChargeModels.lean.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

def primeTwoSiteCertificate (n : ℕ) : ThresholdHilbert :=
  (((n+3 : ℕ) : ℝ) * ((n+4 : ℕ) : ℝ)) • paretoPointHilbert (n+2) -
  (((n+2 : ℕ) : ℝ) * ((n+3 : ℕ) : ℝ)) • paretoPointHilbert (n+1)

theorem inner_primeTwoSiteCertificate (n : ℕ) (f : ThresholdHilbert) :
    inner ℝ f (primeTwoSiteCertificate n) =
      hilbertGibbsPhysical f (n+2) - hilbertGibbsPhysical f (n+1) := by
  rw [primeTwoSiteCertificate, inner_sub_right, inner_smul_right,
    inner_smul_right, inner_paretoPoint, inner_paretoPoint]
  simp only [paretoWeight, Nat.cast_add, Nat.cast_ofNat]
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  have h3 : (n : ℝ)+3 ≠ 0 := by positivity
  have h4 : (n : ℝ)+4 ≠ 0 := by positivity
  field_simp
  ring

theorem primeTwoSiteCertificate_norm_sq (n : ℕ) :
    ‖primeTwoSiteCertificate n‖^2 = 2 * ((n+3 : ℕ) : ℝ)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_primeTwoSiteCertificate]
  have hsub (f g : ThresholdHilbert) (k : ℕ) :
      hilbertGibbsPhysical (f-g) k =
        hilbertGibbsPhysical f k - hilbertGibbsPhysical g k := by
    simp [hilbertGibbsPhysical, sub_div]
  simp [primeTwoSiteCertificate, hsub, hilbertGibbsPhysical_smul,
    hilbertGibbsPhysical_paretoPoint]
  ring

theorem tailAtom_primeTwoSite_observation (n i : ℕ) :
    inner ℝ (tailAtom i) (primeTwoSiteCertificate n) =
      1 / ((i+2 : ℕ) : ℝ) - if i+2 ∣ n+3 then 1 else 0 := by
  have hp : inner ℝ (paretoPointHilbert 0) (primeTwoSiteCertificate n) = 0 := by
    rw [inner_primeTwoSiteCertificate]
    simp
  change inner ℝ (residueAtom i -
    (anchoredEvaluationCLM 1 (residueAtom i)) • paretoPointHilbert 0)
    (primeTwoSiteCertificate n) = _
  rw [inner_sub_left, real_inner_smul_left, hp, mul_zero, sub_zero,
    inner_primeTwoSiteCertificate]
  simp only [hilbertGibbsPhysical_eq, residueAtom, normalizedResidueHilbert_sequence]
  change ((residue (i+2) (n+3)) / ((i+2 : ℕ) : ℝ)) -
    ((residue (i+2) (n+2)) / ((i+2 : ℕ) : ℝ)) = _
  rw [← sub_div]
  have hr := residue_difference (i+2) (n+3) (by omega)
  rw [show n+3-1=n+2 by omega] at hr
  rw [hr]
  have hi : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  split_ifs <;> field_simp
  all_goals ring


theorem primeTwoSiteCertificate_old_observation (n : ℕ)
    (hp : Nat.Prime (n+3)) (i : Fin (n+1)) :
    inner ℝ (tailAtom i.val) (primeTwoSiteCertificate n) = reciprocalSource (n+1) i := by
  rw [tailAtom_primeTwoSite_observation]
  have hd : ¬ i.val+2 ∣ n+3 := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h2 <;> omega
  simp [hd, reciprocalSource]

theorem primeTwoSiteCertificate_capacity_completion (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    2 * ((n+3 : ℕ) : ℝ)^2 = tailCapacity (n+1) +
      ‖primeTwoSiteCertificate n - tailMinimum (n+1)‖^2 := by
  rw [← primeTwoSiteCertificate_norm_sq]
  exact finiteTailCertificate_energy_completion (n+1) (primeTwoSiteCertificate n)
    (primeTwoSiteCertificate_old_observation n hp)

theorem primeTwoSiteCertificate_innovation (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    inner ℝ (tailInnovation (n+1)) (primeTwoSiteCertificate n) =
      schurEta (n+1) - 1 := by
  have h := tailInnovation_inner_feasible_error (n+1) (primeTwoSiteCertificate n)
    (primeTwoSiteCertificate_old_observation n hp)
  rw [inner_sub_right, tailInnovation_inner_minimum, sub_zero,
    inner_sub_right, tailAtom_primeTwoSite_observation] at h
  simp only [show n+1+2 = n+3 by omega, dvd_rfl, if_true] at h
  rw [h]
  unfold schurEta
  ring

theorem primeTwoSiteCertificate_pivot_bound (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    (schurEta (n+1)-1)^2 ≤ schurSigma (n+1) *
      (2 * ((n+3 : ℕ) : ℝ)^2 - tailCapacity (n+1)) := by
  have hpair : inner ℝ (tailInnovation (n+1))
      (primeTwoSiteCertificate n-tailMinimum (n+1)) = schurEta (n+1)-1 := by
    rw [inner_sub_right, primeTwoSiteCertificate_innovation n hp,
      tailInnovation_inner_minimum, sub_zero]
  have hc := real_inner_mul_inner_self_le (tailInnovation (n+1))
    (primeTwoSiteCertificate n-tailMinimum (n+1))
  rw [hpair, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have he := primeTwoSiteCertificate_capacity_completion n hp
  change (schurEta (n+1)-1) * (schurEta (n+1)-1) ≤
    schurSigma (n+1) * ‖primeTwoSiteCertificate n-tailMinimum (n+1)‖^2 at hc
  have hnorm : ‖primeTwoSiteCertificate n-tailMinimum (n+1)‖^2 =
      2 * ((n+3 : ℕ) : ℝ)^2-tailCapacity (n+1) := by linarith
  simpa only [pow_two, hnorm] using hc

theorem prime_schur_inverse_le_capacity (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    1 / schurSigma (n+1) ≤
      4 * ((n+3 : ℕ) : ℝ)^2 + 2 * tailCapacity (n+2) -
        4 * tailCapacity (n+1) := by
  have hbound := primeTwoSiteCertificate_pivot_bound n hp
  have he := capacity_schur_step (n+1)
  rw [show n+1+1=n+2 by omega] at he
  have hs := schurSigma_pos (n+1)
  have hgain : schurSigma (n+1) * (tailCapacity (n+2)-tailCapacity (n+1)) =
      (schurEta (n+1))^2 := by
    rw [he]
    field_simp
    ring
  apply (div_le_iff₀ hs).2
  nlinarith [sq_nonneg (2*schurEta (n+1)-1)]


def primeFourSiteDual (n m : ℕ) : ThresholdHilbert :=
  primeTwoSiteCertificate m - primeTwoSiteCertificate n


theorem primeFourSiteDual_norm_sq (n m : ℕ) (hnm : n+2 ≤ m) :
    ‖primeFourSiteDual n m‖^2 =
      2 * ((n+3 : ℕ) : ℝ)^2 + 2 * ((m+3 : ℕ) : ℝ)^2 := by
  have hsub (f g : ThresholdHilbert) (k : ℕ) :
      hilbertGibbsPhysical (f-g) k =
        hilbertGibbsPhysical f k - hilbertGibbsPhysical g k := by
    simp [hilbertGibbsPhysical, sub_div]
  have hcross : inner ℝ (primeTwoSiteCertificate m) (primeTwoSiteCertificate n) = 0 := by
    rw [inner_primeTwoSiteCertificate]
    have h1 : n ≠ m := by omega
    have h2 : n+2 ≠ m+1 := by omega
    have h3 : n ≠ m+1 := by omega
    simp [primeTwoSiteCertificate, hsub, hilbertGibbsPhysical_smul,
      hilbertGibbsPhysical_paretoPoint, h1,h2,h3]
  rw [primeFourSiteDual, norm_sub_sq_real,
    primeTwoSiteCertificate_norm_sq, primeTwoSiteCertificate_norm_sq, hcross]
  ring


theorem primeFourSiteDual_old_observation (n m : ℕ)
    (hp : Nat.Prime (n+3)) (hr : Nat.Prime (m+3))
    (hnm : n+2 ≤ m) (i : Fin (n+1)) :
    inner ℝ (tailAtom i.val) (primeFourSiteDual n m) = 0 := by
  have hi : i.val < m+1 := by omega
  rw [primeFourSiteDual, inner_sub_right,
    primeTwoSiteCertificate_old_observation m hr (⟨i.val,hi⟩),
    primeTwoSiteCertificate_old_observation n hp i]
  simp only [reciprocalSource, sub_self]


theorem primeFourSiteDual_new_observation (n m : ℕ)
    (hr : Nat.Prime (m+3)) (hnm : n+2 ≤ m) :
    inner ℝ (tailAtom (n+1)) (primeFourSiteDual n m) = 1 := by
  rw [primeFourSiteDual, inner_sub_right,
    primeTwoSiteCertificate_old_observation m hr (⟨n+1, by omega⟩),
    tailAtom_primeTwoSite_observation]
  simp only [reciprocalSource, show n+1+2=n+3 by omega, dvd_rfl, if_true]
  ring


theorem primeFourSiteDual_innovation (n m : ℕ)
    (hp : Nat.Prime (n+3)) (hr : Nat.Prime (m+3))
    (hnm : n+2 ≤ m) :
    inner ℝ (tailInnovation (n+1)) (primeFourSiteDual n m) = 1 := by
  rw [tailInnovation, RiemannResearch.Analysis.FiniteGramCapacity.screened,
    inner_sub_left, RiemannResearch.Analysis.FiniteHilbertGram.inner_synthesis_left]
  simp only [primeFourSiteDual_old_observation n m hp hr hnm, mul_zero,
    Finset.sum_const_zero, sub_zero]
  exact primeFourSiteDual_new_observation n m hr hnm


def primeFourSiteDualResidual (n m : ℕ) : ThresholdHilbert :=
  primeFourSiteDual n m - (1 / schurSigma (n+1)) • tailInnovation (n+1)


theorem primeFourSiteDual_inverse_completion (n m : ℕ)
    (hp : Nat.Prime (n+3)) (hr : Nat.Prime (m+3))
    (hnm : n+2 ≤ m) :
    2 * ((n+3 : ℕ) : ℝ)^2 + 2 * ((m+3 : ℕ) : ℝ)^2 =
      1 / schurSigma (n+1) + ‖primeFourSiteDualResidual n m‖^2 := by
  have hs : schurSigma (n+1) ≠ 0 := ne_of_gt (schurSigma_pos (n+1))
  have hc : inner ℝ (primeFourSiteDual n m) (tailInnovation (n+1)) = 1 := by
    rw [real_inner_comm, primeFourSiteDual_innovation n m hp hr hnm]
  rw [primeFourSiteDualResidual, norm_sub_sq_real, inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    primeFourSiteDual_norm_sq n m hnm, hc]
  change _ = _ + (_ - 2 * (1 / schurSigma (n+1) * 1) +
    (1 / schurSigma (n+1))^2 * schurSigma (n+1))
  field_simp
  ring


theorem prime_schur_inverse_le_two_primes (n m : ℕ)
    (hp : Nat.Prime (n+3)) (hr : Nat.Prime (m+3))
    (hnm : n+2 ≤ m) :
    1 / schurSigma (n+1) ≤
      2 * ((n+3 : ℕ) : ℝ)^2 + 2 * ((m+3 : ℕ) : ℝ)^2 := by
  rw [primeFourSiteDual_inverse_completion n m hp hr hnm]
  exact le_add_of_nonneg_right (sq_nonneg _)


theorem prime_schur_inverse_le_ten_sq (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    1 / schurSigma (n+1) ≤ 10 * ((n+3 : ℕ) : ℝ)^2 := by
  obtain ⟨r,hr,hpr,hr2⟩ := Nat.exists_prime_lt_and_le_two_mul (n+3) (by omega)
  have hpodd : Odd (n+3) := hp.odd_of_ne_two (by omega)
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hsep : n+5 ≤ r := by
    rcases hpodd with ⟨a,ha⟩
    rcases hrodd with ⟨b,hb⟩
    omega
  let m := r-3
  have hmr : m+3=r := by dsimp [m]; omega
  have hnm : n+2 ≤ m := by dsimp [m]; omega
  have h := prime_schur_inverse_le_two_primes n m hp (by simpa only [hmr] using hr) hnm
  rw [hmr] at h
  have hrr : (r : ℝ) ≤ 2 * ((n+3 : ℕ) : ℝ) := by exact_mod_cast hr2
  nlinarith [sq_nonneg ((r : ℝ)-2*((n+3 : ℕ) : ℝ))]


theorem prime_schurSigma_ge_tenth (n : ℕ) (hp : Nat.Prime (n+3)) :
    1 / (10 * ((n+3 : ℕ) : ℝ)^2) ≤ schurSigma (n+1) := by
  have h := (div_le_iff₀ (schurSigma_pos (n+1))).mp
    (prime_schur_inverse_le_ten_sq n hp)
  apply (div_le_iff₀ (by positivity : 0 < 10 * ((n+3 : ℕ) : ℝ)^2)).2
  nlinarith
end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
