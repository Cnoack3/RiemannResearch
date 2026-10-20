import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Centered coprime-prefix normal equations from the actual divisor dictionary

Source: user-provided CRT-carry memorandum, Section 8, 19 October 2026.
The arithmetic inclusion-exclusion and totient-density identities are reused
from `QPrimeSieve` and `QMobiusPrimePacketArithmetic`. This module supplies
the finite-interval identification and normal-equation assembly. No asymptotic
estimate is assumed or proved. The result holds for any positive period when
normal equations for every divisor are available.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteWeightedTailCharge
open ArithmeticCumulative

/-- The finite-set prefix agrees with the existing cumulative coprime count. -/
theorem countPrefix_eq_coprimeCount (L a : ℕ) (ha : a ≤ L) :
    countPrefix (coprimeSites L) a = QPrimeSieve.coprimeCount L a := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 L := by
    intro k hk
    obtain ⟨hk1, hka⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk1, hka.trans ha⟩
  calc
    countPrefix (coprimeSites L) a =
        ∑ k ∈ Finset.Icc 1 L,
          if Nat.Coprime k L then (if k ≤ a then (1 : ℝ) else 0) else 0 := by
      simp only [countPrefix, coprimeSites, sites, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 a, if Nat.Coprime k L then (1 : ℝ) else 0 := by
      have hs := Finset.sum_subset hsub
        (f := fun k => if Nat.Coprime k L then
          (if k ≤ a then (1 : ℝ) else 0) else 0)
        (by
          intro k hk hka
          have hk1 := (Finset.mem_Icc.mp hk).1
          have hnot : ¬ k ≤ a := by
            intro h
            exact hka (Finset.mem_Icc.mpr ⟨hk1, h⟩)
          simp [hnot])
      rw [← hs]
      apply Finset.sum_congr rfl
      intro k hk
      simp [(Finset.mem_Icc.mp hk).2]
    _ = QPrimeSieve.coprimeCount L a := by
      unfold QPrimeSieve.coprimeCount cumulative
      symm
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        have hk' := Finset.mem_range.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro k hk j hj he
        omega
      · intro k hk
        obtain ⟨hk1, hka⟩ := Finset.mem_Icc.mp hk
        exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k hk
        rfl

/-- Actual finite divisor synthesis of the centered prefix. The d=1 term is
zero, so this is already a legal squarefree synthesis when L is squarefree. -/
theorem centered_coprime_prefix (L a : ℕ) (hL : 0 < L) (ha : a ≤ L) :
    countPrefix (coprimeSites L) a -
        ((Nat.totient L : ℝ) / L) * (a : ℝ) =
      -(∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d a) := by
  rw [countPrefix_eq_coprimeCount L a ha]
  have h := QPrimeSieve.divisorSieve_eq_count_sub_linear L a (ne_of_gt hL)
  rw [QMobiusPrimePacket.divisorDensity_eq_totient L (ne_of_gt hL)] at h
  simpa only [QPrimeSieve.divisorSieve, mul_comm] using h.symm

/-- The centered-prefix normal equation follows from the divisor normal
equations. It is not an independent arithmetic assumption. -/
theorem centered_prefix_normal_of_divisor_normals
    (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    (∑ a ∈ sites L, weight L a * (1 - f a) *
      (countPrefix (coprimeSites L) a -
        ((Nat.totient L : ℝ) / L) * (a : ℝ))) = 0 := by
  calc
    _ = -(∑ a ∈ sites L, ∑ d ∈ L.divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            (weight L a * (1 - f a) * residueFraction d a)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      rw [centered_coprime_prefix L a hL (Finset.mem_Icc.mp ha).2]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = -(∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          ∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = 0 := by
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro d hd
      rw [hdiv d hd, mul_zero]

/-- Section 8's signed identity assembled from every actual divisor normal
equation. Only the fitted-vector normal equation and zero endpoint remain. -/
theorem signed_identity_of_divisor_normals
    (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hfit : (∑ a ∈ sites L, weight L a * (1 - f a) * f a) = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    rationalError L f + signedTail L f =
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) := by
  apply signed_identity L hL f hfL hfit
  · exact hdiv L (Nat.mem_divisors.mpr ⟨dvd_refl L, ne_of_gt hL⟩)
  · exact centered_prefix_normal_of_divisor_normals L hL f hdiv

/-- A function synthesized from divisors of L vanishes at the zero residue. -/
theorem divisor_synthesis_endpoint (L : ℕ) (f c : ℕ → ℝ)
    (hf : ∀ a, f a = ∑ d ∈ L.divisors, c d * residueFraction d a) :
    f L = 0 := by
  rw [hf L]
  apply Finset.sum_eq_zero
  intro d hd
  simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- Every divisor normal equation annihilates their fitted linear combination. -/
theorem fitted_normal_of_divisor_synthesis
    (L : ℕ) (f c : ℕ → ℝ)
    (hf : ∀ a, f a = ∑ d ∈ L.divisors, c d * residueFraction d a)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    (∑ a ∈ sites L, weight L a * (1 - f a) * f a) = 0 := by
  calc
    _ = ∑ a ∈ sites L, ∑ d ∈ L.divisors,
        c d * (weight L a * (1 - f a) * residueFraction d a) := by
      apply Finset.sum_congr rfl
      intro a ha
      conv_lhs => rhs; rw [hf a]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ d ∈ L.divisors, c d *
        ∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [hdiv d hd, mul_zero]

/-- Complete finite assembly: the signed identity follows from an actual
divisor synthesis and its normal equations. No coprime-prefix, endpoint, or
fitted-vector normal equation is assumed separately. -/
theorem signed_identity_of_divisor_synthesis
    (L : ℕ) (hL : 0 < L) (f c : ℕ → ℝ)
    (hf : ∀ a, f a = ∑ d ∈ L.divisors, c d * residueFraction d a)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    rationalError L f + signedTail L f =
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) :=
  signed_identity_of_divisor_normals L hL f
    (divisor_synthesis_endpoint L f c hf)
    (fitted_normal_of_divisor_synthesis L f c hf hdiv) hdiv

end RiemannResearch.RH.QRationalCoprimeTail
