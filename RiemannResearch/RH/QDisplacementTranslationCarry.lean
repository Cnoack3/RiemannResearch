/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.OddCarryJointHead
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.ModEq
import RiemannResearch.RH.QSquarefreeHeadBoundary

/-! # Exact translation of the limiting displacement

Source: user-proposed LCM translation. The repository’s finite-head inversion and
squarefree compatibility identify the surviving carry moduli at every physical site. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QDisplacementTranslationCarry
open ZetaTwoHilbert QSquarefreeDisplacementRigidity Pareto

/-- A finite floor expansion at any fixed collection of physical sites. -/
theorem finite_floor_reconstruction (f : ℕ → ℝ) (hf : f 0 = 0) (H n : ℕ) (hn : n ≤ H) :
    f n = ∑ m ∈ Finset.Icc 1 H, mobiusDifference m f * (n / m : ℕ) := by
  have he := mobiusJointHead_signed_error f H n
  rw [mobiusJointHead_exact f H hf n hn, Nat.div_eq_of_lt (show n < H + 1 by omega)] at he
  simp only [Nat.cast_zero, mul_zero, add_zero, sub_self] at he
  linarith

/-- Each additive floor defect is exactly a single binary carry. -/
theorem finite_translation_identity (f : ℕ → ℝ) (hf : f 0 = 0) (L t : ℕ) :
    f (L + t) - f L - f t =
      ∑ m ∈ Finset.Icc 1 (L + t), if m ≤ L % m + t % m then mobiusDifference m f else 0 := by
  classical
  have hsum := finite_floor_reconstruction f hf (L + t)
  calc
    _ = (∑ m ∈ Finset.Icc 1 (L + t), mobiusDifference m f * ((L + t) / m : ℕ)) -
        (∑ m ∈ Finset.Icc 1 (L + t), mobiusDifference m f * (L / m : ℕ)) -
        (∑ m ∈ Finset.Icc 1 (L + t), mobiusDifference m f * (t / m : ℕ)) := by
      rw [← hsum (L + t) le_rfl, ← hsum L (by omega), ← hsum t (by omega)]
    _ = _ := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      have hp : 0 < m := (Finset.mem_Icc.mp hm).1
      by_cases hc : m ≤ L % m + t % m
      · rw [if_pos hc, Nat.add_div_eq_of_le_mod_add_mod hc hp]
        push_cast
        ring
      · rw [if_neg hc, Nat.add_div_eq_of_add_mod_lt (lt_of_not_ge hc)]
        push_cast
        ring

def roughCarrySet (L t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (L + t)).filter (fun m =>
      Squarefree m ∧ ¬ m ∣ L ∧ m ≤ L % m + t % m)

/-- For the actual limiting displacement the exact signed translation error
is supported on squarefree conductors not dividing the chosen period. -/
theorem displacement_translation (L t : ℕ) :
    qSequence displacement (L + t) - qSequence displacement L - qSequence displacement t =
      ∑ m ∈ roughCarrySet L t, mobiusDifference m (qSequence displacement) := by
  classical
  rw [finite_translation_identity _ (qSequence_zero _) L t]
  unfold roughCarrySet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have h1 := (Finset.mem_Icc.mp hm).1
  have hle := (Finset.mem_Icc.mp hm).2
  by_cases hc : m ≤ L % m + t % m
  · have hnd : ¬m ∣ L := by
      intro hd
      simp only [Nat.mod_eq_zero_of_dvd hd, zero_add] at hc
      exact (not_le_of_gt (Nat.mod_lt t h1)) hc
    have hm2 : 2 ≤ m := by
      by_contra! hn
      have hm1 : m = 1 := by omega
      exact hnd (by rw [hm1]; exact one_dvd _)
    by_cases hsf : Squarefree m
    · simp [hc, hnd, hsf]
    · have hz := QSquarefreeCompatibleHeads.nonsquarefree_charge_zero
          (qSequence displacement) (L + t) (fun n hn _ =>
            QSquarefreeDisplacementRegularity.displacement_difference_radical n hn) m hm2 hle hsf
      simp [hc, hsf, hz]
  · simp [hc]

/-- Exact squarefreeness matters: every surviving modulus has a prime
strictly larger than the physical conductor cutoff. -/
theorem roughCarry_large_prime (M t m : ℕ) (hm : m ∈ roughCarrySet (Nat.lcmUpto M) t) :
    ∃ p, Nat.Prime p ∧ p ∣ m ∧ M < p := by
  classical
  have hpred := (Finset.mem_filter.mp hm).2
  have hsf : Squarefree m := hpred.1
  have hnd : ¬m ∣ Nat.lcmUpto M := hpred.2.1
  by_contra! hnone
  apply hnd
  rw [← Nat.prod_primeFactors_of_squarefree hsf]
  apply (Nat.prod_primeFactors_dvd_iff (Nat.lcmUpto_ne_zero M)).mpr
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.primeFactors_lcmUpto]
  exact Nat.mem_primesLE.mpr ⟨hnone p hpr hdiv, hpr⟩

/-- A fixed horizon exposes cancellation between the endpoint and all carry
means. The only nonoscillatory term left is one finite scalar slope. -/
theorem centered_translation (f : ℕ → ℝ) (hf : f 0 = 0) (H L t : ℕ) (hlt : L + t ≤ H) :
    f (L + t) - f t =
      (L : ℝ) * (∑ m ∈ Finset.Icc 1 H, mobiusDifference m f / (m : ℝ)) +
        ∑ m ∈ Finset.Icc 1 H, mobiusDifference m f *
          ((if m ≤ L % m + t % m then (1: ℝ) else 0) - (L % m : ℕ) / (m : ℝ)) := by
  classical
  have hu := finite_floor_reconstruction f hf H (L + t) hlt
  have hv := finite_floor_reconstruction f hf H t (by omega)
  rw [hu, hv, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hp : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmR : (m: ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hrem : ((L % m : ℕ): ℝ) + (m: ℝ) * (L / m : ℕ) = L := by
    exact_mod_cast Nat.mod_add_div L m
  by_cases hc : m ≤ L % m + t % m
  · rw [if_pos hc, Nat.add_div_eq_of_le_mod_add_mod hc hp]
    push_cast
    rw [← hrem]
    field_simp [hmR]
    <;> ring
  · rw [if_neg hc, Nat.add_div_eq_of_add_mod_lt (lt_of_not_ge hc)]
    push_cast
    rw [← hrem]
    field_simp [hmR]
    <;> ring

/-- The finite scalar in centered_translation is precisely the repository's
boundary charge for this horizon, for every Q vector. -/
theorem slope_eq_headCharge (N : ℕ) (f : QHilbert) :
    (∑ m ∈ Finset.Icc 1 (N + 1), mobiusDifference m (qSequence f) / (m: ℝ)) =
      QSquarefreeHeadBoundary.headCharge N f := by
  classical
  let b := fun m : ℕ => mobiusDifference m (qSequence f) / (m: ℝ)
  have hc (m : ℕ) : SquarefreeMobiusProjection.qCoefficientCLM m f =
      - mobiusDifference m (qSequence f) := by
    change - mobiusDifferenceCLM m (ZetaTwoParetoTransfer.toPareto f) = _
    rw [mobiusDifferenceCLM_apply, ZetaTwoParetoTransfer.toPareto_sequence]
  have hb1 : b 1 = qSequence f 1 := by simp [b, mobiusDifference]
  have hs (k : ℕ) : (∑ m ∈ Finset.Icc 1 (k + 1), b m) =
      qSequence f 1 + ∑ i : Fin k, b (i.val + 2) := by
    induction k with
    | zero => simp [hb1]
    | succ k ih =>
      have he : Finset.Icc 1 (k + 1 + 1) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [he, Finset.sum_insert (by simp), Fin.sum_univ_castSucc, ih]
      simp only [Fin.val_last, Fin.val_castSucc]
      ring
  rw [QSquarefreeHeadBoundary.headCharge_eq_coefficients]
  simp_rw [hc]
  simp only [neg_div, Finset.sum_neg_distrib, sub_neg_eq_add]
  exact hs N

end RiemannResearch.RH.QDisplacementTranslationCarry
