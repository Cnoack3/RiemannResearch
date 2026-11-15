/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.NumberTheory.DivisorIncidence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete-Q masses and orthogonal innovations of gcd cells

Source: user-provided CanonicalPrimePowerUpdatesResearch20261107, Section 5.
The inverse-square scaling and the actual gcd-cell masses are proved from the
physical infinite weighted sums. No head truncation or canonical growth
hypothesis occurs.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QGcdCellRefinement
open ZetaTwoHilbert ZetaTwoProbability

def eventSequence (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n = 0 then 0 else if n ∈ S then 1 else 0

theorem eventSequence_abs_le_one (S : Set ℕ) (n : ℕ) :
    |eventSequence S n| ≤ 1 := by
  classical
  unfold eventSequence
  split_ifs <;> norm_num

def eventVector (S : Set ℕ) : QHilbert :=
  encodeQ (eventSequence S)
    (boundedQ_square_summable _ 1 zero_le_one (eventSequence_abs_le_one S))

@[simp] theorem qSequence_eventVector (S : Set ℕ) :
    qSequence (eventVector S) = eventSequence S :=
  qSequence_encodeQ _ _ (by simp [eventSequence])

/-- The complete physical mass, including every positive integer. -/
def eventMass (S : Set ℕ) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * eventSequence S n

theorem eventMass_nonneg (S : Set ℕ) : 0 ≤ eventMass S := by
  classical
  apply tsum_nonneg
  intro n
  have hw := positiveQWeight_nonneg n
  unfold eventSequence
  split_ifs <;> nlinarith

theorem eventMass_summable (S : Set ℕ) :
    Summable (fun n : ℕ => positiveQWeight n * eventSequence S n) := by
  classical
  apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
  · intro n
    have hw := positiveQWeight_nonneg n
    unfold eventSequence
    split_ifs <;> nlinarith
  · intro n
    have hw := positiveQWeight_nonneg n
    unfold eventSequence
    split_ifs <;> nlinarith

theorem eventMass_mono {S T : Set ℕ} (hST : S ⊆ T) :
    eventMass S ≤ eventMass T := by
  classical
  apply Summable.tsum_le_tsum _ (eventMass_summable S) (eventMass_summable T)
  intro n
  have hw := positiveQWeight_nonneg n
  by_cases hn : n = 0
  · simp [eventSequence, hn]
  · by_cases hS : n ∈ S
    · simp [eventSequence, hn, hS, hST hS]
    · by_cases hT : n ∈ T <;> simp [eventSequence, hn, hS, hT, hw]

@[simp] theorem eventMass_empty : eventMass (∅ : Set ℕ) = 0 := by
  simp [eventMass, eventSequence]

@[simp] theorem eventMass_univ : eventMass (Set.univ : Set ℕ) = 1 := by
  classical
  unfold eventMass
  have he : (fun n : ℕ => positiveQWeight n * eventSequence Set.univ n) =
      positiveQWeight := by
    funext n
    by_cases hn : n = 0
    · simp [eventSequence, hn, positiveQWeight]
    · simp [eventSequence, hn]
  rw [he, positiveQWeight_tsum]

theorem eventMass_le_one (S : Set ℕ) : eventMass S ≤ 1 := by
  simpa only [eventMass_univ] using (eventMass_mono (Set.subset_univ S))

theorem eventMass_singleton (n : ℕ) (hn : 0 < n) :
    eventMass ({n} : Set ℕ) = positiveQWeight n := by
  classical
  unfold eventMass
  rw [tsum_eq_single n]
  · simp [eventSequence, ne_of_gt hn]
  · intro k hk
    simp [eventSequence, hk]

theorem eventMass_compl (S : Set ℕ) : eventMass Sᶜ = 1 - eventMass S := by
  classical
  have he : eventMass S + eventMass Sᶜ = 1 := by
    rw [eventMass, eventMass, ← (eventMass_summable S).tsum_add (eventMass_summable Sᶜ)]
    calc
      _ = eventMass Set.univ := by
        apply tsum_congr
        intro n
        by_cases hn : n = 0
        · simp [eventSequence, hn]
        · by_cases hS : n ∈ S <;> simp [eventSequence, hn, hS]
      _ = 1 := eventMass_univ
  linarith

theorem eventMass_union_of_disjoint (S T : Set ℕ) (hST : Disjoint S T) :
    eventMass (S ∪ T) = eventMass S + eventMass T := by
  classical
  rw [eventMass, eventMass, eventMass,
    ← (eventMass_summable S).tsum_add (eventMass_summable T)]
  apply tsum_congr
  intro n
  have hnot : ¬ (n ∈ S ∧ n ∈ T) := fun h => Set.disjoint_left.mp hST h.1 h.2
  by_cases hn : n = 0
  · simp [eventSequence, hn]
  · by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;>
      simp_all [eventSequence]

theorem eventVector_norm_sq (S : Set ℕ) :
    ‖eventVector S‖ ^ 2 = eventMass S := by
  classical
  rw [qNorm_weighted_sq, qSequence_eventVector]
  apply tsum_congr
  intro n
  unfold eventSequence
  split_ifs <;> ring

theorem eventVector_inner (S T : Set ℕ) :
    inner ℝ (eventVector S) (eventVector T) = eventMass (S ∩ T) := by
  classical
  rw [qInner_weighted, qSequence_eventVector, qSequence_eventVector]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [eventSequence, hn]
  · by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;>
      simp [eventSequence, hn, hS, hT]

theorem eventVector_inner_of_subset (S T : Set ℕ) (hST : S ⊆ T) :
    inner ℝ (eventVector S) (eventVector T) = eventMass S := by
  rw [eventVector_inner, Set.inter_eq_left.mpr hST]

def scaledEvent (m : ℕ) (S : Set ℕ) : Set ℕ :=
  {n | ∃ k, k ∈ S ∧ m * k = n}

theorem eventSequence_scaledEvent_mul (m : ℕ) (hm : 0 < m)
    (S : Set ℕ) (k : ℕ) :
    eventSequence (scaledEvent m S) (m * k) = eventSequence S k := by
  classical
  have hmem : m * k ∈ scaledEvent m S ↔ k ∈ S := by
    constructor
    · rintro ⟨j, hj, he⟩
      have hjk : j = k := Nat.eq_of_mul_eq_mul_left hm he
      simpa only [hjk] using hj
    · intro hk
      exact ⟨k, hk, rfl⟩
  by_cases hk : k = 0
  · simp [eventSequence, hk]
  · have hmk : m * k ≠ 0 := Nat.mul_ne_zero (ne_of_gt hm) hk
    simp [eventSequence, hk, hmk, hmem]

theorem positiveQWeight_mul (m k : ℕ) :
    positiveQWeight (m * k) =
      (1 / (m : ℝ) ^ 2) * positiveQWeight k := by
  simp only [positiveQWeight, Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
  ring

/-- Inverse-square scaling for every event, not just all multiples. -/
theorem eventMass_scaledEvent (m : ℕ) (hm : 0 < m) (S : Set ℕ) :
    eventMass (scaledEvent m S) = (1 / (m : ℝ) ^ 2) * eventMass S := by
  classical
  unfold eventMass
  have hreindex :
      (∑' n : ℕ, positiveQWeight n * eventSequence (scaledEvent m S) n) =
        ∑' k : ℕ, positiveQWeight (m * k) * eventSequence S k := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun k : Function.support (fun k : ℕ =>
        positiveQWeight (m * k) * eventSequence S k) => m * k.val)
    · intro a b hab
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left hm hab
    · intro n hn
      have hs : n ∈ scaledEvent m S := by
        by_contra h
        apply hn
        simp [eventSequence, h]
      obtain ⟨k, hk, he⟩ := hs
      have heq : positiveQWeight (m * k) * eventSequence S k =
          positiveQWeight n * eventSequence (scaledEvent m S) n := by
        rw [← he, eventSequence_scaledEvent_mul m hm]
      have hkn : positiveQWeight (m * k) * eventSequence S k ≠ 0 := by
        rw [heq]
        exact hn
      exact ⟨⟨k, hkn⟩, he⟩
    · intro k
      rw [eventSequence_scaledEvent_mul m hm]
  rw [hreindex]
  simp_rw [positiveQWeight_mul, mul_assoc]
  exact tsum_mul_left

def gcdCell (L d : ℕ) : Set ℕ := {n | Nat.gcd n L = d}

/-- Finite Möbius inversion identifies an actual gcd-cell indicator in the
complete Hilbert space. -/
theorem eventVector_gcdCell_eq_sum (L d : ℕ) (hL : 0 < L)
    (hd : d ∈ L.divisors) :
    eventVector (gcdCell L d) =
      ∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) •
          QDivisibilityDensity.qDivisor j := by
  classical
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · simp [hn, eventSequence]
  · have hgp : Nat.gcd n L ∈ L.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, ne_of_gt hL⟩
    have he := RiemannResearch.NumberTheory.DivisorIncidence.moebius_left_inverse
      L d (Nat.gcd n L) hd hgp
    rw [qSequence_eventVector]
    change eventSequence (gcdCell L d) n =
      qSequenceLinear (∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) •
          QDivisibilityDensity.qDivisor j) n
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change eventSequence (gcdCell L d) n =
      ∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) *
          qSequence (QDivisibilityDensity.qDivisor j) n
    simp only [QDivisibilityDensity.qSequence_qDivisor]
    have hpoint (j : ℕ) (hj : j ∈ L.divisors) :
        QDivisibilityDensity.positiveDivisor j n =
          if j ∣ Nat.gcd n L then (1 : ℝ) else 0 := by
      have hg0 : Nat.gcd n L ≠ 0 := Nat.gcd_ne_zero_right (ne_of_gt hL)
      rw [← QDivisorHilbert.positiveDivisor_gcd_cutoff L j n hL
        (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hj)]
      simp [QDivisibilityDensity.positiveDivisor, hg0]
    calc
      _ = if d = Nat.gcd n L then (1 : ℝ) else 0 := by
        simp [eventSequence, gcdCell, hn, eq_comm]
      _ = ∑ j ∈ L.divisors,
          (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) *
            (if j ∣ Nat.gcd n L then (1 : ℝ) else 0) := he.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpoint j hj]

theorem eventVector_gcdCell_mem (L d : ℕ) (hL : 0 < L)
    (hd : d ∈ L.divisors) :
    eventVector (gcdCell L d) ∈ QCRTFiniteCollocation.cellSpace L := by
  rw [eventVector_gcdCell_eq_sum L d hL hd]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact QCRTFiniteCollocation.divisor_mem_cell L j hL (Nat.dvd_of_mem_divisors hj)

/-- Scaling identifies the actual gcd event, with no coprimality premise. -/
theorem gcdCell_mul (a R e : ℕ) (ha : 0 < a) :
    gcdCell (a * R) (a * e) = scaledEvent a (gcdCell R e) := by
  ext n
  constructor
  · intro hn
    have hn' : Nat.gcd n (a * R) = a * e := hn
    have had : a ∣ n := by
      have h := Nat.gcd_dvd_left n (a * R)
      rw [hn'] at h
      exact (dvd_mul_right a e).trans h
    obtain ⟨k, hk⟩ := had
    refine ⟨k, ?_, hk.symm⟩
    change Nat.gcd k R = e
    rw [hk, Nat.gcd_mul_left] at hn'
    exact Nat.eq_of_mul_eq_mul_left ha hn'
  · rintro ⟨k, hk, rfl⟩
    change Nat.gcd k R = e at hk
    change Nat.gcd (a * k) (a * R) = a * e
    rw [Nat.gcd_mul_left, hk]

theorem gcdCell_mass_mul (a R e : ℕ) (ha : 0 < a) :
    eventMass (gcdCell (a * R) (a * e)) =
      (1 / (a : ℝ) ^ 2) * eventMass (gcdCell R e) := by
  rw [gcdCell_mul a R e ha, eventMass_scaledEvent a ha]

/-- The new top-prime-power subcell has exactly p⁻² of the old mass. -/
theorem gcdCell_refinement_mass (a p R e : ℕ) (ha : 0 < a) (hp : 0 < p) :
    eventMass (gcdCell ((p * a) * R) ((p * a) * e)) =
      (1 / (p : ℝ) ^ 2) * eventMass (gcdCell (a * R) (a * e)) := by
  rw [gcdCell_mass_mul (p * a) R e (Nat.mul_pos hp ha),
    gcdCell_mass_mul a R e ha]
  simp only [Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
  ring

/-- Exact complete energy of a centered subcell indicator. -/
theorem event_innovation_norm_sq (E B : Set ℕ) (hBE : B ⊆ E)
    (c : ℝ) (hmass : eventMass B = c * eventMass E) :
    ‖eventVector B - c • eventVector E‖ ^ 2 =
      eventMass E * c * (1 - c) := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    eventVector_norm_sq, eventVector_norm_sq, inner_smul_right,
    eventVector_inner_of_subset B E hBE, hmass]
  ring

theorem event_innovation_inner_old (E B : Set ℕ) (hBE : B ⊆ E)
    (c : ℝ) (hmass : eventMass B = c * eventMass E) :
    inner ℝ (eventVector B - c • eventVector E) (eventVector E) = 0 := by
  rw [inner_sub_left, real_inner_smul_left,
    eventVector_inner_of_subset B E hBE, real_inner_self_eq_norm_sq,
    eventVector_norm_sq, hmass, sub_self]

end RiemannResearch.RH.QGcdCellRefinement
