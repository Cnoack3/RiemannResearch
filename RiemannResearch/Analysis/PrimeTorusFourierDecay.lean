/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.GCongr
import RiemannResearch.Analysis.ActualPrimeTorusFMZSeries

/-!
# Classical Fourier decay implies the prime-torus weighted summability bound

The sufficient dimension condition B > d + 1 follows from integer-lattice rpow
summability and the exact prime-logarithm Fourier height. This supplies the
summability premise in the actual infinite-series FMZ assembly.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open PrimePhaseTorus

private abbrev standardIntLattice (ι : Type*) [Fintype ι] :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

private def intModeToLattice {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    standardIntLattice ι :=
  ⟨fun i => (k i : ℝ), by
    apply ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨k i, by simp⟩⟩

private theorem intModeToLattice_injective {ι : Type*} [Fintype ι] :
    Function.Injective (@intModeToLattice ι _) := by
  intro k l h
  funext i
  have hi := congrFun (congrArg Subtype.val h) i
  change (k i : ℝ) = (l i : ℝ) at hi
  exact_mod_cast hi

private theorem intModeToLattice_norm {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    ‖intModeToLattice k‖ = ‖k‖ := by
  change ‖fun i => (k i : ℝ)‖ = ‖k‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg k)).mpr
    intro i
    simpa only [Int.norm_cast_real] using norm_le_pi_norm k i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (k i : ℝ)))).mpr
    intro i
    simpa only [Int.norm_cast_real] using
      norm_le_pi_norm (fun i => (k i : ℝ)) i

theorem summable_pi_int_norm_rpow {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : r < -(Fintype.card ι : ℝ)) :
    Summable (fun k : ι → ℤ => ‖k‖ ^ r) := by
  have hRank : Module.finrank ℤ (standardIntLattice ι) = Fintype.card ι := by
    rw [ZLattice.rank ℝ (standardIntLattice ι),
      Module.finrank_eq_card_basis (Pi.basisFun ℝ ι)]
  have h := ZLattice.summable_norm_rpow (standardIntLattice ι) r
    (by simpa only [hRank] using hr)
  simpa only [Function.comp_def, intModeToLattice_norm] using
    h.comp_injective (intModeToLattice_injective (ι := ι))

theorem summable_pi_int_one_add_norm_rpow {ι : Type*} [Fintype ι]
    [DecidableEq ι] (r : ℝ) (hr : r < -(Fintype.card ι : ℝ)) :
    Summable (fun k : ι → ℤ => (1 + ‖k‖) ^ r) := by
  have hr0 : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have h := (summable_pi_int_norm_rpow (ι := ι) r hr).update 0 1
  apply Summable.of_norm_bounded h
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) r)]
  by_cases hk : k = 0
  · simp [hk]
  · have hnorm : 0 < ‖k‖ := norm_pos_iff.mpr hk
    simpa [Function.update, hk] using
      Real.rpow_le_rpow_of_nonpos hnorm (by linarith) hr0.le

theorem weighted_logheight_le_norm {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (k : ι → ℤ) :
    (∑ i, |(k i : ℝ)| * c i) ≤ ‖k‖ * ∑ i, c i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (hc i)
  simpa only [Int.norm_eq_abs] using norm_le_pi_norm k i

theorem summable_weighted_of_fourierDecay {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : (ι → ℤ) → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (C B : ℝ) (hC : 0 ≤ C) (hB : (Fintype.card ι : ℝ) + 1 < B)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Summable (fun k : ι → ℤ =>
      ‖a k‖ * (1 + (∑ i, |(k i : ℝ)| * c i))) := by
  let L : ℝ := ∑ i, c i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i hi => hc i)
  have hs := (summable_pi_int_one_add_norm_rpow (ι := ι) (1 - B)
    (by linarith)).mul_left (C * (1 + L))
  apply Summable.of_norm_bounded hs
  intro k
  have hkn : 0 ≤ ‖k‖ := norm_nonneg k
  have hheight : (∑ i, |(k i : ℝ)| * c i) ≤ ‖k‖ * L :=
    weighted_logheight_le_norm c hc k
  have hheight0 : 0 ≤ (∑ i, |(k i : ℝ)| * c i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (hc i))
  have hweight : 1 + (∑ i, |(k i : ℝ)| * c i) ≤
      (1 + L) * (1 + ‖k‖) ^ (1 : ℕ) := by
    simp only [pow_one]
    nlinarith
  have hpow : (1 + ‖k‖) ^ (-B) * (1 + ‖k‖) ^ (1 : ℕ) =
      (1 + ‖k‖) ^ (1 - B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
  calc
    _ ≤ (C * (1 + ‖k‖) ^ (-B)) *
        ((1 + L) * (1 + ‖k‖) ^ (1 : ℕ)) :=
      mul_le_mul (ha k) hweight (by positivity) (by positivity)
    _ = C * (1 + L) * (1 + ‖k‖) ^ (1 - B) := by
      rw [show (C * (1 + ‖k‖) ^ (-B)) *
          ((1 + L) * (1 + ‖k‖) ^ (1 : ℕ)) =
          C * (1 + L) * ((1 + ‖k‖) ^ (-B) * (1 + ‖k‖) ^ (1 : ℕ)) by ring,
        hpow]

def ambientPrimeMode (P : Finset ℕ) (k : P → ℤ) : ℕ → ℤ :=
  fun p => if hp : p ∈ P then k ⟨p, hp⟩ else 0

@[simp] theorem ambientPrimeMode_apply (P : Finset ℕ) (k : P → ℤ) (p : P) :
    ambientPrimeMode P k p = k p := by simp [ambientPrimeMode, p.property]

theorem summable_primeModeWeight_of_fourierDecay
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : (P → ℤ) → ℂ) (C B : ℝ) (hC : 0 ≤ C)
    (hB : (P.card : ℝ) + 1 < B)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Summable (fun k : P → ℤ =>
      ‖a k‖ * primeModeWeight P (ambientPrimeMode P k)) := by
  have h := summable_weighted_of_fourierDecay a (fun p : P => Real.log p.val)
    (fun p => Real.log_nonneg (by exact_mod_cast (hP p.val p.property).one_lt.le))
    C B hC (by simpa using hB) ha
  convert h using 1
  funext k
  rw [primeModeWeight_eq P (ambientPrimeMode P k) hP]
  congr 2
  rw [← Finset.sum_coe_sort]
  simp only [ambientPrimeMode_apply]

/-- Two arithmetic Fourier moments are summable under the strict decay
threshold B > dimension + 2. This supplies the norm in the quantitative
O(1 / log T) corrected FMZ remainder. -/
theorem summable_weighted_sq_of_fourierDecay {ι : Type*} [Fintype ι]
    (a : (ι → ℤ) → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (C B : ℝ) (hC : 0 ≤ C) (hB : (Fintype.card ι : ℝ) + 2 < B)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Summable (fun k : ι → ℤ =>
      ‖a k‖ * (1 + (∑ i, |(k i : ℝ)| * c i)) ^ 2) := by
  classical
  let L : ℝ := ∑ i, c i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i hi => hc i)
  have hs := (summable_pi_int_one_add_norm_rpow (ι := ι) (2 - B)
    (by linarith)).mul_left (C * (1 + L) ^ 2)
  apply Summable.of_norm_bounded hs
  intro k
  have hkn : 0 ≤ ‖k‖ := norm_nonneg k
  have hheight : (∑ i, |(k i : ℝ)| * c i) ≤ ‖k‖ * L :=
    weighted_logheight_le_norm c hc k
  have hheight0 : 0 ≤ (∑ i, |(k i : ℝ)| * c i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (hc i))
  have hlinear : 1 + (∑ i, |(k i : ℝ)| * c i) ≤
      (1 + L) * (1 + ‖k‖) := by nlinarith
  have hweight : (1 + (∑ i, |(k i : ℝ)| * c i)) ^ 2 ≤
      (1 + L) ^ 2 * (1 + ‖k‖) ^ (2 : ℕ) := by
    calc
      _ ≤ ((1 + L) * (1 + ‖k‖)) ^ 2 := by
        gcongr
      _ = _ := mul_pow _ _ _
  have hpow : (1 + ‖k‖) ^ (-B) * (1 + ‖k‖) ^ (2 : ℕ) =
      (1 + ‖k‖) ^ (2 - B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ (C * (1 + ‖k‖) ^ (-B)) *
        ((1 + L) ^ 2 * (1 + ‖k‖) ^ (2 : ℕ)) :=
      mul_le_mul (ha k) hweight (sq_nonneg _) (by positivity)
    _ = C * (1 + L) ^ 2 * (1 + ‖k‖) ^ (2 - B) := by
      rw [show (C * (1 + ‖k‖) ^ (-B)) *
          ((1 + L) ^ 2 * (1 + ‖k‖) ^ (2 : ℕ)) =
          C * (1 + L) ^ 2 * ((1 + ‖k‖) ^ (-B) * (1 + ‖k‖) ^ (2 : ℕ)) by ring,
        hpow]

/-- Classical B > card(P) + 2 Fourier decay supplies the squared arithmetic
Wiener norm used by the quantitative actual-zero prime-torus theorem. -/
theorem summable_primeModeWeight_sq_of_fourierDecay
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : (P → ℤ) → ℂ) (C B : ℝ) (hC : 0 ≤ C)
    (hB : (P.card : ℝ) + 2 < B)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Summable (fun k : P → ℤ =>
      ‖a k‖ * (primeModeWeight P (ambientPrimeMode P k)) ^ 2) := by
  have h := summable_weighted_sq_of_fourierDecay a (fun p : P => Real.log p.val)
    (fun p => Real.log_nonneg (by exact_mod_cast (hP p.val p.property).one_lt.le))
    C B hC (by simpa using hB) ha
  convert h using 1
  funext k
  rw [primeModeWeight_eq P (ambientPrimeMode P k) hP]
  congr 2
  rw [← Finset.sum_coe_sort]
  simp only [ambientPrimeMode_apply]

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
