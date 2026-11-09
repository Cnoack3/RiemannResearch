/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.Analysis.MellinStepSeries
import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.ParetoBoundedMellin
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoUnscaledDilation

/-!
# Complete Pareto Mellin coordinates on finite residue classes

The normalized-conductor Mellin formula and the bounded-step series give the
class moments for every actual zeta zero in the positive half-plane. The
arithmetic grouping uses positive representatives, so the last representative
retains the whole class of multiples. Every progression sum is complete.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.RH.ParetoAtomMellinSignature

/-- The legal dictionary at period `L` uses every positive divisor of `L`. -/
def trialSpace (L : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (fun d : L.divisors =>
    normalizedResidueHilbert d.val (Nat.pos_of_mem_divisors d.property)))

theorem trial_sequence_mod {L : ℕ} {f : ThresholdHilbert} (hf : f ∈ trialSpace L)
    (n : ℕ) : hilbertSequence f (n % L) = hilbertSequence f n := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, rfl⟩
    simp only [normalizedResidueHilbert_sequence, ArithmeticCumulative.residueFraction,
      Nat.mod_mod_of_dvd n (Nat.dvd_of_mem_divisors d.property)]
  | zero =>
    change hilbertSequenceLinear (0 : ThresholdHilbert) (n % L) = hilbertSequenceLinear 0 n
    rw [map_zero]
    rfl
  | add x y hx hy ihx ihy =>
    change hilbertSequenceLinear (x + y) (n % L) = hilbertSequenceLinear (x + y) n
    rw [map_add]
    change hilbertSequence x (n % L) + hilbertSequence y (n % L) =
      hilbertSequence x n + hilbertSequence y n
    rw [ihx, ihy]
  | smul c x hx ih =>
    change hilbertSequenceLinear (c • x) (n % L) = hilbertSequenceLinear (c • x) n
    rw [map_smul]
    change c * hilbertSequence x (n % L) = c * hilbertSequence x n
    rw [ih]

private theorem one_sequence_succ (n : ℕ) : hilbertSequence hilbertOne (n + 1) = 1 := by
  rw [hilbertOne_sequence]
  simp [zeroAnchor]

/-- The error has one value on each class, with positive representatives `1, …, N+1`. -/
def error (N : ℕ) (f : ThresholdHilbert) (r : Fin (N + 1)) : ℝ :=
  hilbertSequence (hilbertOne - f) (r.val + 1)

theorem error_multiples {N : ℕ} {f : ThresholdHilbert} (hf : f ∈ trialSpace (N + 1)) :
    error N f (Fin.last N) = 1 := by
  have hz : hilbertSequence f (N + 1) = 0 := by
    rw [← trial_sequence_mod hf (N + 1), Nat.mod_self, hilbertSequence_zero]
  change hilbertSequenceLinear (hilbertOne - f) (N + 1) = 1
  rw [map_sub]
  change hilbertSequence hilbertOne (N + 1) - hilbertSequence f (N + 1) = 1
  rw [one_sequence_succ, hz, sub_zero]

private theorem sequence_progression {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1))
    (r : Fin (N + 1)) (k : ℕ) :
    hilbertSequence f (r.val + (N + 1) * k + 1) = hilbertSequence f (r.val + 1) := by
  rw [← trial_sequence_mod hf (r.val + (N + 1) * k + 1),
    ← trial_sequence_mod hf (r.val + 1)]
  congr 1
  rw [show r.val + (N + 1) * k + 1 = (r.val + 1) + (N + 1) * k by omega]
  simp

private theorem error_progression {N : ℕ} {f : ThresholdHilbert} (hf : f ∈ trialSpace (N + 1))
    (r : Fin (N + 1)) (k : ℕ) :
    hilbertSequence (hilbertOne - f) (r.val + (N + 1) * k + 1) = error N f r := by
  change hilbertSequenceLinear (hilbertOne - f) (r.val + (N + 1) * k + 1) =
    hilbertSequenceLinear (hilbertOne - f) (r.val + 1)
  rw [map_sub]
  change hilbertSequence hilbertOne (r.val + (N + 1) * k + 1) -
      hilbertSequence f (r.val + (N + 1) * k + 1) =
    hilbertSequence hilbertOne (r.val + 1) - hilbertSequence f (r.val + 1)
  rw [one_sequence_succ, one_sequence_succ, sequence_progression hf]

private theorem progression_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a : ℕ → E} (ha : Summable a) {N : ℕ} (r : Fin (N + 1)) :
    Summable (fun k : ℕ => a (r.val + (N + 1) * k)) := by
  apply ha.comp_injective
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos N) (Nat.add_left_cancel hij)

/-- Complete physical Pareto mass of a residue class. The multiples are `Fin.last N`. -/
def classWeight (N : ℕ) (r : Fin (N + 1)) : ℝ :=
  progressionWeight (N + 1) (r.val + 1)

theorem classWeight_pos (N : ℕ) (r : Fin (N + 1)) : 0 < classWeight N r :=
  progressionWeight_pos _ _ (Nat.succ_pos _) (Nat.succ_pos _)

/-- The compulsory Pareto error on the multiples class has quadratic decay. -/
theorem multiples_mass_bounds (N : ℕ) :
    let L := ((N + 1 : ℕ) : ℝ)
    1 / L ^ 2 ≤ classWeight N (Fin.last N) ∧
      classWeight N (Fin.last N) ≤ 2 / (L * (L + 1)) := by
  intro L
  change 1 / L ^ 2 ≤ progressionWeight (N + 1) (N + 1) ∧
    progressionWeight (N + 1) (N + 1) ≤ 2 / (L * (L + 1))
  constructor
  · simpa only [L, pow_two] using
      progressionWeight_lower (N + 1) (N + 1) (Nat.succ_pos N) (Nat.succ_pos N)
  · have h := progressionWeight_upper_one (N + 1) (N + 1) (Nat.succ_pos N)
    change _ ≤ 1 / (L * (L + 1)) + 1 / (L * (L + 1)) at h
    exact h.trans_eq (by ring)

theorem classWeight_eq_tsum (N : ℕ) (r : Fin (N + 1)) :
    classWeight N r = ∑' k : ℕ, paretoWeight (r.val + (N + 1) * k) := by
  apply tsum_congr
  intro k
  rw [show r.val + 1 + (N + 1) * k = r.val + (N + 1) * k + 1 by omega,
    positiveWeight_succ]

/-- The ordinary Mellin first differences, summed over a whole residue class.
The coordinate uses the normalization `s * Mellin`. -/
def classMellin (N : ℕ) (s : ℂ) (r : Fin (N + 1)) : ℂ :=
  ∑' k : ℕ, mellinFirst s (r.val + (N + 1) * k + 1)

private theorem one_bounded (n : ℕ) : |hilbertSequence hilbertOne n| ≤ 1 := by
  cases n with
  | zero => simp
  | succ n => rw [one_sequence_succ, abs_one]

private theorem first_hasSum_one (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun n : ℕ => mellinFirst s (n + 1)) 1 := by
  have h := hasSum_first_mellin_pairing_of_bounded hilbertOne 1 one_bounded s hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [paretoMellin_one_of_pos s hs, mul_one_div_cancel hs0] at h
  simpa only [one_sequence_succ, Complex.ofReal_one, mul_one] using h

theorem classMellin_summable (N : ℕ) (s : ℂ) (hs : 0 < s.re) (r : Fin (N + 1)) :
    Summable (fun k : ℕ => mellinFirst s (r.val + (N + 1) * k + 1)) :=
  progression_summable (first_hasSum_one s hs).summable r

theorem classMellin_sum (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ∑ r : Fin (N + 1), classMellin N s r = 1 := by
  calc
    _ = ∑' n : ℕ, mellinFirst s (n + 1) :=
      (Nat.sumByResidueClasses (first_hasSum_one s hs).summable (N + 1)).symm
    _ = 1 := (first_hasSum_one s hs).tsum_eq

/-- Regrouping into residue classes keeps the whole Pareto error. -/
theorem error_norm_sq_eq_classes {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) :
    ‖hilbertOne - f‖ ^ 2 = ∑ r, classWeight N r * (error N f r) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  have hfull := hilbertSequence_square_summable (hilbertOne - f)
  rw [hfull.tsum_eq_zero_add]
  simp only [hilbertSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  have h := Nat.sumByResidueClasses ((summable_nat_add_iff 1).mpr hfull) (N + 1)
  change (∑' n : ℕ, positiveWeight (n + 1) * hilbertSequence (hilbertOne - f) (n + 1) ^ 2) =
    ∑ r : Fin (N + 1), ∑' k : ℕ, positiveWeight (r.val + (N + 1) * k + 1) *
      hilbertSequence (hilbertOne - f) (r.val + (N + 1) * k + 1) ^ 2 at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [positiveWeight_succ, error_progression hf r]
  rw [classWeight_eq_tsum, tsum_mul_right]


/-- A periodic step's finite class pairing is its genuine positive-half-plane Mellin value. -/
theorem class_pairing_eq_mellin (N : ℕ) (f : ThresholdHilbert)
    (hperiod : ∀ (r : Fin (N + 1)) (k : ℕ),
      hilbertSequence f (r.val + (N + 1) * k + 1) = hilbertSequence f (r.val + 1))
    {B : ℝ} (hB : ∀ n, |hilbertSequence f n| ≤ B) (s : ℂ) (hs : 0 < s.re) :
    (∑ r, classMellin N s r * (hilbertSequence f (r.val + 1) : ℂ)) =
      s * paretoMellin f s := by
  have h := hasSum_first_mellin_pairing_of_bounded f B hB s hs
  calc
    _ = ∑ r : Fin (N + 1), ∑' k : ℕ, mellinFirst s (r.val + (N + 1) * k + 1) *
        (hilbertSequence f (r.val + (N + 1) * k + 1) : ℂ) := by
      apply Finset.sum_congr rfl
      intro r _
      simp_rw [hperiod r]
      rw [classMellin, tsum_mul_right]
    _ = ∑' n : ℕ, mellinFirst s (n + 1) * (hilbertSequence f (n + 1) : ℂ) :=
      (Nat.sumByResidueClasses h.summable (N + 1)).symm
    _ = _ := h.tsum_eq

/-- The conductor signature annihilates the whole legal trial space. -/
theorem trial_class_pairing_zero {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑ r, classMellin N s r * (hilbertSequence f (r.val + 1) : ℂ)) = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    have hm : g ∈ trialSpace (N + 1) := Submodule.subset_span hg
    rcases hg with ⟨d, rfl⟩
    have hd := Nat.pos_of_mem_divisors d.property
    have hb (n : ℕ) : |hilbertSequence (normalizedResidueHilbert d.val hd) n| ≤ 1 := by
      rw [normalizedResidueHilbert_sequence]
      exact normalizedAtom_abs_le_one d.val n hd
    rw [class_pairing_eq_mellin N _ (sequence_progression hm) hb s hs,
      paretoMellin_normalizedResidue_zero_of_zeta_zero d.val hd s hs hs1 hz, mul_zero]
  | zero =>
    have hzero (n : ℕ) : hilbertSequence 0 n = 0 := by
      change hilbertSequenceLinear (0 : ThresholdHilbert) n = _
      rw [map_zero]
      rfl
    simp only [hzero, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  | add x y hx hy ihx ihy =>
    have hseq (n : ℕ) : hilbertSequence (x + y) n =
        hilbertSequence x n + hilbertSequence y n :=
      congrFun (hilbertSequenceLinear.map_add x y) n
    simp only [hseq, Complex.ofReal_add, mul_add, Finset.sum_add_distrib,
      ihx, ihy, add_zero]
  | smul c x hx ih =>
    have hseq (n : ℕ) : hilbertSequence (c • x) n = c * hilbertSequence x n :=
      congrFun (hilbertSequenceLinear.map_smul c x) n
    simp only [hseq, Complex.ofReal_mul]
    simp_rw [mul_left_comm (classMellin N s _) (c : ℂ)]
    rw [← Finset.mul_sum, ih, mul_zero]

/-- After removing the complete multiples endpoint, the source is the same
for every legal competitor. Critical-line zeros are in the stated domain. -/
theorem error_zero_moment {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑ r : Fin N, classMellin N s r.castSucc * (error N f r.castSucc : ℂ)) =
      1 - classMellin N s (Fin.last N) := by
  have hfull : (∑ r : Fin (N + 1), classMellin N s r * (error N f r : ℂ)) = 1 := by
    have hseq (r : Fin (N + 1)) : error N f r = 1 - hilbertSequence f (r.val + 1) := by
      change hilbertSequenceLinear (hilbertOne - f) (r.val + 1) = _
      rw [map_sub]
      change hilbertSequence hilbertOne (r.val + 1) - _ = _
      rw [one_sequence_succ]
      rfl
    simp only [hseq, Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one,
      Finset.sum_sub_distrib, classMellin_sum N s hs, trial_class_pairing_zero hf s hs hs1 hz,
      sub_zero]
  rw [Fin.sum_univ_castSucc, error_multiples hf, Complex.ofReal_one, mul_one] at hfull
  exact eq_sub_of_add_eq hfull

end RiemannResearch.RH.Pareto.ResidueMellin
