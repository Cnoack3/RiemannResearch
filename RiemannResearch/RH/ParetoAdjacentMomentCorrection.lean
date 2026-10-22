/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoOddMomentHeadNormalization
import RiemannResearch.RH.AdjacentResidueHarmonic

/-!
# Adjacent odd/even correction of the odd moment

Source: independently derived continuation of the supplied head-normalization
handoff, 2026-09-21. No novelty claim. The explicit correction preserves every
physical coordinate below its odd modulus and the reciprocal head, while
changing the odd moment by exactly one. No vanishing energy is claimed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

/-- With d=k+2, this is d (R_d-R_(d+1)) in unnormalized residues. -/
def adjacentMomentPacket (k : ℕ) : ThresholdHilbert :=
  ((k+2 : ℕ) : ℝ)^2 • tailAtom k -
    (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) • tailAtom (k+1)

theorem adjacentMomentPacket_residues (k : ℕ) :
    adjacentMomentPacket k =
      ((k+2 : ℕ) : ℝ)^2 • residueAtom k -
        (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) • residueAtom (k+1) := by
  have he : ((k+2 : ℕ) : ℝ)^2 * (1 / ((k+2 : ℕ) : ℝ)) -
      (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) *
        (1 / ((k+1+2 : ℕ) : ℝ)) = 0 := by
    push_cast
    field_simp
    <;> ring
  unfold adjacentMomentPacket tailAtom
  rw [← map_smul, ← map_smul, ← map_sub]
  change _ - (anchoredEvaluationCLM 1
    (((k+2 : ℕ) : ℝ)^2 • residueAtom k -
      (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) • residueAtom (k+1))) •
        paretoPointHilbert 0 = _
  rw [map_sub, map_smul, map_smul, residueAtom_evaluation, residueAtom_evaluation]
  simp only [smul_eq_mul, he, zero_smul, sub_zero]

theorem adjacentMomentPacket_zero_head (k j : ℕ) (hj : j < k+2) :
    hilbertSequence (adjacentMomentPacket k) j = 0 := by
  rw [adjacentMomentPacket_residues]
  change hilbertSequenceLinear (_ - _) j = 0
  rw [map_sub, map_smul, map_smul]
  change ((k+2 : ℕ) : ℝ)^2 * hilbertSequence (residueAtom k) j -
    (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) *
      hilbertSequence (residueAtom (k+1)) j = 0
  simp only [residueAtom, normalizedResidueHilbert_sequence, residueFraction,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega : j < k+1+2)]
  push_cast
  field_simp
  <;> ring

/-- The complete signed energy, retaining the odd/even cross term. -/
theorem adjacentMomentPacket_energy (k : ℕ) :
    ‖adjacentMomentPacket k‖^2 =
      ((k+2 : ℕ) : ℝ)^4 * ‖tailAtom k‖^2 +
      (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ))^2 * ‖tailAtom (k+1)‖^2 -
      2 * ((k+2 : ℕ) : ℝ)^3 * ((k+3 : ℕ) : ℝ) *
        inner ℝ (tailAtom k) (tailAtom (k+1)) := by
  rw [adjacentMomentPacket, norm_sub_sq_real, real_inner_smul_left, inner_smul_right,
    norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The correction is embedded in the actual full finite dictionary. -/
def adjacentMomentCoefficients (n k : ℕ) (hk : k+1 < n) : Fin n → ℝ :=
  Pi.single (⟨k, by omega⟩ : Fin n) (((k+2 : ℕ) : ℝ)^2) +
    Pi.single (⟨k+1, hk⟩ : Fin n)
      (-(((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)))

theorem adjacentMomentCoefficients_synthesis (n k : ℕ) (hk : k+1 < n) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (adjacentMomentCoefficients n k hk) = adjacentMomentPacket k := by
  classical
  simp [adjacentMomentCoefficients, Fintype.linearCombination_apply,
    adjacentMomentPacket, add_smul, Finset.sum_add_distrib, neg_smul,
    sub_eq_add_neg]

private theorem oddMomentHead_single_any (n : ℕ) (i : Fin n) (r : ℝ) :
    oddMomentHead n (Pi.single i r) = r / ((i.val+2 : ℕ) : ℝ) := by
  classical
  unfold oddMomentHead
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · simp

private theorem oddMomentValue_single_any (n : ℕ) (i : Fin n) (r : ℝ) :
    oddMomentValue n (Pi.single i r) =
      if 2 ∣ i.val+2 then 0 else r / ((i.val+2 : ℕ) : ℝ)^2 := by
  classical
  unfold oddMomentValue
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · simp

theorem adjacentMomentCoefficients_head (n k : ℕ) (hk : k+1 < n) :
    oddMomentHead n (adjacentMomentCoefficients n k hk) = 0 := by
  rw [adjacentMomentCoefficients, oddMomentHead_add,
    oddMomentHead_single_any, oddMomentHead_single_any]
  dsimp
  push_cast
  field_simp
  <;> ring

theorem adjacentMomentCoefficients_moment (n k : ℕ) (hk : k+1 < n)
    (ho : ¬ 2 ∣ k+2) :
    oddMomentValue n (adjacentMomentCoefficients n k hk) = 1 := by
  rw [adjacentMomentCoefficients, oddMomentValue_add,
    oddMomentValue_single_any, oddMomentValue_single_any]
  have he : 2 ∣ k+1+2 := by omega
  simp only [ho, he, ↓reduceIte, add_zero]
  exact div_self (by positivity)

/-- Actual physical sequence, including its exact integer-residue normalization. -/
theorem adjacentMomentPacket_sequence (k j : ℕ) :
    hilbertSequence (adjacentMomentPacket k) j =
      ((k+2 : ℕ) : ℝ) * adjacentResidueDifference (k+2) j := by
  rw [adjacentMomentPacket_residues]
  change hilbertSequenceLinear (_ - _) j = _
  rw [map_sub, map_smul, map_smul]
  change ((k+2 : ℕ) : ℝ)^2 * hilbertSequence (residueAtom k) j -
    (((k+2 : ℕ) : ℝ) * ((k+3 : ℕ) : ℝ)) *
      hilbertSequence (residueAtom (k+1)) j = _
  simp only [residueAtom, normalizedResidueHilbert_sequence, residueFraction,
    adjacentResidueDifference, residue]
  rw [show k+1+2 = k+2+1 by omega, show k+3 = k+2+1 by omega]
  have h₁ : ((k+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h₂ : ((k+2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The entire weighted energy, with no finite-tail substitution. -/
theorem adjacentMomentPacket_norm_eq (k : ℕ) :
    ‖adjacentMomentPacket k‖^2 = ((k+2 : ℕ) : ℝ)^2 *
      (∑' j, positiveWeight j * (adjacentResidueDifference (k+2) j)^2) := by
  rw [hilbert_norm_weighted_sq, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [adjacentMomentPacket_sequence]
  ring

/-- Exact harmonic part and literal nonnegative remainder. -/
theorem adjacentMomentPacket_harmonic_exact (k : ℕ) :
    ‖adjacentMomentPacket k‖^2 = ((k+2 : ℕ) : ℝ)^2 *
      ((harmonic (k+2) : ℝ) - ((k+2 : ℕ) : ℝ) / (((k+2 : ℕ) : ℝ)+1) +
        adjacentResidueRemainder (k+2)) := by
  rw [adjacentMomentPacket_norm_eq, adjacentResidueDifference_energy_exact _ (by omega)]

theorem adjacentMomentPacket_harmonic_upper (k : ℕ) :
    ‖adjacentMomentPacket k‖^2 ≤ ((k+2 : ℕ) : ℝ)^2 * (harmonic (k+2) : ℝ) := by
  rw [adjacentMomentPacket_norm_eq]
  exact mul_le_mul_of_nonneg_left
    (adjacentResidueDifference_energy_upper _ (by omega)) (sq_nonneg _)

theorem adjacentMomentPacket_harmonic_lower (k : ℕ) :
    ((k+2 : ℕ) : ℝ)^2 *
      ((harmonic (k+2) : ℝ) - ((k+2 : ℕ) : ℝ) / (((k+2 : ℕ) : ℝ)+1)) ≤
        ‖adjacentMomentPacket k‖^2 := by
  rw [adjacentMomentPacket_norm_eq]
  exact mul_le_mul_of_nonneg_left
    (adjacentResidueDifference_energy_lower _ (by omega)) (sq_nonneg _)


private theorem adjacent_oddMomentHead_smul (n : ℕ) (a : ℝ) (c : Fin n → ℝ) :
    oddMomentHead n (a • c) = a * oddMomentHead n c := by
  simp [oddMomentHead, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

private theorem adjacent_oddMomentValue_smul (n : ℕ) (a : ℝ) (c : Fin n → ℝ) :
    oddMomentValue n (a • c) = a * oddMomentValue n c := by
  unfold oddMomentValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Repair the odd moment using one odd modulus and its adjacent even modulus. -/
def repairOddMomentAdjacent (n k : ℕ) (hk : k+1 < n) (c : Fin n → ℝ) : Fin n → ℝ :=
  c + (1 - oddMomentValue n c) • adjacentMomentCoefficients n k hk

theorem repairOddMomentAdjacent_moment (n k : ℕ) (hk : k+1 < n)
    (ho : ¬ 2 ∣ k+2) (c : Fin n → ℝ) :
    oddMomentValue n (repairOddMomentAdjacent n k hk c) = 1 := by
  rw [repairOddMomentAdjacent, oddMomentValue_add, adjacent_oddMomentValue_smul,
    adjacentMomentCoefficients_moment n k hk ho]
  ring

theorem repairOddMomentAdjacent_head (n k : ℕ) (hk : k+1 < n) (c : Fin n → ℝ) :
    oddMomentHead n (repairOddMomentAdjacent n k hk c) = oddMomentHead n c := by
  rw [repairOddMomentAdjacent, oddMomentHead_add, adjacent_oddMomentHead_smul,
    adjacentMomentCoefficients_head]
  ring

theorem repairOddMomentAdjacent_synthesis (n k : ℕ) (hk : k+1 < n) (c : Fin n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (repairOddMomentAdjacent n k hk c) =
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c +
      (1 - oddMomentValue n c) • adjacentMomentPacket k := by
  rw [repairOddMomentAdjacent, map_add, map_smul, adjacentMomentCoefficients_synthesis]

theorem repairOddMomentAdjacent_preserves_head (n k : ℕ) (hk : k+1 < n)
    (c : Fin n → ℝ) (j : ℕ) (hj : j < k+2) :
    hilbertSequence (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (repairOddMomentAdjacent n k hk c)) j =
    hilbertSequence (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) j := by
  rw [repairOddMomentAdjacent_synthesis]
  change hilbertSequenceLinear (_ + _) j = _
  rw [map_add, map_smul]
  change _ + (1 - oddMomentValue n c) * hilbertSequence (adjacentMomentPacket k) j = _
  rw [adjacentMomentPacket_zero_head k j hj, mul_zero, add_zero]
  rfl

/-- Exact full energy of the repaired witness, including its signed cross term. -/
theorem repairOddMomentAdjacent_energy (n k : ℕ) (hk : k+1 < n) (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (repairOddMomentAdjacent n k hk c)‖^2 =
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 +
      2 * (1 - oddMomentValue n c) *
        inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
          (adjacentMomentPacket k) +
      (1 - oddMomentValue n c)^2 * ‖adjacentMomentPacket k‖^2 := by
  rw [repairOddMomentAdjacent_synthesis, norm_add_sq_real, inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Quantitative cost for changing the odd moment; all physical head values stay fixed. -/
theorem repairOddMomentAdjacent_correction_energy_le (n k : ℕ) (hk : k+1 < n)
    (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (repairOddMomentAdjacent n k hk c) -
      Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 ≤
    (1 - oddMomentValue n c)^2 * ((k+2 : ℕ) : ℝ)^2 * (harmonic (k+2) : ℝ) := by
  rw [repairOddMomentAdjacent_synthesis, add_sub_cancel_left, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (adjacentMomentPacket_harmonic_upper k) (sq_nonneg (1-oddMomentValue n c))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
