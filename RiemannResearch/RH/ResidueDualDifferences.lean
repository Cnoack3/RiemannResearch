import RiemannResearch.RH.ProjectedDualColumnConcentration
import RiemannResearch.RH.ParetoCoordinateBounds

/-!
# Exact signed divisibility differences of the projected coefficient dual

Source: the signed-Abel next target in AnthropicRHBridges20260928.md.
All identities use the actual finite projected Riesz vector. The reciprocal
charge cancels from its second difference. The weighted identities preserve
the signs of every inverse-Gram coefficient and arithmetic progression sum.
No estimate of these signed discrepancies, and no RH conclusion, is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.RH.ArithmeticCumulative

/-- Physical coordinates of the actual finite projected coefficient dual. -/
def projectedDualPhysical (n d j : ℕ) : ℝ :=
  hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) j

/-- Signed reciprocal charge, retained before cancellation. -/
def projectedDualReciprocalCharge (n d : ℕ) : ℝ :=
  ∑ i : Fin n, projectedDualColumn n d i / ((i.val + 2 : ℕ) : ℝ)

/-- Signed truncated divisor sum of the actual inverse-Gram column. -/
def projectedDualDivisorSum (n d j : ℕ) : ℝ :=
  ∑ i : Fin n, projectedDualColumn n d i * divisorIndicator (i.val + 2) j

theorem projectedDual_expansion (n d : ℕ) :
    (finiteSpace n).starProjection (coefficientRiesz d) =
      ∑ i : Fin n, projectedDualColumn n d i • residueAtom i.val := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n
    ((finiteSpace n).starProjection (coefficientRiesz d))
    ((finiteSpace n).starProjection_apply_mem _)
  have hc (i : Fin n) : projectedDualColumn n d i = a i := by
    unfold projectedDualColumn
    rw [ha, coefficient_finite_sum]
  simpa only [hc] using ha

theorem projectedDualPhysical_expansion (n d j : ℕ) :
    projectedDualPhysical n d j =
      ∑ i : Fin n, projectedDualColumn n d i * residueFraction (i.val + 2) j := by
  unfold projectedDualPhysical
  rw [projectedDual_expansion]
  change hilbertSequenceLinear
    (∑ i : Fin n, projectedDualColumn n d i • residueAtom i.val) j = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change projectedDualColumn n d i * hilbertSequence (residueAtom i.val) j = _
  rw [residueAtom, normalizedResidueHilbert_sequence]

/-- At the first physical site every legal atom equals its reciprocal conductor. -/
theorem projectedDualPhysical_one (n d : ℕ) :
    projectedDualPhysical n d 1 = projectedDualReciprocalCharge n d := by
  rw [projectedDualPhysical_expansion]
  unfold projectedDualReciprocalCharge
  apply Finset.sum_congr rfl
  intro i hi
  have he : 1 < i.val + 2 := by omega
  simp only [residueFraction, Nat.mod_eq_of_lt he, Nat.cast_one]
  ring

/-- A common conductor multiple is an exact zero of the projected dual.
Thus choosing an Abel endpoint here removes its first boundary term. -/
theorem projectedDualPhysical_eq_zero_of_common_multiple (n d j : ℕ)
    (hj : ∀ i : Fin n, i.val + 2 ∣ j) : projectedDualPhysical n d j = 0 := by
  rw [projectedDualPhysical_expansion]
  apply Finset.sum_eq_zero
  intro i hi
  simp [residueFraction, Nat.mod_eq_zero_of_dvd (hj i)]

/-- Factorial endpoints are explicit simultaneous zeros of all legal atoms. -/
theorem projectedDualPhysical_factorial_mul (n d t : ℕ) :
    projectedDualPhysical n d ((n + 1).factorial * t) = 0 := by
  apply projectedDualPhysical_eq_zero_of_common_multiple
  intro i
  exact dvd_mul_of_dvd_left
    (Nat.dvd_factorial (by omega : 0 < i.val + 2)
      (by omega : i.val + 2 ≤ n + 1)) t

/-- Projection contraction bounds every fixed physical site independently of n. -/
theorem projectedDualPhysical_sq_le (n d j : ℕ) :
    projectedDualPhysical n d j ^ 2 ≤
      (j : ℝ) * ((j : ℝ) + 1) * ‖coefficientRiesz d‖ ^ 2 := by
  have h := hilbertSequence_sq_le_norm_sq
    ((finiteSpace n).starProjection (coefficientRiesz d)) j
  have hp : ‖(finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 ≤
      ‖coefficientRiesz d‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((finiteSpace n).norm_starProjection_apply_le _)
  exact h.trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- A dimension-independent bound on a genuinely signed inverse-column sum.
This does not bound its termwise absolute counterpart. -/
theorem projectedDualReciprocalCharge_sq_le (n d : ℕ) :
    projectedDualReciprocalCharge n d ^ 2 ≤ 2 * ‖coefficientRiesz d‖ ^ 2 := by
  rw [← projectedDualPhysical_one]
  have h := projectedDualPhysical_sq_le n d 1
  norm_num at h
  exact h

/-- Exact sawtooth jump obtained from the checked arithmetic primitive identity. -/
theorem residueFraction_forward_eq_divisor (e j : ℕ) (he : 0 < e) :
    residueFraction e (j + 1) - residueFraction e j =
      1 / (e : ℝ) - divisorIndicator e (j + 1) := by
  have h := cumulative_balancedDivisor e (j + 1) he
  rw [cumulative_succ, cumulative_balancedDivisor e j he] at h
  unfold balancedDivisor at h
  linarith

theorem projectedDualPhysical_forward (n d j : ℕ) :
    projectedDualPhysical n d (j + 1) - projectedDualPhysical n d j =
      projectedDualReciprocalCharge n d - projectedDualDivisorSum n d (j + 1) := by
  rw [projectedDualPhysical_expansion, projectedDualPhysical_expansion]
  unfold projectedDualReciprocalCharge projectedDualDivisorSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_sub, residueFraction_forward_eq_divisor (i.val + 2) j (by omega)]
  ring

/-- The drift cancels exactly; only adjacent signed divisor sums remain. -/
theorem projectedDualPhysical_second (n d j : ℕ) :
    projectedDualPhysical n d (j + 2) -
      2 * projectedDualPhysical n d (j + 1) + projectedDualPhysical n d j =
    projectedDualDivisorSum n d (j + 1) - projectedDualDivisorSum n d (j + 2) := by
  have h0 := projectedDualPhysical_forward n d j
  have h1 := projectedDualPhysical_forward n d (j + 1)
  simp only [Nat.add_assoc] at h1
  linarith

/-- Centered arithmetic-progression sampling; no individual term is absolutized. -/
def divisorSamplingDiscrepancy (e p M : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range M,
    A (k + 1) * (divisorIndicator e (p + k + 1) - 1 / (e : ℝ))

/-- Adjacent progression cancellation tested against the second Abel primitive. -/
def adjacentDivisorSampling (e p M : ℕ) (C : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range M,
    C (k + 1) *
      (divisorIndicator e (p + k + 1) - divisorIndicator e (p + k + 2))

/-- First Abel's signed interior is an inverse-column pairing with centered
arithmetic progression discrepancies. -/
theorem projectedDualPhysical_weighted_forward (n d p M : ℕ) (A : ℕ → ℝ) :
    (∑ k ∈ Finset.range M, A (k + 1) *
      (projectedDualPhysical n d (p + k + 1) - projectedDualPhysical n d (p + k))) =
    -(∑ i : Fin n, projectedDualColumn n d i * divisorSamplingDiscrepancy
      (i.val + 2) p M A) := by
  simp only [projectedDualPhysical_forward, projectedDualReciprocalCharge,
    projectedDualDivisorSum, divisorSamplingDiscrepancy]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Second Abel's signed interior is a pairing with adjacent progression sums. -/
theorem projectedDualPhysical_weighted_second (n d p M : ℕ) (C : ℕ → ℝ) :
    (∑ k ∈ Finset.range M, C (k + 1) *
      (projectedDualPhysical n d (p + k + 2) -
        2 * projectedDualPhysical n d (p + k + 1) + projectedDualPhysical n d (p + k))) =
    ∑ i : Fin n, projectedDualColumn n d i * adjacentDivisorSampling
      (i.val + 2) p M C := by
  simp only [projectedDualPhysical_second, projectedDualDivisorSum,
    adjacentDivisorSampling]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
