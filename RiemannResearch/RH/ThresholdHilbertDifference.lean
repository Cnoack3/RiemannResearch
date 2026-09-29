import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.ParetoPrimitiveEnergy

/-!
# The anchored difference as an actual Hilbert operator

Source: direct extension of the user's CRT primitive identity from bounded
sequences to the entire Pareto Hilbert space. The complete shift defect is
retained. Injectivity transfers a derivative limit only when the original
sequence already has a strong limit; no bounded inverse is asserted.
-/

open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem shifted_physical_square_le (f : ThresholdHilbert) (n : ℕ) :
    positiveWeight (n + 1) * hilbertSequence f n ^ 2 ≤
      positiveWeight n * hilbertSequence f n ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
      exact mul_le_mul_of_nonneg_right
        (PrimitiveEnergy.positiveWeight_succ_le (n + 1) (Nat.succ_pos n))
        (sq_nonneg _)

theorem shifted_physical_square_summable (f : ThresholdHilbert) :
    Summable (fun n => positiveWeight (n + 1) * hilbertSequence f n ^ 2) := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (shifted_physical_square_le f) (hilbertSequence_square_summable f)

theorem backwardShift_physical_square_summable (f : ThresholdHilbert) :
    Summable (fun n => positiveWeight n *
      PrimitiveEnergy.backwardShift (hilbertSequence f) n ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [PrimitiveEnergy.backwardShift, Nat.add_sub_cancel] using
    shifted_physical_square_summable f

def hilbertBackwardShift (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (PrimitiveEnergy.backwardShift (hilbertSequence f))
    (backwardShift_physical_square_summable f)

@[simp] theorem hilbertBackwardShift_sequence (f : ThresholdHilbert) :
    hilbertSequence (hilbertBackwardShift f) =
      PrimitiveEnergy.backwardShift (hilbertSequence f) := by
  apply hilbertSequence_sequenceHilbert
  simp [PrimitiveEnergy.backwardShift]

/-- Full reindexing; anchoring at zero supplies the endpoint exactly. -/
theorem hilbertBackwardShift_norm_sq (f : ThresholdHilbert) :
    ‖hilbertBackwardShift f‖ ^ 2 =
      ∑' n, positiveWeight (n + 1) * hilbertSequence f n ^ 2 := by
  rw [hilbert_norm_weighted_sq, hilbertBackwardShift_sequence,
    (backwardShift_physical_square_summable f).tsum_eq_zero_add]
  simp [PrimitiveEnergy.backwardShift, positiveWeight]

theorem hilbertBackwardShift_norm_le (f : ThresholdHilbert) :
    ‖hilbertBackwardShift f‖ ≤ ‖f‖ := by
  have hsq : ‖hilbertBackwardShift f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hilbertBackwardShift_norm_sq, hilbert_norm_weighted_sq]
    exact Summable.tsum_le_tsum (shifted_physical_square_le f)
      (shifted_physical_square_summable f) (hilbertSequence_square_summable f)
  nlinarith [norm_nonneg (hilbertBackwardShift f), norm_nonneg f]

def hilbertBackwardShiftLinear : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertBackwardShift
  map_add' f g := by
    apply hilbertSequence_injective
    simp only [hilbertBackwardShift_sequence, hilbertSequence_add]
    rfl
  map_smul' a f := by
    apply hilbertSequence_injective
    simp only [hilbertBackwardShift_sequence, hilbertSequence_smul]
    rfl

def hilbertBackwardShiftContinuous : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertBackwardShiftLinear.mkContinuous 1 (fun f => by
    simpa only [one_mul, hilbertBackwardShiftLinear, LinearMap.coe_mk, AddHom.coe_mk] using hilbertBackwardShift_norm_le f)

@[simp] theorem hilbertBackwardShiftContinuous_apply (f : ThresholdHilbert) :
    hilbertBackwardShiftContinuous f = hilbertBackwardShift f := rfl

/-- The actual anchored derivative, including its value at the first site. -/
def hilbertDifference : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert - hilbertBackwardShiftContinuous

@[simp] theorem hilbertDifference_apply (f : ThresholdHilbert) :
    hilbertDifference f = f - hilbertBackwardShift f := rfl

@[simp] theorem hilbertDifference_sequence (f : ThresholdHilbert) :
    hilbertSequence (hilbertDifference f) =
      PrimitiveEnergy.difference (hilbertSequence f) := by
  change hilbertSequenceLinear (f - hilbertBackwardShift f) = _
  rw [map_sub]
  change hilbertSequence f - hilbertSequence (hilbertBackwardShift f) = _
  rw [hilbertBackwardShift_sequence]
  rfl

/-- The first-site boundary survives differentiation of the anchored target. -/
@[simp] theorem hilbertDifference_hilbertOne :
    hilbertDifference hilbertOne = hilbertAtom 1 (by decide) := by
  apply hilbertSequence_injective
  rw [hilbertDifference_sequence, hilbertOne_sequence, hilbertAtom_sequence]
  funext n
  cases n with
  | zero => simp [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, zeroAnchor]
  | succ n =>
      cases n with
      | zero => norm_num [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, zeroAnchor]
      | succ n => simp [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, zeroAnchor]

theorem hilbertDifference_norm_le (f : ThresholdHilbert) :
    ‖hilbertDifference f‖ ≤ 2 * ‖f‖ := by
  rw [hilbertDifference_apply]
  calc
    ‖f - hilbertBackwardShift f‖ ≤ ‖f‖ + ‖hilbertBackwardShift f‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith [hilbertBackwardShift_norm_le f]

theorem hilbertDifference_opNorm_le : ‖hilbertDifference‖ ≤ 2 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hilbertDifference_norm_le

theorem hilbertDifference_injective : Function.Injective hilbertDifference := by
  intro f g h
  apply hilbertSequence_injective
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
      have hc := congrFun (congrArg hilbertSequence h) (n + 1)
      simp only [hilbertDifference_sequence] at hc
      change hilbertSequence f (n + 1) - hilbertSequence f n =
        hilbertSequence g (n + 1) - hilbertSequence g n at hc
      linarith

/-- The complete shift defect converges for every Hilbert vector. -/
theorem hilbert_shiftDefect_summable (f : ThresholdHilbert) :
    Summable (fun n => (positiveWeight n - positiveWeight (n + 1)) *
      (hilbertSequence f n * hilbertSequence f n)) := by
  simpa only [sub_mul, ← pow_two] using
    (hilbertSequence_square_summable f).sub (shifted_physical_square_summable f)

/-- The exact energy defect, now without any bounded-sequence hypothesis. -/
theorem hilbert_norm_sub_backwardShift (f : ThresholdHilbert) :
    ‖f‖ ^ 2 - ‖hilbertBackwardShift f‖ ^ 2 =
      PrimitiveEnergy.shiftDefect (hilbertSequence f) := by
  rw [hilbert_norm_weighted_sq, hilbertBackwardShift_norm_sq]
  unfold PrimitiveEnergy.shiftDefect
  simp only [sub_mul, ← pow_two]
  exact ((hilbertSequence_square_summable f).tsum_sub
    (shifted_physical_square_summable f)).symm

/-- All symmetric and shift-defect energy remains in the exact identity. -/
theorem hilbert_full_primitive_energy_identity (f : ThresholdHilbert) :
    4 * ‖f‖ ^ 2 = ‖hilbertDifference f‖ ^ 2 +
      ‖f + hilbertBackwardShift f‖ ^ 2 +
      2 * PrimitiveEnergy.shiftDefect (hilbertSequence f) := by
  have hp := parallelogram_law_with_norm ℝ f (hilbertBackwardShift f)
  have hd := hilbert_norm_sub_backwardShift f
  rw [hilbertDifference_apply]
  nlinarith

/-- An injective derivative identifies an existing strong limit. This does
not infer primitive convergence from derivative convergence alone. -/
theorem hilbertDifference_tendsto_iff_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot]
    {f : α → ThresholdHilbert} {u v : ThresholdHilbert}
    (hf : Tendsto f l (𝓝 u)) :
    Tendsto (fun n => hilbertDifference (f n)) l (𝓝 (hilbertDifference v)) ↔ u = v := by
  constructor
  · intro hd
    apply hilbertDifference_injective
    exact tendsto_nhds_unique
      (hilbertDifference.continuous.continuousAt.tendsto.comp hf) hd
  · rintro rfl
    exact hilbertDifference.continuous.continuousAt.tendsto.comp hf

end
end RiemannResearch.RH.Pareto
