import RiemannResearch.RH.OddCarryJointHead
import RiemannResearch.Analysis.FiniteHilbertGramProjection

/-!
# Hilbert joint heads and actual head-preserving corrections

Source: user-provided RH_Dyadic_Block_CRT_Energy_and_Mobius_Obstruction_2026-09-20.md,
Sections 3, 6, and 7 (statements and finite inverse-Gram proof strategy).
All vectors below are actual weighted residue vectors. No convergence or
inverse provider is introduced as an assumption.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The unscaled positive-modulus residue in the actual Hilbert space.
At modulus zero this definition is zero and is not identified with `residue 0`. -/
def positiveResidueHilbert (d : ℕ) : ThresholdHilbert :=
  if hd : 0 < d then (d : ℝ) • normalizedResidueHilbert d hd else 0

theorem positiveResidueHilbert_sequence (d : ℕ) (hd : 0 < d) :
    hilbertSequence (positiveResidueHilbert d) = residue d := by
  rw [positiveResidueHilbert, dif_pos hd, hilbertSequence_smul,
    normalizedResidueHilbert_sequence]
  funext n
  change (d : ℝ) * (((n % d : ℕ) : ℝ) / d) = ((n % d : ℕ) : ℝ)
  have hdR : (d : ℝ) ≠ 0 := by positivity
  field_simp

theorem positiveResidueHilbert_mem (d : ℕ) :
    positiveResidueHilbert d ∈ closedSpace := by
  unfold positiveResidueHilbert
  split_ifs with hd
  · exact closedSpace.smul_mem _ (normalizedResidue_mem_closedSpace d hd)
  · exact closedSpace.zero_mem

def jointHeadHilbert (f : ℕ → ℝ) (N : ℕ) : ThresholdHilbert :=
  ∑ m ∈ Finset.Icc 1 N, (mobiusDifference m f / (m : ℝ)) •
    (positiveResidueHilbert (N+1) - positiveResidueHilbert m)

theorem jointHeadHilbert_sequence (f : ℕ → ℝ) (N : ℕ) :
    hilbertSequence (jointHeadHilbert f N) = mobiusJointHead f N := by
  change hilbertSequenceLinear (∑ m ∈ Finset.Icc 1 N, _) = _
  rw [map_sum]
  funext n
  simp only [Finset.sum_apply]
  unfold mobiusJointHead
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_smul, map_sub]
  change (mobiusDifference m f / (m : ℝ)) *
    (hilbertSequence (positiveResidueHilbert (N+1)) n -
      hilbertSequence (positiveResidueHilbert m) n) = _
  rw [positiveResidueHilbert_sequence _ (by omega),
    positiveResidueHilbert_sequence _ (by have := (Finset.mem_Icc.mp hm).1; omega)]

theorem jointHeadHilbert_mem (f : ℕ → ℝ) (N : ℕ) :
    jointHeadHilbert f N ∈ closedSpace := by
  apply Submodule.sum_mem
  intro m hm
  exact closedSpace.smul_mem _
    (closedSpace.sub_mem (positiveResidueHilbert_mem _) (positiveResidueHilbert_mem _))

theorem jointHeadHilbert_exact (f : ℕ → ℝ) (N : ℕ) (hf : f 0 = 0)
    (n : ℕ) (hn : n ≤ N) :
    hilbertSequence (jointHeadHilbert f N) n = f n := by
  rw [jointHeadHilbert_sequence]
  exact mobiusJointHead_exact f N hf n hn

/-- Moduli `N+2+i` give every larger-conductor difference with the anchor. -/
def headNullHilbert (N i : ℕ) : ThresholdHilbert :=
  positiveResidueHilbert (N+2+i) - positiveResidueHilbert (N+1)

theorem headNullHilbert_sequence (N i : ℕ) :
    hilbertSequence (headNullHilbert N i) =
      fun n => residue (N+2+i) n - residue (N+1) n := by
  change hilbertSequenceLinear (_ - _) = _
  rw [map_sub]
  change hilbertSequence (positiveResidueHilbert (N+2+i)) -
    hilbertSequence (positiveResidueHilbert (N+1)) = _
  rw [positiveResidueHilbert_sequence _ (by omega),
    positiveResidueHilbert_sequence _ (by omega)]
  rfl

theorem headNullHilbert_mem (N i : ℕ) : headNullHilbert N i ∈ closedSpace :=
  closedSpace.sub_mem (positiveResidueHilbert_mem _) (positiveResidueHilbert_mem _)

theorem headNullHilbert_head (N i n : ℕ) (hn : n ≤ N) :
    hilbertSequence (headNullHilbert N i) n = 0 := by
  rw [headNullHilbert_sequence]
  simp [residue, Nat.mod_eq_of_lt (show n < N+2+i by omega),
    Nat.mod_eq_of_lt (show n < N+1 by omega)]

theorem headNullHilbert_charge (N i j : ℕ) :
    mobiusDifference (N+2+i) (hilbertSequence (headNullHilbert N j)) =
      if i = j then -((N+2+i : ℕ) : ℝ) else 0 := by
  rw [headNullHilbert_sequence, mobiusDifference_sub_function,
    mobiusDifference_residue_initial _ _ (by omega),
    mobiusDifference_residue_initial _ _ (by omega)]
  have hne : N+2+i ≠ 1 := by omega
  have hne' : N+2+i ≠ N+1 := by omega
  have he : N+2+i = N+2+j ↔ i = j := by omega
  simp only [if_neg hne, if_neg hne', he, sub_zero]
  split_ifs with h
  · subst j; ring
  · ring

/-- Independence of the actual correction family, by its exact Möbius charges. -/
theorem headNullHilbert_independent (N : ℕ) : LinearIndependent ℝ (headNullHilbert N) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hseq : (fun n => ∑ j ∈ s, c j * hilbertSequence (headNullHilbert N j) n) = 0 := by
    have h := congrArg hilbertSequenceLinear hc
    rw [map_sum, map_zero] at h
    funext n
    have hn := congrFun h n
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hn
    change (∑ j ∈ s, c j * hilbertSequence (headNullHilbert N j) n) = 0 at hn
    exact hn
  have h := congrArg (mobiusDifference (N+2+i)) hseq
  rw [mobiusDifference_sum] at h
  simp only [headNullHilbert_charge] at h
  have hzero : mobiusDifference (N+2+i) (0 : ℕ → ℝ) = 0 := by simp [mobiusDifference]
  rw [hzero] at h
  have hsum : (∑ j ∈ s, c j * (if i = j then -((N+2+i : ℕ) : ℝ) else 0)) =
      c i * -((N+2+i : ℕ) : ℝ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [Ne.symm hji]
    · exact fun hnot => (hnot hi).elim
  rw [hsum] at h
  have hnz : -((N+2+i : ℕ) : ℝ) ≠ 0 := by
    have hp : (0 : ℝ) < ((N+2+i : ℕ) : ℝ) := by positivity
    linarith
  exact (mul_eq_zero.mp h).resolve_right hnz

theorem finiteHeadNull_independent (N L : ℕ) :
    LinearIndependent ℝ (fun i : Fin L => headNullHilbert N i.val) :=
  (headNullHilbert_independent N).comp Fin.val Fin.val_injective

/-- Genuine inverse-Gram coefficients for the complete signed correction. -/
def headCorrectionCoefficients (N L : ℕ) (f : ThresholdHilbert) : Fin L → ℝ :=
  inverseCoeff (finiteHeadNull_independent N L) f

def headCorrection (N L : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  Fintype.linearCombination ℝ (fun i : Fin L => headNullHilbert N i.val)
    (headCorrectionCoefficients N L f)

theorem headCorrection_mem (N L : ℕ) (f : ThresholdHilbert) :
    headCorrection N L f ∈ closedSpace := by
  unfold headCorrection
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  exact closedSpace.smul_mem _ (headNullHilbert_mem _ _)

theorem headCorrection_head (N L : ℕ) (f : ThresholdHilbert) (n : ℕ) (hn : n ≤ N) :
    hilbertSequence (headCorrection N L f) n = 0 := by
  unfold headCorrection
  rw [Fintype.linearCombination_apply]
  change (hilbertSequenceLinear (∑ i, _)) n = 0
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i : Fin L, headCorrectionCoefficients N L f i *
    hilbertSequence (headNullHilbert N i.val) n) = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [headNullHilbert_head N i.val n hn, mul_zero]

/-- No inverse assumption: the full energy equals the actual signed Schur remainder. -/
theorem headCorrection_energy (N L : ℕ) (f : ThresholdHilbert) :
    ‖f - headCorrection N L f‖ ^ 2 = ‖f‖ ^ 2 -
      ∑ i : Fin L, headCorrectionCoefficients N L f i *
        inner ℝ (headNullHilbert N i.val) f :=
  residual_schur_value (finiteHeadNull_independent N L) f

theorem headCorrection_minimizes (N L : ℕ) (f : ThresholdHilbert) (c : Fin L → ℝ) :
    ‖f - headCorrection N L f‖ ^ 2 ≤
      ‖f - Fintype.linearCombination ℝ (fun i : Fin L => headNullHilbert N i.val) c‖ ^ 2 :=
  residual_minimizes (finiteHeadNull_independent N L) f c

end RiemannResearch.RH.Pareto
