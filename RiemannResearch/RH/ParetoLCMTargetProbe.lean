import RiemannResearch.RH.ParetoLCMRamanujanCertificate
import RiemannResearch.Probability.ProjectionObservationLaw
import RiemannResearch.Analysis.AffineObservationProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Constant-target projection DPP on the full LCM dictionary

The Euclidean coordinates use the complete Pareto class weights and order
the classes as `1, …, L`, with the multiples class last. DPP observations
are orthonormal probes in this quotient. The unit constant-target probe
differs from the physical first-residue-class site of the integer DPP.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.SingleObservationProjection (affine_target_error_split)
open RiemannResearch.Probability.DPP

/-- Weighted evaluation at the positive representatives of the residue classes. -/
def quotientEval (N : ℕ) : ThresholdHilbert →ₗ[ℝ] EuclideanSpace ℝ (Fin (N + 1)) where
  toFun f := WithLp.toLp 2 (fun r =>
    Real.sqrt (classWeight N r) * hilbertSequence f (r.val + 1))
  map_add' f g := by
    ext r
    change Real.sqrt (classWeight N r) * hilbertSequenceLinear (f + g) (r.val + 1) =
      Real.sqrt (classWeight N r) * hilbertSequenceLinear f (r.val + 1) +
        Real.sqrt (classWeight N r) * hilbertSequenceLinear g (r.val + 1)
    rw [map_add]
    exact mul_add _ _ _
  map_smul' c f := by
    ext r
    change Real.sqrt (classWeight N r) * hilbertSequenceLinear (c • f) (r.val + 1) =
      c * (Real.sqrt (classWeight N r) * hilbertSequenceLinear f (r.val + 1))
    rw [map_smul]
    change Real.sqrt (classWeight N r) * (c * hilbertSequenceLinear f (r.val + 1)) = _
    ring

/-- The Euclidean coordinates of the physical constant function. -/
def quotientTarget (N : ℕ) : EuclideanSpace ℝ (Fin (N + 1)) := quotientEval N hilbertOne

@[simp] theorem quotientTarget_apply (N : ℕ) (r : Fin (N + 1)) :
    quotientTarget N r = Real.sqrt (classWeight N r) := by
  change Real.sqrt (classWeight N r) * hilbertSequence hilbertOne (r.val + 1) = _
  rw [hilbertOne_sequence]
  simp [zeroAnchor]

theorem quotient_error_norm_sq {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) :
    ‖quotientTarget N - quotientEval N f‖ ^ 2 = ‖hilbertOne - f‖ ^ 2 := by
  rw [quotientTarget, ← map_sub, EuclideanSpace.norm_sq_eq, error_norm_sq_eq_classes hf]
  apply Finset.sum_congr rfl
  intro r _
  change ‖Real.sqrt (classWeight N r) * error N f r‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (classWeight_pos N r).le]

theorem quotientTarget_norm_sq (N : ℕ) : ‖quotientTarget N‖ ^ 2 = 1 := by
  simpa only [map_zero, sub_zero, hilbertOne_norm_sq] using
    (quotient_error_norm_sq ((trialSpace (N + 1)).zero_mem))

/-- The target can be a coordinate of a full orthonormal basis of the quotient. -/
theorem quotientTarget_basis (N : ℕ) :
    ∃ (u : Finset (EuclideanSpace ℝ (Fin (N + 1))))
      (b : OrthonormalBasis u ℝ (EuclideanSpace ℝ (Fin (N + 1)))) (i : u),
      b i = quotientTarget N := by
  classical
  let t := quotientTarget N
  let s : Set (EuclideanSpace ℝ (Fin (N + 1))) := {t}
  have ho : Orthonormal ℝ (fun i : s => i.val) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.val = t := i.property
    have hj : j.val = t := j.property
    rw [hi, hj, real_inner_self_eq_norm_sq, quotientTarget_norm_sq,
      if_pos (Subtype.ext (hi.trans hj.symm))]
  obtain ⟨u, b, hu, hb⟩ := ho.exists_orthonormalBasis_extension
  have ht : t ∈ u := hu (by simp [s])
  exact ⟨u, b, ⟨t, ht⟩, congrFun hb _⟩

/-- The full divisor-closed legal dictionary in the weighted quotient. -/
def quotientLegalSpace (N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) :=
  (trialSpace (N + 1)).map (quotientEval N)

theorem quotientLegalSpace_eq_packetSpan (N : ℕ) :
    quotientLegalSpace N =
      synthesisSpan (fun q => quotientEval N (packetFamily (N + 1) q)) := by
  rw [quotientLegalSpace, ← packetSpan_eq_trialSpace, synthesisSpan, synthesisSpan,
    Submodule.map_span, ← Set.range_comp]
  rfl

theorem quotient_projection_eq_lcmBest (M : ℕ) :
    (quotientLegalSpace (lcmResidueIndex M)).starProjection (quotientTarget (lcmResidueIndex M)) =
      quotientEval (lcmResidueIndex M) (lcmBest M) := by
  let N := lcmResidueIndex M
  let S := quotientLegalSpace N
  let t := quotientTarget N
  change S.starProjection t = quotientEval N (lcmBest M)
  have hperiod : N + 1 = Nat.lcmUpto M := lcmResidueIndex_succ M
  have hb : lcmBest M ∈ trialSpace (N + 1) := hperiod.symm ▸ lcmBest_mem M
  have hq := affine_target_error_split S t (quotientEval N (lcmBest M))
    (Submodule.mem_map.mpr ⟨_, hb, rfl⟩)
  obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.mp (S.starProjection_apply_mem t)
  have hp := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne f
    (hperiod ▸ hf)
  change ‖hilbertOne - f‖ ^ 2 = ‖hilbertOne - lcmBest M‖ ^ 2 + ‖f - lcmBest M‖ ^ 2 at hp
  rw [← quotient_error_norm_sq hf, ← quotient_error_norm_sq hb, hfeq] at hp
  change ‖t - S.starProjection t‖ ^ 2 =
    ‖t - quotientEval N (lcmBest M)‖ ^ 2 + ‖f - lcmBest M‖ ^ 2 at hp
  have hd : ‖quotientEval N (lcmBest M) - S.starProjection t‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖f - lcmBest M‖,
      sq_nonneg ‖quotientEval N (lcmBest M) - S.starProjection t‖]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hd))).symm

theorem lcm_probe_vacancy {κ : Type*} [Fintype κ] [DecidableEq κ] (M : ℕ)
    (e : κ → EuclideanSpace ℝ (Fin (lcmResidueIndex M + 1)))
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (i : κ) (hi : e i = quotientTarget (lcmResidueIndex M)) :
    (projectionObservationLaw (quotientLegalSpace (lcmResidueIndex M)) e he).real
        {x | x i = false} = lcmError M := by
  rw [projectionObservationLaw_vacancy, hi, quotient_projection_eq_lcmBest]
  exact quotient_error_norm_sq ((lcmResidueIndex_succ M).symm ▸ lcmBest_mem M)

theorem lcmError_eq_packet_determinant (M : ℕ) :
    lcmError M =
      ((packetGram (Nat.lcmUpto M) - Matrix.vecMulVec
        (packetSource (Nat.lcmUpto M)) (packetSource (Nat.lcmUpto M))).det) /
        (packetGram (Nat.lcmUpto M)).det := by
  let H := packetGram (Nat.lcmUpto M)
  let b := packetSource (Nat.lcmUpto M)
  change ‖hilbertOne - lcmBest M‖ ^ 2 = (H - Matrix.vecMulVec b b).det / H.det
  have hH : IsUnit H.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (packetGram_posDef _).isUnit
  have hsub : H - Matrix.vecMulVec b b = H + Matrix.vecMulVec (-b) b := by
    ext i j
    simp [Matrix.vecMulVec, sub_eq_add_neg]
  rw [hsub, Matrix.det_add_outer _ hH, mul_div_cancel_left₀ _ (isUnit_iff_ne_zero.mp hH)]
  rw [lcm_error_eq_one_sub_packet_inverse]
  change 1 - dotProduct b (H⁻¹.mulVec b) = 1 + dotProduct b (H⁻¹.mulVec (-b))
  rw [Matrix.mulVec_neg, dotProduct_neg, sub_eq_add_neg]

/-- Singleton vacancy of the constant-target observation in packet coordinates. -/
theorem lcm_probe_vacancy_eq_packet_determinant {κ : Type*} [Fintype κ] [DecidableEq κ] (M : ℕ)
    (e : κ → EuclideanSpace ℝ (Fin (lcmResidueIndex M + 1)))
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (i : κ) (hi : e i = quotientTarget (lcmResidueIndex M)) :
    (projectionObservationLaw (quotientLegalSpace (lcmResidueIndex M)) e he).real
        {x | x i = false} =
      ((packetGram (Nat.lcmUpto M) - Matrix.vecMulVec
        (packetSource (Nat.lcmUpto M)) (packetSource (Nat.lcmUpto M))).det) /
        (packetGram (Nat.lcmUpto M)).det :=
  (lcm_probe_vacancy M e he i hi).trans (lcmError_eq_packet_determinant M)

end RiemannResearch.RH.Pareto.ResidueMellin
