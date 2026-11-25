import RiemannResearch.RH.PhysicalHeadProductSnake
import RiemannResearch.RH.PhysicalHeadMixedInterpolation
import RiemannResearch.RH.CenteredMeanSnake
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Positive physical sequences as the cokernel of the mixed difference operator

The negative partial sum of a mixed tower cochain stabilizes at each physical
coordinate. Coboundaries decode to actual mixed Hilbert sequences. Arbitrary
physical sequences have finite-head interpolants, giving an algebraic quotient
without closing the space of realizable mixed sequences. The original centered
boundary maps injectively into this quotient with its original sign.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSequenceCokernel

open CoefficientStabilization CenteredMeanSnake CenteredMeanSnake.PhysicalHeadSections
open PhysicalHeadStageAlgebra AffineHeadTower

/-- Coordinate i records the physical value at positive integer i + 1. -/
def readout : ThresholdHilbert →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun i => (physicalEvaluationCLM i).toLinearMap

theorem readout_injective : Function.Injective readout := by
  intro x y h
  apply hilbertSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ i =>
    have hi := congrFun h i
    change physicalEvaluationCLM i x = physicalEvaluationCLM i y at hi
    simpa only [physicalEvaluationCLM_apply] using hi

/-- Actual mixed sequences, with their algebraic image and no coordinatewise closure. -/
def actualMixedSequences : Submodule ℝ (ℕ → ℝ) :=
  LinearMap.range (readout.comp mixedClosure.subtype)

abbrev SequenceQuotient := (ℕ → ℝ) ⧸ actualMixedSequences

private def underlying (N : ℕ) : (stageMean N).ker →ₗ[ℝ] ThresholdHilbert :=
  closedSpace.subtype.comp ((headCompatible N).subtype.comp (stageMean N).ker.subtype)

private theorem underlying_mem (N : ℕ) (x : (stageMean N).ker) :
    underlying N x ∈ mixedClosure :=
  ((mem_stageMean_ker_iff N x.val).mp x.property).1

private theorem underlying_vanishes (N : ℕ) (x : (stageMean N).ker) (i : ℕ) (hi : i < N) :
    physicalEvaluationCLM i (underlying N x) = 0 := by
  have hh := ((mem_stageMean_ker_iff N x.val).mp x.property).2
  have he := congrArg (fun v : ThresholdHilbert => hilbertSequenceLinear v (i + 1)) hh
  change hilbertSequence (compactHead N (underlying N x)) (i + 1) =
    hilbertSequenceLinear 0 (i + 1) at he
  rw [compactHead_sequence, if_pos (show i + 1 ≤ N by omega), map_zero] at he
  simpa only [physicalEvaluationCLM_apply, Pi.zero_apply] using he

private def ofVanishing (N : ℕ) (x : ThresholdHilbert) (hm : x ∈ mixedClosure)
    (hh : ∀ i < N, physicalEvaluationCLM i x = 0) : (stageMean N).ker := by
  have hV := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero x).mp hm).1
  have h0 := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero x).mp hm).2
  let v : closedSpace := ⟨x, hV⟩
  have hc : compactHead N x = 0 := by
    calc
      compactHead N x = compactHead N (0 : ThresholdHilbert) := by
        apply PhysicalHeadMixedInterpolation.compactHead_eq_of_headRestriction_eq
        funext i
        rw [map_zero]
        simpa only [TwoSeedExactHeadEnergy.headRestriction_apply, physicalEvaluationCLM_apply,
          Pi.zero_apply] using hh i.val i.isLt
      _ = 0 := (compactHeadLinear N).map_zero
  have hL : v ∈ headCompatible N := (mem_headCompatible_iff N v).mpr (by
    change compactHead N x = inner ℝ x hilbertOne • compactHead N hilbertOne
    rw [h0, zero_smul, hc])
  exact ⟨⟨v, hL⟩, h0⟩

/-- Sum inside the ambient Hilbert space of the first N entries of a tower cochain. -/
def partialKernelSum : (N : ℕ) → KernelSeq →ₗ[ℝ] ThresholdHilbert
  | 0 => 0
  | N + 1 => partialKernelSum N +
      (underlying N).comp (LinearMap.proj N : KernelSeq →ₗ[ℝ] (stageMean N).ker)

private theorem partial_succ (a : KernelSeq) (N : ℕ) :
    partialKernelSum (N + 1) a = partialKernelSum N a + underlying N (a N) := rfl

private theorem partial_mem (a : KernelSeq) (N : ℕ) : partialKernelSum N a ∈ mixedClosure := by
  induction N with
  | zero => exact mixedClosure.zero_mem
  | succ N ih => exact mixedClosure.add_mem ih (underlying_mem N _)

/-- Realize the algebraic stage kernel inside the mixed Hilbert space. -/
def kernelToMixed (N : ℕ) : (stageMean N).ker →ₗ[ℝ] mixedClosure :=
  (underlying N).codRestrict _ (underlying_mem N)

theorem kernelToMixed_mem (N : ℕ) (x : (stageMean N).ker) :
    (kernelToMixed N x : ThresholdHilbert) ∈ kernel N :=
  (mem_kernel N).mpr ⟨underlying_mem N x, underlying_vanishes N x⟩

/-- An element of the physical kernel gives an element of the stage-mean kernel. -/
def kernelOfMixed (N : ℕ) (m : mixedClosure) (h : (m : ThresholdHilbert) ∈ kernel N) :
    (stageMean N).ker := ofVanishing N m m.property ((mem_kernel N).mp h).2

@[simp] theorem kernelToMixed_ofMixed (N : ℕ) (m : mixedClosure)
    (h : (m : ThresholdHilbert) ∈ kernel N) : kernelToMixed N (kernelOfMixed N m h) = m := rfl

theorem kernelToMixed_injective (N : ℕ) : Function.Injective (kernelToMixed N) := by
  intro x y h
  have hv := congrArg (fun m : mixedClosure => (m : ThresholdHilbert)) h
  exact Subtype.ext (Subtype.ext (Subtype.ext hv))

/-- Finite partial sums of tower cochains in the mixed Hilbert space. -/
def partialMixed (N : ℕ) : KernelSeq →ₗ[ℝ] mixedClosure :=
  (partialKernelSum N).codRestrict _ (fun a => partial_mem a N)

theorem partialMixed_succ (a : KernelSeq) (N : ℕ) :
    partialMixed (N + 1) a = partialMixed N a + kernelToMixed N (a N) := rfl

/-- The minus sign corresponds to the differential given by next minus current. -/
def decode : KernelSeq →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun i => -((physicalEvaluationCLM i).toLinearMap.comp (partialKernelSum (i + 1)))

theorem decode_apply (a : KernelSeq) (i : ℕ) :
    decode a i = -physicalEvaluationCLM i (partialKernelSum (i + 1) a) := rfl

private theorem partial_stable (a : KernelSeq) (i N : ℕ) (hN : i + 1 ≤ N) :
    physicalEvaluationCLM i (partialKernelSum N a) =
      physicalEvaluationCLM i (partialKernelSum (i + 1) a) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [partial_succ, map_add, underlying_vanishes k (a k) i (by omega), add_zero, ih]

private theorem partial_diff (w : KernelSeq) (N : ℕ) :
    partialKernelSum N (kernelDiff w) = underlying N (w N) - underlying 0 (w 0) := by
  induction N with
  | zero => simp [partialKernelSum]
  | succ N ih =>
    rw [partial_succ, ih]
    change _ + (underlying (N + 1) (w (N + 1)) - underlying N (w N)) = _
    abel

theorem partialMixed_diff (w : KernelSeq) (N : ℕ) :
    partialMixed N (kernelDiff w) = kernelToMixed N (w N) - kernelToMixed 0 (w 0) :=
  Subtype.ext (partial_diff w N)

theorem decode_diff (w : KernelSeq) : decode (kernelDiff w) = readout (underlying 0 (w 0)) := by
  funext i
  rw [decode_apply, partial_diff, map_sub, underlying_vanishes _ _ i (Nat.lt_succ_self _),
    zero_sub, neg_neg]
  rfl

private theorem decode_exact (a : KernelSeq) :
    decode a ∈ actualMixedSequences ↔ a ∈ LinearMap.range kernelDiff := by
  constructor
  · rintro ⟨m, hm⟩
    have hs (N : ℕ) (i : ℕ) (hi : i < N) :
        physicalEvaluationCLM i (m.val + partialKernelSum N a) = 0 := by
      have he := congrFun hm i
      change physicalEvaluationCLM i m.val =
        -physicalEvaluationCLM i (partialKernelSum (i + 1) a) at he
      rw [map_add, partial_stable a i N (by omega), he, neg_add_cancel]
    let w : KernelSeq := fun N => ofVanishing N (m.val + partialKernelSum N a)
      (mixedClosure.add_mem m.property (partial_mem a N)) (hs N)
    refine ⟨w, ?_⟩
    funext N
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (m.val + partialKernelSum (N + 1) a) - (m.val + partialKernelSum N a) =
      underlying N (a N)
    rw [partial_succ]
    abel
  · rintro ⟨w, rfl⟩
    exact ⟨⟨underlying 0 (w 0), underlying_mem 0 _⟩, (decode_diff w).symm⟩

private theorem interpolate (s : ℕ → ℝ) (N : ℕ) :
    ∃ m ∈ mixedClosure, ∀ i < N, physicalEvaluationCLM i m = -s i := by
  obtain ⟨B, m, hB, he⟩ := exists_mixed_exact_head (fun k => -s (k - 1)) N
  refine ⟨m, mixedSpace_window_le_closure B hB, fun i hi => ?_⟩
  rw [physicalEvaluationCLM_apply, he _ (Nat.succ_pos _) (by omega)]
  simp

theorem decode_surjective : Function.Surjective decode := by
  intro s
  choose x hM hx using interpolate s
  let z : ℕ → ThresholdHilbert := fun N => if N = 0 then 0 else x N
  have hz0 : z 0 = 0 := by simp [z]
  have hzM (N : ℕ) : z N ∈ mixedClosure := by
    by_cases h : N = 0 <;> simp only [z, h, ite_true, ite_false]
    · exact mixedClosure.zero_mem
    · exact hM N
  have hhead (N i : ℕ) (hi : i < N) : physicalEvaluationCLM i (z N) = -s i := by
    simpa only [z, if_neg (show N ≠ 0 by omega)] using hx N i hi
  let a : KernelSeq := fun N => ofVanishing N (z (N + 1) - z N)
    (mixedClosure.sub_mem (hzM _) (hzM _)) (fun i hi => by
      rw [map_sub, hhead _ _ (by omega), hhead _ _ hi, sub_self])
  have hsum (N : ℕ) : partialKernelSum N a = z N := by
    induction N with
    | zero => exact hz0.symm
    | succ N ih =>
      rw [partial_succ, ih]
      change z N + (z (N + 1) - z N) = z (N + 1)
      abel
  refine ⟨a, funext fun i => ?_⟩
  rw [decode_apply, hsum, hhead _ _ (Nat.lt_succ_self i), neg_neg]

private def quotientDecode : KernelSeq →ₗ[ℝ] SequenceQuotient :=
  actualMixedSequences.mkQ.comp decode

private theorem quotientDecode_ker : LinearMap.range kernelDiff = quotientDecode.ker := by
  ext x
  change x ∈ LinearMap.range kernelDiff ↔ (Submodule.Quotient.mk (decode x) : SequenceQuotient) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact (decode_exact x).symm

/-- The derived-limit cokernel has a concrete realization by positive physical sequences. -/
def physicalCokernelEquiv : KernelCokernel ≃ₗ[ℝ] SequenceQuotient :=
  (Submodule.quotEquivOfEq _ _ quotientDecode_ker).trans
    (quotientDecode.quotKerEquivOfSurjective
      (actualMixedSequences.mkQ_surjective.comp decode_surjective))

@[simp] theorem physicalCokernelEquiv_mk (a : KernelSeq) :
    physicalCokernelEquiv ((LinearMap.range kernelDiff).mkQ a) =
      actualMixedSequences.mkQ (decode a) := rfl

private def ambientDecode : meanZero →ₗ[ℝ] SequenceQuotient :=
  actualMixedSequences.mkQ.comp (readout.comp meanZero.subtype)

private theorem ambientDecode_ker : mixedInMeanZero = ambientDecode.ker := by
  ext x
  change x.val ∈ mixedClosure ↔ (Submodule.Quotient.mk (readout x.val) : SequenceQuotient) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    exact ⟨⟨x.val, h⟩, rfl⟩
  · rintro ⟨m, h⟩
    exact readout_injective h ▸ m.property

private def ambientToRange : BoundaryTarget ≃ₗ[ℝ] LinearMap.range ambientDecode :=
  (Submodule.quotEquivOfEq _ _ ambientDecode_ker).trans ambientDecode.quotKerEquivRange

/-- The ambient centered quotient embeds in the algebraic first derived limit. -/
def ambientIntoCokernel : BoundaryTarget →ₗ[ℝ] KernelCokernel :=
  physicalCokernelEquiv.symm.toLinearMap.comp
    (ambientDecode.range.subtype.comp ambientToRange.toLinearMap)

theorem ambientIntoCokernel_injective : Function.Injective ambientIntoCokernel :=
  physicalCokernelEquiv.symm.injective.comp (Subtype.val_injective.comp ambientToRange.injective)

private theorem partial_unitCarries (N : ℕ) :
    partialKernelSum N unitCarries = patch N - normalizedScreenedTwo := by
  induction N with
  | zero => simp [partialKernelSum, patch]
  | succ N ih =>
    rw [partial_succ, ih]
    change _ + (patch (N + 1) - patch N) = _
    abel

theorem decode_unitCarries : decode unitCarries = readout (defect : ThresholdHilbert) := by
  funext i
  rw [decode_apply, partial_unitCarries, map_sub]
  change -(physicalEvaluationCLM i (patch (i + 1)) -
    physicalEvaluationCLM i normalizedScreenedTwo) =
    physicalEvaluationCLM i (normalizedScreenedTwo - hilbertOne)
  rw [map_sub, (patch_spec (i + 1)).1.2.2 i (Nat.lt_succ_self i)]
  have he : physicalEvaluationCLM i hilbertOne = 1 := by
    rw [physicalEvaluationCLM_apply, hilbertOne_sequence]
    simp [zeroAnchor]
  rw [he]
  ring

/-- The infinite connecting morphism restricts to the original centered boundary. -/
theorem ambientIntoCokernel_boundary :
    ambientIntoCokernel.comp boundary.toLinearMap = productSnake := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply]
  change ambientIntoCokernel (boundary a) = productSnake a
  rw [boundary_apply, map_smul]
  have h1 : ambientIntoCokernel (mixedInMeanZero.mkQ defect) = productSnake 1 := by
    apply physicalCokernelEquiv.injective
    change physicalCokernelEquiv (physicalCokernelEquiv.symm
      (actualMixedSequences.mkQ (readout defect.val))) = _
    rw [LinearEquiv.apply_symm_apply, productSnake_one, physicalCokernelEquiv_mk,
      decode_unitCarries]
  calc
    _ = a • productSnake 1 := congrArg (fun z : KernelCokernel => a • z) h1
    _ = productSnake a := by
      simpa only [smul_eq_mul, mul_one] using (productSnake.map_smul a (1 : ℝ)).symm

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSequenceCokernel
