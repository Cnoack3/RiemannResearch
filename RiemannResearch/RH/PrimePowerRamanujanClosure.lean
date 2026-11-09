import RiemannResearch.RH.PrimePowerRamanujanLimits
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Full elimination of mixed conductors from the target closure

Let C be the closed span of non-prime-power Ramanujan packets with q >= 2,
and let S = I - P_C. The closed span W of S R_q over prime powers contains
S(V), where V is the original legal closure; conversely W is a subspace of V.
The exact mean-zero property gives S(1) = 1. Consequently 1 belongs to W
if and only if it belongs to V.

The correction P_C is essential. This is not a claim that the uncorrected
prime-power packets suffice, nor that the closure condition has been proved.
The RH conclusion retains membership in W as an explicit hypothesis.

Provenance: the full-conductor research agenda, PrimePowerRamanujanSchur,
PrimePowerRamanujanLimits, and the finite Ramanujan/residue span bridge.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

def fullScreening : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  1 - mixedClosure.starProjection

theorem fullScreening_packet (q : ℕ) :
    fullScreening (ramanujanPacketHilbert q) = limitScreenedPacket q := rfl

def screenedPrimeClosure : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (Set.range
    (fun q : {q : ℕ // 1 < q ∧ IsPrimePow q} => limitScreenedPacket q.val))).topologicalClosure

theorem mixed_packet_mem_closure (q : ℕ) (hq : 1 < q) (hp : ¬ IsPrimePow q) :
    ramanujanPacketHilbert q ∈ mixedClosure := by
  apply mixedSpace_window_le_closure q
  apply Submodule.subset_span
  refine ⟨⟨q, ?_⟩, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hp⟩

theorem limitScreenedPacket_eq_zero_of_not_primePow (q : ℕ)
    (hq : 1 < q) (hp : ¬ IsPrimePow q) : limitScreenedPacket q = 0 := by
  unfold limitScreenedPacket
  rw [Submodule.starProjection_eq_self_iff.mpr (mixed_packet_mem_closure q hq hp)]
  exact sub_self _

theorem fullScreening_packet_mem (q : ℕ) (hq : 1 < q) :
    fullScreening (ramanujanPacketHilbert q) ∈ screenedPrimeClosure := by
  rw [fullScreening_packet]
  by_cases hp : IsPrimePow q
  · exact (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨⟨q, hq, hp⟩, rfl⟩)
  · rw [limitScreenedPacket_eq_zero_of_not_primePow q hq hp]
    exact screenedPrimeClosure.zero_mem

theorem fullScreening_residueAtom_mem (i : ℕ) :
    fullScreening (residueAtom i) ∈ screenedPrimeClosure := by
  have hle : Submodule.span ℝ (Set.range
      (fun j : Fin (i + 1) => ramanujanPacketHilbert (j.val + 2))) ≤
      screenedPrimeClosure.comap fullScreening.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact fullScreening_packet_mem (j.val + 2) (by omega)
  rw [finitePacket_span_eq] at hle
  exact hle (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)

theorem fullScreening_closedSpace_mem {f : ThresholdHilbert} (hf : f ∈ closedSpace) :
    fullScreening f ∈ screenedPrimeClosure := by
  have hle : (Submodule.span ℝ (Set.range residueAtom)).topologicalClosure ≤
      screenedPrimeClosure.comap fullScreening.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact fullScreening_residueAtom_mem i
    · exact (show IsClosed (screenedPrimeClosure : Set ThresholdHilbert) from
        isClosed_closure).preimage fullScreening.continuous
  exact hle hf

theorem screenedPrimeClosure_le_closedSpace : screenedPrimeClosure ≤ closedSpace := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact limitScreenedPacket_mem_closedSpace q.val q.property.1
  · exact isClosed_closure

theorem fullScreening_one : fullScreening hilbertOne = hilbertOne := by
  have hmono : Monotone (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) hmono hilbertOne
  have hz (N : ℕ) : (mixedSpace (Finset.Icc 2 N)).starProjection hilbertOne = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (one_mem_mixed_orthogonal _)
  simp_rw [hz] at ht
  have he : (0 : ThresholdHilbert) = mixedClosure.starProjection hilbertOne :=
    tendsto_nhds_unique tendsto_const_nhds ht
  change hilbertOne - mixedClosure.starProjection hilbertOne = hilbertOne
  rw [← he, sub_zero]

/-- For an arbitrary input, the error after finite mixed screening is the
full-screening error plus the squared error of the mixed projection. -/
theorem finite_screened_error_eq_full_add_projection_tail
    (M : ℕ) (x : ThresholdHilbert) :
    ‖hilbertOne - (x - (mixedSpace (Finset.Icc 2 M)).starProjection x)‖ ^ 2 =
      ‖hilbertOne - fullScreening x‖ ^ 2 +
        ‖mixedClosure.starProjection x -
          (mixedSpace (Finset.Icc 2 M)).starProjection x‖ ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 M)
  have hK : K.starProjection hilbertOne = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).mpr (one_mem_mixed_orthogonal _)
  have hL : mixedClosure.starProjection hilbertOne = 0 := by
    have h := fullScreening_one
    change hilbertOne - mixedClosure.starProjection hilbertOne = hilbertOne at h
    exact sub_eq_self.mp h
  have h := nested_projection_energy K mixedClosure (mixedSpace_window_le_closure M)
    (hilbertOne - x)
  simp only [map_sub, hK, hL, zero_sub] at h
  have hleft (y : ThresholdHilbert) : hilbertOne - x - -y = hilbertOne - (x - y) := by abel
  have hright : -mixedClosure.starProjection x - -K.starProjection x =
      -(mixedClosure.starProjection x - K.starProjection x) := by abel
  rw [hleft, hleft, hright, norm_neg] at h
  exact h

/-- The complete error separates the mean defect, the covariance after
screening against the entire mixed space, and the finite projection tail. -/
theorem finite_screened_error_eq_mean_covariance_projection_tail
    (M : ℕ) (x : ThresholdHilbert) :
    ‖hilbertOne - (x - (mixedSpace (Finset.Icc 2 M)).starProjection x)‖ ^ 2 =
      (1 - inner ℝ x hilbertOne) ^ 2 +
        ‖fullScreening x - (inner ℝ x hilbertOne) • hilbertOne‖ ^ 2 +
        ‖mixedClosure.starProjection x -
          (mixedSpace (Finset.Icc 2 M)).starProjection x‖ ^ 2 := by
  have hzero : mixedClosure.starProjection hilbertOne = 0 := by
    have h := fullScreening_one
    change hilbertOne - mixedClosure.starProjection hilbertOne = hilbertOne at h
    exact sub_eq_self.mp h
  have ho := (Submodule.starProjection_apply_eq_zero_iff mixedClosure).mp hzero
  have hp := (mixedClosure.mem_orthogonal hilbertOne).mp ho _
    (mixedClosure.starProjection_apply_mem x)
  have hmean : inner ℝ (fullScreening x) hilbertOne = inner ℝ x hilbertOne := by
    change inner ℝ (x - mixedClosure.starProjection x) hilbertOne = _
    rw [inner_sub_left, hp, sub_zero]
  have he : ‖hilbertOne - fullScreening x‖ ^ 2 =
      (1 - inner ℝ x hilbertOne) ^ 2 +
        ‖fullScreening x - (inner ℝ x hilbertOne) • hilbertOne‖ ^ 2 := by
    have hmean' : inner ℝ hilbertOne (fullScreening x) = inner ℝ x hilbertOne := by
      rw [real_inner_comm, hmean]
    simp only [norm_sub_sq_real, hmean, hmean', real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq]
    ring
  rw [finite_screened_error_eq_full_add_projection_tail, he]

/-- Removing all mixed conductors loses no target information, provided the
prime-power packets are corrected by the full mixed projection. -/
theorem one_mem_screenedPrimeClosure_iff :
    hilbertOne ∈ screenedPrimeClosure ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    exact screenedPrimeClosure_le_closedSpace h
  · intro h
    simpa only [fullScreening_one] using fullScreening_closedSpace_mem h

theorem riemannHypothesis_of_one_mem_screenedPrimeClosure
    (h : hilbertOne ∈ screenedPrimeClosure) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (one_mem_screenedPrimeClosure_iff.mp h))

end RiemannResearch.RH.Pareto.PrimePowerSchur
