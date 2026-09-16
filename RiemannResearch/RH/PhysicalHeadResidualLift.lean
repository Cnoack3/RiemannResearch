import RiemannResearch.Analysis.HeadTailCompression
import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.RH.FiniteTwoSeedHeadRepair

/-!
# Unconditional physical-head solvability and the actual Pareto tail minimum

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 8. The existing triangular interpolant is used at the actual budget
`M`. Thus the compressed normal equation is proved solvable, rather than
left as a domain-specific hypothesis. The resulting raw tail need not lie
in the enlarged legal budget, and no logarithmic arithmetic bound follows.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.HeadTailResidualLift

/-- The genuine physical coordinates `1,...,M`, with their Pareto weights. -/
def physicalHead (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (fun i : Fin M => hilbertAtom (i.val + 1) (by omega)))

instance physicalHead_finiteDimensional (M : ℕ) : FiniteDimensional ℝ (physicalHead M) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem physicalHead_atom_mem (M : ℕ) (i : Fin M) :
    hilbertAtom (i.val + 1) (by omega) ∈ physicalHead M :=
  Submodule.subset_span ⟨i, rfl⟩

theorem physicalHead_zero_after (M : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ physicalHead M) (k : ℕ) (hk : M ≤ k) :
    hilbertSequence f (k + 1) = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      rw [hilbertAtom_sequence]
      have hne : k ≠ i.val := by omega
      simp [hne]
  | zero =>
      change hilbertSequenceLinear (0 : ThresholdHilbert) (k + 1) = 0
      exact congrFun hilbertSequenceLinear.map_zero (k + 1)
  | add f g hf hg ihf ihg =>
      rw [hilbertSequence_add, Pi.add_apply, ihf, ihg, add_zero]
  | smul c f hf ih =>
      rw [hilbertSequence_smul, Pi.smul_apply, ih, smul_zero]

/-- Orthogonal head projection preserves every physical coordinate in the head. -/
theorem physicalHead_projection_coordinate (M : ℕ) (f : ThresholdHilbert) (i : Fin M) :
    hilbertSequence ((physicalHead M).starProjection f) (i.val + 1) =
      hilbertSequence f (i.val + 1) := by
  have h := Submodule.starProjection_inner_eq_zero f
    (hilbertAtom (i.val + 1) (by omega)) (physicalHead_atom_mem M i)
  rw [inner_sub_left, real_inner_comm _ f,
    real_inner_comm _ ((physicalHead M).starProjection f),
    hilbertAtom_inner, hilbertAtom_inner] at h
  have hw : 0 < positiveWeight (i.val + 1) := by unfold positiveWeight; positivity
  nlinarith

theorem physicalHead_projection_apply (M : ℕ) (f : ThresholdHilbert) (k : ℕ) :
    hilbertSequence ((physicalHead M).starProjection f) (k + 1) =
      if k < M then hilbertSequence f (k + 1) else 0 := by
  by_cases hk : k < M
  · simpa only [hk, if_true] using physicalHead_projection_coordinate M f ⟨k, hk⟩
  · rw [if_neg hk]
    exact physicalHead_zero_after M _ ((physicalHead M).starProjection_apply_mem f)
      k (by omega)

/-- This projection vanishes exactly when the first `M` physical coordinates do. -/
theorem physicalHead_projection_zero_iff (M : ℕ) (f : ThresholdHilbert) :
    (physicalHead M).starProjection f = 0 ↔
      ∀ i : Fin M, hilbertSequence f (i.val + 1) = 0 := by
  constructor
  · intro h i
    have hc := physicalHead_projection_coordinate M f i
    have hzseq : hilbertSequence (0 : ThresholdHilbert) = 0 :=
      hilbertSequenceLinear.map_zero
    simpa only [h, hzseq, Pi.zero_apply] using hc.symm
  · intro h
    have hz : ∀ v ∈ physicalHead M, inner ℝ f v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨i, rfl⟩ := hv
          rw [real_inner_comm, hilbertAtom_inner, h i, mul_zero]
      | zero => simp
      | add x y hx hy ihx ihy => rw [inner_add_right, ihx, ihy, add_zero]
      | smul c x hx ih => rw [real_inner_smul_right, ih, mul_zero]
    have hp := Submodule.starProjection_inner_eq_zero f
      ((physicalHead M).starProjection f) ((physicalHead M).starProjection_apply_mem f)
    rw [inner_sub_left, hz _ ((physicalHead M).starProjection_apply_mem f),
      real_inner_self_eq_norm_sq] at hp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((physicalHead M).starProjection f)]

theorem physicalHead_projection_eq_of_coordinates (M : ℕ) (f g : ThresholdHilbert)
    (h : ∀ i : Fin M, hilbertSequence f (i.val + 1) = hilbertSequence g (i.val + 1)) :
    (physicalHead M).starProjection f = (physicalHead M).starProjection g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (physicalHead_projection_zero_iff M (f - g)).mpr
  intro i
  rw [hilbertSequence_sub, Pi.sub_apply, h i, sub_self]

/-- The physical head of the actual finite legal budget is the entire head space. -/
theorem budget_physicalHead_surjective (M : ℕ) (a : ThresholdHilbert)
    (ha : a ∈ physicalHead M) :
    ∃ v : ThresholdHilbert, v ∈ budgetHilbert M ∧
      (physicalHead M).starProjection v = a := by
  refine ⟨hilbertHeadRepair M a, hilbertHeadRepair_mem M a, ?_⟩
  calc
    (physicalHead M).starProjection (hilbertHeadRepair M a) =
        (physicalHead M).starProjection a := by
      apply physicalHead_projection_eq_of_coordinates
      intro i
      exact hilbertHeadRepair_coordinate M a i.val i.isLt
    _ = a := Submodule.starProjection_eq_self_iff.mpr ha

/-- Invertibility is proved for the actual compressed head projection. -/
theorem actual_compressed_head_unique (M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ physicalHead M) :
    ∃! a : physicalHead M,
      (physicalHead M).starProjection ((budgetHilbert M).starProjection (a : ThresholdHilbert)) = x :=
  exists_unique_compressed_solution (budgetHilbert M) (physicalHead M)
    (budget_physicalHead_surjective M) x hx

/-- Any Hilbert vector splits into an old legal vector and a raw physical tail. -/
theorem budget_add_physical_tail (M : ℕ) (f : ThresholdHilbert) :
    ∃ v : ThresholdHilbert, v ∈ budgetHilbert M ∧
      ∃ z : ThresholdHilbert,
        (∀ i : Fin M, hilbertSequence z (i.val + 1) = 0) ∧ f = v + z := by
  refine ⟨hilbertHeadRepair M f, hilbertHeadRepair_mem M f,
    f - hilbertHeadRepair M f, ?_, ?_⟩
  · intro i
    rw [hilbertSequence_sub, Pi.sub_apply,
      hilbertHeadRepair_coordinate M f i.val i.isLt, sub_self]
  · abel

/-- Screening arbitrary physical tails reaches the complete old-space residual range. -/
theorem physical_tail_screening_surjective (M : ℕ) (f : ThresholdHilbert) :
    ∃ z : ThresholdHilbert,
      (∀ i : Fin M, hilbertSequence z (i.val + 1) = 0) ∧
      residual (budgetHilbert M) z = residual (budgetHilbert M) f := by
  obtain ⟨a, _, _, htail, hscreen, _, _⟩ :=
    exists_minimum_raw_lift (budgetHilbert M) (physicalHead M)
      (budget_physicalHead_surjective M) f
  exact ⟨rawLift (budgetHilbert M) f a,
    (physicalHead_projection_zero_iff M _).mp htail, hscreen⟩

/-- Every actual residual has a physical raw tail with exactly that screening. -/
theorem actual_residual_raw_tail_exists (M : ℕ) :
    ∃ z : ThresholdHilbert,
      (∀ i : Fin M, hilbertSequence z (i.val + 1) = 0) ∧
      residual (budgetHilbert M) z = error M := by
  exact physical_tail_screening_surjective M hilbertOne

/-- The attained raw-tail minimum retains the actual weighted inverse-head
term. All feasibility hypotheses for the minimizing witness are discharged. -/
theorem actual_residual_raw_tail_minimum (M : ℕ) :
    ∃ a : ThresholdHilbert, a ∈ physicalHead M ∧
      (physicalHead M).starProjection ((budgetHilbert M).starProjection a) =
        (physicalHead M).starProjection (error M) ∧
      let z := rawLift (budgetHilbert M) hilbertOne a
      (∀ i : Fin M, hilbertSequence z (i.val + 1) = 0) ∧
      residual (budgetHilbert M) z = error M ∧
      ‖z‖ ^ 2 = distance M +
        inner ℝ ((physicalHead M).starProjection (error M)) a ∧
      ∀ y : ThresholdHilbert,
        (∀ i : Fin M, hilbertSequence y (i.val + 1) = 0) →
        residual (budgetHilbert M) y = error M →
        ‖y‖ ^ 2 = ‖z‖ ^ 2 + ‖y - z‖ ^ 2 := by
  obtain ⟨a, ha, hsolve, htail, hscreen, henergy, hmin⟩ :=
    exists_minimum_raw_lift (budgetHilbert M) (physicalHead M)
      (budget_physicalHead_surjective M) hilbertOne
  refine ⟨a, ha, hsolve, (physicalHead_projection_zero_iff M _).mp htail,
    hscreen, henergy, ?_⟩
  intro y hy hyscreen
  exact hmin y ((physicalHead_projection_zero_iff M y).mpr hy) hyscreen

end RiemannResearch.RH.Pareto.CoupledResidual
