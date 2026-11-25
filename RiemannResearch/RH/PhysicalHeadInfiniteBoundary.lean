import RiemannResearch.RH.PhysicalHeadProductSnake
import RiemannResearch.RH.CenteredMeanSquarefreeConverse

/-! # The infinite physical-head snake and its finite quotient energies

A coherent mean-one family for the literal inclusions is one legal vector on
every physical head, hence the ambient constant. The algebraic product-snake
class consequently vanishes exactly when the adjacent Hilbert quotient
energies are summable. The finite identity retains every squared norm.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra

open CoefficientStabilization AffineHeadTower CenteredMeanSnake
open CenteredMeanSnake.PhysicalHeadSections

/-- Coherence for the literal inclusions fixes the underlying legal vector. -/
theorem coherent_stage_values_constant (x : StageSeq) (hx : stageDiff x = 0) (n : ℕ) :
    (x n).val = (x 0).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h := congrFun hx n
      change stageInclusion (Nat.le_succ n) (x (n + 1)) - x n = 0 at h
      exact (congrArg (fun z : headCompatible n => z.val) (sub_eq_zero.mp h)).trans ih

theorem coherent_stage_value_eq_mean (x : stageDiff.ker) (n : ℕ) :
    ((x.val n).val : ThresholdHilbert) = coherentMean x • hilbertOne := by
  have hc : (x.val 0).val ∈ legalConstants := by
    rw [← iInf_headCompatible_eq_legalConstants, Submodule.mem_iInf]
    intro k
    rw [← coherent_stage_values_constant x.val x.property k]
    exact (x.val k).property
  change ((x.val 0).val : ThresholdHilbert) ∈ Submodule.span ℝ {hilbertOne} at hc
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hc
  have hm : coherentMean x = s := by
    change inner ℝ ((x.val 0).val : ThresholdHilbert) hilbertOne = s
    rw [← hs, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, mul_one]
  rw [coherent_stage_values_constant x.val x.property n, hm]
  exact hs.symm

theorem coherentMean_injective : Function.Injective coherentMean := by
  intro x y h
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Subtype.ext
  rw [coherent_stage_value_eq_mean x n, coherent_stage_value_eq_mean y n, h]

theorem coherent_unit_value_eq_one (x : StageSeq) (hx : stageDiff x = 0)
    (hm : ∀ n, stageMean n (x n) = 1) :
    ((x 0).val : ThresholdHilbert) = hilbertOne := by
  let z : stageDiff.ker := ⟨x, hx⟩
  have he : coherentMean z = 1 := hm 0
  simpa only [he, one_smul] using coherent_stage_value_eq_mean z 0

/-- A class-zero lift is the actual constant in the legal Hilbert space. -/
theorem productSnake_one_eq_zero_iff_one_mem :
    productSnake 1 = 0 ↔ hilbertOne ∈ closedSpace := by
  rw [productSnake_one_eq_zero_iff_coherent]
  constructor
  · rintro ⟨x, hx, hm⟩
    rw [← coherent_unit_value_eq_one x hx hm]
    exact (x 0).val.property
  · intro he
    let v : closedSpace := ⟨hilbertOne, he⟩
    have hm : legalPacketMean v = 1 := by
      change inner ℝ hilbertOne hilbertOne = 1
      rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
    have hv (n : ℕ) : v ∈ headCompatible n := by
      apply (mem_headCompatible_iff n v).mpr
      rw [hm, one_smul]
    let x : StageSeq := fun n => ⟨v, hv n⟩
    refine ⟨x, ?_, fun _ => hm⟩
    funext n
    change stageInclusion (Nat.le_succ n) (x (n + 1)) - x n = 0
    apply sub_eq_zero.mpr
    exact Subtype.ext rfl

theorem productSnake_one_eq_zero_iff_centered_boundary :
    productSnake 1 = 0 ↔ CenteredMeanSnake.boundary = 0 :=
  productSnake_one_eq_zero_iff_one_mem.trans CenteredMeanSnake.boundary_eq_zero_iff_one_mem.symm

theorem productSnake_one_eq_zero_iff_rh : productSnake 1 = 0 ↔ RiemannHypothesis :=
  productSnake_one_eq_zero_iff_centered_boundary.trans
    (CenteredMeanSnake.boundary_eq_zero_iff_naturalApproximation.trans
      CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.symm)

/-- The exact squared norm of the adjacent relative snake at one. -/
def adjacentSnakeEnergy (n : ℕ) : ℝ := ‖relativeSnake (Nat.le_succ n) 1‖ ^ 2

theorem adjacentSnakeEnergy_eq_stepEnergy (n : ℕ) : adjacentSnakeEnergy n = stepEnergy n := by
  rw [adjacentSnakeEnergy, relativeSnake_one_norm_sq]
  linarith only [patch_norm_sq_step n]

/-- Relative snakes add as energies over every finite interval starting at zero. -/
theorem partial_adjacentSnakeEnergy (N : ℕ) :
    ∑ i ∈ Finset.range N, adjacentSnakeEnergy i =
      ‖relativeSnake (Nat.zero_le N) 1‖ ^ 2 := by
  simp_rw [adjacentSnakeEnergy_eq_stepEnergy]
  rw [relativeSnake_one_norm_sq]
  change _ = ‖patch N‖ ^ 2 - ‖normalizedScreenedTwo‖ ^ 2
  linarith only [patch_norm_sq N]

theorem productSnake_one_eq_zero_iff_summable_adjacent :
    productSnake 1 = 0 ↔ Summable (fun n : ℕ => ‖relativeSnake (Nat.le_succ n) 1‖ ^ 2) := by
  change productSnake 1 = 0 ↔ Summable adjacentSnakeEnergy
  rw [show adjacentSnakeEnergy = stepEnergy from funext adjacentSnakeEnergy_eq_stepEnergy,
    summable_stepEnergy_iff]
  exact productSnake_one_eq_zero_iff_one_mem.trans one_mem_closedSpace_iff_normalizedScreenedTwo

/-- For a nonzero global class the finite relative-snake energies diverge. -/
theorem finite_snake_norm_sq_tendsto_atTop_of_boundary_ne (h : productSnake 1 ≠ 0) :
    Tendsto (fun N : ℕ => ‖relativeSnake (Nat.zero_le N) 1‖ ^ 2) atTop atTop := by
  have hu : normalizedScreenedTwo ≠ hilbertOne := fun hseed =>
    h (productSnake_one_eq_zero_iff_one_mem.mpr
      (one_mem_closedSpace_iff_normalizedScreenedTwo.mpr hseed))
  simp_rw [← partial_adjacentSnakeEnergy, adjacentSnakeEnergy_eq_stepEnergy]
  exact energy_tendsto_atTop_of_seed_ne hu

/-- The same energies grow sublinearly unconditionally, even in the divergence alternative. -/
theorem finite_snake_norm_sq_sublinear :
    Tendsto (fun N : ℕ => ‖relativeSnake (Nat.zero_le N) 1‖ ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) _ patch_error_sublinear
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← partial_adjacentSnakeEnergy, patch_error_sq]
  simp_rw [adjacentSnakeEnergy_eq_stepEnergy]
  exact le_add_of_nonneg_left (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
