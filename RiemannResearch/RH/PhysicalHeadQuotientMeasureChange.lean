import RiemannResearch.RH.PhysicalHeadInfiniteBoundary
import RiemannResearch.RH.MixedParityQuotientDescent
import RiemannResearch.RH.PrimeSupportMeasureChange
import Mathlib.Tactic.Linarith

/-! # Change of measure for the physical-head quotient descent
The relative snake at one is measured in the native zeta-two quotient by the deeper
zero-head kernel. Uniform two-sided comparison transports the global summability
criterion and connects it to the infinite prime-support Parseval target.
Source: the user's infinite quotient descent and change-of-measure construction. -/

noncomputable section
open Filter
open scoped BigOperators Topology
open RiemannResearch.RH.Pareto RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.QPhysicalQuotientMetric

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra.MeasureChange
open AffineHeadTower CoefficientStabilization MixedConductorBasis

abbrev qHeadKernel (n : ℕ) : Submodule ℝ QHilbert := physicalSpace (kernel n)

instance qHeadKernel_projection (n : ℕ) : (qHeadKernel n).HasOrthogonalProjection := by
  have hc : IsClosed (qHeadKernel n : Set QHilbert) :=
    (kernel_closed n).preimage paretoEquiv.continuous
  let : CompleteSpace (qHeadKernel n) := hc.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The physical Q profile of the actual Pareto projection of the unnormalized parity packet. -/
abbrev qProjectedParity : QHilbert :=
  paretoEquiv.symm (DigammaParseval.projectedParity : ThresholdHilbert)

/-- Encode the signed arithmetic head prefix with its original site values. -/
abbrev qArithmeticPrefix (N : ℕ) : QHilbert :=
  paretoEquiv.symm (DigammaParseval.parityLayerPrefix N : ThresholdHilbert)

/-- The arithmetic head data give the full projected class in every Q quotient. -/
theorem qArithmeticPrefix_class (N : ℕ) :
    (qHeadKernel N).mkQ qProjectedParity = (qHeadKernel N).mkQ (qArithmeticPrefix N) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change paretoEquiv (qProjectedParity - qArithmeticPrefix N) ∈ kernel N
  rw [map_sub, paretoEquiv.apply_symm_apply, paretoEquiv.apply_symm_apply]
  have hp : (DigammaParseval.physicalKernelInMixed N).mkQ
      (DigammaParseval.projectedParity - DigammaParseval.parityLayerPrefix N) = 0 := by
    rw [map_sub, DigammaParseval.parityLayerPrefix_quotient N, sub_self]
  have hk := (Submodule.Quotient.mk_eq_zero (DigammaParseval.physicalKernelInMixed N)).mp hp
  change mixedClosure.subtype (DigammaParseval.projectedParity - DigammaParseval.parityLayerPrefix N)
    ∈ kernel N at hk
  simpa only [map_sub, Submodule.subtype_apply] using hk

/-- The computed Q classes restrict to the prescribed shallower head. -/
theorem qArithmeticPrefix_compatible {N K : ℕ} (h : N ≤ K) :
    MixedConductorBasis.supportQuotientTransition
      (show qHeadKernel K ≤ qHeadKernel N from Submodule.comap_mono (kernel_antitone h))
      ((qHeadKernel K).mkQ (qArithmeticPrefix K)) = (qHeadKernel N).mkQ (qArithmeticPrefix N) := by
  rw [← qArithmeticPrefix_class K, ← qArithmeticPrefix_class N]
  rfl

theorem qHeadKernel_iInf : (⨅ n, qHeadKernel n) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hP : paretoEquiv x ∈ ⨅ n, kernel n := by
    rw [Submodule.mem_iInf] at hx ⊢
    exact fun n => hx n
  rw [kernel_intersection, Submodule.mem_bot] at hP
  apply (Submodule.mem_bot ℝ).mpr
  apply paretoEquiv.injective
  simpa only [map_zero] using hP

/-- The physical Q quotient data have a unique ambient lift. -/
theorem qArithmeticPrefix_unique (x : QHilbert) :
    (∀ n, (qHeadKernel n).mkQ x = (qHeadKernel n).mkQ (qArithmeticPrefix n)) ↔
      x = qProjectedParity := by
  constructor
  · intro h
    have hk : x-qProjectedParity ∈ ⨅ n, qHeadKernel n := by
      rw [Submodule.mem_iInf]
      intro n
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (qHeadKernel n).mkQ (x - qProjectedParity) = 0
      rw [map_sub, h n, qArithmeticPrefix_class n, sub_self]
    rw [qHeadKernel_iInf, Submodule.mem_bot] at hk
    exact sub_eq_zero.mp hk
  · rintro rfl
    exact qArithmeticPrefix_class

theorem qArithmeticPrefix_tendsto :
    Tendsto qArithmeticPrefix atTop (𝓝 qProjectedParity) := by
  let f := paretoEquiv.symm.toContinuousLinearMap.comp mixedClosure.subtypeL
  exact f.continuous.continuousAt.tendsto.comp DigammaParseval.parityLayerPrefix_tendsto

/-- The native Q least-norm representative is computed from the arithmetic prefix. -/
def qMinimumPrefix (N : ℕ) : QHilbert := (qHeadKernel N)ᗮ.starProjection (qArithmeticPrefix N)

theorem qMinimumPrefix_eq_projection (N : ℕ) :
    qMinimumPrefix N = (qHeadKernel N)ᗮ.starProjection qProjectedParity := by
  have hk : qProjectedParity - qArithmeticPrefix N ∈ qHeadKernel N := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (qHeadKernel N).mkQ (qProjectedParity - qArithmeticPrefix N) = 0
    rw [map_sub, qArithmeticPrefix_class, sub_self]
  have h := ((qHeadKernel N)ᗮ.starProjection_apply_eq_zero_iff).mpr
    (show qProjectedParity - qArithmeticPrefix N ∈ (qHeadKernel N)ᗮᗮ from
      by rwa [(qHeadKernel N).orthogonal_orthogonal])
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Re-minimizing each physical quotient in Q converges to the same Pareto projected vector. -/
theorem qMinimumPrefix_tendsto : Tendsto qMinimumPrefix atTop (𝓝 qProjectedParity) := by
  let stages := fun n => (qHeadKernel n)ᗮ
  have hmono : Monotone stages := fun _ _ h =>
    Submodule.orthogonal_le (Submodule.comap_mono (kernel_antitone h))
  have hd : (⨆ n, stages n).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    have hk : x ∈ ⨅ n, qHeadKernel n := by
      rw [Submodule.mem_iInf]
      intro n
      have h : x ∈ (stages n)ᗮ := Submodule.orthogonal_le (le_iSup stages n) hx
      simpa only [stages, Submodule.orthogonal_orthogonal] using h
    rwa [qHeadKernel_iInf] at hk
  have ht := Submodule.starProjection_tendsto_self stages hmono qProjectedParity hd.ge
  exact ht.congr' (Filter.Eventually.of_forall fun n => (qMinimumPrefix_eq_projection n).symm)

theorem qMinimumPrefix_energy (N : ℕ) :
    ‖qProjectedParity‖ ^ 2 = ‖qMinimumPrefix N‖ ^ 2 +
      ‖qProjectedParity - qMinimumPrefix N‖ ^ 2 := by
  rw [qMinimumPrefix_eq_projection]
  simpa only [Submodule.starProjection_orthogonal_val] using
    Submodule.norm_sq_eq_add_norm_sq_starProjection qProjectedParity (qHeadKernel N)ᗮ

/-- The same relative displacement, minimized in the Q quotient by the deeper head kernel. -/
def qRelativeClass {N K : ℕ} (_h : N ≤ K) : QHilbert ⧸ qHeadKernel K :=
  (qHeadKernel K).mkQ (paretoEquiv.symm (patch K - patch N))

private theorem pRelative_norm_sq {N K : ℕ} (h : N ≤ K) :
    ‖(kernel K).mkQ (patch K - patch N)‖ ^ 2 = ‖relativeSnake h 1‖ ^ 2 := by
  have ho : patch K - patch N ∈ (kernel K)ᗮ := displacement_orthogonal_deeper h
  rw [quotient_norm, ((kernel K).starProjection_apply_eq_zero_iff).mpr ho, sub_zero,
    relativeSnake_one_norm_sq]
  exact displacement_norm_sq h

theorem qRelative_norm_sq_comparison {N K : ℕ} (h : N ≤ K) :
    zetaTwo / 2 * ‖qRelativeClass h‖ ^ 2 ≤ ‖relativeSnake h 1‖ ^ 2 ∧
      ‖relativeSnake h 1‖ ^ 2 ≤ zetaTwo * ‖qRelativeClass h‖ ^ 2 := by
  have hc := physical_quotient_norm_sq_comparison (kernel K) (paretoEquiv.symm (patch K - patch N))
  rw [paretoEquiv.apply_symm_apply, pRelative_norm_sq h] at hc
  exact hc

/-- The two metric corrections for every finite relative snake, with their signs. -/
theorem qRelative_energy_balance {N K : ℕ} (h : N ≤ K) :
    let x := paretoEquiv.symm (patch K - patch N)
    let q := (qHeadKernel K).starProjection x
    ‖relativeSnake h 1‖ ^ 2 + ‖paretoEquiv q‖ ^ 2 =
      zetaTwo * (‖qRelativeClass h‖ ^ 2 - inner ℝ (x-q) (QShiftedReciprocal.B (x-q))) := by
  have ho : patch K - patch N ∈ (kernel K)ᗮ := displacement_orthogonal_deeper h
  have he := physical_quotient_energy_balance (kernel K) (paretoEquiv.symm (patch K - patch N))
  dsimp only at he
  rw [paretoEquiv.apply_symm_apply, pRelative_norm_sq h,
    ((kernel K).starProjection_apply_eq_zero_iff).mpr ho, zero_sub, norm_neg] at he
  exact he

/-- The algebraic infinite-head snake vanishes exactly when the adjacent native Q
quotient energies are summable. -/
theorem productSnake_zero_iff_qRelative_summable :
    productSnake 1 = 0 ↔ Summable (fun n : ℕ => ‖qRelativeClass (Nat.le_succ n)‖ ^ 2) := by
  rw [productSnake_one_eq_zero_iff_summable_adjacent]
  constructor
  · intro hp
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hp.mul_left (2 / zetaTwo))
    intro n
    have h := (qRelative_norm_sq_comparison (Nat.le_succ n)).1
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    linarith only [h]
  · intro hq
    exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => (qRelative_norm_sq_comparison (Nat.le_succ n)).2) (hq.mul_left zetaTwo)

/-- The two infinite descents have the same arithmetic endpoint in the Q measure. -/
theorem q_head_summable_iff_support_saturation :
    Summable (fun n : ℕ => ‖qRelativeClass (Nat.le_succ n)‖ ^ 2) ↔
      (∑' k, ‖(MixedConductorBasis.MeasureChange.qLayer k).starProjection
        MixedConductorBasis.MeasureChange.qParity‖ ^ 2) =
          (3 / 4 : ℝ) * ((Real.log 2)⁻¹ - 1) ^ 2 + 1 / 4 :=
  productSnake_zero_iff_qRelative_summable.symm.trans
    (productSnake_one_eq_zero_iff_rh.trans
      MixedConductorBasis.MeasureChange.riemannHypothesis_iff_q_layer_saturation)

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra.MeasureChange.qMinimumPrefix_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qMinimumPrefix_tendsto

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra.MeasureChange.q_head_summable_iff_support_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms q_head_summable_iff_support_saturation

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra.MeasureChange
