import RiemannResearch.Analysis.BoundedInjectiveLift
import RiemannResearch.Analysis.InjectiveLiftDivergence
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exact missing bound for reciprocal density and P/Q symmetry

Source: the user's D-residue density discussion. This specializes the existing
weak-compactness theorem to the physical reciprocal Df(n)=f(n)/n. The correct
smoothed RH target is D1. A source-norm bound remains an explicit open input.
The P/Q equivalence preserves closure and boundedness, but orthogonality
transfers with the density multiplier B rather than by exchanging labels.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QReciprocalTargetLift
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QReciprocalMetric

theorem D_injective : Function.Injective D := by
  intro f g h
  apply Subtype.ext
  funext n
  have hh := congrArg (fun v : QHilbert => v n) h
  change f n / ((n : ℝ) + 1) = g n / ((n : ℝ) + 1) at hh
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  calc
    f n = (f n / ((n : ℝ) + 1)) * ((n : ℝ) + 1) :=
      (div_mul_cancel₀ _ hn).symm
    _ = (g n / ((n : ℝ) + 1)) * ((n : ℝ) + 1) :=
      congrArg (fun z : ℝ => z * ((n : ℝ) + 1)) hh
    _ = g n := div_mul_cancel₀ _ hn

theorem mem_of_bounded_D_tendsto (S : Submodule ℝ QHilbert)
    [CompleteSpace S]
    (C : ℝ) (F : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D x))) :
    x ∈ S ∧ ‖x‖ ≤ C :=
  S.mem_of_bounded_injective_image_tendsto D D_injective C F x hmem hbound hlim

/-- One bounded cofinal subsequence suffices; a bound on every term is unnecessary. -/
theorem mem_of_bounded_subsequence_D_tendsto (S : Submodule ℝ QHilbert)
    [CompleteSpace S]
    (C : ℝ) (F : ℕ → QHilbert) (x : QHilbert) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F (φ n)‖ ≤ C)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D x))) :
    x ∈ S ∧ ‖x‖ ≤ C :=
  S.mem_of_bounded_subsequence_injective_image_tendsto
    D D_injective C F x φ hφ hmem hbound hlim

/-- A bounded approximate D-lift is exactly membership, not a consequence of density. -/
theorem bounded_D_lift_iff_mem (S : Submodule ℝ QHilbert)
    [CompleteSpace S] (x : QHilbert) :
    (∃ C : ℝ, ∃ F : ℕ → QHilbert, (∀ n, F n ∈ S) ∧
      (∀ n, ‖F n‖ ≤ C) ∧
      Tendsto (fun n => D (F n)) atTop (𝓝 (D x))) ↔ x ∈ S := by
  constructor
  · rintro ⟨C, F, hm, hb, ht⟩
    exact (mem_of_bounded_D_tendsto S C F x hm hb ht).1
  · intro hx
    exact ⟨‖x‖, fun _ => x, fun _ => hx, fun _ => le_rfl, tendsto_const_nhds⟩

theorem norm_tendsto_atTop_of_not_mem_D_tendsto
    (S : Submodule ℝ QHilbert) [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S]
    (F : ℕ → QHilbert) (x : QHilbert) (hx : x ∉ S)
    (hmem : ∀ n, F n ∈ S)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D x))) :
    Tendsto (fun n => ‖F n‖) atTop atTop :=
  S.norm_tendsto_atTop_of_not_mem_injective_image_tendsto
    D D_injective F x hx hmem hlim

/-- Conditional research reduction: the bound on unsmoothed legal vectors is open. -/
theorem riemannHypothesis_of_bounded_D_target (C : ℝ) (F : ℕ → QHilbert)
    (hmem : ∀ n, F n ∈ QFullResidueProjection.closure)
    (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D qOne))) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (mem_of_bounded_D_tendsto QFullResidueProjection.closure
      C F qOne hmem hbound hlim).1

theorem riemannHypothesis_of_bounded_subsequence_D_target
    (C : ℝ) (F : ℕ → QHilbert) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop)
    (hmem : ∀ n, F n ∈ QFullResidueProjection.closure)
    (hbound : ∀ n, ‖F (φ n)‖ ≤ C)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D qOne))) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (mem_of_bounded_subsequence_D_tendsto QFullResidueProjection.closure
      C F qOne φ hφ hmem hbound hlim).1

theorem D_target_norm_tendsto_atTop_of_not_RH
    (hRH : ¬ RiemannHypothesis) (F : ℕ → QHilbert)
    (hmem : ∀ n, F n ∈ QFullResidueProjection.closure)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D qOne))) :
    Tendsto (fun n => ‖F n‖) atTop atTop := by
  apply norm_tendsto_atTop_of_not_mem_D_tendsto
    QFullResidueProjection.closure F qOne ?_ hmem hlim
  intro hx
  exact hRH (QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure hx)

/-- Boundedness and convergence of the same physical D-images transfer both ways. -/
theorem bounded_D_target_pareto_iff (F : ℕ → QHilbert) (x : QHilbert) :
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖F n‖ ≤ C) ∧
      Tendsto (fun n => D (F n)) atTop (𝓝 (D x))) ↔
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖toPareto (F n)‖ ≤ C) ∧
      Tendsto (fun n => toPareto (D (F n))) atTop (𝓝 (toPareto (D x)))) :=
  (uniformly_bounded_iff F).and
    (tendsto_toPareto_iff (fun n => D (F n)) (D x)).symm

/-- The density multiplier is the exact correction needed to transfer orthogonality. -/
theorem pareto_inner_density_eq_q_inner (f g : QHilbert) :
    inner ℝ (toPareto (QDensityMetric.B f)) (toPareto g) = inner ℝ f g := by
  calc
    _ = (1 / zetaTwo) *
        (inner ℝ (toPareto f) (toPareto g) +
          inner ℝ (toPareto (D f)) (toPareto g)) := by
      change inner ℝ (toParetoLinear ((1 / zetaTwo) • (f + D f))) _ = _
      rw [map_smul, map_add, inner_smul_left, inner_add_left]
      rfl
    _ = _ := (q_inner_identity f g).symm

theorem pareto_density_orthogonal_iff (W : Submodule ℝ QHilbert) (f : QHilbert) :
    (∀ w ∈ W, inner ℝ (toPareto (QDensityMetric.B f)) (toPareto w) = 0) ↔
      ∀ w ∈ W, inner ℝ f w = 0 := by
  simp only [pareto_inner_density_eq_q_inner]


/-- A single regularized-cost provider controls both the image error and source norm.
The existence of such a family is the open arithmetic obligation. -/
theorem riemannHypothesis_of_regularized_D_cost
    (C : ℝ) (hC : 0 ≤ C) (reg : ℕ → ℝ) (F : ℕ → QHilbert)
    (hreg : ∀ n, 0 < reg n) (hreglim : Tendsto reg atTop (𝓝 0))
    (hmem : ∀ n, F n ∈ QFullResidueProjection.legalSpan)
    (hcost : ∀ n, ‖D (F n - qOne)‖ ^ 2 + reg n * ‖F n‖ ^ 2 ≤ C * reg n) :
    RiemannHypothesis := by
  have hb (n : ℕ) : ‖F n‖ ≤ Real.sqrt C := by
    have hc := hcost n
    have hp : reg n * ‖F n‖ ^ 2 ≤ reg n * C := by
      nlinarith [sq_nonneg ‖D (F n - qOne)‖]
    have hs : ‖F n‖ ^ 2 ≤ C :=
      (mul_le_mul_iff_right₀ (hreg n)).mp (by simpa only [mul_comm] using hp)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
    simpa only [Real.sq_sqrt hC] using hs
  have he (n : ℕ) : ‖D (F n) - D qOne‖ ^ 2 ≤ C * reg n := by
    have hc := hcost n
    rw [map_sub] at hc
    nlinarith [mul_nonneg (hreg n).le (sq_nonneg ‖F n‖)]
  have ht : Tendsto (fun n => C * reg n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hreglim
  have hs : Tendsto (fun n => ‖D (F n) - D qOne‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) he ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D qOne)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact riemannHypothesis_of_bounded_D_target (Real.sqrt C) F
    (fun n => QFullResidueProjection.legalSpan.le_topologicalClosure (hmem n)) hb hlim

end RiemannResearch.RH.QReciprocalTargetLift
