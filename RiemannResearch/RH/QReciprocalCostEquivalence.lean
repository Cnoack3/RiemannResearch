import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QReciprocalRegularizedCriterion
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complete D-cost equivalence and an improved RH sufficient condition
Source: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 6.
Finite-span approximation gives the converse to the O(reg) membership criterion.
Failure of membership forces normalized cost divergence for every source family.
The near-linear D criterion transfers the existing shifted-reciprocal Mellin
criterion. Its complete arithmetic cost provider remains open. No analytic
RH converse from Bagchi's Theorem 1 is inserted as an assumption or axiom.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QReciprocalCostEquivalence
open ZetaTwoHilbert QReciprocalMetric QReciprocalTargetLift
open QReciprocalRegularizedCriterion

def cost (α : ℝ) (x v : QHilbert) : ℝ := ‖D (v - x)‖ ^ 2 + α * ‖v‖ ^ 2

theorem exists_cost_le_of_mem_closure (S : Submodule ℝ QHilbert)
    (x : QHilbert) (hx : x ∈ S.topologicalClosure) (α : ℝ) (hα : 0 < α) :
    ∃ v ∈ S, cost α x v ≤ (1 + (‖x‖ + 1) ^ 2) * α := by
  have hx' : x ∈ _root_.closure (S : Set QHilbert) := hx
  obtain ⟨v,hv,he⟩ := Metric.mem_closure_iff.mp hx'
    (min 1 (Real.sqrt α)) (lt_min zero_lt_one (Real.sqrt_pos.mpr hα))
  have he1 : ‖v - x‖ ≤ 1 := by
    have := he.le.trans (min_le_left _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using this
  have heα : ‖v - x‖ ≤ Real.sqrt α := by
    have := he.le.trans (min_le_right _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using this
  have hvb : ‖v‖ ≤ ‖x‖ + 1 := by
    have h := norm_add_le (v - x) x
    rw [sub_add_cancel] at h
    linarith
  have hd : ‖D (v - x)‖ ≤ ‖v - x‖ := coordinates_norm_le _
  have he2 : ‖D (v - x)‖ ^ 2 ≤ α := by
    have hs := Real.sq_sqrt hα.le
    nlinarith [norm_nonneg (D (v - x)), norm_nonneg (v - x)]
  have hb2 : ‖v‖ ^ 2 ≤ (‖x‖ + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hvb 2
  refine ⟨v, hv, ?_⟩
  unfold cost
  nlinarith [mul_le_mul_of_nonneg_left hb2 hα.le]

theorem mem_closure_of_cost_bound (S : Submodule ℝ QHilbert)
    (x : QHilbert) (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hrlim : Tendsto reg atTop (𝓝 0)) (C : ℝ) (hC : 0 ≤ C)
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ S)
    (hc : ∀ j, cost (reg j) x (F j) ≤ C * reg j) :
    x ∈ S.topologicalClosure := by
  have hb (j : ℕ) : ‖F j‖ ≤ Real.sqrt C := by
    have hh := hc j
    unfold cost at hh
    have hsq : ‖F j‖ ^ 2 ≤ C := by nlinarith [sq_nonneg ‖D (F j - x)‖, hr j]
    have hs := Real.sq_sqrt hC
    nlinarith [norm_nonneg (F j), Real.sqrt_nonneg C]
  have he (j : ℕ) : ‖D (F j) - D x‖ ^ 2 ≤ C*reg j := by
    have hh := hc j
    unfold cost at hh
    rw [map_sub] at hh
    nlinarith [mul_nonneg (hr j).le (sq_nonneg ‖F j‖)]
  have hu : Tendsto (fun j => C * reg j) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrlim
  have hs := squeeze_zero (fun j => sq_nonneg ‖D (F j) - D x‖) he hu
  have ht : Tendsto (fun j => D (F j)) atTop (𝓝 (D x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  let T : Submodule ℝ QHilbert := (Submodule.span ℝ (Set.range F)).topologicalClosure
  letI : TopologicalSpace.SeparableSpace T := by
    apply TopologicalSpace.IsSeparable.separableSpace
    change TopologicalSpace.IsSeparable
      ((Submodule.span ℝ (Set.range F)).topologicalClosure : Set QHilbert)
    rw [Submodule.topologicalClosure_coe]
    exact ((Set.countable_range F).isSeparable.span (R := ℝ)).closure
  have hxT : x ∈ T :=
    (mem_of_bounded_D_tendsto T C.sqrt F x
      (fun j => Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨j, rfl⟩)) hb ht).1
  have hle : Submodule.span ℝ (Set.range F) ≤ S.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact S.le_topologicalClosure (hm j)
  exact (Submodule.topologicalClosure_minimal _ hle
    S.isClosed_topologicalClosure) hxT

theorem mem_closure_iff_regularized_cost (S : Submodule ℝ QHilbert)
    (x : QHilbert) (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hrlim : Tendsto reg atTop (𝓝 0)) :
    x ∈ S.topologicalClosure ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∃ F : ℕ → QHilbert,
      (∀ j, F j ∈ S) ∧ (∀ j, cost (reg j) x (F j) ≤ C * reg j) := by
  constructor
  · intro hx
    choose F hm hc using fun j => exists_cost_le_of_mem_closure S x hx (reg j) (hr j)
    exact ⟨1 + (‖x‖ + 1) ^ 2, by positivity, F, hm, hc⟩
  · rintro ⟨C,hC,F,hm,hc⟩
    exact mem_closure_of_cost_bound S x reg hr hrlim C hC F hm hc

theorem normalized_cost_tendsto_atTop_of_not_mem
    (S : Submodule ℝ QHilbert)
    (x : QHilbert) (hx : x ∉ S.topologicalClosure)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j) (hrlim : Tendsto reg atTop (𝓝 0))
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ S) :
    Tendsto (fun j => cost (reg j) x (F j) / reg j) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro C
  by_contra h
  have hcofinal : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ cost (reg j) x (F j) / reg j < C := by
    intro N
    by_contra hn
    apply h
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro j hj
    by_contra hjC
    exact hn ⟨j,hj,lt_of_not_ge hjC⟩
  choose φ hφge hφbound using hcofinal
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  apply hx
  apply mem_closure_of_cost_bound S x (reg ∘ φ) (fun j => hr (φ j))
    (hrlim.comp hφ) (max C 0) (le_max_right _ _) (F ∘ φ) (fun j => hm (φ j))
  intro j
  exact ((div_le_iff₀ (hr (φ j))).mp (hφbound j).le).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (hr (φ j)).le)

theorem normalized_cost_tendsto_atTop_of_not_RH
    (hRH : ¬ RiemannHypothesis) (reg : ℕ → ℝ)
    (hr : ∀ j, 0 < reg j) (hrlim : Tendsto reg atTop (𝓝 0))
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ QFullResidueProjection.legalSpan) :
    Tendsto (fun j => cost (reg j) qOne (F j) / reg j) atTop atTop := by
  apply normalized_cost_tendsto_atTop_of_not_mem
    QFullResidueProjection.legalSpan qOne ?_ reg hr hrlim F hm
  intro hx
  exact hRH (QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure hx)

/-- Conditional research reduction: the near-linear cost estimates are open. -/
theorem riemannHypothesis_of_near_linear_D_cost
    (U : ℕ → QHilbert) (hU : ∀ j, U j ∈ QFullResidueProjection.legalSpan)
    (hc : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      ‖D (qOne - U j)‖ ^ 2 + regularizationScale j * ‖U j‖ ^ 2 ≤
        C * (regularizationScale j) ^ (1 - η)) : RiemannHypothesis := by
  apply riemannHypothesis_of_near_linear_regularized_cost U hU
  intro η hη
  obtain ⟨C, hC, h⟩ := hc η hη
  exact ⟨C, hC, fun j => le_trans (add_le_add
    (shifted_norm_sq_le_D (qOne - U j)) le_rfl) (h j)⟩

end RiemannResearch.RH.QReciprocalCostEquivalence
