/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The exact residual floor of legally projected CRT cylinders

Source: the user's request to apply general CRT descent simultaneously to
all squarefree atoms, 25 October 2026. The elementary cylinder
`qOne - qDivisor L` converges to the target in the actual complete Q norm.
Orthogonally projecting this cylinder to the closed legal squarefree span
retains exactly the limiting residual energy and a vanishing nonnegative
projection square. No target-membership assumption is hidden in this identity.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTCylinderProjection
open ZetaTwoHilbert ZetaTwoOptimizerStage QDivisibilityDensity

/-- The bounded ambient CRT cylinder which is one away from multiples of L. -/
def cylinderApprox (L : ℕ) : QHilbert := qOne - qDivisor L

/-- Its actual best approximation in the closed legal squarefree span. -/
def legalCylinderApprox (L : ℕ) : QHilbert :=
  closure.starProjection (cylinderApprox L)

theorem cylinderApprox_sequence (L n : ℕ) (hn : 0 < n) :
    qSequence (cylinderApprox L) n = if L ∣ n then 0 else 1 := by
  change qSequenceLinear (qOne - qDivisor L) n = _
  rw [map_sub]
  change qSequence qOne n - qSequence (qDivisor L) n = _
  rw [qSequence_qOne, qSequence_qDivisor]
  by_cases hdiv : L ∣ n <;>
    simp [qOneSequence, positiveDivisor, Nat.ne_of_gt hn, hdiv]

/-- Exact complete-Q cylinder error, including all multiples of L. -/
theorem cylinderApprox_error_sq (L : ℕ) (hL : 0 < L) :
    ‖qOne - cylinderApprox L‖ ^ 2 = 1 / (L : ℝ) ^ 2 := by
  have he : qOne - cylinderApprox L = qDivisor L := by
    unfold cylinderApprox
    abel
  rw [he, qDivisor_norm_sq L hL]

theorem legalCylinderApprox_mem_closure (L : ℕ) :
    legalCylinderApprox L ∈ closure :=
  closure.starProjection_apply_mem _

/-- The entire signed error vector separates into its normal and legal parts. -/
theorem one_sub_legalCylinderApprox (L : ℕ) :
    qOne - legalCylinderApprox L =
      limitingResidual + closure.starProjection (qDivisor L) := by
  unfold legalCylinderApprox cylinderApprox limitingResidual
  rw [map_sub]
  abel

/-- Projecting ambient CRT approximants leaves the original residual floor. -/
theorem legalCylinderApprox_error_sq (L : ℕ) :
    ‖qOne - legalCylinderApprox L‖ ^ 2 =
      ‖limitingResidual‖ ^ 2 + ‖closure.starProjection (qDivisor L)‖ ^ 2 := by
  have hr : limitingResidual ∈ closureᗮ :=
    Submodule.sub_starProjection_mem_orthogonal qOne
  have ho : inner ℝ limitingResidual (closure.starProjection (qDivisor L)) = 0 := by
    rw [real_inner_comm]
    exact ((closure.mem_orthogonal _).mp hr) _ (closure.starProjection_apply_mem _)
  rw [one_sub_legalCylinderApprox, norm_add_sq_real, ho]
  ring

/-- Both sides of the exact energy excess are controlled with no RH hypothesis. -/
theorem legalCylinderApprox_error_excess_bounds (L : ℕ) (hL : 0 < L) :
    0 ≤ ‖qOne - legalCylinderApprox L‖ ^ 2 - ‖limitingResidual‖ ^ 2 ∧
      ‖qOne - legalCylinderApprox L‖ ^ 2 - ‖limitingResidual‖ ^ 2 ≤
        1 / (L : ℝ) ^ 2 := by
  have he : ‖qOne - legalCylinderApprox L‖ ^ 2 - ‖limitingResidual‖ ^ 2 =
      ‖closure.starProjection (qDivisor L)‖ ^ 2 := by
    rw [legalCylinderApprox_error_sq]
    ring
  rw [he]
  refine ⟨sq_nonneg _, ?_⟩
  have hn := Submodule.norm_starProjection_apply_le closure (qDivisor L)
  have hs : ‖closure.starProjection (qDivisor L)‖ ^ 2 ≤ ‖qDivisor L‖ ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn hn
      (norm_nonneg (closure.starProjection (qDivisor L))) (norm_nonneg (qDivisor L))
  simpa only [qDivisor_norm_sq L hL] using hs

theorem cylinderApprox_tendsto_one (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => cylinderApprox (d j)) atTop (𝓝 qOne) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
    (qDivisor_tendsto_zero d hd)
  simpa only [cylinderApprox, sub_zero] using h

/-- Every cofinal conductor sequence gives the same legally projected limit. -/
theorem legalCylinderApprox_tendsto (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => legalCylinderApprox (d j)) atTop
      (𝓝 (closure.starProjection qOne)) := by
  exact (closure.starProjection.continuous.tendsto qOne).comp
    (cylinderApprox_tendsto_one d hd)

theorem legalCylinderApprox_error_tendsto (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => ‖qOne - legalCylinderApprox (d j)‖ ^ 2) atTop
      (𝓝 (‖limitingResidual‖ ^ 2)) := by
  have hr : Tendsto (fun j => qOne - legalCylinderApprox (d j)) atTop
      (𝓝 limitingResidual) := by
    simpa only [limitingResidual] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
        (legalCylinderApprox_tendsto d hd))
  exact hr.norm.pow 2

/-- The cylinder construction followed by legal projection reaches the target
exactly when the original squarefree target-membership obligation holds. -/
theorem legalCylinderApprox_tendsto_one_iff (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => legalCylinderApprox (d j)) atTop (𝓝 qOne) ↔
      qOne ∈ closure := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (legalCylinderApprox_tendsto d hd) h
    exact Submodule.starProjection_eq_self_iff.mp he
  · intro h
    have he : closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr h
    simpa only [he] using legalCylinderApprox_tendsto d hd



theorem cylinder_leakage_exact (L : ℕ) :
    cylinderApprox L - legalCylinderApprox L =
      limitingResidual - (qDivisor L - closure.starProjection (qDivisor L)) := by
  unfold legalCylinderApprox cylinderApprox limitingResidual
  rw [map_sub]
  abel

theorem cylinder_infDist_eq (L : ℕ) :
    Metric.infDist (cylinderApprox L) (closure : Set QHilbert) =
      ‖cylinderApprox L - legalCylinderApprox L‖ := by
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := cylinderApprox L) (closure.starProjection_apply_mem (cylinderApprox L))
    simpa only [dist_eq_norm, legalCylinderApprox] using h
  · apply (Metric.le_infDist (show (closure : Set QHilbert).Nonempty from
        ⟨0, closure.zero_mem⟩)).mpr
    intro y hy
    have h := Submodule.norm_starProjection_apply_le closureᗮ (cylinderApprox L - y)
    rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hy, sub_zero,
      Submodule.starProjection_orthogonal_val] at h
    simpa only [legalCylinderApprox, dist_eq_norm] using h

/-- The normal part of every cofinal CRT approximation converges to the actual residual. -/
theorem cylinder_leakage_tendsto (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => cylinderApprox (d j) - legalCylinderApprox (d j))
      atTop (𝓝 limitingResidual) := by
  exact (cylinderApprox_tendsto_one d hd).sub (legalCylinderApprox_tendsto d hd)

/-- Ambient cylinder convergence does not remove the legal-distance floor. -/
theorem cylinder_infDist_tendsto (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => Metric.infDist (cylinderApprox (d j)) (closure : Set QHilbert))
      atTop (𝓝 ‖limitingResidual‖) := by
  simpa only [cylinder_infDist_eq] using (cylinder_leakage_tendsto d hd).norm

theorem cylinder_infDist_tendsto_zero_iff (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => Metric.infDist (cylinderApprox (d j)) (closure : Set QHilbert))
      atTop (𝓝 0) ↔ limitingResidual = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (tendsto_nhds_unique (cylinder_infDist_tendsto d hd) h)
  · intro h
    simpa only [h, norm_zero] using cylinder_infDist_tendsto d hd

/-- An explicit full-norm error estimate, retaining the residual floor. -/
theorem cylinder_infDist_error_le (L : ℕ) :
    |Metric.infDist (cylinderApprox L) (closure : Set QHilbert) -
      ‖limitingResidual‖| ≤ ‖qDivisor L‖ := by
  rw [cylinder_infDist_eq]
  have h := abs_norm_sub_norm_le
    (cylinderApprox L - legalCylinderApprox L) limitingResidual
  have he : (cylinderApprox L - legalCylinderApprox L) - limitingResidual =
      -(closureᗮ.starProjection (qDivisor L)) := by
    rw [cylinder_leakage_exact, Submodule.starProjection_orthogonal_val]
    abel
  rw [he, norm_neg] at h
  exact h.trans (Submodule.norm_starProjection_apply_le closureᗮ (qDivisor L))

end RiemannResearch.RH.QCRTCylinderProjection
