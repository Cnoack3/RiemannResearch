/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Exact preservation of finite observations in subspace approximation

Source: finite-dimensional image and section argument, developed for the
user's CRT squarefree-span converse, 13 October 2026. No completeness of
the algebraic subspace or uniform bound on the section is assumed.
-/

noncomputable section
namespace RiemannResearch.Analysis

/-- Finite observations can be kept exactly while approximating a closure vector.
The correcting section is continuous because its domain is finite dimensional. -/
theorem exists_near_with_same_finite_observations
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (S : Submodule ℝ H) (T : H →L[ℝ] Y) {x : H}
    (hx : x ∈ S.topologicalClosure) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : H, g ∈ S ∧ T g = T x ∧ ‖x - g‖ < ε := by
  let f : S →ₗ[ℝ] Y := T.toLinearMap.comp S.subtype
  let K := f.range
  have hsurj : f.rangeRestrict.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨A, hA⟩ := f.rangeRestrict.exists_rightInverse_of_surjective hsurj
  let B : K →L[ℝ] H := LinearMap.toContinuousLinearMap (S.subtype.comp A)
  have hB (y : K) : T (B y) = (y : Y) :=
    congrArg Subtype.val (LinearMap.congr_fun hA y)
  have hmem (y : K) : B y ∈ S := (A y).property
  have hTx : T x ∈ K := by
    apply closure_minimal (s := (S : Set H)) ?_
      ((K.closed_of_finiteDimensional).preimage T.continuous) hx
    intro v hv
    exact ⟨⟨v, hv⟩, rfl⟩
  have hD : 0 < 1 + ‖B‖ * ‖T‖ := by positivity
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp
    (show x ∈ closure (S : Set H) from hx) _ (div_pos hε hD)
  have hTv : T v ∈ K := ⟨⟨v, hv⟩, rfl⟩
  let z : K := ⟨T (x - v), by simpa only [map_sub] using K.sub_mem hTx hTv⟩
  refine ⟨v + B z, S.add_mem hv (hmem z), ?_, ?_⟩
  · rw [map_add, hB]
    change T v + T (x - v) = T x
    rw [map_sub]
    abel
  · have he : x - (v + B z) = (x - v) - B z := by abel
    rw [he]
    have hz : ‖z‖ = ‖T (x - v)‖ := rfl
    have hb : ‖B z‖ ≤ ‖B‖ * ‖T‖ * ‖x - v‖ := by
      calc
        ‖B z‖ ≤ ‖B‖ * ‖z‖ := B.le_opNorm z
        _ ≤ ‖B‖ * (‖T‖ * ‖x - v‖) := by
          rw [hz]
          exact mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ = _ := by ring
    have hd : ‖x - v‖ < ε / (1 + ‖B‖ * ‖T‖) := by
      simpa only [dist_eq_norm] using hdist
    have hs := (lt_div_iff₀ hD).mp hd
    calc
      ‖(x - v) - B z‖ ≤ ‖x - v‖ + ‖B z‖ := norm_sub_le _ _
      _ ≤ ‖x - v‖ + ‖B‖ * ‖T‖ * ‖x - v‖ := add_le_add_right hb _
      _ < ε := by nlinarith

end RiemannResearch.Analysis
