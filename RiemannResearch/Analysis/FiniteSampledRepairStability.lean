/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteConstrainedProjection
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Exact stability of sampled minimum-energy head repair

Finite row-synthesis repair of a sampled baseline. The row family may be
dependent. Normal-equation witnesses explicitly supply feasibility.
Source: elementary finite-Hilbert derivation for the continuation agenda;
no mathematical novelty is claimed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteSampledRepairStability

open FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Repairing a baseline removes precisely a row-span component of its error.
The equality is stronger than nonexpansiveness and retains the removed energy.
There is no independence assumption on the rows. -/
theorem repair_distance_completion (v : ι → H) (b d₀ d : ι → ℝ) (e : H)
    (h₀ : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d₀) = b i)
    (hd : ∀ i, inner ℝ (v i) (e + Fintype.linearCombination ℝ v d) = b i) :
    ‖e‖ ^ 2 =
      ‖e + Fintype.linearCombination ℝ v d -
        Fintype.linearCombination ℝ v d₀‖ ^ 2 +
      ‖Fintype.linearCombination ℝ v d -
        Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
  let k := e + Fintype.linearCombination ℝ v d -
    Fintype.linearCombination ℝ v d₀
  have hk : ∀ i, inner ℝ (v i) k = 0 := by
    intro i
    dsimp [k]
    rw [inner_sub_right, hd i, h₀ i, sub_self]
  have hp : inner ℝ (Fintype.linearCombination ℝ v (d - d₀)) k = 0 := by
    rw [inner_synthesis_left]
    simp only [hk, mul_zero, Finset.sum_const_zero]
  have hp' : inner ℝ k (Fintype.linearCombination ℝ v (d - d₀)) = 0 := by
    rw [real_inner_comm]
    exact hp
  have he : e = k - Fintype.linearCombination ℝ v (d - d₀) := by
    dsimp [k]
    rw [map_sub]
    abel
  calc
    ‖e‖ ^ 2 = ‖k - Fintype.linearCombination ℝ v (d - d₀)‖ ^ 2 := by rw [← he]
    _ = ‖k‖ ^ 2 + ‖Fintype.linearCombination ℝ v (d - d₀)‖ ^ 2 := by
      rw [norm_sub_sq_real, hp']
      ring
    _ = _ := by rw [map_sub]

theorem repaired_distance_le (v : ι → H) (b d₀ d : ι → ℝ) (e : H)
    (h₀ : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d₀) = b i)
    (hd : ∀ i, inner ℝ (v i) (e + Fintype.linearCombination ℝ v d) = b i) :
    ‖e + Fintype.linearCombination ℝ v d -
      Fintype.linearCombination ℝ v d₀‖ ^ 2 ≤ ‖e‖ ^ 2 := by
  rw [repair_distance_completion v b d₀ d e h₀ hd]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Exact sampled repair energy. `r` is an orthogonal projection residual;
`e` is the baseline's error within the legal finite span. Normal witnesses
give both the optimal correction and the correction of the sampled baseline. -/
theorem sampled_repair_error_completion
    (v : ι → H) (b d₀ d : ι → ℝ) (r e : H)
    (h₀ : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d₀) = b i)
    (hd : ∀ i, inner ℝ (v i) (e + Fintype.linearCombination ℝ v d) = b i)
    (hre : inner ℝ r e = 0)
    (hrv : ∀ i, inner ℝ r (v i) = 0) :
    ‖r - (e + Fintype.linearCombination ℝ v d)‖ ^ 2 =
      ‖r‖ ^ 2 + ‖Fintype.linearCombination ℝ v d₀‖ ^ 2 +
      ‖e + Fintype.linearCombination ℝ v d -
        Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
  have hrs (a : ι → ℝ) :
      inner ℝ r (Fintype.linearCombination ℝ v a) = 0 := by
    rw [real_inner_comm, inner_synthesis_left]
    have hz : ∀ i, inner ℝ (v i) r = 0 := by
      intro i
      rw [real_inner_comm, hrv i]
    simp only [hz, mul_zero, Finset.sum_const_zero]
  have hry : inner ℝ r (e + Fintype.linearCombination ℝ v d) = 0 := by
    rw [inner_add_right, hre, hrs, add_zero]
  have hp : inner ℝ (Fintype.linearCombination ℝ v d₀)
      (e + Fintype.linearCombination ℝ v d) =
      ‖Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_synthesis_left, inner_synthesis_left]
    simp only [hd, h₀]
  have hc : ‖e + Fintype.linearCombination ℝ v d‖ ^ 2 =
      ‖Fintype.linearCombination ℝ v d₀‖ ^ 2 +
      ‖e + Fintype.linearCombination ℝ v d -
        Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
    have hp' : inner ℝ (e + Fintype.linearCombination ℝ v d)
        (Fintype.linearCombination ℝ v d₀) =
        ‖Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
      rw [real_inner_comm]
      exact hp
    rw [norm_sub_sq_real, hp']
    ring
  rw [norm_sub_sq_real, hry, hc]
  ring

/-- Deterministic stability: repair never magnifies the sampled baseline
error above the unavoidable optimal head-repair floor. -/
theorem sampled_repair_error_le
    (v : ι → H) (b d₀ d : ι → ℝ) (r e : H)
    (h₀ : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d₀) = b i)
    (hd : ∀ i, inner ℝ (v i) (e + Fintype.linearCombination ℝ v d) = b i)
    (hre : inner ℝ r e = 0)
    (hrv : ∀ i, inner ℝ r (v i) = 0) :
    ‖r - (e + Fintype.linearCombination ℝ v d)‖ ^ 2 ≤
      ‖r‖ ^ 2 + ‖Fintype.linearCombination ℝ v d₀‖ ^ 2 + ‖e‖ ^ 2 := by
  rw [sampled_repair_error_completion v b d₀ d r e h₀ hd hre hrv]
  exact add_le_add le_rfl (repaired_distance_le v b d₀ d e h₀ hd)

section ProjectionApplication

open FiniteConstrainedProjection

variable {κ : Type*} [Fintype κ]

/-- Specialization to the actual finite legal projection. The sampled
baseline has coefficient vector `c`; both corrections are finite syntheses
of projected physical observation rows. Neither row independence nor a
head-Gram inverse is required. -/
theorem projected_sampled_repair_error_completion
    {v : ι → H} (hv : LinearIndependent ℝ v) (h : κ → H)
    (x : H) (c : ι → ℝ) (d₀ d : κ → ℝ)
    (h₀ : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d₀) = headMismatch hv h x i)
    (hd : ∀ i, inner ℝ (h i)
      (Fintype.linearCombination ℝ v c +
        Fintype.linearCombination ℝ (projectedRow hv h) d) = inner ℝ (h i) x) :
    ‖x - (Fintype.linearCombination ℝ v c +
      Fintype.linearCombination ℝ (projectedRow hv h) d)‖ ^ 2 =
      ‖projectionResidual hv x‖ ^ 2 +
      ‖Fintype.linearCombination ℝ (projectedRow hv h) d₀‖ ^ 2 +
      ‖(Fintype.linearCombination ℝ v c +
          Fintype.linearCombination ℝ (projectedRow hv h) d) -
        (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
          Fintype.linearCombination ℝ (projectedRow hv h) d₀)‖ ^ 2 := by
  let e := Fintype.linearCombination ℝ v (c - inverseCoeff hv x)
  have he : e = Fintype.linearCombination ℝ v c -
      Fintype.linearCombination ℝ v (inverseCoeff hv x) := by
    dsimp [e]
    rw [map_sub]
  have hs : ∀ i, inner ℝ (projectedRow hv h i)
      (e + Fintype.linearCombination ℝ (projectedRow hv h) d) =
        headMismatch hv h x i := by
    intro i
    change inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ v (c - inverseCoeff hv x) +
        Fintype.linearCombination ℝ (projectedRow hv h) d) = _
    rw [inner_add_right, ← projectedRow_pairing hv h (c - inverseCoeff hv x) i,
      ← projectedRow_pairing_rowSynthesis hv h d i, map_sub, inner_sub_right]
    have ht := hd i
    rw [inner_add_right] at ht
    simp only [headMismatch, projectionResidual, inner_sub_right]
    linarith
  have hre : inner ℝ (projectionResidual hv x) e = 0 :=
    residual_orthogonal hv x (c - inverseCoeff hv x)
  have hrq : ∀ i, inner ℝ (projectionResidual hv x) (projectedRow hv h i) = 0 := by
    intro i
    exact residual_orthogonal hv x (inverseCoeff hv (h i))
  have hx : x - (Fintype.linearCombination ℝ v c +
      Fintype.linearCombination ℝ (projectedRow hv h) d) =
      projectionResidual hv x - (e +
        Fintype.linearCombination ℝ (projectedRow hv h) d) := by
    rw [he]
    unfold projectionResidual
    abel
  have hk : e + Fintype.linearCombination ℝ (projectedRow hv h) d -
      Fintype.linearCombination ℝ (projectedRow hv h) d₀ =
      (Fintype.linearCombination ℝ v c +
        Fintype.linearCombination ℝ (projectedRow hv h) d) -
      (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
        Fintype.linearCombination ℝ (projectedRow hv h) d₀) := by
    rw [he]
    abel
  rw [hx]
  have result := sampled_repair_error_completion (projectedRow hv h)
    (headMismatch hv h x) d₀ d (projectionResidual hv x) e h₀ hs hre hrq
  rw [hk] at result
  exact result

end ProjectionApplication

end RiemannResearch.Analysis.FiniteSampledRepairStability

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteSampledRepairStability

open FiniteHilbertGram FiniteConstrainedProjection FiniteFeasibleGramRepair

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype κ] in
/-- A single feasible vector supplies a minimum-energy normal correction for
 every sampled baseline, including dependent observation rows. The exact
 Pythagorean identity records the part of the sampling error removed by repair. -/
theorem exists_sampled_normals_of_feasible (v : ι → H) (b : ι → ℝ)
    (y : H) (hy : ∀ i, inner ℝ (v i) y = b i) :
    ∃ d₀ : ι → ℝ,
      (∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d₀) = b i) ∧
      ∀ e : H, ∃ d : ι → ℝ,
        (∀ i, inner ℝ (v i) (e + Fintype.linearCombination ℝ v d) = b i) ∧
        ‖e‖ ^ 2 =
          ‖e + Fintype.linearCombination ℝ v d -
            Fintype.linearCombination ℝ v d₀‖ ^ 2 +
          ‖Fintype.linearCombination ℝ v d -
            Fintype.linearCombination ℝ v d₀‖ ^ 2 := by
  obtain ⟨d₀, h₀⟩ := exists_normal_of_feasible v b y hy
  refine ⟨d₀, h₀, ?_⟩
  intro e
  obtain ⟨d, hd⟩ := exists_normal_of_feasible v
    (fun i => b i - inner ℝ (v i) e) (y - e) (by
      intro i
      rw [inner_sub_right, hy i])
  have hds : ∀ i, inner ℝ (v i)
      (e + Fintype.linearCombination ℝ v d) = b i := by
    intro i
    rw [inner_add_right, hd i]
    ring
  exact ⟨d, hds, repair_distance_completion v b d₀ d e h₀ hds⟩

/-- A finite legal exact-head interpolant is sufficient to construct the
 normal corrections required for sampled repair. Neither observation-row
 independence nor a supplied head-Gram inverse is required. -/
theorem exists_projected_sampled_normals_of_feasible
    {v : ι → H} (hv : LinearIndependent ℝ v) (h : κ → H)
    (x : H) (cExact : ι → ℝ)
    (hExact : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v cExact) =
      inner ℝ (h i) x) :
    ∃ d₀ : κ → ℝ,
      (∀ i, inner ℝ (projectedRow hv h i)
        (Fintype.linearCombination ℝ (projectedRow hv h) d₀) =
          headMismatch hv h x i) ∧
      ∀ c : ι → ℝ, ∃ d : κ → ℝ,
        (∀ i, inner ℝ (h i)
          (Fintype.linearCombination ℝ v c +
            Fintype.linearCombination ℝ (projectedRow hv h) d) =
              inner ℝ (h i) x) ∧
        ‖Fintype.linearCombination ℝ v (c - inverseCoeff hv x)‖ ^ 2 =
          ‖(Fintype.linearCombination ℝ v c +
              Fintype.linearCombination ℝ (projectedRow hv h) d) -
            (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
              Fintype.linearCombination ℝ (projectedRow hv h) d₀)‖ ^ 2 +
          ‖Fintype.linearCombination ℝ (projectedRow hv h) d -
            Fintype.linearCombination ℝ (projectedRow hv h) d₀‖ ^ 2 := by
  have hy : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ v (cExact - inverseCoeff hv x)) =
        headMismatch hv h x i := by
    intro i
    rw [← projectedRow_pairing hv h (cExact - inverseCoeff hv x) i,
      map_sub, inner_sub_right, hExact i]
    simp only [headMismatch, projectionResidual, inner_sub_right]
  obtain ⟨d₀, h₀, hsample⟩ := exists_sampled_normals_of_feasible
    (projectedRow hv h) (headMismatch hv h x)
    (Fintype.linearCombination ℝ v (cExact - inverseCoeff hv x)) hy
  refine ⟨d₀, h₀, ?_⟩
  intro c
  obtain ⟨d, hd, he⟩ := hsample
    (Fintype.linearCombination ℝ v (c - inverseCoeff hv x))
  have hobs : ∀ i, inner ℝ (h i)
      (Fintype.linearCombination ℝ v c +
        Fintype.linearCombination ℝ (projectedRow hv h) d) =
          inner ℝ (h i) x := by
    intro i
    have hi := hd i
    rw [inner_add_right, ← projectedRow_pairing hv h (c - inverseCoeff hv x) i,
      ← projectedRow_pairing_rowSynthesis hv h d i, map_sub,
      inner_sub_right] at hi
    simp only [headMismatch, projectionResidual, inner_sub_right] at hi
    rw [inner_add_right]
    linarith
  refine ⟨d, hobs, ?_⟩
  have hk :
      Fintype.linearCombination ℝ v (c - inverseCoeff hv x) +
        Fintype.linearCombination ℝ (projectedRow hv h) d -
        Fintype.linearCombination ℝ (projectedRow hv h) d₀ =
      (Fintype.linearCombination ℝ v c +
        Fintype.linearCombination ℝ (projectedRow hv h) d) -
      (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
        Fintype.linearCombination ℝ (projectedRow hv h) d₀) := by
    rw [map_sub]
    abel
  rwa [hk] at he

end RiemannResearch.Analysis.FiniteSampledRepairStability
