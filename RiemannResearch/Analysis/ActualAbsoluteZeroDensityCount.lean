/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroTailReflection

/-!
# Restriction of an absolute-height density bound to positive ordinates

Guth–Maynard (2026), Theorem 1.2, uses an inclusive absolute-height
cutoff. Restriction to the positive-height subset retains analytic
multiplicity at every zero and requires no symmetry factor.
<https://doi.org/10.4007/annals.2026.203.2.6>
-/

noncomputable section
open Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The source counts all actual strip zeros of absolute height at most T,
with analytic multiplicity and an inclusive real-part threshold. -/
def AbsoluteZeroCountBound (σ T b : ℝ) : Prop :=
  ∃ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ IsNontrivialZero ρ ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
    ((∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ b

theorem rightInclusiveCount_le_of_absoluteZeroCountBound {σ T b : ℝ}
    (h : AbsoluteZeroCountBound σ T b) : rightInclusiveCount T σ ≤ b := by
  classical
  obtain ⟨Z, hZ, hb⟩ := h
  let S := (cutoff T).filter (fun ρ : ℂ => σ ≤ ρ.re)
  have hS : S ⊆ Z := by
    intro ρ hρ
    obtain ⟨hc, hβ⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hγ, hT⟩ := mem_cutoff.mp hc
    exact (hZ ρ).mpr ⟨hz, hβ, by rwa [abs_of_nonneg hγ.le]⟩
  have he : rightInclusiveCount T σ = ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    unfold rightInclusiveCount realSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hβ : σ ≤ ρ.re <;> simp [hβ, analyticOrderNatAt, zeroMult]
  rw [he]
  apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)).trans
  simpa only [Nat.cast_sum] using hb

end RiemannResearch.Analysis.ActualZeroOrdinate
