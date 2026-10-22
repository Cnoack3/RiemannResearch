/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteWeightedEnergyComparison
import RiemannResearch.Analysis.NaturalPowerCutoff
import RiemannResearch.RH.DampedMobiusHeadApproximation
import RiemannResearch.RH.BurnolFiniteEnergyReduction

/-!
# A prescribed-cutoff signed-head criterion

The exact signed density tail controls the discrepancy between a finite
arithmetic residue sum and the actual centered damped prefix. A uniform
bound on that head error permits one prescribed residue cutoff for each
physical head. The cutoff no longer has an eventual quantifier.

The signed off-diagonal estimate remains an explicit arithmetic obligation.
Burnol, arXiv:math/0202166, Theorem 4.2 supports the final cofinal-damping
application; the finite comparisons here are elementary. No uniform bound
across damping stages is required.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

/-- Conditional research reduction at a prescribed residue cutoff M(H).
The head-error premise can be discharged by a suitable polynomial cutoff.
The remaining off-diagonal bound is equivalent to fixed-damping energy. -/
theorem centered_damped_energy_iff_prescribed_signed_head_bound
    {ε : ℝ} (hε : 0 < ε) (M : ℕ → ℕ) (K : ℝ)
    (herror : ∀ H : ℕ,
      (∑ n ∈ Finset.range H, positiveWeight n *
        (hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)) n -
            (dampedMobiusPrefix ε n -
              (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)) ^ 2) ≤ K) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ↔
    ∃ B : ℝ, ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H (M H) ≤ B := by
  have hcompare (H : ℕ) :=
    RiemannResearch.Analysis.sum_weighted_sq_comparison_of_sub_sq_le
      (Finset.range H) positiveWeight
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)))
      (fun n => dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)
      (fun n _ => positiveWeight_nonneg n) K (herror H)
  constructor
  · intro hs
    let E : ℝ := ∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2
    refine ⟨2 * E + 2 * K, ?_⟩
    intro H
    have ht : (∑ n ∈ Finset.range H, positiveWeight n *
        (dampedMobiusPrefix ε n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ≤ E :=
      Summable.sum_le_tsum (Finset.range H)
        (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) hs
    have hc := (hcompare H).1
    have he := dampedMobius_partial_head_eq_signed ε H (M H)
    simp only [paretoHeadPairing, mul_assoc, ← pow_two] at he
    have hd := dampedMobiusHeadDiagonal_nonneg ε H (M H)
    linarith
  · rintro ⟨B, hB⟩
    have hb (H : ℕ) : (∑ n ∈ Finset.range H, positiveWeight n *
        (dampedMobiusPrefix ε n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ≤
        2 * (dampedMobiusDiagonalBudget ε + B) + 2 * K := by
      have hc := (hcompare H).2
      have he := dampedMobius_partial_head_eq_signed ε H (M H)
      simp only [paretoHeadPairing, mul_assoc, ← pow_two] at he
      have hd := dampedMobiusHeadDiagonal_le hε H (M H)
      have ho := hB H
      linarith
    exact summable_of_sum_range_le
      (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) hb

/-- Conditional RH reduction with one prescribed cutoff per head and per
damping stage. Both error and signed-energy constants may depend on the
stage. Only the signed-energy estimates remain arithmetic obligations once
the explicit cutoff error provider is supplied. -/
theorem riemannHypothesis_of_prescribed_signed_head_bound
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (M : ℕ → ℕ → ℕ) (K : ℕ → ℝ)
    (herror : ∀ j H : ℕ,
      (∑ n ∈ Finset.range H, positiveWeight n *
        (hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j H)) n -
            (dampedMobiusPrefix (ε j) n -
              (n : ℝ) * (1 / riemannZeta (1 + (ε j : ℂ))).re)) ^ 2) ≤ K j)
    (hbound : ∀ j, ∃ B : ℝ, ∀ H : ℕ,
      dampedMobiusHeadOffDiagonal (ε j) H (M j H) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_centered_damped_square_summable ε hpos hlim
  intro j
  refine ⟨(1 / riemannZeta (1 + (ε j : ℂ))).re, ?_⟩
  exact (centered_damped_energy_iff_prescribed_signed_head_bound
    (hpos j) (M j) (K j) (herror j)).mpr (hbound j)

/-- Unconditional bounded approximation error at an explicit polynomial
cutoff. The estimate is valid at every positive damping. -/
theorem dampedMobius_polynomial_head_error_le
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hscale : 1 ≤ 2 * (k : ℝ) * ε)
    (H : ℕ) :
    (∑ n ∈ Finset.range H, positiveWeight n *
      (hilbertSequence
        (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) ((H+1)^k)) n -
          (dampedMobiusPrefix ε n -
            (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)) ^ 2) ≤ 1 / ε ^ 2 := by
  have hk : 1 ≤ k := by
    by_contra hk
    have hz : k = 0 := by omega
    norm_num [hz] at hscale
  have hM : 1 ≤ (H+1)^k := by
    have hp : 0 < (H+1)^k := by positivity
    omega
  exact (dampedMobius_head_error_le hε H ((H+1)^k)
      (RiemannResearch.Analysis.le_succ_pow H k hk) hM).trans
    (div_le_div_of_nonneg_right
      (RiemannResearch.Analysis.head_mul_polynomial_cutoff_rpow_le_one H k ε hscale)
      (sq_nonneg ε))

/-- Exact arithmetic criterion using a single explicit polynomial cutoff
for each head. Only the signed off-diagonal bound remains unresolved. -/
theorem centered_damped_energy_iff_polynomial_signed_head_bound
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hscale : 1 ≤ 2 * (k : ℝ) * ε) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ↔
    ∃ B : ℝ, ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H ((H+1)^k) ≤ B :=
  centered_damped_energy_iff_prescribed_signed_head_bound hε
    (fun H => (H+1)^k) (1 / ε^2) (dampedMobius_polynomial_head_error_le hε k hscale)

/-- Conditional research reduction: polynomially prescribed signed-head
bounds at dampings tending to zero imply RH. The exponent may grow and the
energy bound may depend on the damping stage. -/
theorem riemannHypothesis_of_polynomial_signed_head_bound
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (k : ℕ → ℕ) (hscale : ∀ j, 1 ≤ 2 * (k j : ℝ) * ε j)
    (hbound : ∀ j, ∃ B : ℝ, ∀ H : ℕ,
      dampedMobiusHeadOffDiagonal (ε j) H ((H+1)^(k j)) ≤ B) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_prescribed_signed_head_bound ε hpos hlim
    (fun j H => (H+1)^(k j)) (fun j => 1 / (ε j)^2)
    (fun j H => dampedMobius_polynomial_head_error_le (hpos j) (k j) (hscale j) H)
    hbound

/-- One explicit arithmetic-only remaining hypothesis. Every damping
1/(j+3) is strictly below one half, and every cutoff exponent is j+3.
No common bound across j is requested. -/
theorem riemannHypothesis_of_reciprocal_polynomial_signed_head_bound
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ H : ℕ,
      dampedMobiusHeadOffDiagonal (1 / ((j+3 : ℕ) : ℝ)) H ((H+1)^(j+3)) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_polynomial_signed_head_bound
    (fun j => 1 / ((j+3 : ℕ) : ℝ)) (fun j => by positivity) ?_
    (fun j => j+3) ?_ hbound
  · have ht : Tendsto (fun j : ℕ => ((j+3 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ht
  · intro j
    have hd : ((j+3 : ℕ) : ℝ) ≠ 0 := by positivity
    have he : 2 * ((j+3 : ℕ) : ℝ) * (1 / ((j+3 : ℕ) : ℝ)) = 2 := by
      field_simp [hd]
    rw [he]
    norm_num

end RiemannResearch.RH.Pareto
