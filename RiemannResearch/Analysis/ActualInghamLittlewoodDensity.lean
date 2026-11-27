/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodProfile
import RiemannResearch.Analysis.ActualInghamLittlewoodWindow

/-!
# The Gabriel–Littlewood zero-density estimate

For all heights at least two the actual multiplicity count satisfies the
Ingham height exponent `q = 3(1-σ)/(2-σ)` and logarithmic exponent
`2+q = (7-5σ)/(2-σ)`. The constant is uniform on the closed half strip.
This is the order in Chourasiya and Simonič, Theorem 1,
<https://arxiv.org/abs/2507.15184>.
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The two Gabriel endpoints, both horizontal Littlewood terms, and a
single outward collar give the sharp logarithmic profile for the inclusive
count with analytic multiplicity. -/
theorem exists_ingham_littlewood_density_all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      let q := 3 * (1 - σ) / (2 - σ)
      rightInclusiveCount T σ ≤ C * min (T * Real.log T) (T ^ q * (Real.log T) ^ (2 + q)) := by
  obtain ⟨D, hD, hwindow⟩ := exists_actual_littlewood_comparable_count
  exact exists_ingham_littlewood_profile_of_comparable_count hD hwindow

/-- Difference between the Ingham height exponent and the exponent in
the strong density hypothesis of Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh. -/
theorem ingham_height_exponent_sub_strong_density {σ : ℝ} (hσ : σ < 2) :
    3 * (1 - σ) / (2 - σ) - 2 * (1 - σ) =
      (1 - σ) * (2 * σ - 1) / (2 - σ) := by
  field_simp [ne_of_gt (sub_pos.mpr hσ)]
  <;> ring

theorem strong_density_height_exponent_lt_ingham {σ : ℝ} (hσ : 1 / 2 < σ) (hs : σ < 1) :
    2 * (1 - σ) < 3 * (1 - σ) / (2 - σ) := by
  apply sub_pos.mp
  rw [ingham_height_exponent_sub_strong_density (by linarith)]
  exact div_pos (mul_pos (sub_pos.mpr hs) (by linarith)) (by linarith)

/-- At log-height L the strong-density comparison has logarithm L-1.
The logarithm of the quotient of the two bare height powers is (L-1)/(3L-1). -/
theorem ingham_strong_density_microscopic_endpoint {L : ℝ} (hL : 1 < L) :
    let σ := 1 / 2 + 1 / (2 * L)
    L * (2 * (1 - σ)) = L - 1 ∧
      L * (3 * (1 - σ) / (2 - σ) - 2 * (1 - σ)) = (L - 1) / (3 * L - 1) := by
  dsimp only
  have hL0 : L ≠ 0 := by linarith
  have hden : 3 * L - 1 ≠ 0 := by linarith
  have hpos : 0 < 2 * L := by linarith
  have hh : 1 / (2 * L) < 1 / 2 := (div_lt_iff₀ hpos).2 (by linarith)
  have hσ : 1 / 2 + 1 / (2 * L) < 2 := by linarith
  constructor
  · field_simp [hL0]
    <;> ring
  · rw [ingham_height_exponent_sub_strong_density hσ]
    field_simp [hL0, hden, ne_of_gt (sub_pos.mpr hσ)]
    <;> ring

#print axioms ingham_strong_density_microscopic_endpoint

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_littlewood_density_all_heights' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_ingham_littlewood_density_all_heights

end RiemannResearch.Analysis.ActualZeroOrdinate
