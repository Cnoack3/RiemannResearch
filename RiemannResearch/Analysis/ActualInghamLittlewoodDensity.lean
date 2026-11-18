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

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_littlewood_density_all_heights' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_ingham_littlewood_density_all_heights

end RiemannResearch.Analysis.ActualZeroOrdinate
