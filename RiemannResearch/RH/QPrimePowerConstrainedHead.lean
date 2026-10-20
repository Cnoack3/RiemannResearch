/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerTwoStage
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual minimum-norm logarithmic-head interpolation

Source: user-provided RH/CRT continuation agenda, 20 October 2026, Priority 3.
The two-stage sieve supplies feasibility. The existing complete-Q inverse
Gram construction minimizes over the entire finite divisor dictionary.
Its exact removed-energy term is retained; no uniform bound is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The actual complete-Q minimum-norm vector with the logarithmic head supplied by T. -/
def logarithmicHeadOptimizer (x y r : ℕ) (hr : r ∈ conductors (primorial y)) : QHilbert :=
  affineOptimizer (conductors (primorial y)) (conductor_gt_one (primorial y))
    x r hr (twoStageVector x y) 0

/-- The head is exact and every squarefree divisor is available to the minimization. -/
theorem logarithmicHeadOptimizer_feasible (x y r : ℕ)
    (hx : 2 ≤ x) (hxy : x ≤ y) (hdvd : primorial x ∣ primorial y)
    (hgap : finitePrimeProduct x ≠ finitePrimeProduct y)
    (hr : r ∈ conductors (primorial y)) (hrx : x < r) :
    logarithmicHeadOptimizer x y r hr ∈ divisorStage (primorial y) ∧
      ∀ n, 0 < n → n ≤ x →
        qSequence (logarithmicHeadOptimizer x y r hr) n = (Nat.log 2 n : ℝ) := by
  have hB : twoStageVector x y ∈ dictionary (conductors (primorial y)) := by
    rw [← divisorStage_eq_dictionary (primorial y) (primorial_pos y)]
    exact twoStageVector_mem_divisorStage x y hdvd
  have h := affineOptimizer_same_head (conductors (primorial y))
    (conductor_gt_one (primorial y)) x r (by omega) hr hrx (twoStageVector x y) 0 hB
  refine ⟨?_, ?_⟩
  · rw [divisorStage_eq_dictionary (primorial y) (primorial_pos y)]
    exact h.1
  · intro n hn hnx
    exact (h.2 n hn hnx).trans (qSequence_twoStageVector_head x y n hx hxy hnx hgap)

/-- Exact energy completion against every legal vector with the logarithmic head. -/
theorem logarithmicHeadOptimizer_completion (x y r : ℕ)
    (hx : 2 ≤ x) (hxy : x ≤ y) (hdvd : primorial x ∣ primorial y)
    (hgap : finitePrimeProduct x ≠ finitePrimeProduct y)
    (hr : r ∈ conductors (primorial y)) (hrx : x < r)
    (f : QHilbert) (hf : f ∈ divisorStage (primorial y))
    (hhead : ∀ n, 0 < n → n ≤ x → qSequence f n = (Nat.log 2 n : ℝ)) :
    ‖f‖ ^ 2 = ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 +
      ‖f - logarithmicHeadOptimizer x y r hr‖ ^ 2 := by
  have hB : twoStageVector x y ∈ dictionary (conductors (primorial y)) := by
    rw [← divisorStage_eq_dictionary (primorial y) (primorial_pos y)]
    exact twoStageVector_mem_divisorStage x y hdvd
  have hf' : f ∈ dictionary (conductors (primorial y)) := by
    rwa [← divisorStage_eq_dictionary (primorial y) (primorial_pos y)]
  have h := affineOptimizer_same_head_completion (conductors (primorial y))
    (conductor_gt_one (primorial y)) x r (by omega) hr hrx (twoStageVector x y) 0 hB
    f hf' (fun n hn hnx => (hhead n hn hnx).trans
      (qSequence_twoStageVector_head x y n hx hxy hnx hgap).symm)
  simpa only [zero_sub, norm_neg, logarithmicHeadOptimizer] using h

/-- The entire energy removed from T is the squared norm of its legal correction. -/
theorem logarithmicHeadOptimizer_seed_completion (x y r : ℕ)
    (hr : r ∈ conductors (primorial y)) :
    ‖twoStageVector x y‖ ^ 2 = ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 +
      ‖twoStageVector x y - logarithmicHeadOptimizer x y r hr‖ ^ 2 := by
  have h := affineOptimizer_completion_of_mem (conductors (primorial y))
    (conductor_gt_one (primorial y)) x r hr (twoStageVector x y) 0 (twoStageVector x y)
    (by simp only [sub_self]; exact (zeroHeadSpan _ _ _).zero_mem)
  simpa only [zero_sub, norm_neg, logarithmicHeadOptimizer] using h

/-- Full signed inverse-Gram formula for the actual removed energy. -/
theorem logarithmicHeadOptimizer_energy_exact (x y r : ℕ)
    (hr : r ∈ conductors (primorial y)) :
    let v := fun d : freeConductors (conductors (primorial y)) x r =>
      compensatedResidue (d : ℕ) r
    let hv := compensated_linearIndependent (conductors (primorial y))
      (conductor_gt_one (primorial y)) x r hr
    ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 = ‖twoStageVector x y‖ ^ 2 -
      ∑ d, inverseCoeff hv (-twoStageVector x y) d * cross v (-twoStageVector x y) d := by
  simpa only [zero_sub, norm_neg, logarithmicHeadOptimizer] using
    affineOptimizer_error_formula (conductors (primorial y))
      (conductor_gt_one (primorial y)) x r hr (twoStageVector x y) 0

/-- This bound is supplied by a concrete feasible vector, not an assumed infimum. -/
theorem logarithmicHeadOptimizer_energy_le_seed (x y r : ℕ)
    (hr : r ∈ conductors (primorial y)) :
    ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 ≤ ‖twoStageVector x y‖ ^ 2 := by
  rw [logarithmicHeadOptimizer_seed_completion x y r hr]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Enlarging the complete divisor dictionary has an exact Pythagorean energy gain.
The head is fixed; this does not control the energy as the head itself grows. -/
theorem logarithmicHeadOptimizer_nested_completion (x y z r s : ℕ)
    (hx : 2 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z)
    (hdxy : primorial x ∣ primorial y) (hdyz : primorial y ∣ primorial z)
    (hgapy : finitePrimeProduct x ≠ finitePrimeProduct y)
    (hgapz : finitePrimeProduct x ≠ finitePrimeProduct z)
    (hr : r ∈ conductors (primorial y)) (hrx : x < r)
    (hs : s ∈ conductors (primorial z)) (hsx : x < s) :
    ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 =
      ‖logarithmicHeadOptimizer x z s hs‖ ^ 2 +
        ‖logarithmicHeadOptimizer x y r hr - logarithmicHeadOptimizer x z s hs‖ ^ 2 := by
  have hU := logarithmicHeadOptimizer_feasible x y r hx hxy hdxy hgapy hr hrx
  exact logarithmicHeadOptimizer_completion x z s hx hxz (dvd_trans hdxy hdyz)
    hgapz hs hsx (logarithmicHeadOptimizer x y r hr)
    (divisorStage_mono hdyz hU.1) hU.2

/-- The true constrained minimum decreases as periods grow at a fixed head. -/
theorem logarithmicHeadOptimizer_nested_energy_le (x y z r s : ℕ)
    (hx : 2 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z)
    (hdxy : primorial x ∣ primorial y) (hdyz : primorial y ∣ primorial z)
    (hgapy : finitePrimeProduct x ≠ finitePrimeProduct y)
    (hgapz : finitePrimeProduct x ≠ finitePrimeProduct z)
    (hr : r ∈ conductors (primorial y)) (hrx : x < r)
    (hs : s ∈ conductors (primorial z)) (hsx : x < s) :
    ‖logarithmicHeadOptimizer x z s hs‖ ^ 2 ≤
      ‖logarithmicHeadOptimizer x y r hr‖ ^ 2 := by
  rw [logarithmicHeadOptimizer_nested_completion x y z r s hx hxy hxz
    hdxy hdyz hgapy hgapz hr hrx hs hsx]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.QPrimePowerSieve
