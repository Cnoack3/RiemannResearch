/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensCriticalAverageDisplacement
import RiemannResearch.Analysis.MertensAveragePowerEndpoint

/-! # Pointwise corollaries of the critical Cesàro displacement test -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis ZetaTwoHilbert

/-- Little-o at the critical exponent forces RH under the two-part power
estimate for a cofinal family of canonical heads. -/
theorem riemannHypothesis_of_power_defect_and_critical_little_o
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (a β C : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hcrit : (1+a)*β = a)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      |1 - Pareto.canonicalMobiusHead (q j) (n+1)| ≤
        C * min (q j : ℝ) (((n:ℝ)+1) * (q j:ℝ)^(-a)))
    (hd : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      |qSequence displacement (n+1)| ≤ η * ((n:ℝ)+1)^β) : RiemannHypothesis :=
  riemannHypothesis_of_power_defect_and_critical_prefix q hq a β C ha hβ hβ1 hC hcrit hlegal
    hdef (power_prefix_little_o_of_pointwise _ β hβ.le hd)

/-- An ordinary Mertens power estimate and critical little-o growth of the
actual displacement imply RH, including growth with no fixed power saving
below the critical exponent. -/
theorem riemannHypothesis_of_mertens_power_and_critical_little_o
    (s C : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M (n : ℝ)| ≤ C*(n:ℝ)^s)
    (hd : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      |qSequence displacement (n+1)| ≤ η * ((n:ℝ)+1)^((1-s)/(2-s))) :
    RiemannHypothesis :=
  riemannHypothesis_of_mertens_power_and_critical_prefix s C hs hs1 hC hM
    (power_prefix_little_o_of_pointwise _ _ (div_nonneg (sub_nonneg.mpr hs1.le) (by linarith)) hd)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
