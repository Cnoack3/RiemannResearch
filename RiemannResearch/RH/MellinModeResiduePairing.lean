import RiemannResearch.RH.CompactFrequencyMellinRigidity
import RiemannResearch.Analysis.MellinNormalizedResidue

/-!
# Exact residue pairings of individual Mellin modes

Source: user-provided compact-frequency rigidity argument. The analytic
summation input is the existing `residueFraction_first_hasSum_zeta`; this
module supplies the exact weight and indexing bridge to `mellinMode`.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction

open RiemannResearch.Analysis.Cesaro

/-- The Pareto weight cancels the quadratic prefactor exactly. -/
theorem weighted_mellinMode_eq (s : ℂ) (n : ℕ) :
    (paretoWeight n : ℂ) * mellinMode s n = mellinFirst s (n + 1) := by
  have h1 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < (n : ℝ) + 1 by positivity))
  have h2 : (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < (n : ℝ) + 2 by positivity))
  calc
    _ = ((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s) := by
      unfold paretoWeight mellinMode
      push_cast
      field_simp [h1, h2] <;> ring
    _ = mellinFirst s (n + 1) := by
      simp [mellinFirst, Nat.cast_add, add_assoc]

/-- The array coordinate agrees with the normalized physical residue. -/
theorem normalizedResidueCoordinate_eq_residueFraction (d n : ℕ) :
    normalizedResidueCoordinate d n =
      (ArithmeticCumulative.residueFraction d (n + 1) : ℂ) := by
  simp [normalizedResidueCoordinate, ArithmeticCumulative.residueFraction]

/-- Absolute convergence and exact summation on the whole positive half-plane,
away from the removable zeta-pole expression. -/
theorem mellinMode_residue_hasSum (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (d : ℕ) (hd : 2 ≤ d) :
    HasSum (fun n => (paretoWeight n : ℂ) * mellinMode s n *
      normalizedResidueCoordinate d n)
      ((1 / (d : ℂ) - (d : ℂ) ^ (-s)) * riemannZeta s) := by
  simpa only [weighted_mellinMode_eq,
    normalizedResidueCoordinate_eq_residueFraction] using
    residueFraction_first_hasSum_zeta d (by omega) s hs hs1

theorem mellinMode_residue_summable (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (d : ℕ) (hd : 2 ≤ d) :
    Summable (fun n => (paretoWeight n : ℂ) * mellinMode s n *
      normalizedResidueCoordinate d n) :=
  (mellinMode_residue_hasSum s hs hs1 d hd).summable

theorem mellinMode_residuePairing (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (d : ℕ) (hd : 2 ≤ d) :
    residuePairing (mellinMode s) d =
      ((1 / (d : ℂ) - (d : ℂ) ^ (-s)) * riemannZeta s) :=
  (mellinMode_residue_hasSum s hs hs1 d hd).tsum_eq

end RiemannResearch.RH.Pareto.SpectralObstruction
