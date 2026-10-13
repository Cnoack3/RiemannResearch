import RiemannResearch.RH.CanonicalMobiusPNT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sublinear complete error of the canonical exact-head witness

Source: the direct unconditional upper-bound conclusion in the user-provided
CRT exact-head/tail record, 2026-09-30. The proof here uses the repository's
unconditional PNT-backed sublinear norm theorem and a norm inequality. It
proves the error-energy limit, not the manuscript's specific constant-12
bound, and does not claim bounded or vanishing unnormalized error.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

theorem canonicalMobiusHilbert_error_sublinear :
    Tendsto (fun N => ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun N : ℕ =>
      (2 * ‖hilbertOne‖ ^ 2) * (1 / (N : ℝ)) +
        2 * (‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * ‖hilbertOne‖ ^ 2)).add (canonicalMobiusHilbert_sublinear.const_mul 2)
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))
    (fun N => ?_) hupper
  have hs : ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤
      2 * ‖hilbertOne‖ ^ 2 + 2 * ‖canonicalMobiusHilbert N‖ ^ 2 := by
    have hnorm := norm_sub_le hilbertOne (canonicalMobiusHilbert N)
    have hsq := (sq_le_sq₀
      (norm_nonneg (hilbertOne - canonicalMobiusHilbert N))
      (add_nonneg (norm_nonneg hilbertOne) (norm_nonneg (canonicalMobiusHilbert N)))).mpr hnorm
    nlinarith [sq_nonneg (‖hilbertOne‖ - ‖canonicalMobiusHilbert N‖),
      norm_nonneg (hilbertOne - canonicalMobiusHilbert N), norm_nonneg hilbertOne,
      norm_nonneg (canonicalMobiusHilbert N)]
  calc
    _ ≤ (2 * ‖hilbertOne‖ ^ 2 + 2 * ‖canonicalMobiusHilbert N‖ ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
    _ = _ := by ring

end RiemannResearch.RH.Pareto
