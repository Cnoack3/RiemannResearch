import RiemannResearch.RH.DyadicResidueOrbitGrowth
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

/-!
# Actual positive-damping projected terminal convergence

Source: independently developed from the proved quadratic projected-residue
bound and Mathlib's geometric-polynomial summability theorem. Every statement
here fixes the positive integer n and assumes positive damping. Constants
need not be uniform in n or in damping, so no uniform Mobius-family estimate
or RH conclusion is supplied.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The full norm series of projected terminal residues converges at every
positive damping, for each fixed positive physical starting conductor. -/
theorem dyadicProjectedResidueTerminal_norm_summable
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun J : ℕ => ‖triadicDampingRatio ε ^ J •
      dyadicQuotientProjection
        (hilbertResidue (n * 3 ^ (J + 1)) (by positivity))‖) := by
  let q := triadicDampingRatio ε
  let L := Nat.log 2 n + 1
  have hnL : n ≤ 2 ^ L :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n).le
  have hq0 : 0 ≤ q := (triadicDampingRatio_pos ε).le
  have hq1 : q < 1 := triadicDampingRatio_lt_one hε
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  let a := ‖dyadicQuotientProjection (hilbertResidue n hn)‖
  let c := 4 * (L : ℝ) / Real.sqrt 2 + ‖hilbertResidue 3 (by norm_num)‖
  let d := 8 / Real.sqrt 2
  have h0 : Summable (fun J : ℕ => q ^ J) :=
    summable_geometric_of_lt_one hq0 hq1
  have h1 : Summable (fun J : ℕ => (J : ℝ) * q ^ J) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm)
  have h2 : Summable (fun J : ℕ => (J : ℝ) ^ 2 * q ^ J) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hmajor : Summable (fun J : ℕ =>
      (a + c) * q ^ J + (c + d) * ((J : ℝ) * q ^ J) +
        d * ((J : ℝ) ^ 2 * q ^ J)) :=
    ((h0.mul_left (a + c)).add (h1.mul_left (c + d))).add (h2.mul_left d)
  apply Summable.of_nonneg_of_le (fun J => norm_nonneg _) _ hmajor
  intro J
  have hb := dyadicQuotientProjection_residue_triadic_norm_le_quadratic n L J hn hnL
  push_cast at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 _)]
  calc
    _ ≤ q ^ J * (a + ((J : ℝ) + 1) *
        (4 * ((L : ℝ) + 2 * J) / Real.sqrt 2 +
          ‖hilbertResidue 3 (by norm_num)‖)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hq0 _)
    _ = _ := by dsimp [a, c, d]; ring

/-- The terminal is an actual summable Hilbert-valued orbit. -/
theorem dyadicProjectedResidueTerminal_summable
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun J : ℕ => triadicDampingRatio ε ^ J •
      dyadicQuotientProjection
        (hilbertResidue (n * 3 ^ (J + 1)) (by positivity))) :=
  (dyadicProjectedResidueTerminal_norm_summable n hn hε).of_norm

/-- Positive damping removes the genuine projected terminal in Hilbert norm.
This is a fixed-n limit; there is no uniform assertion as damping vanishes. -/
theorem dyadicProjectedResidueTerminal_tendsto_zero
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun J : ℕ => triadicDampingRatio ε ^ J •
      dyadicQuotientProjection
        (hilbertResidue (n * 3 ^ (J + 1)) (by positivity)))
      Filter.atTop (nhds 0) :=
  (dyadicProjectedResidueTerminal_summable n hn hε).tendsto_atTop_zero

end
end RiemannResearch.RH.Pareto
