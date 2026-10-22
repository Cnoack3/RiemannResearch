import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# An exact legal period-36 approximation certificate

Source: user-provided `RH_Two_Seed_Threshold.tex`, revised September 7, 2026,
Section 10, Proposition `crt-cost-example`; the accompanying
`certify_weighted_crt_cost.py` supplies the eight generators.  The coefficients
below are a separately rounded rational witness, not the program's minimizer.
The certificate uses two retained progression weights and an elementary
telescoping tail upper bound.  There are no floating-point or native computations.

This file proves the finite rational certificate.  Its application to the
infinite weighted sequence norm requires the progression-weight theorem and
the exact periodic regrouping of the norm; neither is assumed proved here.
It does not prove the lower bound for constrained fitting or the phase constant.
-/

namespace RiemannResearch.RH.TwoSeedThreshold

noncomputable section

/-- The exact residue difference representing the legal generator `T_m R_a`. -/
def certificateGenerator (a m k : ℕ) : ℝ :=
  ((k % (a * m) : ℕ) : ℝ) - ((k % m : ℕ) : ℝ)

/-- An explicit legal combination of the eight period-36 generators. -/
def legalWitness36 (k : ℕ) : ℝ :=
  (556 * certificateGenerator 2 1 k +
   117 * certificateGenerator 2 2 k +
    18 * certificateGenerator 2 3 k +
     6 * certificateGenerator 2 6 k +
     7 * certificateGenerator 2 9 k +
     2 * certificateGenerator 2 18 k +
   367 * certificateGenerator 3 1 k +
    50 * certificateGenerator 3 3 k) / 1000

/-- Two exact retained weights plus the elementary telescoping upper tail.
For `1 ≤ r ≤ 36`, this bounds the mass of the progression `r + 36ℕ`. -/
def residueUpper36 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 36) * (r + 37)) +
  1 / (36 * ((r : ℝ) + 37))

theorem legalWitness36_periodic (k : ℕ) :
    legalWitness36 (k + 36) = legalWitness36 k := by
  have h1 : (k + 36) % 1 = k % 1 := by omega
  have h2 : (k + 36) % 2 = k % 2 := by omega
  have h3 : (k + 36) % 3 = k % 3 := by omega
  have h4 : (k + 36) % 4 = k % 4 := by omega
  have h6 : (k + 36) % 6 = k % 6 := by omega
  have h9 : (k + 36) % 9 = k % 9 := by omega
  have h12 : (k + 36) % 12 = k % 12 := by omega
  have h18 : (k + 36) % 18 = k % 18 := by omega
  have h36 : (k + 36) % 36 = k % 36 := by omega
  simp only [legalWitness36, certificateGenerator, show 2 * 1 = 2 from rfl,
    show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl,
    show 2 * 6 = 12 from rfl, show 2 * 9 = 18 from rfl,
    show 2 * 18 = 36 from rfl, show 3 * 1 = 3 from rfl,
    show 3 * 3 = 9 from rfl, h1, h2, h3, h4, h6, h9, h12, h18, h36]

theorem legalWitness36_zero : legalWitness36 0 = 0 := by
  norm_num [legalWitness36, certificateGenerator]

/-- Outward-rounded error caps, in millionths, for positive residues 1,...,36.
Each cap is proved independently below, avoiding a very large rational lcm. -/
private def residueErrorCap36 (r : Fin 36) : ℝ :=
  (![2974, 173, 4, 9439, 8438, 4625, 4623, 74, 1033, 614, 3941, 4585,
    120, 187, 218, 213, 2066, 1814, 182, 120, 84, 42, 1637, 1057,
    151, 197, 7, 438, 354, 398, 320, 1, 4, 12, 1412, 1322] : Fin 36 → ℝ) r /
      1000000

set_option maxHeartbeats 2000000 in
/-- The explicit upper certificate is strictly better than the paper's
`0.053` threshold.  All 36 residue classes, including the zero class represented
by 36, occur with their full squared error. -/
theorem legalWitness36_upper_certificate :
    (∑ r : Fin 36, residueUpper36 (r.val + 1) *
      (1 - legalWitness36 (r.val + 1)) ^ 2) < (53 : ℝ) / 1000 := by
  have h (r : Fin 36) : residueUpper36 (r.val + 1) *
      (1 - legalWitness36 (r.val + 1)) ^ 2 ≤ residueErrorCap36 r := by
    fin_cases r <;>
      norm_num [residueUpper36, legalWitness36, certificateGenerator, residueErrorCap36]
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun r _ => h r))
  norm_num [Fin.sum_univ_succ, residueErrorCap36]

/-- Application of the rational certificate to any correctly enclosed
36-residue weight vector.  The enclosure premise is explicit and is not
a substitute for the infinite progression-tail theorem. -/
theorem legalWitness36_error_lt_of_weights
    (w : Fin 36 → ℝ)
    (hw : ∀ r, w r ≤ residueUpper36 (r.val + 1)) :
    (∑ r : Fin 36, w r * (1 - legalWitness36 (r.val + 1)) ^ 2) <
      (53 : ℝ) / 1000 := by
  apply lt_of_le_of_lt _ legalWitness36_upper_certificate
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)

end
end RiemannResearch.RH.TwoSeedThreshold
