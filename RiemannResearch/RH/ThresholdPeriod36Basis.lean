import RiemannResearch.RH.ThresholdFiniteCertificate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The independent legal period-36 basis

Source: `RH_Two_Seed_Threshold.tex`, revised September 7, 2026, Section 10,
Proposition `crt-cost-example`.  Independence is proved by exact evaluation
at the positive integers 1,2,3,4,6,9,12,18, without weighted Gram estimates.
Spanning of the four omitted conductor-dividing generators follows by exact
residue cancellation; it does not assert weighted coarse surjectivity.
-/

open scoped BigOperators

namespace RiemannResearch.RH.TwoSeedThreshold
noncomputable section

def period36Basis : Fin 8 → ℕ → ℝ :=
  ![certificateGenerator 2 1, certificateGenerator 2 2,
    certificateGenerator 2 3, certificateGenerator 2 6,
    certificateGenerator 2 9, certificateGenerator 2 18,
    certificateGenerator 3 1, certificateGenerator 3 3]

/-- Exact injectivity of synthesis for the eight stated basis columns. -/
theorem period36Basis_synthesis_injective (c : Fin 8 → ℝ)
    (hc : ∀ k : ℕ, ∑ i : Fin 8, c i * period36Basis i k = 0) :
    ∀ i, c i = 0 := by
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h6 := hc 6
  have h9 := hc 9
  have h12 := hc 12
  have h18 := hc 18
  norm_num [Fin.sum_univ_succ, period36Basis, certificateGenerator, Fin.succ] at h1 h2 h3 h4 h6 h9 h12 h18
  change c 0 + c 6 = 0 at h1
  change c 1 * 2 + c 6 * 2 = 0 at h2
  change c 0 + (c 1 * 2 + (c 2 * 3 + c 7 * 3)) = 0 at h3
  change c 2 * 3 + (c 6 + c 7 * 3) = 0 at h4
  change c 1 * 2 + (c 3 * 6 + c 7 * 6) = 0 at h6
  change c 0 + (c 2 * 3 + (c 3 * 6 + c 4 * 9)) = 0 at h9
  change c 4 * 9 + c 7 * 3 = 0 at h12
  change c 1 * 2 + (c 3 * 6 + c 5 * 18) = 0 at h18
  intro i
  fin_cases i
  · change c 0 = 0
    linarith
  · change c 1 = 0
    linarith
  · change c 2 = 0
    linarith
  · change c 3 = 0
    linarith
  · change c 4 = 0
    linarith
  · change c 5 = 0
    linarith
  · change c 6 = 0
    linarith
  · change c 7 = 0
    linarith

theorem period36Basis_linearIndependent : LinearIndependent ℝ period36Basis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply period36Basis_synthesis_injective c
  intro k
  have h := congrFun hc k
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h

theorem period36_omitted_3_2 (k : ℕ) :
    certificateGenerator 3 2 k = certificateGenerator 2 3 k +
      certificateGenerator 3 1 k - certificateGenerator 2 1 k := by
  norm_num [certificateGenerator]

theorem period36_omitted_3_4 (k : ℕ) :
    certificateGenerator 3 4 k = certificateGenerator 2 6 k +
      certificateGenerator 2 3 k + certificateGenerator 3 1 k -
      certificateGenerator 2 1 k - certificateGenerator 2 2 k := by
  norm_num [certificateGenerator]

theorem period36_omitted_3_6 (k : ℕ) :
    certificateGenerator 3 6 k = certificateGenerator 2 9 k +
      certificateGenerator 3 3 k - certificateGenerator 2 3 k := by
  norm_num [certificateGenerator]

theorem period36_omitted_3_12 (k : ℕ) :
    certificateGenerator 3 12 k = certificateGenerator 2 18 k +
      certificateGenerator 2 9 k + certificateGenerator 3 3 k -
      certificateGenerator 2 3 k - certificateGenerator 2 6 k := by
  norm_num [certificateGenerator]

end
end RiemannResearch.RH.TwoSeedThreshold
