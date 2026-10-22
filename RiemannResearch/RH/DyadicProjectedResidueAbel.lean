import RiemannResearch.RH.DyadicProjectedResidueTerminal

/-!
# Exact infinite Abel identity for each actual projected residue column

Source: the finite weighted telescope and fixed-positive-damping terminal
summability from `DyadicSignedMeanEnergyVerification20260910(1).md`.
The argument uses genuine Hilbert summability to split and subtract series.
Every theorem fixes the positive physical conductor n and positive damping.
No uniform estimate in the conductor or in vanishing damping, nor an
interchange with the infinite signed Mobius sum, is asserted here.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The projected residue orbit including its initial residue is summable
at each fixed positive conductor and positive damping. -/
theorem dyadicProjectedResidueOrbit_summable
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertResidue (n * 3 ^ j) (by positivity))) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (dyadicProjectedResidueTerminal_summable n hn hε).const_smul
    (triadicDampingRatio ε)
  simpa only [smul_smul, pow_succ'] using hs

/-- The actual damped triadic residue column is a summable Hilbert series.
This follows from the exact residue cocycle and the two residue orbit sums. -/
theorem dyadicProjectedTriadicColumn_summable
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (n * 3 ^ j) (by positivity)
          (hilbertResidue 3 (by norm_num)))) := by
  have hs := (dyadicProjectedResidueTerminal_summable n hn hε).sub
    (dyadicProjectedResidueOrbit_summable n hn hε)
  apply hs.congr
  intro j
  rw [hilbertDilation_residue_eq_sub]
  simp only [pow_succ, Nat.mul_assoc, map_sub, smul_sub]

/-- Exact Abel formula for the full actual projected triadic column.
The terminal has been removed using proved Hilbert summability; the
remaining complete residue orbit is retained with its exact coefficient. -/
theorem dyadicProjectedTriadicColumn_tsum_eq
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (∑' j : ℕ, triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (n * 3 ^ j) (by positivity)
          (hilbertResidue 3 (by norm_num)))) =
      -dyadicQuotientProjection (hilbertResidue n hn) +
        (1 - triadicDampingRatio ε) •
          ∑' j : ℕ, triadicDampingRatio ε ^ j •
            dyadicQuotientProjection
              (hilbertResidue (n * 3 ^ (j + 1)) (by positivity)) := by
  have hs := dyadicProjectedResidueTerminal_summable n hn hε
  have ht := dyadicProjectedResidueOrbit_summable n hn hε
  have hterm (j : ℕ) :
      triadicDampingRatio ε ^ j •
        dyadicQuotientProjection
          (hilbertDilation (n * 3 ^ j) (by positivity)
            (hilbertResidue 3 (by norm_num))) =
      triadicDampingRatio ε ^ j •
        dyadicQuotientProjection
          (hilbertResidue (n * 3 ^ (j + 1)) (by positivity)) -
        triadicDampingRatio ε ^ j •
          dyadicQuotientProjection
            (hilbertResidue (n * 3 ^ j) (by positivity)) := by
    rw [hilbertDilation_residue_eq_sub]
    simp only [pow_succ, Nat.mul_assoc, map_sub, smul_sub]
  simp_rw [hterm]
  rw [hs.tsum_sub ht]
  have hsplit := ht.tsum_eq_zero_add
  simp only [pow_zero, Nat.mul_one, one_smul] at hsplit
  have htail :
      (∑' j : ℕ, triadicDampingRatio ε ^ (j + 1) •
        dyadicQuotientProjection
          (hilbertResidue (n * 3 ^ (j + 1)) (by positivity))) =
      triadicDampingRatio ε •
        ∑' j : ℕ, triadicDampingRatio ε ^ j •
          dyadicQuotientProjection
            (hilbertResidue (n * 3 ^ (j + 1)) (by positivity)) := by
    simpa only [smul_smul, pow_succ'] using
      (hs.hasSum.const_smul (triadicDampingRatio ε)).tsum_eq
  rw [htail] at hsplit
  rw [hsplit, sub_smul, one_smul]
  abel

end
end RiemannResearch.RH.Pareto
