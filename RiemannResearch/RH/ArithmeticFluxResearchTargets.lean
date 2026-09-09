import RiemannResearch.RH.ParetoResidueLogMean

/-!
# Exact cutoff logarithmic flux: the remaining general statement

Source: equation (23) of the contracting-evolution research report.
Residue jumps, discrete Abel identities, and full logarithmic residue means
are proved elsewhere. This records the exact arbitrary-cutoff generator
formula and its limit as an unproved proposition, not a theorem or axiom.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open scoped BigOperators

def arithmeticGeneratorJump (a m n : ℕ) : ℝ :=
  (residue (a*m) n - residue m n) -
    (residue (a*m) (n-1) - residue m (n-1))

def arithmeticGeneratorCutoffFlux (a m N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, arithmeticGeneratorJump a m n / (n : ℝ)

/-- The two harmonic cutoffs are retained before taking the limit. -/
def ArithmeticGeneratorLogFluxTarget : Prop :=
  ∀ a m : ℕ, 0 < a → 0 < m →
    (∀ N : ℕ, arithmeticGeneratorCutoffFlux a m N =
      (harmonic (N/m) : ℝ) - (harmonic (N/(a*m)) : ℝ)) ∧
    Filter.Tendsto (arithmeticGeneratorCutoffFlux a m) Filter.atTop (nhds (Real.log a))

end
end RiemannResearch.RH.Pareto
