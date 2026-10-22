import RiemannResearch.RH.ParetoGibbsHilbert
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Open target: the complete spectral set of the actual Pareto Gibbs operator

Status: unproved research target. This file declares a proposition, not a
proof or an axiom. The proved mean-zero contraction bound alone does not
establish that every point of the proposed interval occurs in the spectrum.

Source: the spectral-set claim in
`RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md`, based on the
weighted Hankel spectral theorem of T. Kalvoda and P. Šťovíček,
https://arxiv.org/abs/1506.01064. That reference supports the proposed
spectral identification; its spectral representation has not been formally
transported to the present operator.

The ambient algebra here is the algebra of bounded real-linear
endomorphisms of the genuine complete weighted Hilbert space. Thus
`spectrum ℝ` tests real resolvent parameters using bounded inverses in
that algebra. For this real self-adjoint operator, the stated real spectral
set is the appropriate real form of the reported spectral identification.
The proposition specifies spectral values, without specifying spectral
multiplicity or absolute continuity.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Open: identify the complete spectral set, including the occurrence of
every point of the continuous interval, for the actual bundled operator. -/
def paretoGibbsFullSpectrumTarget : Prop :=
  spectrum ℝ hilbertGibbsContinuous = Set.Icc 0 (Real.pi / 4) ∪ {1}

end
end RiemannResearch.RH.Pareto
