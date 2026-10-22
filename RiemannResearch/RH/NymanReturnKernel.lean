import RiemannResearch.RH.NymanConductorArithmetic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # The actual cumulative-beta kernel for arithmetic returns -/

open scoped BigOperators
namespace RiemannResearch.RH

/-- Exact cumulative conductor coefficients at the ordinary coordinate x.
The zero coefficient is zero, so this counts the positive arithmetic jumps. -/
noncomputable def nymanCumulativeBeta (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, nymanConductorBeta n k

/-- The half-density cumulative kernel. Its exact jumps recover the actual
Nyman arithmetic return after one integration by parts. -/
noncomputable def nymanReturnKernel (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * nymanCumulativeBeta n (Real.exp t)

end RiemannResearch.RH
