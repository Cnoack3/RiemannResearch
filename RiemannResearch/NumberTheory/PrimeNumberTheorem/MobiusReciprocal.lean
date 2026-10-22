/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences

/-!
# Classical reciprocal Möbius cancellation

Mathematical reference: Terence Tao, "A remark on partial sums involving the
Möbius function", arXiv:0908.4323, introduction, equation (1):
https://arxiv.org/abs/0908.4323.
Tao records this classical consequence of the prime number theorem and
attributes the equivalence to Landau. The elementary bound |m_N| ≤ 1 alone
does not prove the limit.

Formal proof source: `mu_pnt_alt` in PNT+,
`PrimeNumberTheoremAnd/Consequences.lean`, pinned at
a5154676af9aa3095150ee410cdda80555aa0642:
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.
The local `NumberTheory/PrimeNumberTheorem` compatibility port supplies it
on the project's Mathlib version. This module converts its real cutoff and
half-open sum to the positive, inclusive sum, with no cancellation premise.
-/


noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

private theorem mobiusReciprocalSum_eq_range (N : ℕ) :
    mobiusReciprocalSum N =
      ∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  unfold mobiusReciprocalSum
  apply Finset.sum_subset
  · intro d hd
    have hd' := Finset.mem_Icc.mp hd
    exact Finset.mem_range.mpr (by omega)
  · intro d hd hnot
    have hd' := Finset.mem_range.mp hd
    have hd0 : d = 0 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      omega
    simp [hd0]

/-- The actual reciprocal Möbius sums tend to zero, with no unproved
arithmetic premise. The formal provider is PNT+'s `mu_pnt_alt`. -/
theorem mobiusReciprocalSum_tendsto_zero :
    Tendsto mobiusReciprocalSum atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp RiemannResearch.NumberTheory.PrimeNumberTheorem.mu_pnt_alt
  have hnat : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.floor_natCast, ← mobiusReciprocalSum_eq_range]
    using hreal.comp hnat

end RiemannResearch.RH.Pareto
