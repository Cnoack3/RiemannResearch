# Proof status: the actual Pareto Dirichlet exponential

**Date:** 2026-11-13. **Status:** Lean verification passed for the complete public module and all 13 new modules. Bazel target `//RiemannResearch/RH:ParetoDirichletExponential` exited with code 0. [Verification invocation](https://app.buildbuddy.io/invocation/9cf04a20-f8d3-4e55-96c3-66433e128550).

The formalization uses actual Dirichlet convolution and its unit δ₁. For `g_k(n) = (n mod k)/k`, `convolutionExp (residueAF k)` is the genuine infinite series ∑ᵣ g_k^{⋆r}/r!. The arithmetic input is identified exactly with the existing normalized physical Pareto residue. The positive constant-one arithmetic function `zetaReal` is distinct from the convolution unit.

The proved generalized-divisor estimate is

\[
\sum_{n\ge1}\frac{((\zeta^{\star r})(n))^2}{n^2}
\le (12e^2)^r r!.
\]

It supplies absolute convergence of the actual Hilbert Taylor series for every bounded real arithmetic input. Continuous physical-coordinate evaluation identifies that Hilbert sum with the scalar arithmetic exponential. Thus the proof establishes complete Pareto energy for the universal envelope exp⋆(ζ) and for every residue exponential.

The public module `RH/ParetoDirichletExponential.lean` defines `residueExponential : ℕ → ThresholdHilbert` with no external energy assumption. Its coefficients converge to δ₁ because fixed residue coordinates eventually equal n/k; dominated convergence in the exponential index justifies passage through the infinite scalar series. The inequalities δ₁ ≤ E_k ≤ exp⋆(ζ), together with the checked envelope energy, then prove E_k → δ₁ in the actual Hilbert norm.

Actual closed-span legality along arbitrarily large primes is equivalent to `closedSpace = ⊤`. Closedness puts the unit limit in V; the existing first-coordinate and residue-density equivalences yield 1 ∈ V and V = H. The project already proves that this implies Mathlib RH.

The RH conclusion from cofinal exponential legality is a **conditional research reduction**. **Open:** prove the actual cofinal-legality hypothesis, equivalently the residue-density statement. The converse RH-to-density provider remains **Open as a formalization dependency**. The RH equivalence therefore displays `hDensity : RiemannHypothesis → closedSpace = ⊤` explicitly. Neither obligation is supplied by the new files.

For every prime p, choosing a distinct prime q gives E_p(q^a) ≥ (a+1)/(2p²). The exponential is therefore unbounded. Finite linear combinations of normalized residues have bounded physical sequences, so the actual exponential lies outside the algebraic residue span. **Open in these modules:** membership in the closed residue span for one specified prime. Unboundedness does not decide that separate question.

The focused catalog [THEOREM_CATALOG_DIRICHLET_EXPONENTIAL_20261113.md](../THEOREM_CATALOG_DIRICHLET_EXPONENTIAL_20261113.md) records the module paths and declaration map. The bounded-input results do not assert that exponentiation maps every vector of H or V back into H.
