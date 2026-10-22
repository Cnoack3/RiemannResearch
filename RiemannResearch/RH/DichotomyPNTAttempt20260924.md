# Dichotomy plus PNT: Lean proof attempt and exact obstruction
Date: 2026-09-24
Starting commit: e54c4b17a0255421f13643dcbed3653c5b736158

## Conclusion

This attempt did not prove unconditional RH. The PNT input is already used
inside the actual residual-tail dichotomy. It forces divergence in the
positive-residual branch; it does not give an opposing upper bound.

The new verified result is an exact Hilbert-space compatibility construction.
It shows that exact-head interpolation, orthogonality, vanishing Hilbert tails,
and sublinear full error energy can all coexist with the divergent branch.
Its hyperplane is not identified with the arithmetic legal space.

## What the actual repository results say

Write r for the actual limiting projection residual, L = ||r||^2, and
T_N = ||hilbertTailShift r N||^2. For the canonical exact-head legal candidate
F_N, write A_N = ||hilbertOne - F_N||^2.

The established results give:

- T_N -> 0, because r is a Hilbert vector.
- L^2 <= T_N A_N, by the exact-head Cauchy--Schwarz argument.
- A_N/N -> 0, using the established PNT provider.
- If L > 0, then N T_N -> +infinity.
- If L = 0, then r = 0 and every T_N = 0.

Relevant declarations:

- CanonicalMobiusPNT.mobiusReciprocalSum_tendsto_zero
  (namespace RiemannResearch.RH.Pareto).
- CanonicalMobiusPNT.canonicalMobiusHilbert_sublinear.
- ExactHeadResidualTail.residual_tail_product_lower
  (namespace RiemannResearch.RH.Pareto.CoefficientStabilization).
- ParetoResidualTailDichotomy.actual_normalized_residual_tail_dichotomy.
- ResidualTailPNT.residual_tail_eventual_explicit_lower.

The filenames above qualify the sources, not the Lean namespaces. PNT's
reciprocal Mobius cancellation is documented in Tao, “A remark on partial
sums involving the Mobius function,” arXiv:0908.4323, introduction:
https://arxiv.org/abs/0908.4323. The local provider is the pinned PNT+
compatibility port, not an axiom imported from prose.

The quantitative full-energy ceiling is also consistent with the divergent
branch. It transfers to a lower bound on N T_N. It supplies no upper bound
on N T_N. The separate exact-head optimum dichotomy
BalancedExactHeadEnergy.energy_limit_dichotomy says the optimum tends to
one or to infinity; a sublinear bound does not eliminate infinity.

## New exact Hilbert construction

The new module is RH/ParetoTailRateCompatibility.lean.

First, exists_hilbert_of_tail_energy proves that any decreasing sequence
t_N tending to zero is exactly the tail energy of a Hilbert vector:
its coordinates are sqrt(t_n - t_(n+1)). This retains the entire infinite
tail.

Choose

    t_N = 1/sqrt(N+1),       e_N = sqrt(N+1).

Lean verifies exactly t_N e_N = 1, together with

    t_N -> 0,   N t_N -> +infinity,   e_N -> +infinity,   e_N/N -> 0.

This is realized by a unit vector g in the actual Pareto Hilbert space.
Its coordinates are nonnegative, its first coordinate is positive, and
c = inner(g, hilbertOne) is strictly positive.

Let mask_N(g) retain g's coordinates at indices n >= N and vanish before N.
Define

    F_N = hilbertOne - (c/t_N) * mask_N(g).

The main declaration
TailRateCompatibility.exists_hyperplane_exact_head_sublinear_divergence
proves the existence of these vectors with all of the following:

- inner(g, F_N) = 0;
- hilbertSequence(F_N)(k) = 1 for every 1 <= k <= N;
- ||hilbertOne - F_N||^2 = c^2 sqrt(N+1);
- these error energies tend to positive infinity;
- these error energies divided by N tend to zero.

The auxiliary exists_hyperplane_exact_head_error establishes the sharp
identity for any target vector:

    ||tail_N(g)||^2 * ||target - F_N||^2 = inner(g,target)^2.

Thus the Cauchy--Schwarz tail-product bound can be an equality.

Geometrically, the orthogonal hyperplane does not contain hilbertOne since
c > 0. Its projection residual is c*g, with energy c^2 and tail energy
c^2/sqrt(N+1); the resulting tail/error product is exactly c^4. The checked
main declaration states the inner-product, exact-head and energy identities
directly; it does not identify this hyperplane with the arithmetic legal
space or invoke a projection API for that geometric interpretation.

## Arithmetic attempt and remaining obligation

The signed-average formulas in CanonicalMobiusSignedAverages retain the
complete infinite tail covariance. Bounds on the individual candidate norms
do not provide the cancellation needed in the growing signed quadratic form.
The fixed-modulus discrepancy identities likewise do not bound that form.

The precise existing sufficient obligation is still

    exists C : Real, frequently N atTop, N * residualTailEnergy N <= C.

The actual theorem
CoefficientStabilization.riemannHypothesis_of_frequently_bounded_actual_tail
then gives Mathlib RiemannHypothesis with PNT already discharged.

No provider of that estimate was obtained. The construction above refutes
only the inference from the listed analytic properties alone; it is not
a counterexample to RH or to the Mobius identities. An advance along this
route must estimate the actual residual or the actual signed arithmetic
covariance more strongly.

## Verification

The coherent Lean candidate completed successfully with exit code 0
(job_GxFpIITN6nvo29IMKgmcHcP0SKD57mhr). Audits of the three principal
declarations listed only propext, Classical.choice and Quot.sound.
The persisted source contains no placeholders or project-local axioms.
The final checkpoint validates the saved module before publication.
