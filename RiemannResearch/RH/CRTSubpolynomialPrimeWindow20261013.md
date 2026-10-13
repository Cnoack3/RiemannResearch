# Subpolynomial CRT tails and an explicit prime window

Date: 13 October 2026. Source: Christian Noack's exact-head CRT research request.
Status: verified conditional research reductions; the required arithmetic
growth estimate is not proved.

## What is established, and what remains open

The original uniformly bounded exact-head tail assumption is not established
here. The new result weakens that sufficient hypothesis to subpolynomial
growth, and also isolates a concrete finite sum for a fixed Mobius trial.
No unconditional proof of the Riemann Hypothesis is claimed.

Write
```text
r_d(n) = (n mod d) / d,
B(M,L,F) = sum_{a=M+1}^L |1-F(a)|^2/a^2.
```
An admissible trial has squarefree L, F in the real span of r_d with
2 <= d and d dividing L, and F(n)=1 for 1 <= n <= M.
All sums and coefficients below are real unless otherwise indicated.

## A weaker sufficient hypothesis for the original CRT trials

For any sequence of admissible trials with M_j tending to infinity, it is
enough that
```text
log(1+B(M_j,L_j,F_j)) / log(M_j+1) --> 0.
```
Uniform boundedness is unnecessary. In particular this allows any fixed
polylogarithmic upper bound in M_j.

A countable finite-certificate version is:
```text
For each integer j >= 0, find one admissible (M,L,F) with
    M >= j+1,
    B(M,L,F) <= (M+1)^(1/(j+1)).
Then RH.
```
There is no nesting requirement on the periods or supports.

An even more flexible sparse formulation is also proved: for every positive
epsilon and eta there exists an admissible trial with
B(M,L,F) < eta * (M+1)^epsilon. No predetermined sequence is required.

The reason is quantitative. If s=beta+i*gamma is an actual zeta zero with
beta>1/2 and s != 1, every admissible trial satisfies
```text
B(M,L,F) >= (2*beta-1)/(zeta(2)*|s|^2) * (M+1)^(2*beta-1).
```
The proof first preserves the Mellin error identity, then applies the
localized exact-head norm lower bound. The full Pareto error is at most
zeta(2)*B, using the already verified Q comparison.

## One explicit arithmetic family; no coefficient search

For a prime p, put
```text
A_{p-1} = sum_{d=1}^{p-1} mu(d)/d,
F_p(n) = -sum_{d=1}^{p-1} mu(d)*r_d(n) + p*A_{p-1}*r_p(n).
```
This is the existing canonicalMobiusHead(p-1), not a new unproved family.

Already proved, including the new squarefree-span membership:
- F_p(n)=1 for 1 <= n <= p-1.
- Nonsquarefree interior conductors have zero Mobius coefficient, and p is
  squarefree. Thus F_p belongs to a squarefree common-period divisor span.
- |F_p(n)| <= 2*(p-1), hence |1-F_p(n)| <= 2*p.
- Its floor expansion is
  F_p(n)=sum_{d<p} mu(d)*floor(n/d) - p*A_{p-1}*floor(n/p).
  The existing exact identity retains the signed cancellation.

Define the explicit quadratic-window energy
```text
E(p) = sum_{n=p}^{4*p^2} |1-F_p(n)|^2/n^2.
```
The new verified tail estimate is
```text
||1-F_p||_P^2 <= E(p) + 1,
where P({n})=1/(n*(n+1)), n>=1.
```
Indeed the infinite tail is at most (2*p)^2/(4*p^2+1) <= 1.
The quadratic cutoff need not be a CRT period.

Consequently, either of the following arithmetic providers suffices for RH:
1. Along cofinal primes p_j,
   log(1+E(p_j))/log(p_j) tends to zero.
2. For every integer j>=0 there is a prime p>=j+2 with
   E(p) <= p^(1/(j+1)).

All support, exact-head, and infinite-tail facts for this fixed family are
proved. Only the stated finite-window growth provider remains missing.
The reduction does not assert that a particular provider is easy or follows
from the prime number theorem.

## Lean declarations and scope

- Analysis/VanishingExponentBudget.lean:
  relativeLog_tendsto_zero_of_reciprocal_exponent.
- RH/CRTReciprocalPowerObstruction.lean:
  periodic_error_le_zetaTwo_mul_reciprocalEnergy;
  normalizedResidue_exact_head_residual_power_lower;
  crtTailEnergy_power_lower_of_zeta_zero.
- RH/CRTSubpolynomialTail.lean:
  riemannHypothesis_of_squarefree_crt_power_infimum_zero;
  riemannHypothesis_of_squarefree_crt_subpolynomial_tail;
  riemannHypothesis_of_squarefree_crt_reciprocal_exponents.
- RH/ParetoReciprocalWindow.lean:
  paretoInner_eq_reciprocal_window_and_tail;
  paretoInner_le_reciprocal_window_add_tail.
- RH/CanonicalPrimeSubpolynomialWindow.lean:
  canonicalMobiusHilbert_mem_squarefreeCRTSpan;
  canonicalPrime_error_le_window_add_one;
  riemannHypothesis_of_canonical_prime_subpolynomial_window;
  riemannHypothesis_of_canonical_prime_reciprocal_exponents.

Except for the generic logarithm lemma, all are in
RiemannResearch.RH.Pareto. Conclusions named RiemannHypothesis use Mathlib's
actual RiemannHypothesis, through the verified right-half-strip equivalence.
The RH theorems carry their arithmetic provider explicitly as a hypothesis.
