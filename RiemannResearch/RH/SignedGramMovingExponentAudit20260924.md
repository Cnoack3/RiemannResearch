# Signed Gram moving-exponent audit (2026-09-24)

No unconditional proof of RH was obtained.

The new module RawMobiusSignedGramMovingExponent proves three conditional
research reductions for the actual ordered signed off-diagonal energy Q_N.

1. Q_N ≤ C(N+1)^α cofinally, α>0, implies zero-freeness for Re(s)>(1+α)/2,
   with s ≠ 1.
2. Exponents α_j → 0 suffice, each with its own constant and cofinal set.
   Neither uniform constants, positive exponents, nor common good indices
   are needed in this sequence version.
3. A single frequent envelope Q_N ≤ C(N+1)^α_N with α_N → 0 also implies RH.

The estimates themselves remain Open. The proofs are monotonicity/quantifier
assembly over existing checked Mellin and signed-Gram results.

Literature checked directly:
- Baez-Duarte, arXiv:math/0011254, Remark 4.5: zero-freeness gives raw L^r
  convergence below the endpoint; endpoint convergence does not follow.
  https://arxiv.org/pdf/math/0011254
- Baez-Duarte, arXiv:math/0205003, after (2.6): fractional-part Mellin identity.
  Proposition 3.1 and the Burnol ratio estimate in its proof assume RH.
  They cannot be used as unconditional arithmetic providers.
  https://arxiv.org/pdf/math/0205003
- Baez-Duarte, arXiv:math/0202141, Corollary 3.1 and following paragraph:
  damped-family subsequences motivate the new quantifier assembly.
  That analytic criterion is not newly formalized here.
  https://arxiv.org/pdf/math/0202141
- Alouges, Darses, Hillion, arXiv:2006.02953v2, Theorem 3: both weighted
  approximation decay (2.12) and coefficient-tail decay (2.13) are needed.
  Unconditional density does not provide their simultaneous rate.
  https://arxiv.org/pdf/2006.02953

The unconditional budget bound controls B_N/N, tending to zero. It does not
give a sequence of exponents approaching zero. The completed N² far tail
does not control the remaining middle window.

A countable arithmetic target is α_j=1/(j+1), allowing independent constants
and cofinal sets. Even a cofinal square-root bound would exclude zeros
right of 3/4; this is a substantive arithmetic target, not a routine lemma.
A feasible unconditional formalization target remains the centered CRT
covariance/divisor-square identity and finite-interval large-sieve provider.

All three original proof bodies passed isolated Lean verification, exit 0,
with only propext, Classical.choice and Quot.sound. An unused positivity
hypothesis was removed before final checkpoint. Saved-module validation and
publication are reported in the response. No sorry or extra axioms are added.
