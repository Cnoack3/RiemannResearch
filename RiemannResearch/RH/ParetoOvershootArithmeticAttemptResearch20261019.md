# Attempt at the arithmetic overshoot endpoint estimate

**Status: the requested unconditional arithmetic upper bound remains unproved.**
The new Lean results establish exact finite-head localization, an unconditional
uniform tail bound, and a conditional finite-head criterion. They do not provide
the remaining arithmetic head estimate or prove RH.

Source: Christian Noack's request of 19 October 2026 to prove the actual Pareto
overshoot estimate in Lean, using Wolfram only for symbolic computation and
web search for relevant mathematics.

## Exact requested assertion

Let F_M be the actual orthogonal projection of 1 onto the full Pareto legal
space spanned by g_d(n) = (n mod d)/d, 2 <= d <= M. Every expectation uses
the complete probability weights P(n) = 1/[n(n+1)], n >= 1. Set

    r_M = 1 - F_M,
    delta_M = ||r_M||_P^2,
    omega_M = E_P[(F_M - 1)_+],
    a = 1 - 1/sqrt(2).

The requested assertion is

    for every epsilon > 0 and every M0, some M >= M0 satisfies
    omega_M <= a delta_M + epsilon.

The existing checked criterion identifies this assertion with vanishing of
the actual limiting residual. Its RH implication is already formalized.
No unconditional provider of this assertion was found in this attempt.

## Established exact finite-head and tail results

Define the finite arithmetic sum

    B_(M,H) = sum_(1 <= k <= H) (F_M(k) - 1)_+ / [k(k+1)].

The new generic negative-part vector is the complete physical sequence r_-.
Its norm is at most ||r||. The primary identity retains the full tail pairing:

    omega_M = B_(M,H) + <(r_M)_-, 1_(k>H)>_P.

The last term is nonnegative. Since the exact Pareto tail mass is 1/(H+1),
Cauchy--Schwarz gives the unconditional two-sided enclosure

    0 <= omega_M - B_(M,H) <= sqrt(delta_M/(H+1)).

The Lean statement writes the upper allowance equivalently as
`||projectionResidual n|| * sqrt(1/(H+1))`.
The actual projection residual norm is at most 1, so the tail is uniformly
bounded by 1/sqrt(H+1), without assuming RH or vanishing residual energy.

Take H = M-1. Then B_(M,M-1) converges to the complete limiting overshoot.
Consequently the requested cofinal bound is equivalent to the finite condition

    for every epsilon > 0 and every M0, some M >= M0 satisfies
    B_(M,M-1) <= a delta_M + epsilon.

The stage index in Lean is n=M-1, with conductors 2,...,n+1 and physical
head sites 1,...,n. The finite sum uses the actual projection, whose
coefficients are the true inverse-Gram coefficients. This input remains Open.
No finite truncation error is being used to replace this input.

## Lean source and validation

- `RH/ParetoNegativeMassHead.lean`: the actual negative-part vector, its norm
  bound, exact finite sum, exact complete tail pairing, positivity, and tail
  enclosure. Seven public theorems and two definitions.
- `RH/ParetoOvershootHeadCriterion.lean`: the actual projection head sum,
  unconditional tail enclosure, convergence of diagonal heads, and the
  conditional cofinal equivalence and RH consumer. Five public theorems and
  one definition.

The coherent candidate and all 12 public axiom checks passed
`job_lrmajfiqgiMyazUYjWdGWUw8uQAZMnQi`. Each depends only on `propext`,
`Classical.choice`, and `Quot.sound`. This targeted verification is distinct
from the mandatory final checkpoint of the aggregate and changed modules.

## Why the direct estimates did not close the proof

The earlier exact endpoint gap gives a nonnegative lower bound. Combining
it with ||r||_1 <= ||r|| does not give the required arithmetic upper bound.
As a symbolic consistency check only, Wolfram simplifies the following
simultaneous scalar inequalities to True at

    delta = 1/64, omega = 1/128, x = 1/64:
    a delta + ((3 sqrt(2)-4)/4) delta^2 <= omega,
    omega <= (sqrt(delta)-delta)/2,
    omega > a delta,
    (2-sqrt(2)) delta + (sqrt(2)/4) x^2 <= x,
    x <= 2 omega.

These numbers are not actual optimizer data and do not refute the requested
estimate. They show why these scalar inequalities alone cannot supply the
missing arithmetic upper estimate. Wolfram was used only for exact symbolic
algebra; the new project proofs were checked independently by Lean.

## Primary literature checked

Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis* (2006), Theorem 1 and the final
discussion of the discrete Gram-distance problem:
https://arxiv.org/abs/math/0607733
The paper supplies the discrete closure background, not the upper estimate
requested here.

Sandro Bettin, J. Brian Conrey, David W. Farmer, *An optimal choice of
Dirichlet polynomials for the Nyman-Beurling criterion*, Theorem 1:
https://arxiv.org/abs/1211.5191
Its sharp asymptotic assumes RH and an additional reciprocal-zeta-derivative
moment hypothesis. It cannot serve as an unconditional arithmetic provider
in this proof. No assertion is made that the literature search was exhaustive.

## Remaining research obligation

Prove the finite cofinal inequality for B_(M,M-1) from the actual signed
inverse-Gram coefficients, or produce an independent unconditional argument
that forces the limiting residual to vanish. The new formalization isolates
this obligation; it does not discharge it.
