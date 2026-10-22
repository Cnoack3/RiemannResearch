# Squarefree Q closure without an assumed uniform bound

Research record for Christian Noack. October 17, 2026.

## Outcome

The requested assertion is
```
qOne ∈ qSquarefreeCRTSpan.topologicalClosure
```
for the actual inverse-square Hilbert space, with
Q(n)=1/(zeta(2)n^2) and g_d(n)=(n mod d)/d, d>=2 squarefree.

This investigation does not prove that assertion. It establishes a precise
dual route with no hypothesis about a uniformly bounded approximating
family, proves that any separator must have infinite physical support, and
extends the localized zero obstruction to arbitrarily sparse power-cost
comparisons. The corresponding arithmetic providers remain Open.

Bagchi's Remark 8 gives the squarefree discrete criterion. The equivalent
weight discussion permits weights comparable to n^-2, so the requested
closure statement is equivalent to RH. This reverse literature implication
is not newly formalized here.

Source: Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, Remark 8 and the discussion after
Theorem 1, https://arxiv.org/abs/math/0607733.

## 1. A route with no assumed approximant bound

Let S be the algebraic real span of the squarefree legal atoms, and H its
norm closure in L^2(Q). Standard Hilbert-space orthogonal duality gives

    1 ∈ H
      iff
    for every h ∈ L^2(Q),
      [<h,g_d>_Q = 0 for every squarefree d>=2] implies <h,1>_Q = 0.

There is no approximating sequence, coefficient bound, or energy bound in
this statement. It is an exact equivalence, not a proof of its right side.

Proof: S-perp is exactly the set of vectors annihilating every generator,
and (S-perp)-perp is the norm closure of S. In the actual project this is
proved by `annihilator_iff` and `closure_iff_annihilator_mean_zero`.

The complete physical form is

    [sum_{n>=1} h(n) g_d(n)/(zeta(2)n^2) = 0 for all squarefree d>=2]
      implies
    sum_{n>=1} h(n)/(zeta(2)n^2) = 0.

All these series converge absolutely by weighted Cauchy--Schwarz. Lean
uses the actual Q Hilbert realization and retains the entire infinite
series in `closure_iff_weighted_annihilator`.

## 2. The exact obstruction if closure fails

If 1 is outside H, there exists h in L^2(Q) such that

    <h,g_d>_Q = 0 for every squarefree d>=2,
    <h,1>_Q = 1.

For every finite legal squarefree combination F,

    1 <= ||h||_Q^2 * ||1-F||_Q^2.

Indeed <h,1-F>_Q=1, and Cauchy--Schwarz gives the displayed inequality.
This supplies a positive norm-distance obstruction without making any
assumption about F's norm.

Lean declarations:
- `normalized_separator_of_not_closure`;
- `normalized_separator_error_lower`.

## 3. Why the obstruction must be infinite

The existing `Pareto.squarefree_finite_observation_annihilator` proves
unconditionally that every finite-coordinate linear functional vanishing
on all squarefree atoms also vanishes on 1. Its proof uses exact legal
interpolation of arbitrary finite physical heads.

The new Q specialization proves:
- `inner_eq_finite_head`: the pairing is a literal finite head sum when
  the test vector really has finite physical support;
- `finite_support_annihilator_mean_zero`: such an annihilator has mean zero;
- `normalized_separator_has_tail`: every normalized separator has a
  nonzero physical coordinate beyond every finite cutoff.

Therefore testing longer and longer finite heads cannot alone settle the
infinite dual statement. Approximating an arbitrary annihilator by arbitrary
finite truncations also does not solve the problem: those truncations need
not continue annihilating the atoms.

## 4. An explicit arithmetic tail formulation

This section is a paper derivation, not an additional Lean theorem.

Set a_n=Q(n)h(n). Then

    sum n^2 |a_n|^2 < infinity,
    sum |a_n| < infinity.

Conversely every real a satisfying the first condition comes from the
Q vector h(n)=zeta(2)n^2 a_n. Thus the precise open arithmetic implication is

    sum a_n g_d(n)=0 for all squarefree d>=2
      implies
    sum a_n=0,

under the stated weighted square summability.

Put A(k)=sum_{n>=k} a_n. Then A(k)=o(k^(-1/2)), by Cauchy--Schwarz applied
to the weighted square-summable tail.

For each fixed d>=2, summation by parts inside each finite block gives

    sum_{r=1}^{d-1} (r/d) a_{md+r}
      = (1/d) sum_{r=1}^d A(md+r) - A((m+1)d).

Consequently

    sum_{n>=1} a_n g_d(n)
      = sum_{m>=0} [(1/d) sum_{r=1}^d A(md+r) - A((m+1)d)].

This block series is absolutely convergent: the absolute value of a block
is at most the sum of |a_{md+r}| over that block. Individual ungrouped
series in A need not converge and must not be separated.

The desired arithmetic conclusion is A(1)=0. The facts that these block
averages vanish and that A(k)=o(k^(-1/2)) do not currently prove it.

## 5. A conditional zero explains the remaining difficulty

This section records the classical analytic separator strategy, not a
newly verified zeta identity in this module.

For a hypothetical zero s with beta=Re(s)>1/2, let

    a_n=n^(-s)-(n+1)^(-s).

Then sum n^2|a_n|^2 is finite, sum a_n=1, and

    sum a_n g_d(n) = (d^(-1)-d^(-s)) zeta(s) = 0.

The identity follows first by convergent summation in Re(s)>1 and then
analytic continuation to Re(s)>0, with the removable point s=1 handled.
Taking real parts gives a real annihilator with nonzero mean.

Thus the missing infinite dual uniqueness assertion must exclude exactly
the kind of continuous separator supplied by an off-critical zero.
Scalar or coordinatewise continuation of a profinite construction does
not remove this continuous-functional obstruction.

## 6. A second route allowing unbounded error energies

The existing verified localized Mellin theorem gives the complete Q bound

    [(2 Re(s)-1)/(zeta(2)||s||^2)] n^(2 Re(s)-1)
      <= ||1-F||_Q^2

whenever s is an off-critical zero and F is squarefree legal with
F(k)=1 for 1<=k<n.

The new theorem
`QExactHeadSubpolynomial.riemannHypothesis_of_arbitrarily_small_power_cost`
therefore proves RH from the following hypothesis:

For every a>0, every c>0, and every cutoff N, there exist n>=max(1,N)
and a finite squarefree legal F such that

    F(k)=1 for 1<=k<n,
    ||1-F||_Q^2 < c n^a.

Proof: given an off-critical zero, choose
a=2 Re(s)-1 and c=(2 Re(s)-1)/(zeta(2)||s||^2). The supplied candidate
contradicts the complete lower bound.

This allows arbitrarily sparse stages and different choices for every
power, constant, and cutoff. No uniform bound on the chosen energies is
assumed. A cofinal family with subpolynomial energies, even energies
tending to infinity, would suffice.

The power-cost existence assertion is an Open arithmetic provider.
This theorem proves actual Mathlib RH conditionally; it does not by itself
supply the reverse RH-to-squarefree-closure theorem from the literature.

## 7. What was attempted and what remains

The direct infinite-CRT approach supplies pointwise legal approximants and
unconditional convergence after taking physical differences. The previous
records demonstrate that the natural primitive families can have escaping
Q energy. This investigation therefore passes to the full continuous dual
and to sparse power-cost comparisons instead of assuming primitive bounds.

Highest-priority next obligations:

1. Prove mean zero for every squarefree annihilator in the full weighted
   square-summable class. Preserve the block grouping above.
2. Alternatively, prove arbitrarily cheap positive-power exact heads for
   the complete signed affine minima. The costs may be unbounded.
3. Investigate approximation of infinite annihilators by finite-support
   annihilators while preserving annihilation. Ordinary coordinate
   truncation is insufficient; no such density theorem is asserted.
4. If using damped Mobius sums, establish convergence in the Q Hilbert
   space itself. Coordinate analytic continuation alone does not establish
   closed-span membership.

No trigamma convergence route is used.

## 8. Formal verification and scope

New module: `RH/QSquarefreeDualClosure.lean`.
Extended module: `RH/QExactHeadSubpolynomial.lean`.

Server snippet checks succeeded:
- job_TyKqgf19YEFcYKgt8zgA8Udx8Q8_tZRE: initial dual and sparse-power proofs;
- job_ELRPsVcwdkPmfNkiEMumECWXksbzNqmu: complete dual module, finite-support
  specialization, and cofinal sparse-power theorem.

Axiom reports for the weighted dual criterion, infinite-support
separator theorem, and sparse-power RH consumer list only
`propext`, `Classical.choice`, and `Quot.sound`.

These checks certify the exact declared implications. They do not certify
a provider of the infinite dual uniqueness or sparse-power hypothesis.
Final project publication is gated by the server checkpoint, whose terminal
job and commit are reported with delivery.
