# Canonical prime coefficient summability — 2026-11-12

## Conclusion

Absolute summability of the canonical coefficients of the actual prime
projection d_W has **not** been established. The new results identify an
exact necessary and sufficient increment bound and an obstruction to
deducing it from the Q norm alone.

The mathematical statements below use the actual inverse-square physical
Hilbert space, not a Haar replacement.

## Definitions

Let Q(n)=1/(zeta(2)n^2) for n>=1, g_p(n)=(n mod p)/p, and
W=closure(span{g_p : p prime}) in L2(Q). Extend physical functions by f(0)=0.

For f in W define

    Delta f(n) = f(n)-f(n-1),
    a_p(f) = f(1)-f(p)+f(p-1) = f(1)-Delta f(p).

For a finite prime set E let m(E)=product_{p in E} p, with m(empty)=1.

## Exact identities and checked declarations

The RH module is
RiemannResearch/RH/QPrimeCoefficientSummability.lean.
Its namespace is RiemannResearch.RH.QPrimeCoefficientSummability.

- canonicalCoefficient_qResidue: a_p(g_q)=1 if p=q and 0 otherwise.
- canonicalCoefficient_tendsto: Q-norm convergence implies convergence of
  each fixed canonical coefficient.
- primeProduct_difference:

      Delta f(m(E)) = f(1)-sum_{p in E} a_p(f).

  The proof is first made on prime atoms and then extended by linearity and
  continuity to W. It does not interchange an infinite series with evaluation.

- finite_absolute_budget_exact: put
  E_plus={p in E : a_p(f)>=0}, E_minus={p in E : a_p(f)<0}. Then

      sum_{p in E}|a_p(f)| =
        Delta f(m(E_minus))-Delta f(m(E_plus)).

  Both signed subsets and both increments are retained.

- summable_abs_of_increment_bounds: if there are fixed real L,U such that

      L <= Delta f(m(E)) <= U

  for EVERY finite prime set E, then

      sum_p |a_p(f)| <= U-L < infinity.

- increment_bounds_of_summable_abs: if A=sum_p |a_p(f)| is finite, then

      f(1)-A <= Delta f(m(E)) <= f(1)+A

  for every finite E.

- summable_abs_iff_increment_bounds: the preceding two directions give a
  necessary and sufficient criterion. Since m(E) runs through the positive
  squarefree integers, this is exactly bounded oscillation of the increments
  on squarefree sites.

- summable_abs_of_physically_bounded: a bound |f(n)|<=C for all n gives

      sum_p |a_p(f)| <= 4 C.

- no_uniform_coefficient_norm_bound: there is NO constant C such that

      |a_p(f)| <= C ||f||_Q

  for all f in W and all primes p. Indeed a_p(g_p)=1 while ||g_p||_Q tends
  to zero as p tends to infinity. This is a barrier to a uniform norm estimate,
  not a counterexample to absolute summability for the actual d_W.

The reusable finite-subset arguments are in
RiemannResearch/Analysis/SubsetSumSummability.lean:
sum_abs_eq_positive_sub_negative, sum_abs_le_of_subset_sum_bounds,
summable_abs_of_subset_sum_bounds, and
tsum_abs_le_of_subset_sum_bounds.

## Application to the actual displacement: conditional, still open

Let d=f_Q-f_P and d_W=projection_W^Q(d). Since d_W belongs to W, all
identities above apply to its canonical a_p.

The existing normal equation gives

    d_W = projection_W^Q(B r_P),   (B h)(n)=h(n)/(n+1).

Although B r_P tends to zero physically, no bound preserving that regularity
under projection_W^Q is supplied here. The missing provider is:

    There exist finite L,U such that
    L <= Delta d_W(m(E)) <= U for every finite prime set E.

Equivalently, the exact finite absolute budgets must be uniformly bounded.
A bound for each fixed E, with constants growing with m(E), does not discharge
this obligation. Coordinatewise convergence of finite inverse-Gram coefficients
also does not discharge it.

No unconditional theorem Summable (fun p => abs (a_p(d_W))) is claimed.
No new RH implication or RH equivalence has been established in these modules.
In particular, the existing boundedness rigidity theorem for the full d
must not be silently applied to its component d_W.

## Profinite interpretation

For X=product_p Z/pZ, the universal property assembles residue coordinates.
For a fixed real coefficient family, convergence of sum_p a_p r_p/p at EVERY
x in X forces sum_p |a_p|<infinity, by choosing separate positive- and
negative-sign endpoint residue tuples. Conversely absolute summability gives
uniform convergence, hence a continuous real-valued function on X.

This analytic tail requirement is not a conclusion of CRT or Bezout.
The preceding paragraph is a mathematical explanation; the new Lean modules
formalize the physical coefficient and increment criterion.

## Provenance and verification

Source: this conversation's canonical coefficient and prime-atom argument,
with standard finite positive/negative splitting. No novelty claim is made.

Michel Balazard, "An arithmetical function related to Baez-Duarte's criterion
for the Riemann hypothesis", arXiv:1812.04309, Proposition 4 and formula (6),
provides the published context for continuous arithmetic coefficient
functionals and the distinction between pointwise and Hilbert expansions.
https://arxiv.org/abs/1812.04309
The new finite-product proof does not require that external result as an axiom.

Verification is performed by the Lean server with Bazel/BuildBuddy.
The final response records the terminal checkpoint job and published commit.

Focused proof verification: job_lGI7LmjmZR9-Rmc9ZMJRBp-8Jd9R-NlC, Bazel/BuildBuddy, exit 0, 57.927 seconds server verification time.
Evidence: https://app.buildbuddy.io/invocation/d87e13ff-bab0-4319-9336-510752173f21
This focused result precedes final module integration and the mandatory full checkpoint.

## Additional inverse-Gram sign investigation (external computation)

An attempted route was to control coefficient variation through a uniform
sign pattern of the inverse prime Gram matrices. Wolfram evaluated the
complete-Q matrices, using the finite-period identity

    G(p,q) = (1/(zeta(2)*L^2)) *
      sum_{r=1}^L ((r mod p)/p)*((r mod q)/q)*psi_1(r/L),
    L=lcm(p,q),

where psi_1 is the trigamma function. This retains every infinite-tail term;
there is no finite integer cutoff.

For the first ten primes, evaluated at 25-digit precision, positive
off-diagonal inverse entries included

    G_10^{-1}(p=2,q=13) = 0.0304907110345158823848995...
    G_10^{-1}(p=2,q=29) = 0.813894274554815972130428...
    G_10^{-1}(p=11,q=29) = 3.30793969132255190604274...

Thus the hoped-for nonpositive off-diagonal pattern is not supported by
this computation. These are external numerical diagnostics, not Lean
theorems or interval certificates, and do not decide actual a_p summability.

## Integrated-module axiom audit

The integrated modules and four principal declaration audits passed job
job_cpuIBpCssM143G7M2BDobiecFGbA9QpM (Bazel/BuildBuddy, exit 0; 53.214 seconds).
Guarded output confirms exactly [propext, Classical.choice, Quot.sound] for
finite_absolute_budget_exact, summable_abs_iff_increment_bounds,
summable_abs_of_physically_bounded, and no_uniform_coefficient_norm_bound.
The explicit increment bounds in the theorem types remain hypotheses.
https://app.buildbuddy.io/invocation/3b56f821-2a86-4047-baf0-a3ea357eb210
