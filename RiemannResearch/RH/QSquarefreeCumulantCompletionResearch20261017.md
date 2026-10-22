# All-order squarefree cumulants, projective completion, and physical Q realization

Date: 17 October 2026.

This continues commit de3660c827e46ba5a145f2acd93e8ba9e2134123 and its
QSquarefreeLatticePacketsResearch20261016.md record. The construction is
motivated by the user's infinite CRT and convolution log/exp proposal.
The finite square-zero extension itself is standard and uses Mathlib's
Mathlib.Algebra.TrivSqZeroExt.Basic. No novelty claim or RH estimate is
imported from an external reference.

## What the new development establishes

Three modules have distinct responsibilities:

* NumberTheory/SquarefreeCumulantTower.lean constructs every finite labeled
  squarefree coefficient algebra, its actual subset convolution,
  normalized moment/cumulant coordinates, and inverse log/exp maps.
* NumberTheory/SquarefreeCumulantLimit.lean constructs variable restrictions,
  proves their compatibility with the transforms, and constructs the
  projective-limit ring and completed normalized coordinates.
* RH/QSquarefreeFormalSynthesis.lean realizes coefficients by literal residue
  atoms in the complete Q Hilbert space, gives exact physical energy tests,
  proves finite reparameterization and closed-span preservation, and exhibits
  compatible cumulants whose physical syntheses are unbounded.

The existing two-prime module is reused and the new tower is proved to
specialize to its log/exp formulas. The existing physical packet,
coordinate-dual, Pareto-transfer, and exact-head averaging modules are reused.
The new sources are subject to mandatory Lean-server checkpoint validation
before publication. A successful snippet is not described as a complete
project verification.

## 1. The finite algebra and all-order transforms

For n labeled distinct primes, let

    A_0 = R,
    A_(n+1) = A_n[X_n]/(X_n^2).

Here R is the real field. The formal Lean construction is an iterated
TrivSqZeroExt; multiplication at each step is

    (a,b)(c,d) = (ac, ad+bc).

The Boolean index type Index n selects a subset of the n variables.
coefficientEquiv identifies A_n with all real arrays on Index n.
coefficient_mul proves that the ring product is the actual disjoint-subset
convolution, recursively expressed by

    (u*v)(S) = sum_(T disjoint U, T union U = S) u(T)v(U).

An equivalent description is R[X_0,...,X_(n-1)]/(X_0^2,...,X_(n-1)^2).
The new code constructs the iterated algebra and its coefficient equivalence;
a separate quotient-polynomial equivalence is not asserted.

augmentation is the constant coefficient. augmentation_nilpotent proves

    augmentation(a)=0  ==>  a^(n+1)=0.

Coordinates n suppresses the constant coefficient. moment n inserts constant
one. coordinatesOf is inverse to moment on precisely the augmentation-one
arrays; no other coefficient restrictions are imposed.

Writing a zero-constant argument as a + X_n b and a normalized moment array
as u + X_n v, the exact recursions are

    exp_*(a + X_n b) = exp_*(a) (1 + X_n b),
    log_*(u + X_n v) = log_*(u) + X_n exp_*(-log_*(u)) v.

The following are proved for every n:

    log_*(exp_*(k)) = k,
    exp_*(log_*(m)) = m,
    exp_*(k+l) = exp_*(k)*exp_*(l),
    log_*(m*r) = log_*(m)+log_*(r).

Associativity and commutativity are proved for the normalized product.
The exponential has augmentation one and exp_*(-k) is its ring inverse.
The two-prime specialization is exactly

    log_*(a,b,c)=(a,b,c-ab),
    exp_*(a,b,k)=(a,b,k+ab).

These are all-order recursive identities in the genuine squarefree ring.
A separate formalization equating these maps to partition sums or to explicit
factorial Taylor polynomials has not been added; neither is needed for the
proved inverse, multiplicative, restriction, or synthesis identities.

## 2. Restrictions and the infinite projective-limit algebra

An arbitrary subset of a finite labeled prime set is represented by a Boolean
mask. restrictAlgebra sets the deleted variables to zero. It is a ring
homomorphism. restrictCoordinates performs the same operation on suppressed
coordinates. The code proves:

    restriction_S o restriction_T = restriction_(S intersection T),
    restriction(exp_*(k)) = exp_*(restriction(k)),
    restriction(log_*(m)) = log_*(restriction(m)),
    restriction(m*r) = restriction(m)*restriction(r).

A finite prime set can be labeled in any order; no arithmetic property enters
the formal algebra. For a countable prime enumeration, prefix stages are
cofinal among finite prime sets. Adjacent prefix restriction drops the last
variable.

The inverse-limit ring is constructed concretely as

    Completion = { (a_n)_n : a_n in A_n,
                   drop(a_(n+1)) = a_n for every n }.

The ring laws are inherited pointwise, and lift and lift_unique give its
universal property for compatible ring maps. CompletedCoordinates is the
analogous compatible family of normalized moment/cumulant coordinates.

expStarLimit and logStarLimit are defined levelwise and are inverse.
They retain exponential multiplicativity and logarithmic additivity at
every order. momentLimit is compatible with the actual ring product.

finiteApproximation supplies finite-polynomial truncations of every
projective element, with

    evaluation_n(finiteApproximation(a,N)) = evaluation_n(a)  for N >= n.

Thus formal approximation is established by eventual exact agreement at
every finite projection. A separate topological-ring instance and a separate
identification with arrays indexed directly by all finite prime subsets are
not claimed here. The constructed algebraic inverse limit and its universal
property are the formal object.

This variable-restriction completion permits infinitely many singleton
coefficients. It must not be silently identified with the ordinary
augmentation-adic completion of the algebraic polynomial ring in infinitely
many variables, which has a different finite-support requirement.

## 3. Actual physical synthesis, with all carries

Let p_j be distinct primes and

    L_n = product_(j<n) p_j,
    d_S = product_(j in S) p_j,
    g_d(k) = (k mod d)/d,
    Q(k) = 1/(zeta(2) k^2), k>=1.

The physical realization of a finite moment array a_n is

    F_n = sum_(S subset {0,...,n-1}) a_n(S) g_(d_S).

The empty-subset term multiplies g_1=0. Consequently normalizing that one
coefficient to one does not change F_n. Every other coefficient remains free.

synthesis_sequence proves the literal value formula

    F_n(k) = sum_S a_n(S) ((k mod d_S)/d_S).

synthesis_atomic_norm proves

    ||F_n||_Q^2
      = sum_(k>=1) Q(k) [sum_S a_n(S) ((k mod d_S)/d_S)]^2.

These are actual residues and the full atomic-Q infinite sum. Every CRT
carry is retained inside the residue. No replacement by a sum of prime
fractional parts or by Haar averaging occurs. This development does not
construct a new CRT pushforward measure; it uses the existing literal
atomic Q realization directly.

synthesis_mem_stage and synthesis_legal put the result in the finite divisor
stage and the algebraic squarefree legal span. Their hypotheses are the
actual positivity and squarefreeness of L_n; repeated or noncoprime labels
are not silently declared squarefree.

## 4. Exact physical admissibility tests

Let G_(m,n)(S,T)=<g_(d_S),g_(d_T)>_Q, including different stage sizes, and
write c_n for the complete finite coefficient vector. The code gives

    E_n = c_n^T G_(n,n) c_n = ||F_n||_Q^2,

    D_(m,n)
      = E_m + E_n - 2 c_m^T G_(m,n) c_n
      = ||F_m-F_n||_Q^2.

All signed cross terms are retained.

For a fixed compatible formal family, its canonical finite-stage syntheses
are uniformly bounded if and only if

    exists B<infinity, for every n, E_n <= B.

They have a strong Q realization if and only if the complete Gram Cauchy
condition holds:

    for every epsilon>0, there is N such that
    sqrt(D_(m,n)) < epsilon for all m,n>=N.

Both equivalences are formalized. This is an exact analytic characterization
through explicit physical Gram forms, not a new arithmetic upper bound.
Boundedness alone is not asserted to imply strong convergence.

For any target t the full error identity is

    ||t-F_n||_Q^2
       = ||t||_Q^2 - 2 sum_S c_n(S)<t,g_(d_S)>_Q + E_n.

The distinction between a fixed compatible family and general legal
approximants is essential. General approximants can alter their higher
coefficients from one stage to the next while every fixed coefficient
converges. No theorem here asserts that every vector in the closed span has
bounded canonical truncations of its recovered coefficients. In particular,
one must not substitute that stronger assertion into an RH equivalence.

## 5. A concrete formal family with no bounded canonical realization

Take compatible normalized moment arrays with

    m(empty)=1, m({p_j})=p_j, m(S)=0 when |S|>=2.

singletonCompletion constructs this projective element.
singletonCoordinates and logStarLimit give a compatible infinite cumulant
family, and singleton_cumulant_synthesis identifies its actual syntheses:

    F_n = sum_(j<n) p_j g_(p_j).

At physical site one,

    F_n(1)=n.

The exact atomic evaluation bound gives

    ||F_n||_Q^2 >= n^2/zeta(2).

singleton_not_bounded and compatible_cumulants_not_bounded prove that these
norms exceed every proposed bound. Nevertheless, finite polynomial
truncations of this formal family stabilize at every fixed projection.
This is an explicit obstruction to inferring physical boundedness from
existence, compatibility, or formal projective convergence of cumulants.

## 6. Coefficient recovery and uniqueness of physical realizations

For m>=2 define the continuous legal-coefficient functional

    C_m(f) =
      -sum_(d|m) mu(m/d) [f(d)-f(d-1)],  f(0)=0.

coefficientCLM_apply proves this physical formula, and coefficientCLM_residue
proves C_m(g_d)=1_(m=d) for d>0. Strong Q convergence therefore forces
convergence of every recovered legal coefficient. This coefficient
functional is distinct from the orthonormal divisor-wavelet coordinate map.

The family (C_m)_(m>=2) separates the entire Q Hilbert space:
eq_zero_of_coefficients_zero and coefficients_injective prove this by
transporting to the existing finite Mobius-difference inversion theorem.
Thus an infinite coefficient family can have at most one physical Q
realization with those recovered coefficients.

For the target one,

    C_m(1)=-mu(m).

coefficients_eq_mobius_iff proves that a Q vector with all those recovered
coefficients is exactly one. The arithmetic values -mu(m) are already known;
the open issue is legal physical realization with the required norm control.
For a prime this target coefficient is +1, since mu(p)=-1.

## 7. Does the completion enlarge the approximation mechanism?

At every finite stage, cumulant_synthesis_range proves exactly

    range(cumulant synthesis) = range(arbitrary moment synthesis).

All cumulants together provide an invertible nonlinear coordinate system for
the existing finite legal space. They do not add a new finite physical
direction beyond its complete squarefree dictionary.

strong_limit_mem_closed_span proves that every strong physical limit of
legal finite functions lies in the old closed squarefree legal span.
weak_limit_mem_closed_span proves the same for weak limits, formulated by
convergence of pairings against every Q vector.

Consequently the completion by itself adds no new physical vector outside
that closed span. It can organize prime blocks, interactions, and finite
optimization, but any improvement toward RH must supply a physical energy
estimate. Reparameterization, inverse limits, formal logarithms, and passage
to weak limits cannot replace that estimate.

## 8. The explicit missing RH provider

The theorem riemannHypothesis_of_bounded_cumulant_heads assembles the new
all-order synthesis with the existing exact-head averaging criterion.

Its domain-specific hypotheses are:

* each physical period is positive and squarefree;
* F_n(j)=1 for every 1<=j<=n;
* a single finite B bounds the complete signed physical error

      ||1||_Q^2
        - 2 sum_S c_n(S)<1,g_(d_S)>_Q
        + c_n^T G_(n,n)c_n <= B.

The last two assertions are not proved by the formal algebra. Under these
explicit hypotheses, the existing legal block averages converge strongly to
one, and the established closure-to-RH bridge applies.

Equivalently, for the complete exact-head affine optimizer from
QSquarefreeAffineHead.lean, seek cofinal squarefree periods with uniformly
bounded minimumError as the head grows. Its period-enlargement identity
retains the exact gain ||optimizer_L-optimizer_K||_Q^2. The new cumulant
coordinates do not change that complete minimum.

Open: prove such a complete budget, or another independently sufficient
arithmetic provider. No RH proof or unconditional vanishing of the minimum
is asserted.

## Focused next research targets

1. Express the existing full exact-head inverse-Gram optimizer in the new
   cumulant coordinates. Compare the exact cumulative prime-block gains with
   the complete minimum; retain source correlations and every remainder.
2. Seek a signed arithmetic identity controlling that complete error across
   increasing heads. The needed estimate must concern the literal atomic-Q
   realization, rather than coefficient magnitudes alone.
3. Study the domain of bounded canonical truncations separately from the
   larger space of strong limits of stage-dependent legal approximants.
4. If useful to later consumers, formalize partition-sum coefficient formulas
   and a topological-ring structure on the projective limit. These improve
   algebraic interfaces; they do not discharge the physical budget.
