# CRT collocation, complete leakage, and zeta-zero obstructions

7 November 2026. Continuation of the user-provided
`CRT_Collocation_and_Zero_Growth_2026-11-06.md`.

## Status and primary sources

This development establishes the actual finite full-conductor collocation
construction, exact complete-Q energy and Parseval identities, and conditional
connections to Mathlib's `RiemannHypothesis`. It does **not** prove the required
bound on the canonical collocation norms, or RH.

The primary published source is B. Bagchi, *On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis*, Proceedings of the
Indian Academy of Sciences, Mathematical Sciences **116** (2006), 137–146,
[DOI 10.1007/BF02829783](https://doi.org/10.1007/BF02829783),
[author-paper PDF](https://repository.ias.ac.in/968/1/307.pdf).
Theorem 1 and the equivalent-weight observation supply the interpretation of
the full residue closure. The Mellin calculations in Theorem 2 and the proof
of Theorem 5 supply the zero-annihilator strategy. They do not establish a
uniform inverse bound for the new collocation matrix.

A preceding published source is L. Báez-Duarte, *A strengthening of the
Nyman–Beurling criterion for the Riemann hypothesis*, Rendiconti Lincei,
Matematica e Applicazioni **14** (2003), 5–11,
[preprint math/0202141](https://arxiv.org/abs/math/0202141).
This is background for the restricted discrete approximation criterion, not a
provider for the remaining collocation growth hypothesis.

A related published comparison is F. Alouges, S. Darses, and E. Hillion,
*Polynomial approximations in a generalized Nyman–Beurling criterion*,
Journal de théorie des nombres de Bordeaux **34** (2022), 767–785,
[DOI 10.5802/jtnb.1227](https://doi.org/10.5802/jtnb.1227),
[accepted manuscript](https://arxiv.org/pdf/2006.02953).
Its unconditional construction still requires coefficient control for the
RH implication. Its Gram system differs from this CRT system; its density
theorem does not supply the canonical CRT norm bound.

The finite construction and the quantitative CRT proposal originate in the
user's handoff. No claim of historical novelty is made. Existing project
machinery reused here includes the actual Q Hilbert space, physical difference
operator, complete divisor-wavelet basis, divisor-test totality, weak Hilbert
compactness, full inverse-Gram projections, and the actual Mellin functional.

## 1. Objects and the finite construction

Put Z = zeta(2), Q(n) = 1/(Z n^2) for positive n, and anchor all sequences at
zero at n = 0. Let g_m(n) = fractional_part(n/m), with **all** conductors
allowed. For an integer L >= 2, define

- V_L = span{g_m : m divides L}; g_1 = 0.
- C_L = span{1_{a divides N} : a divides L}, the finite gcd-cell space.
- T_L = the Q-orthogonal projection onto C_L.
- a_L = 1_{L divides N} and h_L = 1 - a_L.

`QCRTFiniteCollocation.lean` proves that T_L restricted to V_L is injective,
and that its image is exactly

    {h in C_L : <h,a_L>_Q = 0}.

In particular there is a **unique actual legal vector** F_L in V_L satisfying
T_L F_L = h_L. The Lean definition `canonical` chooses the unique solution;
it does not postulate a solution or an invertible matrix. For every a dividing L,

    <F_L,1_{a divides N}>_Q = 1/a^2 - 1/L^2,
    E_Q[F_L(aN)] = 1 - a^2/L^2.

This is the conditional-moment system in the handoff. It is different from the
orthogonal-projection normal equations; F_L is not asserted to minimize the
approximation error.

The proof uses D = I-S, where S is the anchored physical backward shift.
The existing project verifies that S is a contraction and D is injective.
The reusable module `Analysis/FiniteAccretiveCollocation.lean` keeps the identity

    2<f,Df> = ||Df||^2 + ||f||^2 - ||Sf||^2.

Thus <f,Df> = 0 forces f = 0. Finite-dimensional injectivity then gives
surjectivity of the collocation system. No quantitative lower singular-value
bound is obtained from this finite-dimensional argument.

## 2. Exact complete error and arithmetic Parseval

Let z_L = F_L-h_L = (I-T_L)F_L and V(L) = ||z_L||_Q^2. The checked identities are

    ||1-F_L||_Q^2 = L^(-2) + V(L),
    ||F_L||_Q^2 = 1 - L^(-2) + V(L).

Every norm contains the complete infinite Q tail.

Write W_r = sum_{a|r} mu(r/a) a^2 1_{a divides N}, so that
||W_r||_Q^2 = J_2(r). The existing divisor Hilbert basis supplies completeness;
the new `QCRTLeakageParseval.lean` proves the Hilbert-space inversion

    sum_{r|L} W_r = L^2 a_L,

and the exact low coordinates

    <F_L,W_r>_Q = 1_{r=1} - J_2(r)/L^2       (r divides L).

Consequently, for Psi_r = W_r/sqrt(J_2(r)),

    <F_L,Psi_r>_Q = 1_{r=1} - sqrt(J_2(r))/L^2.

The normalized display follows by scaling the checked unnormalized formula;
the persisted theorem uses the unnormalized basis. Most importantly, the
complete series identity itself is checked:

    V(L) = sum_{r not dividing L} |<F_L,W_r>_Q|^2/J_2(r).

For L = lcm(1,...,M), this includes both primes larger than M and excessive
powers of primes at most M. No squarefree truncation or omitted prime-power
remainder is used.

## 3. Bounded leakage forces vanishing optimal error and RH

`QCRTBoundedCriterion.lean` proves the following sufficient condition:

    M_j -> infinity, M_j >= 2,
    V(lcm(1,...,M_j)) <= C for every j, for some finite C >= 0
        implies RiemannHypothesis.

The more general statement allows any cutoff sequence L_j -> infinity for
which each positive integer eventually divides L_j.

The key theorem is more general still: bounded vectors in the actual full
legal closure, whose inner products against every divisibility indicator
tend to those of 1, force 1 into that closure. The proof extracts a weak
subsequence **inside the closed legal space** and uses the already proved
totality of all divisibility indicators to identify its limit with 1.

This supplies the missing implication from a norm bound to the desired
projection limit; it is not an inference from the existence of a CRT limit.
It immediately makes the existing full inverse-Gram candidates converge in
the complete Q norm to 1. The LCM tower also exhausts the full legal span, and
the actual orthogonal projections onto V_{lcm(1,...,M)} converge to the full
legal projection unconditionally. Under the bounded-canonical hypothesis,
their complete squared errors tend to zero.

The final RH implication uses the project's existing
`QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure`, whose
conclusion is Mathlib's RH. No converse RH-to-density hypothesis is inserted.
This is a **conditional research reduction**. Its domain-specific hypothesis
is still Open: boundedness of the actual canonical family on a cofinal
subsequence. Neither finite solvability nor weak compactness proves that bound.

The corresponding P-error conclusion follows on paper from equivalent weights
and finite-support exhaustion. This addition checks the Q projection errors
explicitly; it does not add a separately named theorem about P LCM minimizers.

## 4. Exact zero obstruction acting only on leakage

Let ell_s be the existing actual continuous Mellin functional `qMellinContinuous`
on the real Q Hilbert space, with complex values, for Re(s)>1/2. Define the
actual continuous linear map and its norm

    tailMellin(L,s) = ell_s composed with (I-T_L),
    K_L(s) = ||tailMellin(L,s)||.

These are definitions using actual operators, not an assumed detector.
At a zeta zero s != 1 with Re(s)>1/2, the project Mellin residue identity gives
ell_s(F_L)=0 and ell_s(1)=1/s. The new checked signed balance is

    1/s = ell_s(a_L) - ell_s(z_L).

Since T_L z_L = 0, the checked bound is

    1/|s| <= |ell_s(a_L)| + K_L(s) sqrt(V(L)).

This isolates complete leakage from the multiples-of-L endpoint. In
particular, if the right-hand budget tends to zero for every s in the open
right half of the critical strip, RH follows. The Lean theorem
`riemannHypothesis_of_vanishing_mellin_budget` leaves precisely that budget
convergence as its domain-specific hypothesis.

### Verified arithmetic tail and improved constants

The paper-only analytic estimate in the preceding revision is now formalized.
Write beta=Re(s), t=2 beta, and

    D_t(L) = sum_{n>=1, n not dividing L} n^(-t),  t>1,
    A_beta = 1 + 2^(beta-1).

The generic number-theory modules prove the exact identities

    D_t(L) = sum_{n>=1} n^(-t) - sum_{d|L} d^(-t)
           = zeta(t) [1 - product_p (1-p^(-t(v_p(L)+1)))],

including convergence of the actual infinite product. The formal real
zeta(t) is written as its absolutely convergent positive-integer series.
No prime outside the modulus, or excessive prime-power depth, is omitted.
The complete union bound is also checked:

    D_t(L) <= zeta(t) sum_p p^(-t(v_p(L)+1)).

Every integer up to M divides L_M=lcm(1,...,M), so the checked basic bound is

    D_t(L_M) <= M^(1-t)/(t-1).

Finite exact escape prefixes plus an integral bound on their remaining tail
give additional certified enclosures. These are analytic enclosures; they do
not certify floating-point rounding.

The actual gcd-cell sampler is constructed using finite Möbius inversion.
The proof works with the complex-valued functional on the existing real Q
Hilbert space and proves both real and imaginary signed pairings. Its raw
witness is

    w_s(n) = Z n^2 [n^(-s)-(n+1)^(-s)].

The exact nonnegative defect energy is

    H_s(L) = sum_{n>=1} Q(n) |w_s(n)-w_s(gcd(n,L))|^2.

It vanishes termwise at divisors of L. On the escape set, gcd(n,L)<=n/2.
For 1/2<beta<=1 the checked consequences are

    H_s(L) <= A_beta^2 Z |s|^2 D_(2 beta)(L),
    K_L(s) <= A_beta sqrt(Z D_(2 beta)(L)).

A further checked improvement keeps a second complete arithmetic energy:

    S_t(L) = sum_(n not dividing L) gcd(n,L)^(2-t)/n^2,
    K_L(s) <= sqrt(Z) [sqrt(D_(2 beta)(L))+sqrt(S_(2 beta)(L))].

The bound S_t(L)<=2^(t-2)D_t(L) recovers A_beta, while retaining S separately
can give a substantially smaller value. QGcdCellEstimates also proves the
exact computable formula, for every real t and L>0,

    S_t(L) = Z sum_(d|L) d^(2-t) sum_(j|L,d|j) mu(j/d)/j^2
                - sum_(d|L) d^(-t).

Thus the handoff coefficient 2 improves to A_beta<2 throughout the open
critical strip. For each fixed s, K_(L_M)(s) tends to zero unconditionally.
This is a statement about a fixed Mellin functional; it does not provide a
bound on the moving canonical vectors.

### Exact residual endpoint, with no endpoint provider

The signed boundary identity is formalized before its absolute estimate:

    |1-Z[n^(-s)-(n+1)^(-s)]_(n=L)|^2
        <= H_s(L) ||1-F_L||_Q^2.

At a right-half-strip zeta zero this yields the fully explicit inequality

    1/|s| <= A_beta sqrt(Z D_(2 beta)(L)) ||1-F_L||_Q
                + Z L^(-1-beta).

This is precisely the handoff's residual-norm endpoint, with its improved
coefficient. The separate leakage-only identity remains exact:

    1/s = ell_s(a_L)-ell_s(F_L-h_L).

For that endpoint, continuity and ||a_L||_Q=1/L already prove convergence to
zero. The subpolynomial theorem therefore needs no assumed endpoint decay.

### Verified subpolynomial criterion and exact growth exponent

If zeta(s)=0 and 1/2<beta<1, the actual complete leakage eventually satisfies

    V(L_M) >= [(2 beta-1)/(4 A_beta^2 Z |s|^2)] M^(2 beta-1).

The previous factor 16 in the denominator has improved to 4 A_beta^2<16.
Both ||F_(L_M)|| and ||1-F_(L_M)|| dominate sqrt(V(L_M)). Consequently:

    liminf log(1+||F_(L_M)||_Q)/log M = 0  implies Mathlib RH,
    liminf log(1+||1-F_(L_M)||_Q)/log M = 0  implies Mathlib RH.

The formal definitions use L_(M+2), avoiding zero denominators and small
cutoff exceptions, and an extended nonnegative liminf. This avoids the
default value that Lean's total real liminf may assign to an unbounded
sequence. The equivalent explicit cofinal condition is also proved:
for every epsilon>0 and every N there is M>=N whose relative log norm is
below epsilon. No upper bound on the full sequence is required.

The exponent is sharp for this elementary tail comparison: for every
epsilon>0, a zero at beta forces, eventually,

    log(1+||F_(L_M)||_Q)/log M >= beta-1/2-epsilon.

Thus a cofinal upper exponent alpha excludes zeros with beta>1/2+alpha.
These are proved conditional implications. Their remaining arithmetic
hypothesis, the actual canonical norm bound, is still OPEN.

### Logarithmic improvement from checked prime counting

The new number-theory continuation separates the exact escape sum into

    sum_{p<=M} p^(-t(v_p(L_M)+1)) + sum_{p>M} p^(-t).

The first forbidden power exceeds M, and Mathlib's Chebyshev prime-counting
theorem controls the finite depth term. A complete dyadic cover controls
the large-prime tail. This proves, for each t>1 and epsilon>0, eventually,

    D_t(L_M) <= zeta(t)(log 4+epsilon)
        [1+2/(1-2^(1-t))] M^(1-t)/log M.

A fully explicit version replaces log 4+epsilon by 2 log 4+2 and holds
for every M>=2. The minimum with M^(1-t)/(t-1) is checked, so the available
numerical enclosure never worsens. The explicit log bound alone need not be
smaller at moderate M because its constant is deliberately conservative.

Further checked depth bounds retain the exact split at an arbitrary prime
threshold K. They give

    small-prime depth <= pi(K) M^(-t) + sum_{p>K} p^(-2t),

and an improved square-cutoff formula at M=K^2. This isolates the smaller
depth contribution without changing the actual canonical family.

The logarithmic improvement is connected to the actual family in Lean. A
right-half-strip zero at beta forces, for some c_s>0 and all sufficiently
large M,

    ||F_(L_M)||_Q^2 >= c_s M^(2 beta-1) log M.

Equivalently the norm has the extra square-root logarithmic factor. The
checked critical-power theorem now excludes a zero at beta whenever, for
some fixed C, ||F_(L_M)||_Q<=C M^(beta-1/2) occurs cofinally. The boundary
exponent itself is excluded, unlike the earlier relative-log upper-exponent
criterion. This is still conditional on the actual norm bound.

The logarithmic saving is an arithmetic improvement to the zero obstruction.
It is not a provider for the open canonical growth bound.

### Matching lower bound: the Euler-tail order is sharp

The same owning arithmetic module now proves, for every t>1 and M>=32,

    D_t(L_M) >= 4 * 32^(-t) M^(1-t)/log M.

The proof uses the retained Mathlib theorem `Chebyshev.pi_ge`, including its
log(n+1) correction, and the already checked upper bound on pi(M). It proves

    pi(32M)-pi(M) >= 4 M/log M.

Every prime in (M,32M] fails to divide L_M and contributes at least (32M)^(-t).
Summing these actual escape terms gives the lower bound. No PNT, RH, or
unformalized numerical prime-counting hypothesis is used.

Together with the upper bound, this establishes the order M^(1-t)/log M up
to positive constants depending on t. In particular the complete scalar tail
cannot be little-o of this scale. A faster rate for D alone cannot remove the
remaining canonical norm obligation. More refined projected-Mellin cancellation
would be a different question.


## 5. Why the present energy estimate does not control leakage

The exact checked contraction identity for the canonical lift is

    ||D F_L-h_L||_Q^2 + (||F_L||_Q^2-||S F_L||_Q^2)
       = ||h_L||_Q^2 = 1-L^(-2).

Combining it with the complete norm identity gives the further checked equality

    ||S F_L||_Q^2 = V(L) + ||D F_L-h_L||_Q^2.

Thus V(L) occurs with coefficient one in both primitive and shifted energy.
It cancels from the contraction defect. A bound on that defect supplies no
bound on V(L) through these identities alone. The equality is preserved in
the formalization; no uncontrolled term is silently dropped.

This is not a counterexample to boundedness of the canonical family. Proving
or disproving that boundedness remains an arithmetic research problem.

The new [stability memorandum](CRTCollocationStabilityResearch20261107.md)
records three further formal results. First, every uniform inverse bound for
all collocation targets fails as L grows. Second, the actual canonical norms
diverge along prime moduli, which are not divisor-exhausting and are distinct
from the LCM tower. Third, for nested cutoffs the exact increment energy
separates the telescoping target increment from the complete leakage
increment, retaining its cross term. These results prevent inappropriate
transfers of general inverse, positivity, or orthogonality arguments.

## 6. Wolfram full-period computations

Wolfram Language was used to reconstruct the actual finite moment matrices.
For a,m dividing L, put k=m/gcd(a,m). The entries used were

    B(a,m) = (1/(Z k^2)) sum_{r=1}^k fractional_part(a r/m) zeta(2,r/k),
    t(a) = 1-a^2/L^2,

with a ranging over proper divisors of L and m over divisors greater than one.
The coefficients solve Bc=t. For any L-periodic H, the complete expectation
was evaluated as

    E_Q[H] = (1/(Z L^2)) sum_{r=1}^L H(r) zeta(2,r/L).

This retains the entire infinite physical tail analytically. Values through
L=27720 used arbitrary precision; the final two large cutoffs used machine
precision. All displayed values are rounded numerical observations:

| L | Number of coefficients | Complete ||1-F_L||_Q^2 | Complete ||F_L||_Q^2 |
|---:|---:|---:|---:|
| 2 | 1 | 0.250000000000000 | 0.750000000000000 |
| 4 | 2 | 0.146642956733035 | 1.021642956733035 |
| 6 | 3 | 0.065473017740848 | 1.009917462185292 |
| 12 | 5 | 0.082601564453877 | 1.068712675564988 |
| 60 | 11 | 0.053729291633512 | 1.053173736077957 |
| 420 | 23 | 0.036804379080269 | 1.036793041211788 |
| 840 | 31 | 0.046198090098666 | 1.046195255631545 |
| 2520 | 47 | 0.029984987806915 | 1.029984672866124 |
| 27720 | 95 | 0.029076491879528 | 1.029076489276711 |
| 360360 | 191 | 0.032628803211079 | 1.032628803195680 |
| 720720 | 239 | 0.033448814301311 | 1.033448814297451 |

The earlier handoff values were reproduced and extended. At L=27720 the
full-period minimum is about -23.1746 despite the small complete Q norm.
At L=420,840,2520,
the numerical period minima are approximately -1.2510,-1.5851,-2.7033, so a
positivity-based explanation should not be presumed. The residual energy is
not numerically monotone. At L=360360 and 720720 the minima are about
-66.9685 and -171.7354. The corresponding moment residual infinity norms are
1.7e-13 and 2.1e-13. These are floating-point diagnostics, not error bounds.
None of these observations is a Lean theorem, interval certificate, or
asymptotic bound.

The admissions M=13 and M=16 show why the leakage correlation matters:

| From L | To L | Squared-norm ratio | Squared increment norm | Leakage cross inner product |
|---:|---:|---:|---:|---:|
| 27720 | 360360 | 1.003451943520218 | 0.030217657634197 | 0.015743818720503 |
| 360360 | 720720 | 1.000794100551169 | 0.022559091720473 | 0.021759262894025 |

The complete increment energy is much larger than the change in squared norm;
its correlation with the old leakage is essential. This is a finite numerical
observation about the exact quantities in the checked nested-cutoff identity.

The separate arithmetic sampler experiment at t=3/2 gives the following
full-tail values. Here K_bound=sqrt(Z)(sqrt(D)+sqrt(S)); the last column compares
it with the original bound 2 sqrt(Z M^(1-t)/(t-1)). The S values were computed
from its finite local-factor product; the equivalent finite Mobius identity
is Lean-verified, but these floating-point evaluations are not certificates.

| M | D_(3/2)(L_M) | S_(3/2)(L_M) | K_bound | Ratio to original bound |
|---:|---:|---:|---:|---:|
| 10 | 0.462591380761024 | 0.107199313003719 | 1.29223791446213 | 0.633465895256237 |
| 50 | 0.139457947952029 | 0.016422612205995 | 0.643316001864829 | 0.471571569686990 |
| 100 | 0.091172929351668 | 0.008109165469237 | 0.502758839595712 | 0.438268718761222 |
| 1000 | 0.019536723922592 | 0.000466244426517 | 0.206960609418778 | 0.320825185127062 |

## 7. Continuation obligations, in priority order

1. **OPEN, decisive:** prove cofinal subpolynomial growth in M of the actual
   canonical LCM norms, or of the complete residual norms. All required
   analytic Euler-tail, sampler, and residual-endpoint estimates are now
   proved. This growth bound would apply the checked Mathlib RH theorem.
2. **Alternative OPEN condition:** bounded canonical leakage on a cofinal LCM
   subsequence applies the earlier weak-compactness route and gives actual
   optimal Q projection error tending to zero.
3. **Use the special target:** exploit cancellation in B_L^(-1)t_L. A uniform
   inverse bound on the full trial space is impossible, as the new formal
   instability theorem shows. This does not imply divergence of F_(L_M).
4. **Avoid the energy promotion gap:** the exact shift defect controls an
   n^(-3)-scale energy; it has not been promoted to the complete n^(-2) norm.
5. **Further quantitative work:** sharpen the two retained sampler energies
   and prime/depth constants, while keeping the actual canonical growth
   obligation separate from improvements to its zero detector.

All conditional results retain their hypotheses. No converse RH-to-bounded-
collocation theorem is asserted. RH itself remains unproved here.

## 8. Verification and persistence

The preceding finite construction, complete Parseval identity, bounded-family
criterion, and Mellin annihilator were published at commit
`0fb2590c08fff6c746258cc5cc5b8fbda8ac2bcf`. The present continuation adds fourteen
owning modules, all exported by the root aggregate:

| Area | New owning modules |
|---|---|
| Arithmetic escape tails | `NumberTheory/DivisorEscapeTail`, `DivisorEscapeEulerProduct`, `DivisorEscapePrimeTail` |
| Sampler arithmetic and divisor count | `NumberTheory/GcdSampleTail`, `DivisorCountSqrt` |
| Cofinal growth analysis | `Analysis/CofinalLogGrowth` |
| Actual sampler and Mellin functional | `RH/QGcdSampling`, `QCRTProjectedMellin`, `QCRTExactEndpoint` |
| Canonical growth and RH reductions | `RH/QCRTZeroGrowth` |
| Cell geometry and inverse instability | `RH/QGcdCellEstimates`, `QCRTInverseInstability` |
| Prime and nested canonical cutoffs | `RH/QCRTPrimeCutoffGrowth`, `QCRTNestedCutoffs` |

The actual owning modules were imported together and checked in server job
`job_Y-NHrRTo0q3HUoOgT7QZK3Y0xZr1GUoH`, which succeeded with server-reported
verification time 18.649 seconds. This was a modular compilation, not merely
a concatenated theorem snippet. The axiom audit covered fourteen principal
results, including the Euler-product identity, explicit logarithmic tail
bound, separated sampler estimate, actual residual endpoint, both liminf RH
criteria, critical-power zero exclusion, logarithmic norm floor, exact finite
sampler formula, inverse instability, prime-cutoff growth, and nested energy.
Every audited declaration reported only `propext`, `Classical.choice`, and
`Quot.sound`. The subsequent matching-lower-bound candidate passed
`job__A9uD8lLirroZC2FOf4Jo7WR8T3MbkbJ` in 6.846 seconds, with the same axiom set,
and was merged into `DivisorEscapePrimeTail.lean` for the final checkpoint.
No proof of the open canonical growth condition is thereby supplied.

The final server checkpoint audits the repository delta, validates the root
aggregate and affected modules, and publishes the result. Its terminal result
and exact commit are recorded in the accompanying delivery. Successful
individual checks alone are not represented as that publication gate.

The retained workspace is `ws_mwWauOIKeaTQFsXlLf9olVQpDUYrLPst`.
Queue/wait time and server verification time are distinct; no cache, disk,
or networking cause is inferred from an end-to-end delay.

## Appendix: reproducible Wolfram Language experiment

```wolfram
(* Full-tail numerical CRT collocation. These are arbitrary-precision
   experiments, not interval certificates or Lean proofs.
   The period weights sum all physical Q tails using Hurwitz zeta. *)
ClearAll[crtCollocation];
crtCollocation[ell_Integer, precision_Integer : 40] /; ell >= 2 := Module[
  {ds, rows, cols, z, mat, rhs, coeff, vals, weights, err, norm},
  ds = Divisors[ell];
  rows = Most[ds];
  cols = Rest[ds];
  z = N[Zeta[2], precision];
  mat = Table[
    With[{k = m/GCD[a, m]},
      N[Sum[FractionalPart[a r/m] Zeta[2, r/k], {r, 1, k}]/(z k^2),
        precision]],
    {a, rows}, {m, cols}];
  rhs = N[1 - rows^2/ell^2, precision];
  coeff = LinearSolve[mat, rhs];
  vals = Table[Sum[coeff[[i]] FractionalPart[n/cols[[i]]],
      {i, Length[cols]}], {n, 1, ell}];
  weights = Table[N[Zeta[2, n/ell]/(z ell^2), precision], {n, 1, ell}];
  err = Total[weights (1 - vals)^2];
  norm = Total[weights vals^2];
  <|"L" -> ell, "Dimension" -> Length[cols], "ErrorSquared" -> err,
    "NormSquared" -> norm, "Leakage" -> (err - 1/ell^2),
    "MinimumOnPeriod" -> Min[vals],
    "MomentResidualInfinityNorm" -> Max[Abs[mat.coeff - rhs]],
    "EnergyIdentityResidual" -> (norm - err - 1 + 2/ell^2)|>
];
crtCollocation /@ {2, 4, 6, 12, 60, 420, 840, 2520}
```


For the larger two cutoffs, the following Wolfram implementation reuses
reduced residue moments and forms the full period by cumulative differences.
It uses machine precision and does not certify rounding errors.

```wolfram
ClearAll[fastCRT];
fastCRT[ell_Integer] := Module[
  {ds=Divisors[ell], rows, cols, z=N[Zeta[2]], w, entry,
   mat, rhs, c, inc, v, weights},
  rows=Most[ds]; cols=Rest[ds];
  w[k_Integer] := w[k] = PolyGamma[1,Range[k]/N[k]]/(z N[k]^2);
  entry[a_Integer,k_Integer] := entry[a,k] =
    N[Mod[a Range[k],k]/k].w[k];
  mat=Table[With[{g=GCD[a,m]},
      entry[Mod[a/g,m/g],m/g]], {a,rows},{m,cols}];
  rhs=N[1-rows^2/ell^2]; c=LinearSolve[mat,rhs];
  inc=ConstantArray[Total[c/cols],ell];
  Do[inc[[Range[cols[[i]],ell,cols[[i]]]]]-=c[[i]],
    {i,Length[cols]}];
  v=Accumulate[inc]; weights=w[ell];
  <|"L"->ell,"Dimension"->Length[cols],
    "ErrorSquared"->weights.((1-v)^2),
    "NormSquared"->weights.(v^2),"Minimum"->Min[v],
    "MomentResidual"->Norm[mat.c-rhs,Infinity],
    "EndpointRoundoff"->Last[v]|>
];
fastCRT /@ {360360,720720}
```
