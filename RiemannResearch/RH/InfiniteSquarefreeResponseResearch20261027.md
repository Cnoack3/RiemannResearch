# Infinite squarefree response variation and unconditional summability

Source: the user-requested continuation of commit
05bfaee0881896be2bc21f843c6e2fba5d8bac57 and
SquarefreeMomentBudgetResearch20261027.md. This note records the complete
canonical-stage assembly and its precise limits. It does not prove RH.

## Objects, indexing, and zero innovations

Work in the actual Q Hilbert space, with Q(n)=1/(zeta(2)n^2) for n>=1.
The Lean realization uses normalized coordinates
f[n-1]=sqrt(Q(n))*f_physical(n), together with a zero physical anchor at n=0.
Every norm and physical sum below includes the complete infinite tail.

The repository stage V_N contains exactly the squarefree residue atoms g_d
with 2<=d<=N+1. Set P_N=P_(V_N), r_N=1-P_N1,
b_N=P_N B r_N, and Bf(n)=f(n)/(n+1). The closed union is V, with
P=P_V, r=1-P1, and b=PBr.

The canonical dictionary is v_N=g_(N+2) if N+2 is squarefree, and v_N=0
otherwise. Define u_N by Mathlib's gramSchmidtNormed on this dictionary.
Zero innovations remain zero at their original natural-number indices.
The nonzero subtype is orthonormal, and

    V_(N+1) = V_N + span{u_N},
    P_(N+1)f = P_Nf + <f,u_N> u_N.

These identities include zero and dependent innovations; no independence
hypothesis or re-enumeration of active conductors is assumed.

## Exact signed update and complete infinite budget

Write a_N=<1,u_N> and c_N=<B r_(N+1),u_N>. Then

    Delta b_N = b_(N+1)-b_N = c_N u_N - a_N P_N B u_N,
    ||Delta b_N||^2 = c_N^2 + a_N^2 ||P_N B u_N||^2,
    ||Delta b_N||^2 <= ||r_N||^2 ||B u_N||^2.

The first equality retains the signed correction. In the second equality
the two output vectors are orthogonal. The last bound follows from symmetry
of B, Cauchy--Schwarz, projection contraction, and the exact energy split
||r_N||^2=||r_(N+1)||^2+a_N^2.

The complete physical-coordinate Bessel estimate is

    sum_N ||B u_N||^2 <= sum_(n>=1) 1/(n+1)^2 = zeta(2)-1.

It is proved by restricting each finite set to the nonzero subtype and
applying the already checked full-coordinate Bessel theorem. Passing to the
infinite sum uses nonnegativity and bounded finite sums, not physical truncation.

At stage 1, P_1 1=1_odd and r_1=1_even. Consequently

    ||r_1||^2=1/4,  b_0=b_1=0,
    ||r_N||^2<=1/4 for N>=1.

Therefore the requested unconditional theorem is

    sum_(N>=0) ||b_(N+1)-b_N||_Q^2 <= (zeta(2)-1)/4.

The infinite exact energy equality is also retained:

    sum_N ||Delta b_N||^2
      = sum_N c_N^2 + sum_N a_N^2 ||P_N B u_N||^2.

The same formalization removes the unused first parity direction:

    sum_N ||Delta b_N||^2
      <= (zeta(2)-1-||B u_0||^2)/4.

This is an exact symbolic improvement; the bound is not claimed optimal.
The explicit evaluation

    ||B u_0||^2 = 4(zeta(2)-2 log 2)/(3 zeta(2))

was a supplementary paper calculation on 27 October. On 28 October it was
formalized in QParitySmoothingEnergy.lean as B_direction_zero_norm_sq,
using the complete odd series in Analysis/OddReciprocalSquare.lean.
The declaration movingCorrection_variation_explicit_parity inserts this
arithmetic value into the verified symbolic bound. The subsequent actual
conductor-three stage gives a further strict improvement, with its response
cost retained, in QInitialResponseImprovement.lean. See
ParitySmoothingEnergyResearch20261028.md for exact formulas, verification
scope, and the distinction between checked declarations and paper evaluations.

## Both signed series converge unconditionally

The coefficient square series sum a_N^2 and sum c_N^2 converge. For a_N,
this follows from the already checked projection-innovation energy theorem;
for c_N, the exact step identity and the B budget give a summable majorant.
The vectors c_N u_N belong to mutually orthogonal innovation subspaces.
Thus their series converges unconditionally in QHilbert.

The second series converges absolutely in Hilbert norm:

    sum_N ||a_N P_N B u_N||
      <= sqrt(sum_N a_N^2)*sqrt(sum_N ||B u_N||^2) < infinity.

The Lean summability proof uses the equivalent sufficient Young majorant
(|a_N|^2+||B u_N||^2)/2, avoiding any unproved interchange of limits.
Subtracting the two Summable vector series proves unconditional summability
of the actual Delta b_N. Lean's Summable is the finite-subset-net notion.
It is not merely convergence along the displayed order.

Only after obtaining unconditional summability do we use ordered telescoping
and the previously established b_N -> b to identify every complete tail:

    sum_(j>=0) (b_(j+N+1)-b_(j+N)) = b-b_N.

In particular the total sum is b. Multiplying each increment by any real
sign sequence epsilon_N with |epsilon_N|<=1 preserves unconditional
summability, although its sum generally changes.

## Stronger unconditional regularity

Let E_N=||r_N||^2, E_inf=||r||^2 and
T_N=sum_(j>=N)||B u_j||^2. The checked variation-tail estimate is

    sum_(j>=N)||Delta b_j||^2 <= E_N T_N.

T_N tends to zero because it is a tail of a convergent nonnegative series.
No assumption E_inf=0 is used.

One extra application of B gives absolute Hilbert-norm summability:

    sum_N ||B Delta b_N|| < infinity.

For the orthogonal term, apply Cauchy--Schwarz to |c_N| ||B u_N||.
For the correction, boundedness of B preserves its absolute summability.
At every physical site n the original increments are absolutely summable:

    V(n) := sum_N |Delta b_N(n)| < infinity.

This also follows directly by mapping the unconditional vector series
through the continuous Q-evaluation functional: unconditional scalar
summability in the real line is absolute summability.

The stronger complete-weight assertion is

    sum_(n>=1) Q(n) [V(n)/(n+1)]^2 < infinity.

To see this without omitting tails, the series sum_N |B Delta b_N| converges
in QHilbert, since its term norms equal ||B Delta b_N||. Its physical values
are exactly V(n)/(n+1), by continuous evaluation. This constructs an actual
QHilbert total-variation envelope after one smoothing.

The following sharper quantitative consequences are additional paper proofs;
they are not labeled formalized unless matching declarations are listed:

1. Put C_N=sum_(j>=N)c_j^2 and A_N=E_N-E_inf=sum_(j>=N)a_j^2.
   Then C_N<=E_N T_N. For arbitrary finite F contained in {j>=N} and
   |epsilon_j|<=1,

       ||sum_(j in F) epsilon_j Delta b_j||
         <= (sqrt(E_N)+sqrt(A_N))*sqrt(T_N).

   The orthogonal part has squared norm at most C_N; the other part is
   bounded by sqrt(A_N*T_N). Both terms are retained before estimation.

2. Evaluation Bessel and Cauchy--Schwarz give, for physical n>=1,

       sum_(j>=N)|Delta b_j(n)|
         <= sqrt(zeta(2))*n*(sqrt(C_N)+sqrt(A_N*T_N)).

   Hence these absolute tails, divided by n, tend uniformly to zero.
   Every finite-stage increment is bounded and periodic, so V(n)/n -> 0.

3. With d_N=(P-P_N)1, the exact endpoint identity is

       b-b_N=(P-P_N)Br-P_N B d_N.

   Its outputs lie in orthogonal subspaces. Expanding the tail projection
   in the u_j gives a first squared norm at most E_inf*T_N. Cauchy--Schwarz
   on the expansion of d_N gives a second at most A_N*T_N. Thus

       ||b-b_N||^2 <= E_N T_N.

   This is stronger than a triangle bound on the endpoint; it is distinct
   from the formally checked sum-of-squared-increments estimate.

## RH boundary

None of these statements bounds the unsmoothed response by a common
logarithmic envelope or proves a common positive exponential-moment budget.
All added formal results are unconditional. They do not invoke RH or an
unresolved arithmetic regularity provider.

The surviving obligation from the original memorandum remains: some kappa>0
and finite M such that for every finite set S of physical sites and every N0
there is N>=N0 with

    sum_(n in S) Q(n) exp(kappa*|b_N(n)|) <= M.

Existing checked consumers turn such additional hypotheses into residual
vanishing/RH. This development does not provide those hypotheses.
Even square-summable variation and unconditional convergence of a genuine
projection response need not give exponential integrability. As an abstract
counterexample, take V=span{1_odd,1_even*n^a}, 0<a<1/2, and the two-step
nested chain followed by a constant sequence. Its final response is a
positive multiple of 1_even*n^a. Positivity follows from strict negative
covariance of decreasing 1/(n+1) and increasing n^a under weights proportional
to Q(n)1_even*n^a. It has no positive stretched exponential moment. This
example is not the squarefree legal space; squarefree-specific arithmetic
must supply the missing information.

## Formal declaration map and verification scope

- Analysis/InfiniteResponseSeries.lean: general orthogonal/absolute signed-series
  assembly, bounded-sign convergence, infinite variation comparison, and tail HasSum.
- RH/QCanonicalInnovation.lean: original-index Gram--Schmidt directions,
  zero cases, exact rank-one projection/response identities and step energy.
- RH/QSquarefreeResponseSeries.lean: actual parity cap, complete Bessel assembly,
  both signed-series summability proofs, infinite exact energy equality,
  movingCorrection_variation, movingCorrection_variation_excluding_parity,
  movingCorrection_increment_hasSum, movingCorrection_tail_hasSum,
  signed_movingCorrection_increment_summable, movingCorrection_variation_tail_le,
  B_movingCorrection_increment_norm_summable, and
  movingCorrection_increment_physical_abs_summable, smoothingTail_tendsto_zero,
  smoothedTotalVariation_physical, smoothedTotalVariation_weighted_summable,
  and smoothedTotalVariation_weighted_identity.

Saved-module verification job job_yaJZ_cLss-on34Jy_5M-PaD91SrW5AUJ succeeded
with verified=true and exit code 0. Three principal declarations were audited;
their axiom lists were exactly propext, Classical.choice, and Quot.sound.
The server reported 14.330 seconds, including dependency/module preparation;
this is not pure kernel time. Queue delay was approximately 0.006 seconds.
Workspace-opening round-trip time was not separately instrumented.
Later supplementary-envelope checks and the terminal publication checkpoint
are recorded by the final response. A successful snippet does not certify an
entire project; final publication requires the server checkpoint validation.

Supplementary check job_oZItPfTB2pnl9Hfitb4jd-tzoQG2pkxD succeeded with
verified=true, exit code 0, and reported duration 6.059 seconds. It checked
the smoothing-tail limit and complete weighted total-variation envelope.
The audited envelope theorem again used only propext, Classical.choice,
and Quot.sound. Final saved-module acceptance remains the publication checkpoint.
