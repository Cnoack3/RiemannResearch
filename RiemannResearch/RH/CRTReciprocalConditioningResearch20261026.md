# Infinite CRT attempt on the squarefree constant-energy bound

26 October 2026. The full constant-energy bound for the actual correction is
still Open. This continuation supplies a bounded CRT-conditioned source, an
exact transfer of its normal equations to the legal squarefree projection,
a quantitative reciprocal-conditioning error, and convergence in the complete
weighted energy for arbitrary bounded moving inputs. It does not prove RH.

## Spaces, indexing, and the precise open target

Write z=ζ(2), Q(n)=1/(z n²) on positive integers, g_d(n)=(n mod d)/d,
V_N=span{g_d:2<=d<=N+1, d squarefree}, P_N the Q-orthogonal projection,
r_N=1-P_N1, Bf(n)=f(n)/(n+1), and b_N=P_NBr_N. Stages retain the masked
conductor cutoff; they are not indexed by the first N active conductors.

For a_k(n)=n/(k+6+log n)^k, let

    E_k(H,f)=Σ_(1<=n<=H) a_k(n)Q(n)|f(n)|².

The unresolved obligation is: some fixed natural k, a divergent H(N), and
finite C such that E_k(H(N),b_N)<=C at arbitrarily large stages. The repository
already proves this implies squarefree residual vanishing and then RH.

## The correct CRT measure

For L>=1 and 1<=a<=L (a=L represents residue zero), put

    w_L(a)=Σ_(j>=0)Q(a+jL),
    C_Lf(a)=Σ_(j>=0)Q(a+jL)f(a+jL)/w_L(a).

These are complete infinite progression sums. They are not Haar averages.
The Q law on profinite integers is atomic, with mass Q(n) at integer n.
For example Q(n=1 modL) tends to 1/z, whereas Haar gives 1/L. The repository
already records this distinction in QCRTProfiniteResearch20261020.md.

Prime valuations are independent geometrically distributed variables under
Q, but unit residues are not independent uniform CRT coordinates. Ehm's
construction supports the former assertion, not the latter:
https://www.numdam.org/item/10.1016/j.crma.2007.07.023.pdf, Section1.

## New complete-energy source estimate

Set u_(N,L)=C_LBr_N. The physical evaluation inequality gives

    |Bf(n)| <= sqrt(z)||f||_Q.

The positive complete-fiber average preserves this bound. Therefore

    Σ_(n>=1) |C_LBr_N(n)|²/[z n(8+log n)²]
      <= ||r_N||_Q² D <= D,
    D=Σ_(n>=1)1/[n(6+log n)²] < infinity.

The same D bounds every finite physical head, for every L>=1 and every N.
This is a bound on the ambient conditioned SOURCE, not on b_N.

Implemented declarations:

- QResidueConditional.conditionalValue_abs_le;
- QReciprocalConditioning.conditionalReciprocal_bound;
- QReciprocalConditioning.conditionalReciprocal_energy_summable;
- QReciprocalConditioning.conditionalReciprocal_energy_le;
- QSquarefreeCRTResponse.conditionalReciprocal_residual_energy_le;
- QSquarefreeCRTResponse.conditionalReciprocal_residual_head_energy_le.

The auxiliary physical site zero is set to zero; it carries no Q mass.

## Infinite-modulus passage in the complete weighted energy

Let f_j be ANY family in QHilbert with ||f_j||<=C, C>=0. Let L_j be positive
integers tending to infinity. No convergence or periodicity of f_j is needed,
and the moduli need not be nested. The new result is

    Σ_(n>=1) |C_(L_j)Bf_j(n)-Bf_j(n)|²/[z n(8+log n)²] -> 0.

For a bounded scalar sequence |h(n)|<=A, the exact first-site/tail split gives

    |C_Lh(a)-h(a)| <= 2A(w_L(a)-Q(a))/w_L(a)
      <= 2Az a²/L².

For each fixed positive n, eventually n<=L_j, so the physical conditional
source uses n itself as its anchor. Taking A=sqrt(z)C proves coordinate
convergence, with error at most 2 z^(3/2) C n²/L_j². On the whole sequence,
the error is at most 2sqrt(z)C. Consequently the weighted square is bounded by

    4C²/[n(6+log n)²],

a summable majorant. Dominated convergence for the infinite sum proves the
claim. Auxiliary site zero has zero energy throughout.

Applying this to f_j=r_(S(j)) gives the same result for ANY squarefree stage
schedule S, using only ||r_N||<=1. In particular, increasing common CRT
moduli give a valid passage to infinity even when the residual changes with
the stage. This conclusion concerns the source BEFORE legal projection.
Indeed Br_N itself already has a uniform weighted budget. The role of CRT
here is an exact finite-period representation of its normal equations plus
a justified infinite-modulus limit; it does not supply weighted stability
of the squarefree projection.

Implemented declarations:

- QResidueConditional.fiberSum_first_tail;
- QResidueConditional.conditionalValue_deviation_tail_bound;
- QResidueConditional.conditionalValue_deviation_mass_bound;
- QResidueConditional.conditionalValue_deviation_bound;
- QReciprocalConditioning.conditionalReciprocal_sequence_error_bound;
- QReciprocalConditioning.conditionalReciprocal_weighted_error_tendsto_zero;
- QSquarefreeCRTResponse.conditionalReciprocal_residual_weighted_error_tendsto_zero.

## Exact transfer to the squarefree stage

If every active conductor at stage N divides L, the fiber averages preserve
every normal moment against g_d. Thus

    P_N(C_LBf)=P_NBf,
    b_N=P_Nu_(N,L).

No squarefreeness hypothesis on L itself is needed: the active dictionary
remains squarefree. A common squarefree modulus can be obtained from the
product of primes through N+1. The formal theorem exposes the exact
divisibility hypothesis for each active conductor.

The proof uses complete fiber sums, positive-site periodicity, and the
repository's uniqueness of synthesized normal-equation solutions. It does
not assume periodicity at auxiliary site zero.

Define e_(N,L)=u_(N,L)-b_N. Then e_(N,L) lies in V_N-perp, and for every head
the exact weighted identity is

    E_k(H,u)=E_k(H,b_N)+E_k(H,e)
      +2Σ_(n<=H)a_k(n)Q(n)b_N(n)e(n).

The new weighted cross term is retained. Ordinary Q orthogonality does not
make it zero. This is the precise point at which the source budget does not
yet become the requested correction budget.

Implemented in QSquarefreeCRTResponse:
stage_projection_conditionalReciprocal,
movingCorrection_eq_conditioned_projection,
conditionedRemainder_mem_orthogonal,
conditioned_source_weighted_energy_exact.

## Exact reciprocal bias and complete tail bound

Put B_j=1/(a+jL+1), β_L(a)=C_LB(a), δ_L(a)=B_0-β_L(a). Then

    w_L(a)δ_L(a)=Σ_(j>=0)Q(a+jL)(B_0-B_j).

The first term vanishes; every later term is retained. With
T_L(a)=Σ_(j>=1)Q(a+jL), the previously proved periodic-tail estimates give

    0<=w_L(a)δ_L(a)<=T_L(a)/(a+1),
    T_L(a)<=1/L²,
    0<=δ_L(a)<=z a²/[L²(a+1)]  (1<=a<=L).

For a periodic signed sequence r, factoring its value out of its own fiber
gives C_L(Br)(a)=r(a)β_L(a). No independence or positivity of r is assumed.
The formal factorization uses an all-site periodic scalar sequence; an actual
residual is interpreted with its periodic extension at auxiliary zero.

Implemented in QReciprocalConditioning:
conditionalValue_reciprocal_mul, reciprocalMean_defect_exact,
reciprocalMean_defect_weighted, reciprocalMean_defect_bound.

## Further ordinary estimates, not separate Lean declarations

The following derivations are paper arguments. They are not covered by the
scalar/source theorem axiom checks below.

For periodic r, fiberwise variance gives the complete identity

    ||Br||²=||C_LBr||²+||Br-C_LBr||²,
    Σ_jQ(a+jL)(B_j-B_0)²
      =Σ_jQ(a+jL)(B_j-β_L(a))²+w_L(a)δ_L(a)².

Since 0<=B_0-B_j<=B_0,

    Var(B|a) <= E[(B_0-B)²|a] <= B_0δ_L(a) <= z/L²,
    ||(I-C_L)Br||² <= z/L² ||r||².

On the whole Q space one also has

    ||(I-C_L)B||² <= z/L²+1/(L+2)².

Indeed, split the domain into sites1 throughL and the remaining sites. Images
of distinct head basis vectors occupy distinct residue fibers and are
orthogonal. At sitea their squared norms are
B_0²(1-Q(a)/w_L(a))<=z/L². On the tail, B has operator norm<=1/(L+2), and
I-C_L is a Q contraction. Cauchy--Schwarz combines the two orthogonal DOMAIN
norms; the two output ranges are not assumed orthogonal.

For a common period of the actual stage, set s_L(n)=r_N(a)/(a+1) on the fiber
of a. Then b_N=P_Ns_L-P_N(δ_Lr_N). Since δ²<=B_0δ<=z/L²,

    ||b_N-P_Ns_L||² <= z/L²||r_N||²,
    E_k(H,b_N-P_Ns_L) <= a_k(H)z/L²||r_N||².

Thus complete CRT tails contribute a controlled error. E_k(H,P_Ns_L) is still
uncontrolled. The analogous headResponse projection is
P_N-P_(tailStage(N,J)), onto V_N intersect tailStage(N,J)-perp; the same
contraction argument applies to it.

## Why legality and weighted stability cannot be assumed

The repository already proves C_3g_2 lies outside the closed squarefree span,
and also proves the primorial example C_6g_5 is illegal. The declarations are
QModThreeConditionalObstruction.residue_two_legal_conditional_not and
QPrimorialSixConditionalObstruction.input_legal_output_not. This continuation
uses them as existing obstructions, not as newly discovered results.

Even ambient Q-contractivity does not imply uniform weighted-energy
contractivity. An ordinary example is f=1_{n=M}. Then
C_Mf=z^(-1)1_{M divides n}. For fixed k>1 and A=k+6+log M,

    S_k(C_Mf)/S_k(f)
      = A^k/z² Σ_(j>=1)1/[j(A+log j)^k]
      >= A/[z²(k-1)] -> infinity.

Here S_k denotes the complete weighted energy. The lower bound is the
integral of the positive decreasing summand on[1,infinity). For k<=1 the
output has infinite S_k. This is a counterexample to a GENERIC conditional
expectation estimate, not to the actual correction bound. The smoothed
sources Br_N avoid this obstruction, as the new source theorem shows.

## Primary literature reviewed

- Alouges--Darses--Hillion, Polynomial approximations in a generalized
  Nyman--Beurling criterion, https://arxiv.org/html/2006.02953v2.
  Their unconditional approximation component is separate from the remaining
  coefficient/Gram-matrix control. This is methodological context, not a
  provider for our actual squarefree projection.
- Bettin--Conrey--Farmer, An optimal choice of Dirichlet polynomials for the
  Nyman--Beurling criterion, https://arxiv.org/pdf/1211.5191, Theorem1.
  The tapered Mobius coefficients are supported on squarefree integers, but
  their stated asymptotic assumes RH and an inverse-zeta-derivative moment
  bound. It cannot be imported as an unconditional estimate here.

## Wolfram finite diagnostics

These are numerical checks and pattern recognition, not an infinite proof or
a certified numerical-error bound. Complete progression weights were used:

    w_m(a)=psi_1(a/m)/(z m²),
    v_m(a)=[psi_1(a/m)/m²+(psi(a/m)-psi((a+1)/m))/m]/z.

The second is exactly Σ_jQ(a+jm)/(a+jm+1), by partial fractions. For each pair
d,e use m=lcm(d,e), G_de=Σ_aw_m(a)g_d(a)g_e(a), and
J_de=Σ_av_m(a)g_d(a)g_e(a). Also μ_d=<1,g_d>, ν_d=<B1,g_d>. The actual
correction coefficients solve G bcoeff=ν-JG^(-1)μ. No Haar Gram is substituted.

45-digit numerical evaluation gave the following rounded diagnostics:

| Masked stage N | Active atoms | ||r_N||² | E_2(N,b_N) |
|---:|---:|---:|---:|
| 5 | 4 | 0.02718156686 | 6.06508125e-7 |
| 10 | 7 | 0.01439979164 | 1.05196010e-6 |
| 15 | 10 | 0.01277462109 | 1.08948377e-6 |
| 20 | 13 | 0.01092407456 | 1.01892334e-6 |

These data support investigating a common budget but cannot establish one.

## Verification and remaining obligation

Saved-source integration passed job_QNKxMrTTLqNUq0eLvA8F13ECAxC3N8xm:
verified true, exit 0, 22.839 server seconds. This checked the complete source
budget, reciprocal bias, exact squarefree projection, and retained cross term.

After adding the infinite-modulus theorem, saved-source verification passed
job_NLnqgZnIoeUrV2x4goKpzc_vHSa7Un2v: verified true, exit 0, 15.879 server
seconds. Six principal declarations, including the generic deviation bound,
the arbitrary-moving-input convergence theorem, its actual residual
specialization, projection identity, source head budget, and exact weighted
identity, reported only propext, Classical.choice, and Quot.sound.
The residual specialization assumes only positive moduli tending to infinity;
its stage schedule is arbitrary. Projection identities additionally expose
the active-conductor divisibility hypothesis. These type hypotheses are not
discharged by an axiom report.

Those durations are server verification durations, not request latency.
Polling was delayed by at least the returned 30-second retry interval.
Final project publication additionally uses the server checkpoint audit and
validation gate; an accepted checkpoint request alone is not verification.

Open: weighted control of P_N on this particular bounded signed CRT source,
or direct control of its retained weighted cross term. Infinite CRT,
martingale convergence, and prime-valuation independence do not discharge it.
