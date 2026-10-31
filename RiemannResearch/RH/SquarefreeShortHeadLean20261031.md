# Squarefree short-head responses: Lean formalization and refinements

Date: 31 October 2026.

This continues `SquarefreePrefixResponseResearch20261030.md` and
`SquarefreeShortHeadSchurResearch20261030.md`. The results below concern the
ordinary canonical projection onto the complete squarefree dictionary,
including composite conductors. Every Gram matrix and projection uses the
complete Q inner product. No uniform arithmetic source envelope or proof of
RH is asserted.

## Objects and conventions

For physical integers m >= 1, let Q(m)=1/(zeta(2)m^2),
D_N={d: 2<=d<=N+1, d squarefree}, and g_d(m)=(m mod d)/d.
Write V_N=span{g_d:d in D_N}, F_N=P_N 1, r_N=1-F_N,
epsilon_N=||r_N||_Q^2, Bf(m)=f(m)/(m+1), and b_N=P_N B r_N.
The existing formal development supplies epsilon_N>0 at every finite stage.

Let k_{N,n}=P_N e_n, where e_n is the Q evaluation representer. The actual
short source and signed response formalized here are

\[
 z_{N,H,n}(m)=1_{m\le H}\left(\frac1{m+1}-\frac1{n+1}\right)r_N(m),
 \qquad T_{N,H}(n)=\langle k_{N,n},z_{N,H,n}\rangle_Q.
\]

`QSquarefreeShortHeadResponse.response_eq_head_pairing` connects this source
to the existing kernel-localization formula. Physical indices start at 1;
the underlying lp coordinates start at 0.

## Improved divisor estimate and complete inverse Gram

Put

\[
 L_H=\sum_{a=1}^H\frac{|\mu(a)|}{a},\qquad
 \delta_H=2-\frac1H,\qquad C_H=\zeta(2)(\delta_H L_H)^2\quad(H\ge1).
\]

The finite weighted backward shift has norm at most (H-1)/H. Applying the
finite dilation estimate to the exact signed Mobius inversion gives, for
every finite conductor synthesis f=sum_d c_d g_d with d>=2,

\[
 \left(\sum_d\frac{c_d}{d}\right)^2+
 \sum_{d\le H}\left(\frac{c_d}{d}\right)^2
 \le C_H\,\|1_{m\le H}f\|_Q^2.
\]

All high coefficients remain in the slope square. The supporting identities
are `normalizedResidueSynthesis_charge_energy_exact` and
`qSynthesis_head_coercivity`. The finite convolution bound does not assume
signed Mobius cancellation. Lean also proves L_H<=1+log H and
(delta_H L_H)^2<4 L_H^2. Thus this is a strict finite-cutoff improvement of
the previous factor 4; the logarithmic exponent is unchanged.

Choose a legal squarefree anchor H<d0<=N+1 and use
rho_0=d0 g_d0 and rho_d=d g_d-d0 g_d0 for every squarefree 2<=d<=H.
Let W=V_N intersect {f:f(m)=0 for m<=H}, psi_i=(I-P_W)rho_i, and let
S be the complete Gram of the psi_i. Lean proves

\[
 b^T S^{-1}b\le C_H\sum_i b_i^2.
\]

This is uniform in N and in the anchor. The entire head-null subspace is
projected away; no infinite tail is replaced by a truncated Gram.
The exact energy split keeps its full tail norm square. A legal anchor
exists by Bertrand's theorem whenever 1<=H and 2H<=N+1.

The concrete Schur family spans V_N intersect W-perp. If
y_i(n)=psi_i(n) and q_i=<rho_i,z_{N,H,n}>_Q, the full signed response is

\[
 T_{N,H}(n)=y(n)^TS^{-1}q.
\]

`QSquarefreeSchurRepresentation.shortHead_response_eq_schur_inverseGram`
identifies the actual canonical source with this formula, without a span
or arithmetic-provider hypothesis. The resulting finite estimate is

\[
 T_{N,H}(n)^2\le C_H^2\left(\sum_i y_i(n)^2\right)
                                  \left(\sum_i q_i^2\right).
\]

The factor C_H is independent of N. The two remaining vectors still
depend on N and n; no uniform polylogarithmic bound for their product is
proved. The exact signed inverse pairing can be much smaller than this
Cauchy bound, so the latter is a sufficient route rather than an equivalent
arithmetic obligation.

For the full normalized family {d g_d:d in D_N}, retaining the slope square
gives the stronger rank-one estimate, with k=|D_N|,

\[
 b^T\operatorname{Gram}(d g_d)^{-1}b
 \le C_{N+1}\left(\sum_d b_d^2-
       \frac{(\sum_d b_d)^2}{k+1}\right).
\]

`inverse_rankOne_deficit` records the exact coefficient completion square
and the original coercivity slack before obtaining this inequality.
`QFullGramRankOne.completeSquarefree_inverseGram_rankOne` discharges the
coercivity hypothesis for the actual full squarefree family.

## Signed variance, complementary channel, and stage changes

Write epsilon=||r||^2, E1=<r,z>, E2=||z||^2,
u=z-(E1/epsilon)r, D^2=||(I-P_N)u||^2, and V=E2-E1^2/epsilon.
Then the formal exact identity is

\[
 \|P_Nz\|^2=V-D^2.
\]

When H<n, put
K=||k_{N,n}||^2,
L=zeta(2)n^2-K-r_N(n)^2/epsilon, and a=r_N(n)E1/epsilon.
Both K and L are nonnegative, and the two signed channels satisfy

\[
 T^2\le K(V-D^2),\qquad (T+a)^2\le L D^2.
\]

The complete signed complementary equality is proved before Cauchy-Schwarz.
Eliminating D^2 yields the additional joint constraint

\[
 ((K+L)T+Ka)^2\le KL((K+L)V-a^2).
\]

This can help when the loss D^2 is unknown. If its actual value is known,
the intersection of the original two inequalities may be tighter.

For M<=N, the formal stage identities retain
||k_N-k_M||^2=||k_N||^2-||k_M||^2 and
||F_N-F_M||^2=epsilon_M-epsilon_N. The exact response difference contains
both the kernel change and the source change. Finite energy controls these
changes for fixed tests; it does not supply uniform control at moving n.

The partial normal equations are also retained exactly:

\[
 \langle v,1_{m\le H}r_N\rangle_Q
 =-\langle v,1_{m>H}r_N\rangle_Q\quad(v\in V_N).
\]

The finite-head source annihilates W. Its moments against psi_i and rho_i
are equal. This transfers the equations without assuming cancellation
between neighboring multiplicative ranges.

## Weaker conditional RH hypotheses

The pointwise criterion now permits a different unbounded set of stages
for each fixed physical site. More substantially, a single common
arithmetic constant C>=0 and exponent A in N suffice if, for every dyadic
M=2^j, arbitrarily large N satisfy

\[
 \sum_{n=M+1}^{2M}T_{N,H_M}(n)^2
 \le CM(6+\log M)^{2A},\qquad
 H_M=\left\lfloor\frac{M}{6+\log M}\right\rfloor.
\]

This exact implication to RH is formalized as
`QSquarefreeShortHeadBlocks.riemannHypothesis_of_frequently_dyadic_shortHead_meanSquare`.
The unbounded stage set may depend on the block. The proof passes finite
blocks to the strong projection limit, obtains complete logarithmically
weighted summable energy, and applies the existing conditional RH theorem.
It does not require pointwise control at every stage and site.

Localization proves |b_N(n)-T_{N,H_M}(n)|<=2 sqrt(zeta(2))(6+log M) on the
whole block. The exact weighted-Young identity preserves the loss

\[
 \sum b^2=(1+t)\sum T^2+(1+1/t)\sum(b-T)^2
          -t^{-1}\sum(tT-(b-T))^2.
\]

For t>0 the transfer constant is (1+t)C+4 zeta(2)(1+1/t).
When C>0 it is minimized at t=2 sqrt(zeta(2))/sqrt C, giving
(sqrt C+2 sqrt(zeta(2)))^2 instead of 2C+8 zeta(2).
The optimized actual-block theorem also retains the nonnegative loss on
the left. The block arithmetic envelope above remains **Open**.

## Diagnostic check at N=240, n=221

These are exploratory float64 calculations from the complete-period Q
Gram, not interval certificates or asymptotic evidence. There are 149
conductors, H=19, and 13 compressed coordinates.

| Quantity | Value |
|---|---:|
| Full b_N(n) | -0.0489055412321 |
| Lower response | -0.0491975407425 |
| Actual short response T | -0.0426665815001 |
| Finite source/evaluation upper bound for abs(T) | 2.69119246718 |
| Old Schur inverse bound | 53.8286309089 |
| Improved Schur inverse bound | 51.0328225168 |
| Observed inverse norm | 4.15089316265 |
| Joint ellipse lower endpoint | -0.535274036315 |
| Joint ellipse upper endpoint | 0.518884807439 |
| Full normalized rank-one C_241 | 126.198847015 |
| Smallest eigenvalue of C_241(I-11^T/150)-Gram(dg_d)^(-1) | 0.830735676271 |

The actual short response lies in all the stated numerical intervals.
The joint ellipse improves the variance-only radius 0.604029643950, but
the loss-informed complementary interval [-0.387077188590,0.318206419629]
is tighter in this example. The finite source/evaluation bound is valid but
much looser: the actual evaluation and signed-moment norms are approximately
18.6065854956 and 0.00283418690283. At t=1, the Young loss square is
0.00132697162768 and the floating identity discrepancy is below 5e-19.

All eight original lower ranges remain negative:

| Physical range | Signed contribution |
|---|---:|
| 1 | -0.00637989555610 |
| 2--3 | -0.00147732211631 |
| 4--7 | -0.0173828224836 |
| 8--15 | -0.0122560732143 |
| 16--31 | -0.00799261242043 |
| 32--63 | -0.00244179318703 |
| 64--127 | -0.00122475486832 |
| 128--220 | -0.0000422668964261 |

## Remaining arithmetic task and formal scope

The inverse-Gram estimates are unconditional. They do not by themselves
bound the pairing of the signed source moments with the evaluation vector.
A polylogarithmic bound for that actual pairing, or the weaker common
dyadic mean-square envelope, remains **Open**. No adjacent-range sign
cancellation is assumed, and no uniform-in-N-and-n estimate is claimed.

The new formalization covers the divisor energy, inverse-Gram bounds,
centered signed source identities, partial normal equations, stage-gap
identities, and the stated conditional RH reductions. The October 30
memorandum's separate multiplicative-range Abel identities are still
paper-level unless covered by a separately identified existing declaration.
The float64 diagnostics are not Lean-certified.


## Verification record

The separate-import check of all 18 new Lean modules succeeded:
`job_f7lm0ApRjtS7S46HsR7jNLtKLzZR4dER` (37.831 seconds reported by the
server). It checks the actual module files and import graph, including the
optimized block theorem and the concrete inverse-Gram source formula.

The focused foundation audit succeeded:
`job_c7yHeoDnemDAajJT1x6lNS-fLKgTz1qA` (6.653 server seconds).
The actual Schur response estimate, full normalized rank-one inverse bound,
joint ellipse, optimized block estimate, and frequent dyadic short-head RH
implication depend only on `propext`, `Classical.choice`, and `Quot.sound`.
This audit does not discharge hypotheses in their types: the common
arithmetic envelope is still Open.

These verification durations exclude client queue/polling time.

The first publication checkpoint, `job_n7ZeLghLF3eEEs1aUBgTbUvanBKwki-T`,
terminated with a cache-upload timeout: `lake cache put` exceeded 3600
seconds. Its total server job duration was 3681.527 seconds. No new commit
was published by that failed checkpoint. This was an infrastructure failure;
the separate-import and foundation checks above had succeeded.

The preserved workspace was resumed for recovery on 31 October 2026.
Reopening took 92.611 seconds of client request time; this is distinct
from Lean verification time. All 18 staged Lean source files matched the
verified recovery archive. Publication remains gated by a successful server
checkpoint of the complete unpublished delta and any integrated main changes.
The final checkpoint job, scope, and exact commit are reported with delivery.
