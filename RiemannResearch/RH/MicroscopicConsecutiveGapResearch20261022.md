# Microscopic consecutive zeta ordinates: proved transfers and analytic consequences

Date: 2026-10-22.

## 1. Convention and status

List ALL positive nontrivial zero ordinates in nondecreasing order, retaining
analytic multiplicity and different zeros with the same ordinate. Put

\[
L_T=\frac{\log T}{2\pi},\qquad
g_{n,T}=L_T(\gamma_{n+1}-\gamma_n),\qquad
M_T=N(2T)-N(T).
\]

The new Lean files prove finite moment/gap transfers and exact actual-zero
criteria. The analytic consequences below use cited, unconditional classical
theorems whose proofs are NOT newly formalized here. In particular, a proof
of the exponential tail below in ordinary mathematics is distinct from a
kernel verification of Tsang's theorem.

## 2. An unconditional exponential upper tail

There are absolute constants A,c>0 such that, for every fixed u>=1,

\[
\boxed{\limsup_{T\to\infty}
\frac{\#\{n:T<\gamma_n\le2T,\ g_{n,T}\ge u\}}{M_T}
\le A e^{-cu}.}
\]

This is a standard consequence of uniform high moments, not a novelty claim.
The limit in T is taken for each fixed u. No simultaneous moving-u assertion
is intended.

Analytic input: Tsang's moment theorem, as stated in Theorem 2 of Simonic,
Trudgian and Turnage-Butterbaugh, *Some explicit and unconditional results on
gaps between zeroes of the Riemann zeta-function*,
<https://arxiv.org/pdf/2010.10675>. For H=T and h=u/(2L_T), it implies

\[
\frac1T\int_T^{2T}|S(t+h)-S(t)|^{2k}dt
\le (Ck\log(2+u))^k+(Ck^2)^k
\]

for every positive integer k and sufficiently large T, with absolute C.
The threshold for T may depend on k and u. The uniform growth in k is
essential; bounds with unspecified constants depending on k would not
justify the optimization below.

Proof of the transfer: a gap with g>=u, except possibly the one crossing
2T, provides a disjoint interval of starts of length at least h for which
N(t+h)-N(t)=0. If B_T counts these gaps and E_T is this empty-window set,

\[
(B_T-1)h\le |E_T|.
\]

Riemann-von Mangoldt, uniformly for t in [T,2T] and fixed u, gives on E_T
S(t+h)-S(t)=-u/2+o(1). Hence its absolute value is at least u/3 for large T.
Markov's inequality and M_T~TL_T yield

\[
\limsup B_T/M_T\le \frac C u
\left[\left(\frac{Ck\log(2+u)}{u^2}\right)^k
+\left(\frac{Ck^2}{u^2}\right)^k\right].
\]

Choose k=floor(a u), for a sufficiently small absolute a>0. For large u,
both bases are at most 1/4, and k>=au/2. This proves the displayed
exponential estimate. Enlarging A handles bounded u. Zero gaps never enter
this upper-tail count, and the single endpoint error tends to zero.

## 3. Exact finite moment transfers

For a finite gap family, write SL(s)=average (g-s)_+, SF(s)=average (s-g)_+,
and m=average g. The exact identity is

\[
SF(s)=s-m+SL(s).
\]

For circular gaps at intensity one and a window shorter than the circumference,
the geometric empty-window identity is
SL(s)=P(X_s=0), where X_s counts points in a uniformly translated interval.
A finite configuration has a finite count law, so its probabilities can
be represented by nonnegative weights summing to one. Our Lean theorem
keeps the geometric identity explicit as a hypothesis; it does not silently
replace the repository's truncated endpoint model by a circle.

If EX=s and EX^2=s^2+V, the exact square identity

\[
\mathbb E\big[(sX-(s^2+V))^2\big]=V(s^2+V)
\]

implies P(X=0)<=V/(s^2+V). Consequently, for y>s>0,

\[
\boxed{P_{\rm gaps}(g\ge y)
\le \frac{V(s)}{(y-s)(s^2+V(s))}.}
\]

There is also the higher-moment transfer
P_gaps(g>=y)<=E|X_s-s|^m/[s^m(y-s)]. These are finite exact inequalities,
not assumptions of sine-kernel statistics.

Integer-valued counts admit a further proved refinement. For every integer
k>=1, the polynomial (X-k)(X-k-1) is nonnegative and majorizes
k(k+1) times the zero indicator. Therefore, with q=s^2+V,

\[
P(X=0)\le\frac{q-(2k+1)s+k(k+1)}{k(k+1)}.
\]

One can take the minimum over k and combine it with the gap stop-loss bound.
For s>0 the optimal integer majorant is obtained with k=floor(q/s).
Its equality law is supported on {0,k,k+1}, with masses
p_k=((k+1)s-q)/k, p_{k+1}=(q-ks)/(k+1), and the remaining mass at zero.
These masses are nonnegative for feasible integer moments. The inequality
for every positive k is formalized; the optimality characterization is the
ordinary algebraic argument just given.

For integer counts, the complete factorial identity is

\[
V+s^2-s=2E(X-1)_++E[(X-1)_+(X-2)_+].
\]

The final term is nonnegative and is retained in the formal identity.
For mean-one gaps this gives, whenever y<s,

\[
P_{\rm gaps}(g\le y)\le
\frac{V(s)+s^2-s}{2(s-y)}.
\]

Thus sine-kernel variance at every fixed scale would supply cubic small-gap
upper bounds. Its required limiting variance remains an analytic hypothesis.
An unconditional O(log(2+s)) variance bound only controls the large-s tail;
it cannot be substituted for the precise cancellation V(s)+s^2-s near zero.

## 4. Exact zero-gap criterion and its RH meaning

`ActualConsecutiveGapCriterion.lean` uses the existing chronological list of
actual zeta-zero copies. It excludes the artificial last gap to T.
It proves that all genuine interior gaps are positive if and only if every
zero through T is simple and has real part 1/2. Equivalently, the integer
count of zero interior gaps vanishes. The same equivalence holds cofinally.

The reason is that an off-line zero and its reflected partner have exactly
the same ordinate; multiplicity likewise creates repeated entries.
Consequently strict ordering cannot be an unconditional enumeration premise.
This condition is stronger than RH alone because it includes simplicity.
Density-one positivity does not exclude finitely many or zero-density
exceptions and therefore does not prove RH.

For an RH-only analogue, enumerate each distinct COMPLEX zero once. Do not
deduplicate the ordinates: doing so erases the very horizontal collisions
that carry information about RH. This analogue is not newly formalized here.

## 5. Current unconditional comparisons

Recent preprints supply stronger positive-density information than the
classical existence of small and large gaps. Lamzouri, *Isolated zeros of
the Riemann zeta function and zeros of linear combinations of Dirichlet L-functions*, October 19, 2026,
<https://arxiv.org/html/2610.26841v1>, Theorems 1.1-1.2, proves a lower
proportion 0.50875 with both neighboring gaps exceeding one sixth of the
mean scale. Runs of 3,4,5 gaps with respective thresholds
0.1458,0.1299,0.1182 have lower proportions 0.345,0.1812,0.0175.
These are cited results, not Lean providers in this contribution.

Tianyu Zhao, <https://arxiv.org/html/2603.17334v1>, gives positive proportions
above 1+9e-7 and below 1-9e-7, each exceeding 2e-42. Fujii's fixed-moment
bounds, <https://www.jstage.jst.go.jp/article/pjab1945/51/10/51_10_741/_pdf>,
then give the ordinary mathematical consequence

\[
0<3.24\cdot10^{-54}\le\liminf_T\operatorname{avg}(g_{n,T}-1)^2
\le\limsup_T\operatorname{avg}(g_{n,T}-1)^2<\infty.
\]

The numeric lower bound comes from two disjoint events, each contributing
(2e-42)(9e-7)^2. In particular, vanishing microscopic gap variance is false.

## 6. Research boundary

The useful unresolved target is quantitative control near zero, including
collisions, rather than only large-gap integrability. Full sine-kernel
variance, or suitably complete pair statistics including multiplicities,
would imply strong repulsion. Mesoscopic variance theorems do not provide
this fixed-scale limit.

Pair statistics do not generally determine consecutive-gap distributions.
The sets {0,1,4,10,12,17} and {0,1,8,11,13,17} have the same positive
pair-difference multiset {1,...,13,16,17}, but consecutive gaps
(1,3,6,2,5) and (1,7,3,2,4). Periodicizing with period 40 and applying a
uniform random shift preserves the pair statistics and distinguishes the
nearest-neighbor laws. This is a general non-identifiability example, not
a counterexample to a special implication of sine-kernel pair statistics.

None of the tail bounds establishes the uniform arithmetic head-repair
estimate from the preceding continuation. A proposed connection must still
control the means and complete Gram quadratic forms for the growing family
of arithmetic tests.

## 7. Verification ledger

The final report records the exact snippet and checkpoint jobs. Workspace
resumption was batched with a web lookup, so its individual round-trip time
was not measured. Queue and polling delays are separate from the server's
reported Lean duration. Analytic literature theorems and asymptotic
consequences in Sections 2 and 5 are not claimed as kernel-verified here.

The combined candidate passed `job_IpGcQZW2IkOT9za93zjDg6Xr8LIymrzy`: exit 0,
verified=true. Server verification time was 5.947 seconds; queue delay was
approximately 0.0016 seconds. Seven central declarations used only propext,
Classical.choice and Quot.sound. Subsequent source cleanup removed only two
unused tactic/simp arguments. Publication requires the containing checkpoint
to validate the persisted modules and aggregate export.
