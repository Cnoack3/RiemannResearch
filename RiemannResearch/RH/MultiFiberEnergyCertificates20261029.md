# Complete multi-fiber Q and Pareto energy certificates

29 October 2026. Source: the user's proposed d=5 two-fiber certificates and
request to complete the physical-support assembly of
`Analysis/WeightedConstraintEnergy.lean` from commit
`b13b916ca7e382068ad80b6e7a70c372df7ed306`.

This development also uses the existing radical-compatible Hilbert space,
the complete weighted norm identities, and the sequence-preserving Q/Pareto
maps. The earlier paper-level infinite-fiber calculation is recorded in
[GeneralSquarefreeConstraintEnergy20261029.md](GeneralSquarefreeConstraintEnergy20261029.md).
No novelty claim is made. No uniform upper-energy hypothesis or RH is assumed.

## 1. Arithmetic and the constraints

Let d >= 2 be squarefree, and let T be any finite set of integers m > d
with rad(m)=d. Powers m=d^k with k>=2 are particular examples.
Every m in T is a positive multiple of d, so m>=2d>d+1.
Two distinct such multiples differ by at least d>=2. Hence the pairs
{m-1,m} are mutually disjoint and lie strictly beyond d. They are disjoint
from the prescribed head {1,...,d-1} and the shared coordinate d.

For a radical-compatible F, with F(d-1)=1,

\[
 F(m)-F(m-1)=F(\operatorname{rad}(m))-F(\operatorname{rad}(m)-1)
 =F(d)-1.
\]

Thus every row is the exact signed identity

\[
 F(d)+F(m-1)-F(m)=1.
\]

The remaining prescribed head values are used only in the energy split.
The Lean family theorems state d+1<m explicitly; powers supply this fact
through `Nat.power_fiber_beyond_head`. Radical separation is proved for any
finite fiber, without assuming pairwise disjointness in the final applications.

## 2. The complete identity comes first

Let a(n)>0 for n>=1, suppose E_a(F)=sum F(n)^2/a(n)<infinity, and set

\[
 A=a(d),\quad B_m=a(m-1),\quad C_m=a(m),\quad
 x=F(d),\ y_m=F(m-1),\ z_m=F(m),\quad
 S=\sum_{m\in T}\frac1{B_m+C_m}.
\]

Define the actual selected physical support and its full complement energy by

\[
 J=\{1,\ldots,d-1\}\cup\{d\}\cup\bigcup_{m\in T}\{m-1,m\},
 \qquad \Omega=\sum_{\substack{n\ge1\\n\notin J}}\frac{F(n)^2}{a(n)}.
\]

All selected sites are disjoint. Summability therefore gives an exact
head/selected-sites/complement decomposition. Applying
`shared_family_completion` to that finite selected sum gives

\[
\begin{aligned}
E_a(F)={}&\sum_{n=1}^{d-1}\frac1{a(n)}+\frac{S}{1+AS}
 +\left(\frac1A+S\right)
     \left(x-\frac{AS}{1+AS}\right)^2\\
&+\sum_{m\in T}\left[
  \frac{(y_m-B_m(1-x)/(B_m+C_m))^2}{B_m}
 +\frac{(z_m+C_m(1-x)/(B_m+C_m))^2}{C_m}
 \right]+\Omega.
\end{aligned}
\]

Every square remainder and every omitted physical coordinate survives.
The implementation includes n=0, where the actual Q and Pareto weights
vanish, and so adds no energy. The lower inequality discards only the
explicit nonnegative remainder terms.

The correction is sharp for the relaxed problem consisting only of these
selected rows: take x=AS/(1+AS),
y_m=B_m/[(B_m+C_m)(1+AS)],
z_m=-C_m/[(B_m+C_m)(1+AS)], and zero at unselected positive sites.
This is not a claim that this relaxed minimizer satisfies every other
radical constraint or belongs to the legal CRT span.

## 3. General finite-family Hilbert inequalities

For Q(n)=1/[zeta(2)n^2], put

\[
 S_Q(d,T)=\sum_{m\in T}\frac1{(m-1)^2+m^2}.
\]

The exact identity in Section 2 has a(n)=n^2 and is divided in its entirety
by zeta(2). In particular,

\[
 \boxed{\|F\|_Q^2\ge
 \frac{\displaystyle\sum_{n=1}^{d-1}n^{-2}
       +S_Q(d,T)/(1+d^2S_Q(d,T))}{\zeta(2)}.}
\]

For P(n)=1/[n(n+1)], the pair denominator simplifies exactly:
(m-1)m+m(m+1)=2m^2. Thus set

\[
 S_P(d,T)=\frac12\sum_{m\in T}\frac1{m^2},
 \qquad
 \boxed{\|F\|_P^2\ge
 \frac{d-1}{d}+\frac{S_P(d,T)}{1+d(d+1)S_P(d,T)}.}
\]

Both bounds apply to radical-compatible vectors. Existing checked inclusions
give their closed-legal-span specializations. The native Pareto theorem
states compatibility directly in its physical coordinates; no equality of
Q and Pareto projections is assumed.

For any finite K subset {2,3,...}, take T={d^k:k in K}. Strict monotonicity
of k -> d^k proves injectivity, so these conductances equal the corresponding
sums over k with no multiplicity loss. Lean supplies both the radical and
disjointness facts for these powers.

## 4. Exact d=5, two-fiber certificates

Take K={2,3}, T={25,125}. The selected support is exactly
{1,2,3,4,5,24,25,124,125}; its complete complement is retained.

\[
 S_Q=\frac1{1201}+\frac1{31001},\qquad
 \frac{S_Q}{1+25S_Q}=\frac{32202}{38037251}.
\]

\[
 \frac{32202}{38037251}-\frac1{1226}
   =\frac{1442401}{46633669726}>0.
\]

\[
 \boxed{\|F\|_Q^2\ge
  \frac{205/144+32202/38037251}{\zeta(2)}.}
\]

For Pareto,

\[
 S_P=\frac1{1250}+\frac1{31250},\qquad
 \frac{S_P}{1+30S_P}=\frac{13}{16015},
\]

\[
 \frac{13}{16015}-\frac1{1280}=\frac{25}{819968}>0,
 \qquad
 \boxed{\|F\|_P^2\ge\frac45+\frac{13}{16015}.}
\]

These are symbolic rational equalities and Hilbert inequalities, with no
floating-point computation or sampled tail.

## 5. Larger families: what improves and what saturates

For A>=0 and 0<=S<S',

\[
 \frac{S'}{1+AS'}-\frac{S}{1+AS}
 =\frac{S'-S}{(1+AS')(1+AS)}>0.
\]

Thus every new positive pair improves the certificate, while correctly
counting the shared coordinate only once. Adding independent single-row
bounds would double-count that coordinate. The exact increment identity
was already checked in `WeightedConstraintEnergy`; the new
`family_correction_insert_strict` assembles it for finite physical families.

The following infinite-family calculations are ordinary mathematical proofs,
not additional Lean declarations in this change. For K={2,...,N}, N>=2,
geometric summation yields

\[
 S_{P,N}=\frac{1-d^{-2(N-1)}}{2d^2(d^2-1)},\quad
 S_{P,\infty}=\frac1{2d^2(d^2-1)},\quad
 \delta_{P,\infty}=\frac1{d(d+1)(2d^2-2d+1)}.
\]

Pass to the limit in the finite lower inequalities by continuity of S/(1+AS).
For d=5 this gives

\[
 \|F\|_P^2\ge\frac45+\frac1{1230}=\frac{197}{246},\qquad
 \frac1{1230}-\frac{13}{16015}=\frac1{787938}.
\]

Since 5 is prime, its entire later radical fiber consists of these powers.
This is the saturation value of this shared-fiber correction; it is not
asserted to be the optimal energy under all radical or legal constraints.

For composite squarefree d, use all m>d with rad(m)=d. Unique prime
factorization and finite products of absolutely convergent geometric series
give the larger conductance

\[
 S_{P,\mathrm{all}}=
 \frac12\left(\prod_{p\mid d}\frac1{p^2-1}-\frac1{d^2}\right).
\]

The same disjointness proof applies to this entire countable fiber.
The infinite exact identity also holds: each pair remainder is nonnegative
and at most its pair energy, so the remainder series converges; decompose
the complete energy over the head, the shared site, all pairs, and the
remaining complement before applying the scalar completion with S=S_infty.
This justifies preservation of the infinite complement as well as the limit
of the lower certificates.

For Q powers, set alpha_d=2-2/d^2+1/d^4. Since m=d^k>=d^2,

\[
 \alpha_d m^2\le (m-1)^2+m^2\le 2m^2.
\]

Consequently S_Q,infty is finite and satisfies

\[
 \frac1{2d^2(d^2-1)}\le S_{Q,\infty}
 \le\frac1{\alpha_d d^2(d^2-1)}.
\]

After retaining powers through N, its unadded conductance is at most

\[
 \frac{d^{-2(N+1)}}{\alpha_d(1-d^{-2})}.
\]

The exact increment identity bounds the unadded correction by this same
quantity. Thus increasingly high powers have a controlled geometric gain.

## 6. Structural consequence for exact-head minimization

The constant physical sequence 1 (anchored to zero at coordinate zero)
satisfies every radical-compatibility constraint and has energy 1 in both
probability metrics. This is an existing kernel-checked fact. Applying the
new finite-family bounds to it proves the new declaration
`radical_family_certificates_le_one`: both complete finite-family lower
certificates are at most 1, unconditionally.

More generally, even imposing every radical constraint leaves 1 feasible.
Therefore radical constraints alone cannot force the compatible exact-head
minimum above 1 or force divergence. This does not prove that 1 belongs to
the closed legal squarefree CRT span V. That membership is the missing
global issue. A lower bound in the larger compatible space supplies no
upper bound in V or its finite legal spans.

The complete-square formula gives a useful quantitative obstruction for a
proposed energy budget. If e=E_a(F)-head-S/(1+AS), then e>=0 and

\[
 \left|F(d)-\frac{AS}{1+AS}\right|^2
 \le\frac{e}{1/A+S}.
\]

Each pair square and the omitted energy is likewise bounded by e. Thus a
candidate with an energy budget very close to this lower certificate must
place its shared coordinate and pairs near the displayed scalar optimizer.
Any conflicting independently proved constraint can raise the lower bound.
These deviation consequences are paper-level readings of the checked exact
identity; they are not separate declarations.

For contrast, let mu_H be the infimum of complete energy among finite legal
CRT vectors equal to 1 through H, assuming those finite-head sets are
nonempty as established elsewhere in this project. If mu_H stayed bounded,
choose nearly minimizing vectors. Their coordinates converge to 1 and they
are Hilbert bounded, so a weakly convergent subsequence has weak limit 1.
Since V is a closed linear subspace, it is weakly closed, and hence 1 is in V.
Thus if 1 is not in V, these nested legal minima must tend to infinity.
This weak-compactness implication is an ordinary proof here, not a new Lean
declaration. The radical-space certificates cannot decide which case holds.
The still-open target is a uniform upper bound for complete *legal*
exact-head energies, with all coordinates included.

## 7. Formalization and verification scope

- `Analysis/WeightedSharedFamilyEnergy.lean`: finite physical support sums;
  `complete_family_split`, `complete_family_completion`, and
  `complete_family_lower_bound`; nonnegative remainders and entire omitted
  series; strict improvement on adjoining a positive pair.
- `NumberTheory/RadicalFiberSeparation.lean`: separation for distinct
  multiples and arbitrary radical fibers; radical of every positive power
  of a squarefree integer; head separation and distinct-power disjointness.
- `RH/SquarefreeMultiFiberEnergy.lean`: arbitrary finite radical-family
  complete Q and Pareto identities and bounds; native Pareto formulation;
  finite power-family and closed-legal-span bounds; exact two-fiber constants
  and complete d=5 inequalities; the unconditional unit-energy cap on these
  lower certificates.

Assumptions of the application theorems are precisely Hilbert membership,
radical compatibility, the prescribed head, and the displayed elementary
finite-family conditions. Summability, denominator positivity, physical
pair disjointness, and the radical constraints are proved providers, not
unresolved analytic hypotheses. There is no density, RH, or upper-energy
assumption. No `sorry`, `admit`, project-local axiom, or unsafe declaration
is introduced.

The generic completion and power-disjointness check succeeded in server job
`job_1XL05VMgkW1p6m_vxCjx8Ng5_vwzjTix` (reported verification duration
10.009 seconds). The general Hilbert application and d=5 inequalities
succeeded in `job_BS3daUQ7tNSEr7AP9qUSuYSCNh_haaQp` (60.219 seconds).
The final structural cap, fresh-pair improvement, and symbolic certificates
succeeded in `job_AdhmRH5VZmGK75XXZaKGWuOwaPGJw47K` (15.458 seconds).
Representative axiom inspections returned only `propext`, `Classical.choice`,
and `Quot.sound`. These durations are server-reported verification durations,
not workspace-opening or client polling timings. Initial workspace opening
ran concurrently with GitHub reads; its individual duration was not measured.
Queue admission reported position 1. Status polls follow the server's
requested delay; those delays are not counted as proof-checking measurements.
Final source acceptance and publication use one checkpoint with push enabled;
its terminal result is reported with the delivered commit.
