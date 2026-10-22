# Feasible complete-Gram head repair and the remaining arithmetic bound

22 October 2026. Continuation of `RiemannResearch_Continuation_Agenda_2026-10-22.md`,
starting from commit `ba87546eb4e0fa6fb0adf06ba607de094330bbdf`.

## 1. Conclusion and verification scope

The finite head-repair calculation can be completed without an invertible
physical-head Gram. This is essential for the actual squarefree legal span:
its physical observation rows are dependent as soon as four sites are present.
The corrected formulation gives an exact directional arithmetic provider,
which feeds the existing complete-Q bounded-exact-head theorem and hence RH.
It does not prove that provider or RH.

The core coherent candidate, including rank-free solvability, exact repair,
sampled repair stability, the actual Q consumer, and the rank obstruction,
passed `job_J3EsWCrx8r5PV3GerVTGR1GCZBWxSRP9`, exit 0, verified=true.
The server reported 8.445 seconds for that job; this is not workspace-opening
or user-visible round-trip time. Six central axiom audits reported only
`propext`, `Classical.choice`, and `Quot.sound`. Explicit hypotheses are not
discharged by an axiom audit. The complementary covariance and actual weighted-frame consumer also passed
`job_R9o_ZtxHDeOgoLZd_AIl8BaRiT2YwzMQ`, exit 0, verified=true, reported
6.323 seconds, with two further ordinary-foundation axiom audits.
The core job queue delay was approximately 0.0013 seconds; status polling was
separate and respected the requested 30-second interval. Workspace-opening
duration was not measured separately. The containing publication must also pass the
server checkpoint over the final modules and their project dependents.

| Module | Role |
| --- | --- |
| `Analysis/FiniteFeasibleGramRepair.lean` | Arbitrary compatible Gram sources; attained norm completion; exact dual; dependent-row repair; frame and complementary-covariance bounds |
| `Analysis/FiniteSampledRepairStability.lean` | Exact sampled repair, with removed and retained error energies |
| `RH/QSquarefreeHeadRepair.lean` | Actual physical Q observations and uniform directional bound to closure, capacity, and RH |
| `RH/QSquarefreeHeadRank.lean` | Actual four-site relation, failure of arbitrary interpolation, and dependence of projected head rows |
| `RH/QSquarefreeHeadFrame.lean` | Probability-normalized frame provider, complete candidate energy at most `1/c`, and its conditional RH consequence |

## 2. Why literal full row rank cannot be assumed

Write `S` for the algebraic squarefree legal span, with
`g_d(n)=(n mod d)/d`, squarefree `d>=2`. The existing square-jump theorem implies

\[
F(4)-F(3)=F(2)-F(1)\qquad(F\in S).
\]

Thus the four physical rows satisfy `row 1 - row 2 - row 3 + row 4 = 0`.
This persists under arbitrary finite legal changes of dictionary. In
particular, the complete projected-head Gram is singular for every `M>=4`.
The constant head satisfies the same relation, so this does not obstruct it.

The new declaration `not_independent_projected_heads` makes the applicability
issue explicit. It does not refute the agenda's conditional full-rank theorem;
it shows why that branch is unsuitable for the literal squarefree heads.

The repository already supplies forced low-conductor Möbius coefficients,
one-large-conductor feasible baselines, the exhaustive affine feasible span,
and complete affine minima in `QResidueHeadSpace` and `QSquarefreeAffineHead`.
These are prior results, not new arithmetic bounds from this continuation.

An alternative ordinary-mathematical implementation is to compress the heads
to `F(1)` and `Delta F(s)-F(1)` at squarefree `2<=s<=M`. A dictionary containing
all these squarefree conductors and one squarefree conductor above `M` has
maximal head rank equal to the number of squarefree integers in `[1,M]`.
The corresponding divisor-incidence block is triangular. This compression
observation is not newly formalized here, and it does not bound the complete
energy.

## 3. Rank-free HEAD and REPAIR

For any finite family of Hilbert observation vectors `v_i`, let

\[
U_d=\sum_i d_i v_i,\qquad W_{ij}=\langle v_i,v_j\rangle.
\]

If the normal equations `W d=b` hold, then

\[
\|U_d\|^2=d^Tb,
\qquad
\|Y\|^2=d^Tb+\|Y-U_d\|^2
\]

for every feasible `Y`, meaning `inner(v_i,Y)=b_i`. This gives the attained
minimum and uniqueness of the minimizing Hilbert vector even when the
multiplier is not unique. Feasibility implies existence of a normal solution;
more generally it is enough that every synthesis null relation annihilate `b`.

For `B>=0`, the new `bounded_normal_iff_directional` proves the exact equivalence

\[
\exists d:\ Wd=b,\quad \|U_d\|^2\le B
\quad\Longleftrightarrow\quad
\forall y:\ (y^Tb)^2\le B\,y^TWy.
\]

The right side forces compatibility on `ker W`, so no hidden rank or separate
feasibility assumption remains. No pseudoinverse API is needed in Lean.

Now let `V` be an independent finite legal dictionary span, `P_V` its actual
complete-norm projection, and `h_n` the Riesz vector of physical evaluation.
Put `q_n=P_V h_n`, `p=P_V 1`, `delta=||1-p||^2`, and `r_n=1-p(n)`.
For `W d=r`, `u=sum d_n q_n` gives the legal exact-head vector `F*=p+u` and

\[
\boxed{\|1-F^*\|^2=\delta+d^Tr.}
\]

Every feasible legal `F` satisfies the stronger exact completion

\[
\|1-F\|^2=\delta+d^Tr+\|F-F^*\|^2.
\]

In conventional matrix notation `W=C G^{-1} C^T`, with the complete Gram `G`.
The cost may be written `r^T W^dagger r` when feasible; the formal statements
use normal-equation witnesses instead of asserting an inverse of singular W.

## 4. The exact actual-Q arithmetic provider

The implemented observations are `qSiteRiesz(n)` for positive `n`, whose
pairing is the literal `qSequence` coordinate. Coordinate zero is excluded.
All norms are the complete norms under `Q(n)=1/(zeta(2)n^2)`.

For legal finite dictionaries `V_M`, define the projected rows and defects
above. The remaining provider is

\[
\boxed{\exists B\ge0\quad\forall M\ \forall y\in\mathbb R^M:
       (y^Tr_M)^2\le B\,y^TW_My.}
\]

`closure_capacity_rh_of_uniform_directional_repairs` converts this provider
to legal exact heads with complete residual energy at most `1+B`, then to
squarefree closure, divergence of the existing squarefree capacity, and
Mathlib's `RiemannHypothesis`. The Gram system's solvability is derived.

**Open:** the uniform directional estimate for the actual legal dictionaries.
It is the original uniform repair problem in an exact useful dual form, not
a proof that the arithmetic difficulty has disappeared. No claim is made
that RH implies this particular squarefree closure.

## 5. Sampling cannot lower the constrained arithmetic minimum

Let the exact baseline be `p=P_V 1`, and let a sampled legal baseline be
`p+e`. Let `u_0` be the minimum repair of `p`, and `u` the minimum repair of
`p+e`, both represented by projected observation rows. Set `k=e+u-u_0`.
The normal equations give the exact identities

\[
\|e\|^2=\|k\|^2+\|u-u_0\|^2,
\qquad
\boxed{\|1-(p+e+u)\|^2=\delta+\|u_0\|^2+\|k\|^2.}
\]

Thus exact repair does not amplify sampling error. Arbitrarily accurate
stagewise zero sampling can remove the last term, but cannot remove the
deterministic floor `delta+||u_0||^2`.

For a signal error `epsilon`, set `A=G^{-1}` and
`K=A-A C^T W^dagger C A`. The matrix version is

\[
\|1-F_{\rm repaired}\|^2
  =\delta+r^TW^\dagger r+\epsilon^TK\epsilon,
\quad 0\le K\le A.
\]

The abstract Hilbert identities and their projection specialization are
formalized. The displayed pseudoinverse notation is an explanatory translation.
For any Landau/ordinate split retain
`epsilon_L^T K epsilon_L + 2 epsilon_L^T K d + d^T K d`.
For an arbitrary correction, the baseline/correction cross term must remain
until the exact normal equations justify its elimination.

The existing integrated-packet zero signal is naturally `ell_P=Lambda` in
the Pareto norm. It is not `ell_Q` by definition. A zero-based argument may
perform this generic repair in P and transfer the same function's full norm
to Q. It must not identify the P and Q projection vectors or Gram matrices.

## 6. Weighted frame criterion and complementary covariance

The physical coordinate Gram is `D=diag(1/Q(n))`. Probe Pythagoras yields

\[
\operatorname{Gram}((I-P_V)h_n)=D-W,
\qquad
|y^Tr|^2\le\delta\,y^T(D-W)y.
\]

The generic exact identity and inequality are implemented with signed probe
synthesis. The matrix identification uses the actual coordinate Riesz vectors.
This inequality alone is insufficient: a comparison with W remains necessary.
In fact `D-W<=K W` on all physical directions is impossible because W has
structural null vectors while D is positive definite.

Put `H=D^{-1/2} W D^{-1/2}`. Its nonzero spectrum belongs to `[0,1]`.
On the row span, a uniform lower frame estimate with constant `c>0` is

\[
c\|u\|_Q^2\le\sum_{n\le M}Q(n)|u(n)|^2
\qquad(u\in\operatorname{span}\{P_Vh_n:n\le M\}).
\]

For a feasible constant head, the minimum vector has right side
`sum_{n<=M} Q(n)<=1`, giving complete energy at most `1/c`, not `M/c`.
`QSquarefreeHeadFrame` formalizes the probability-mass bound, the finite
construction, and the resulting conditional RH implication.

**Open:** this frame estimate, with a constant independent of M, for a
specified arithmetical dictionary family. For fixed dictionaries it controls
all compatible sources and is stronger than target-only control. With freely
chosen dictionaries it is not a weaker existential criterion than UB: the
one-dimensional spans of bounded exact-head candidates already furnish it
for positive head lengths.

A further ordinary spectral consequence, not separately Lean-formalized, is
`repair_cost <= delta*(1/lambda_plus - 1)`, where `lambda_plus` is the least
positive eigenvalue of H and the source is nonzero and feasible. It follows
by restricting the complementary inequality to `range H`. A shrinking
projection deficit can therefore compensate for deteriorating conditioning.
No current input bounds this product uniformly.

## 7. What second-order information would actually suffice

An ordinary probabilistic sufficient provider is a random physical defect
`D_M(t)` with mean `r_M` and an uncentered second-moment estimate

\[
\mathbb E[(y^TD_M)^2]\le B\,y^TW_My\quad\text{for every }M,y.
\]

Jensen then supplies the directional provider. The exact decomposition is
`E[D_M D_M^T]=r_M r_M^T+Cov(D_M)`. Centered variance alone cannot control
the mean defect: adding a deterministic vector leaves covariance unchanged.
This bridge is described mathematically, not claimed as a new Lean result.

Maples--Rodgers, Lemma 3.3, gives unconditional averaged transfer between
complex-zero and ordinate statistics for fixed smoothed tests. At second
order their Fourier bump permits physical bandwidth below `log(T)/16`.
This goes beyond the scalar displacement bound's sufficient growing band.
The constants depend on the tests; no uniform actual-head metric estimate
for the required growing test family follows from that statement alone.
Source: <https://arxiv.org/html/1404.3080v2>, Lemmas 3.1 and 3.3.

The unconditional pair form of Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh
retains real parts of zeros. It does not identify the physical head Gram or
prove ordinary unrestricted sine-kernel statistics.
Source: <https://arxiv.org/abs/2306.04799>, Theorem 1.

## 8. Next steps and explicit obligations

1. Fix a feasible arithmetical dictionary schedule using the existing affine
   squarefree-head modules. Estimate its target-direction cost, its weighted
   frame constant, or the deficit/positive-spectrum product.
2. Keep complete infinite energies. Numerical experiments require exact
   periodic formulas or a certified infinite-tail upper bound.
3. If using zeros, construct the actual map to physical defects and retain
   means, signed covariance, boundary terms, and the P/Q change of law.
4. Quantify fixed-test analytic bounds uniformly over that identified family.
5. The Selberg density provider remains a formalization obligation for known
   unconditional mathematics. Providing it would not settle the uniform
   physical-head bound.

No RH premise, simplicity premise, independent-zero-phase model, global
multiplicity bound, project-local axiom, or proof placeholder is introduced
by the new finite reductions. The unresolved arithmetic providers are
explicit hypotheses, and the RH conclusions are conditional research reductions.
