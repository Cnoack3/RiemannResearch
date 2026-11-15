# P/Q augmented density: all single-cutoff primorial lifts fail

Prepared 14 November 2026 (client date). Continuation of the published
P/Q augmented-density results at `8d46119bc3623a72c4abb5834a18c44e05f69f3d`.

## Main conclusion

RH remains open. The new result closes the entire two-parameter single-cutoff
family proposed in Priority B of the continuation, rather than only its
previously treated diagonal K=L_N.

Write Z=zeta(2), L_N=product of primes at most N, and
a_N=phi(L_N)/L_N. For every sequence of positive integers K_N, set

```math
v_{N,K_N}=a_N K_N g_{K_N}
  -\sum_{d\mid L_N}\mu(d)g_d.
```

Both complete source norms tend to infinity:

```math
\|v_{N,K_N}\|_Q\to\infty,
\qquad \|v_{N,K_N}\|_P\to\infty.
```

There is **no growth assumption on K_N** in this obstruction. Each source
belongs to the finite legal span. Its damped image converges strongly to D1
for every positive cutoff schedule; see the verified extension below. Thus changing the single cutoff cannot
repair the missing bounded-source condition.

This is a checked extension of the repository. No priority or novelty claim
relative to all mathematical literature is made.

## Exact identity and quantitative bound

For positive L and K,

```math
v_{L,K}(n)=C_L(n)-a_LK\lfloor n/K\rfloor,
\qquad a_L=\varphi(L)/L.
```

The full squared Q norm is the infinite sum of this expression squared against
Q(n)=1/(Zn^2), with the repository's zero coordinate having zero weight.

For any conductor L covering all integers 2 through 3M, with a_L M >= 4,

```math
\frac{M a_L^3}{128Z}\leq\|v_{L,K}\|_Q^2
\quad\text{for every }K\geq1.
```

In particular, for N>=3 and N a_N>=24,

```math
\boxed{\quad
\frac{N a_N^3}{768Z}\leq\|v_{N,K}\|_Q^2
\quad\text{for every }K\geq1.\quad}
```

Proof structure:

1. **Small cutoffs K<=M.** On 2M<=n<3M the covered count is exactly one.
   Since K floor(n/K)>=M, the source is at most 1-a_L M.
   Summing this entire finite block gives
   M a_L^2/(36Z)<=||v||_Q^2.
2. **Large cutoffs K>M.** Set H=floor(a_L M/2). Pair the H sites immediately
   before K with the H sites immediately after K. The count increases by at
   most H between paired sites, while the cutoff subtracts a_L K.
   The pairwise squared energy is at least (a_L K)^2/8.
   Summing the disjoint pairs gives H a_L^2/(32Z)<=||v||_Q^2.
3. The first Mertens theorem already proved in the repository yields
   log(a_N)>=-log(N)/6-C for one fixed C. Hence N a_N^3 tends to infinity.
   This arithmetic growth input is proved in Lean, not left as a hypothesis.
4. Norm equivalence transfers the divergence to P.

No infinite tail is discarded from the claimed norm: finite blocks are lower
bounds for the complete, summable squared norm.

## Consequence for a concrete Priority A provider

Define the literal finite legal approximant

```math
b_{N,K,k}=Z^{-1}g_k+(Zk)^{-1}v_{N,K}.
```

The complete signed identity is

```math
Zk\,(Bg_k-b_{N,K,k})=kDg_k-v_{N,K}.
```

For every positive K_N and every positive cofinal k_N, the scaled provider error
**tends to infinity**:

```math
k_N\|Bg_{k_N}-b_{N,K_N,k_N}\|_Q\to\infty.
```

This family therefore fails the o(1/k_N) acceptance criterion decisively.
The statement concerns these explicit approximants, not all finite legal
approximants.

A further checked theorem says: if additional corrections c_N make
v_{N,K_N}+c_N uniformly bounded, then ||c_N||_Q tends to infinity.
Consequently bounded-norm perturbations cannot rescue this family.

## Declarations

All namespaces below have prefix `RiemannResearch.RH.`.

| Module | Main declarations | Status |
|---|---|---|
| `PrimorialDensityLowerBound.lean` | `PrimorialDensity.exists_log_density_lower`, `density_cube_growth` | Unconditional arithmetic theorems |
| `PrimorialCutoff.lean` | `PrimorialCutoff.cutoffLift_mem`, `cutoffLift_sequence`, `cutoff_norm_sq_exact` | Exact finite membership and identities |
| `PrimorialCutoff.lean` | `cutoff_jump_energy`, `cutoff_small_energy`, `cutoff_uniform_energy`, `primorial_uniform_energy_explicit` | Complete norm lower bounds |
| `PrimorialCutoff.lean` | `primorial_cutoff_norms_tendsto` | Divergence for every positive cutoff sequence, in P and Q |
| `PrimorialCutoff.lean` | `primorial_cutoff_damped_tendsto` | Strong convergence to D1 for every positive cutoff schedule |
| `PrimorialCutoff.lean` | `necessary_correction_norm_tendsto` | Unavoidable divergence of corrections to bounded sources |
| `PrimorialCutoffLeakage.lean` | `PrimorialCutoffLeakage.providerApprox_mem`, `provider_error_identity`, `provider_error_norm_identity` | Exact finite provider and signed error |
| `PrimorialCutoffLeakage.lean` | `primorial_provider_scaled_error_tendsto` | Scaled error diverges for this provider family |

The existing `PQNormalizedLeakage.riemannHypothesis_of_finite_approximation_provider`
is preserved unchanged. Its unrestricted arithmetic provider remains open.

## Literature investigation

The following primary sources were inspected.

- Luis Baez-Duarte, *A strengthening of the Nyman-Beurling criterion for the
  Riemann Hypothesis, 2* (2002), https://arxiv.org/abs/math/0205003.
  Its constructive shifted-Mobius approximation uses RH to establish closure
  membership. Pointwise convergence and the functional-equation estimate
  cannot be substituted for that step.
- Michel Balazard and Anne de Roton, *Sur un critere de Baez-Duarte pour
  l'hypothese de Riemann* (2008/2010),
  https://arxiv.org/abs/0812.1689. Their quantitative distance upper bound is
  explicitly under RH.
- Sandro Bettin, J. Brian Conrey and David W. Farmer, *An optimal choice of
  Dirichlet polynomials for the Nyman-Beurling criterion* (2012),
  https://arxiv.org/abs/1211.5191. The optimal asymptotic for the smoothed
  Mobius choice assumes RH and an inverse-zeta-derivative moment bound.
- Jean-Francois Burnol, *A lower bound in an approximation problem involving
  the zeros of the Riemann zeta function* (2001/2002),
  https://arxiv.org/abs/math/0103058. The unconditional distance lower bound
  is consistent with slow convergence of genuine optimizers; it does not
  provide the missing upper bound.
- Leo Goldmakher, *A quick proof of Mertens' theorem*,
  https://web.williams.edu/Mathematics/lg5/mertens.pdf.
  This supports the elementary Mertens input already formally available.
- Harold G. Diamond and Janos Pintz, *Oscillation of Mertens' product formula*
  (2009), https://www.numdam.org/article/JTNB_2009__21_3_523_0.pdf.
  The classical a_N log N -> exp(-gamma) gives the stronger informal rate
  ||v||_Q^2 >> N/(log N)^3 from the checked finite inequality.
  That rate is an external corollary here: the new Lean code uses the weaker,
  completely checked logarithmic lower bound instead.

These results motivate smoothing, but none supplies an unconditional
o(1/k) provider. Their continuous Hilbert-space formulations also require
the appropriate transfer before use in this discrete Q model.

## Wolfram exploration

Wolfram Language computed partial Q source energies through n=4N, minimizing
over 1<=K<=2N. These are exploratory finite sums, not complete-norm estimates
or formal certificates.

| N | a_N (approx.) | Minimizing tested K | Minimum tested partial squared norm |
|---:|---:|---:|---:|
| 10 | 0.22857143 | 1 | 0.45460780 |
| 30 | 0.15794722 | 1 | 0.74426447 |
| 100 | 0.12031729 | 109 | 1.18166261 |
| 300 | 0.09745855 | 347 | 1.41430234 |

The proof does not depend on these computations.

## Remaining RH work

The single-cutoff family is eliminated. Signed multiscale combinations and
different finite legal approximants remain possible. For any proposed
combination, derive the complete signed Gram energy, including all cross
terms, before estimating it. The present correction theorem means that a
bounded final source requires cancellation between components of diverging
norm; a triangle-inequality estimate on their separate norms cannot certify
that cancellation.

The acceptance criteria remain:
- actual finite legal b_j at every stage;
- cofinal conductors k_j;
- complete error k_j ||B g_(k_j)-b_j||_Q -> 0;
or actual finite legal sources w_j with one common norm bound and
D w_j -> D1.

No density invariance, vanishing residual, RH, or unproved arithmetic
hypothesis was inserted into the new unconditional obstruction.

## Verification record

The core obstruction, its arithmetic growth lemma, both norm divergences,
the cofinal damped convergence, the explicit bound, and the correction
theorem passed a queued Bazel snippet check:

- Job: `job_u3mUQYo6aeuXBS9SYz3MPQ27KFwvUuMO`.
- Result: `verified=true`; server job elapsed 81.514 seconds.
- BuildBuddy: https://app.buildbuddy.io/invocation/d85d0016-7988-4a11-8b8b-f49ebb6e0710.

The permanent modules, including the provider corollary, were compiled as
imports of the successful guarded audit:

- Job: `job_WXx4Vy4-TvPIKwKVgO3t4HL12WimajcF`.
- Result: `verified=true`; server job elapsed 57.626 seconds.
- BuildBuddy: https://app.buildbuddy.io/invocation/ccf1e956-b16a-472c-bb57-432f1665b127.
- Eleven named declarations were guarded to depend only on
  `[propext, Classical.choice, Quot.sound]`.
- The exact theorem types expose the elementary positivity and cofinality
  conditions; the source-divergence theorem has no RH or arithmetic-provider
  hypothesis.

Publication uses the mandatory managed Bazel/BuildBuddy checkpoint for the
complete target `//:RiemannResearch`, including downstream consumers and
all project packages. The final publishing receipt supplies its job ID and
exact commit; a failed checkpoint blocks publication.

Retained workspace token:
`ws_7DCmDIw7bhSfWmPzfDKzqxTUy7PpbbYr`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_7DCmDIw7bhSfWmPzfDKzqxTUy7PpbbYr/RiemannResearch`.
This is a Lean-server path, not a local attachment path.


## Compactness review and coefficient extension — 14 November 2026

This continuation starts from published commit
13df1e0c895794f6cecde835a577c6f96f5ec253. The all-cutoff source-divergence
theorem above was already present there. The user reviewed this extension
and authorized committing and publishing it on 14 November 2026.

### Stronger damped convergence

The revised primorial_cutoff_damped_tendsto removes its cofinality hypothesis.
For every positive cutoff schedule K_N, including constant and oscillating
schedules, D v_(N,K_N) converges strongly in Q to D1. The new finite estimates
retain the exact sieve density:

\[
 \|D v_{L,K}-D1\|_Q
 \le \delta_L \sqrt{T_Q(K-1)}+\sqrt{T_Q(N)}
 \le \delta_L+\sqrt{T_Q(N)}.
\]

Here L covers 2 through N and T_Q(M) is the complete Q mass on n>M.
The first term's coefficient was previously bounded by 1. Keeping delta_L
makes the convergence uniform over all positive K. The proof uses the
existing elementary finite-prime-product decay and summable Q tails.

New declarations in PrimorialCutoff:
cutoffLift_damped_error, q_tailMass_le_one,
cutoffLift_damped_error_uniform, scalar_tendsto_zero_of_bounded,
bounded_rescaling_damped_tendsto_zero.

If t_N v_(N,K_N) has uniformly bounded Q norm, then t_N tends to zero,
and D(t_N v_(N,K_N)) tends to zero. Scalar normalization therefore loses D1.
The same boundedness obstruction holds in P by the existing norm equivalence.

### Arbitrarily chosen correcting coefficients

New module: RH/PrimorialCoefficientObstruction.lean.

Define the finite legal vector

\[
 F_{L,K,a}=a g_K-\sum_{d\mid L}\mu(d)g_d,
 \qquad a\in\mathbb R.
\]

The exact physical sequence is C_L(n)-delta_L n+a g_K(n).
For a positive multiple H of K, while both sites lie in the covered head,

\[
 F_{L,K,a}(n+H)-F_{L,K,a}(n)=-\delta_L H.
\]

Thus the arbitrary coefficient cancels exactly. Pair the H sites in [H,2H)
with [2H,3H); summing
(x^2+y^2)>=(x-y)^2/2 against a lower bound for the actual Q weights gives

\[
 \frac{H\delta_L^2}{18\zeta(2)}
 \le \|F_{L,K,a}\|_Q^2.
\]

Taking H=K floor(M/K), with 1<=K<=M, gives H>=M/2 and therefore

\[
 \boxed{\frac{M\delta_L^2}{36\zeta(2)}
 \le \|F_{L,K,a}\|_Q^2}
 \qquad\text{for every }a\in\mathbb R.
\]

Only positivity, K<=M, and coverage through 3M are needed; there is no
delta_L M>=2 assumption. All norms include the entire infinite tail.

For L_N=primorial N, arbitrary real coefficients a_N, and every positive
schedule eventually satisfying K_N<=floor(N/3), the squared Q source norms
tend to infinity. The existing growth of floor(N/3) delta_N^3, together
with 0<delta_N<=1, discharges the arithmetic growth input. No RH premise
occurs in this theorem.

Central declarations:
coefficientLift_eq, coefficientLift_mem, coefficientLift_sequence,
coefficientLift_head_difference, coefficientLift_block_energy,
coefficientLift_small_energy, coefficientLift_small_norm_sq_tendsto.

This does not exclude freely chosen coefficients with large cutoffs, or
several signed correction residues. The existing all-cutoff divergence
theorem concerns the prescribed coefficient a_N=delta_N K_N.

### Which replacement actually supports compactness?

| Construction | Source bound | Actual limit or remaining condition |
|---|---|---|
| Original diagonal primorial lift | Diverges in P and Q | D-image tends to D1 |
| Prescribed-coefficient single cutoff, arbitrary positive K_N | Diverges in P and Q | D-image tends to D1 without cofinality |
| Freely chosen coefficient, K_N<=floor(N/3) eventually | Complete squared Q norm diverges | Optimizing this coefficient cannot repair boundedness |
| Uniformly bounded scalar rescaling of the prescribed family | Bounded by assumption | D-image tends to 0 |
| Full finite Q projection p_N of 1 | Norm at most 1, unconditionally | Strong limit is projection of 1 onto V |
| Optimal exact-head vectors in closed V | Uniform energy bound remains Open | Existing QOptimalExactHead identifies this bound with 1 in V |
| Several signed legal corrections or Tikhonov minimizers | No new uniform bound established | Must prove full signed cost control and the correct target |

QFiniteBoundedLift already proves that existence of any uniformly bounded
finite legal D-lift to D1 is equivalent to existence of finite legal
unit-ball vectors converging strongly to 1. The canonical full inverse-Gram
candidates have norm at most 1; their D-images converge to D1 if and only if
1 belongs to V. QReciprocalTargetLift proves that this membership implies RH.

The exact projection coefficients are G_N^{-1} b_N, with the complete Q Gram
matrix and b_i=<g_i,1>_Q. Their unconditional limit is P_V 1, not a
proved identification with 1. A bounded trial found by source-norm
minimization alone is not evidence that its target has been preserved.

For a feasible finite-conductor exact-head system A c=1 and positive-definite
complete source Gram matrix G, the minimum-energy coefficients are
G^{-1} A^T (A G^{-1} A^T)^{-1} 1. This formula requires full row rank of A.
It is a linear-algebra candidate, not a new uniform arithmetic estimate.


For several signed correction residues, write s=-sum_(d|L) mu(d)g_d and
r=sum_i c_i g_(K_i). With complete Gram matrix G_ij=<g_(K_i),g_(K_j)>_Q
and b_i=<g_(K_i),s>_Q, the exact energy is

\[
 \|s+r\|_Q^2=\|s\|_Q^2+2b^\top c+c^\top Gc.
\]

When G is invertible, the unconstrained energy minimizer is c=-G^{-1}b,
with minimum ||s||^2-b^T G^{-1}b. This does not constrain the damped target;
if the correction span includes s, it can simply cancel the source to zero.
A useful optimization must retain the target error or exact-head constraints.

For Tikhonov cost ||D(f-1)||_Q^2+lambda||f||_Q^2, a bound C lambda along
lambda down to zero supplies both a uniform source bound and the correct
damped limit. This is the existing conditional theorem
QReciprocalTargetLift.riemannHypothesis_of_regularized_D_cost.
Minimizer existence alone does not give C independent of lambda.

### Weaker topologies

A norm-closed linear subspace of a Hilbert space is weakly closed.
Consequently Hilbert weak convergence, or weak-star convergence after Riesz
identification, preserves the same legal closure and cannot bypass the source
norm obstruction. Closed norm balls support weak compactness, but proving
membership of the correct weak limit remains necessary.

The topology defined by ||Df||_Q is strictly weaker: it is physical
square summability with weights 1/(zeta(2)n^4). The displayed sieve already
converges to 1 in that topology. Pointwise convergence likewise loses
complete-source energy control. Neither establishes 1 in the original
P/Q legal closure.

For the unrestricted legal approximation problem, the precise dichotomy
remains: if 1 is outside V, every legal sequence with D-image tending to D1
has source norm tending to infinity; if 1 lies in V, the canonical finite
projections are bounded strong approximants. The present work proves
family-specific obstructions, not nonmembership of 1 in V.

### Complete-energy Wolfram checks

For an L-periodic source f with K dividing L, Wolfram evaluated the complete
Q energy via the convergent residue-class identity

\[
 \|f\|_Q^2 =
 \frac{1}{\zeta(2)L^2}\sum_{r=1}^L f(r)^2\psi_1(r/L).
\]

These are numerical evaluations of an exact infinite-tail formula, not
kernel certificates or asymptotic evidence.

| N | L_N | Diagonal K=L_N | Prescribed coefficient, K=2 | Minimum over a at K=2 |
|---:|---:|---:|---:|---:|
| 3 | 6 | 1.081644 | 0.680354 | 0.059668 |
| 5 | 30 | 2.304360 | 0.684076 | 0.104850 |
| 7 | 210 | 9.137701 | 0.716903 | 0.159601 |
| 11 | 2310 | 77.254995 | 0.744395 | 0.195550 |

Every displayed quantity is source energy, not error to 1. In particular the
smallest entries do not by themselves retain the desired target. The new
theorem proves eventual divergence for arbitrary coefficient choices at
fixed K=2, despite these small finite values.

The literature review additionally checked Baez-Duarte's
A strengthening of the Nyman-Beurling criterion (arXiv:math/0202141),
A divergent Vasyunin correction (arXiv:math/0506318), and Bettin-Conrey-Farmer
(arXiv:1211.5191). The last paper's logarithmically smoothed Mobius polynomial
has a sharp conditional asymptotic under RH and an inverse-zeta-derivative
moment condition. It cannot supply an unconditional bound in an RH proof.

### Review status

The permanent source modules and eight selected declarations passed the guarded
Bazel/BuildBuddy audit: job_EoqSXpb8h2b1ktqT19e0GsI5zqCBmmSb, 58.251 seconds
server job elapsed. Every guarded report contains exactly propext,
Classical.choice, and Quot.sound.
Receipt: https://app.buildbuddy.io/invocation/c85dc26b-5912-4eb2-bcf9-1fe424520a80.

The full project target //:RiemannResearch then passed in
job_Fk5jUQWwjOGQbRL6k-iSwFAY7ZTH2rRK, 191.782 seconds server job elapsed,
with backend bazel and BuildBuddy. This covers downstream consumers and the
new root export. Receipt:
https://app.buildbuddy.io/invocation/1d66c11a-2bd8-4f2e-b7fa-d5b486ab8526.

The subsequent catalog edits are documentation only. No Lean source changed
after that full-project check. Publication was authorized after review and is
performed through the managed full-project Bazel/BuildBuddy checkpoint.
The retained workspace is
ws_uapFHlU7P3G6COy0w6v5dq5dObI06leL, based on
13df1e0c895794f6cecde835a577c6f96f5ec253.
The remaining arithmetic target is still Open:
construct actual finite legal f_j with one common bound on ||f_j||_Q and
D f_j -> D1, or equivalently prove the canonical unit-ball projection
sequence preserves the target. No such provider is claimed here.
