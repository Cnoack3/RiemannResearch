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
belongs to the finite legal span. If K_N tends to infinity, its damped image
still converges strongly to D1. Thus changing the single cutoff cannot
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
| `PrimorialCutoff.lean` | `primorial_cutoff_damped_tendsto` | Strong convergence to D1 for cofinal cutoffs |
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
