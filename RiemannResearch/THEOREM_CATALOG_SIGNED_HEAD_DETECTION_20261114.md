# Actual signed-head detection: bounds, obstructions, and review

Date: 14 November 2026. Starting revision:
`4383b0b81dfd284c0845cd182f50a26644cb44c5`.
Retained workspace: `ws_FORguE7ZeEWRBMEHezcT0XdjWF855Bob`.

Status: user-approved for managed checkpoint publication. The structural
theorems are unconditional. A uniform arithmetic lower bound remains **Open**.
Nothing here proves RH.

## What the investigation found

The original two-coordinate certificate can lose all the observable gain.
Numerically, at M=2,3,4,8,16,32 both lower signed heads are negative, whereas
the actual dyadic gain and complete transported sources are positive.
This does not disprove an eventual bound, and the numerical specializations
are not Lean proofs.

The new unconditional replacement retains the complete sum/difference norm
identities and their nonnegative tails. It recovers either sign of each source
using longer finite heads, converges to the exact two-source square at each
fixed budget, and can be combined with the original certificate without loss.
It does not prove that either source is nonzero at every late arithmetic stage.

## Exact signed identities and the new bound

All residuals and spaces below are the existing actual two-seed Pareto objects:

\[
r_M=\mathbf 1-P_{V_M}\mathbf 1,\qquad E_M=\|r_M\|^2,
\qquad G_M=E_M-E_{2M}.
\]

For p=2,3 put B=floor(2M/p), v=D_p r_B, and

\[
A_{M,2}=2E_M-r_M(1),\qquad
A_{M,3}=3E_M-\tfrac32r_M(1)-\tfrac12r_M(2).
\]

The existing complete identities are

\[
s_{M,p}=A_{M,p}-\langle r_M,v\rangle,
\qquad \|v\|^2=pE_B.
\]

Define finite observations in the actual Pareto norm:

\[
F^\pm_{M,p,K}=\sum_{n=1}^{K}\frac{(r_M(n)\pm p r_B(\lfloor n/p\rfloor))^2}{n(n+1)},
\]

where physical coordinate zero is anchored to zero, as in the Lean definitions.
Set

\[
\ell_{M,p,K}=A_{M,p}-\frac{E_M+pE_B-F^-_{M,p,K}}2,
\qquad
u_{M,p,K}=A_{M,p}+\frac{E_M+pE_B-F^+_{M,p,K}}2.
\]

The primary new equalities, with every tail retained, are

\[
s_{M,p}=\ell_{M,p,K}+
\frac{\|r_M-v\|^2-F^-_{M,p,K}}2,
\]
\[
u_{M,p,K}=s_{M,p}+
\frac{\|r_M+v\|^2-F^+_{M,p,K}}2.
\]

Both remainder numerators are nonnegative. Consequently

\[
\ell_{M,p,K}\le s_{M,p}\le u_{M,p,K}.
\]

Let

\[
J_{M,K}=\sum_{p=2,3}\max(0,\ell_{M,p,K},-u_{M,p,K})^2,
\quad S_M=s_{M,2}^2+s_{M,3}^2,
\quad \widehat H_{M,K}=\max(H_M,J_{M,K}).
\]

The strongest new unconditional bound is

\[
H_M\le\widehat H_{M,K}\le T_M G_M,
\qquad J_{M,K}\longrightarrow S_M,
\qquad \widehat H_{M,K}\longrightarrow S_M
\quad (K\to\infty,\; M\text{ fixed}).
\]

Thus G_M >= widehat(H)/(T_M) whenever T_M>0. Also,

\[
(\exists K,\;J_{M,K}>0)\ \Longleftrightarrow\ S_M>0.
\]

This is a completeness statement for these **two transported sources**.
It is not completeness for every direction in V_(2M). The exact complete
energies E_M and E_B are inputs to the interval, so numerical use requires
their reliable evaluation as well as the finite coordinate observations.

Main declarations in `RH/CoupledResidualFiniteHead.lean`:

- `sourceMain_binary`, `sourceMain_ternary`.
- `coordinateHeadEnergy_physical`, `coordinateHeadEnergy_le`,
  `coordinateHeadEnergy_tendsto`.
- `source_lower_tail_identity`, `source_upper_tail_identity`.
- `finiteSource_interval`, `finiteSourceMagnitude_sq_le`.
- `finiteSourceSquare_le_trace_gain`, `projected_error_ge_finiteSourceSquare`.
- `combinedSourceSquare_le_trace_gain`, `combinedSourceSquare_tendsto`.
- `exists_positive_finiteSourceSquare_iff`.

## A proved obstruction for the original certificate

Lean proves, for the actual residuals,

\[
r_M(1)\ge E_M\ \text{and}\ r_M(2)\ge0
\quad\Longrightarrow\quad H_M=0.
\]

Indeed E_floor(2M/3) >= E_M, so in this cone the binary lower source is
at most (1-sqrt(2)) E_M, and the ternary lower source is at most
(3/2-sqrt(3)) E_M. Both are strictly negative because E_M>0.

If T_M>0, **no real multiplier A** can then satisfy
E_M T_M <= A H_M. Therefore a positive original certificate must leave
this cone: r_M(1)<E_M or r_M(2)<0.

Declarations:
- `headSourceSquare_eq_zero_of_head_cone`.
- `head_cone_escape_of_positive_certificate`.
- `head_certificate_impossible_in_cone`.

Cone membership for all large M is not asserted. The numerical cases M=3,4
have substantial margins, but no theorem evaluating these particular
inverse-Gram projections is supplied by the Lean module.

## Reproducible arithmetic experiments

The separately retained [`coupled_residual_head_probe.py`](https://chatgpt.com/library?file_id=libfile_fde3_f-b623776613f88191b633267ac259960d_b4363c4030c88191b769fe4d9fd2e85e&account_id=personal)
uses the canonical independent family
g_(p,m)(n)=m(floor(n/m) mod p), retaining all ternary generators and binary
generators with 3 not dividing m. This is exactly the spanning family in
`TwoThreeHilbertBudget.lean`, of dimension 2M-floor(M/3).

For a pair of generator periods, L=lcm(pm,qk), the complete weighted pairing
is evaluated over one finite period with

\[
w_L(a)=\sum_{j\ge0}\frac1{(a+jL)(a+jL+1)}
=\frac{\psi((a+1)/L)-\psi(a/L)}{L},\qquad 1\le a\le L.
\]

The normal equations use these complete weights; an infinite Hilbert inner
product is not replaced by a truncated sum. Floating-point evaluation of
the digamma function and linear solve is still numerical, not certified
interval arithmetic. The table is evidence for testing strategies only.

| M | E_M | G_M | binary lower / E_M | ternary lower / E_M | original H_M | K tested | J_(M,K)/T_M |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 0.06061486918 | 0.009565399896 | -0.50507027 | -0.58629104 | 0 | 32 | 0.00040485547 |
| 3 | 0.05256509327 | 0.008290189291 | -0.85340665 | -1.25065630 | 0 | 128 | 0.00015041965 |
| 4 | 0.05104946929 | 0.009672408520 | -0.91062650 | -1.47461819 | 0 | 128 | 0.00000143723 |
| 8 | 0.04137706077 | 0.006629652651 | -0.76288559 | -1.20940852 | 0 | 512 | 0.00000565719 |
| 16 | 0.03474740812 | 0.002377874409 | -0.78776369 | -1.25937231 | 0 | 2048 | 0.00000856610 |
| 32 | 0.03236953371 | 0.003320235219 | -0.76246471 | -1.16742844 | 0 | 2048 | 0.00000519602 |

Independent 60-digit mpmath recalculations of energies and the first two
residual coordinates at M=2,3,4 agreed with the double-precision results to
within 3.54e-16. This cross-check does not promote them to Lean-verified
specializations. No universal sign or rate is inferred from this table.

Reproduce with numpy, scipy, and mpmath installed:

```sh
OPENBLAS_NUM_THREADS=1 python coupled_residual_head_probe.py --mp-check 2 3 4
```

## Finite-dimensional countermodels

`Analysis/ResidualProjectionObstruction.lean` uses Euclidean R^3, the old
space {0}, and its strict enlargement span(e_0,e_1).

1. The two correction columns have identity Gram matrix, but residual e_2
   has norm one, zero source vector, and zero projection gain.
2. For residual epsilon e_0+e_2 the squared residual norm is 1+epsilon^2
   and the gain is epsilon^2. Every c>0 admits a strictly positive gain
   smaller than c times the residual energy.
3. In the full correction space R^3, the same two observed source columns
   both miss residual e_2 although the actual projection gain is one.

Declarations: `plane_strict_enlargement`, `identity_gram_zero_gain`,
`target_energy`, `target_gain`, `arbitrarily_small_positive_relative_gain`,
and `identity_gram_blind_positive_gain`.

These reject arguments using only dimension, independent correction columns,
well-conditioned Gram matrices, or positivity of total residual energy.
They are not counterexamples to the arithmetic projection conjecture.

## Prime/zero spaces, CRT, and published estimates

The current `QFullPrimeZeroResidual.lean` is inspected at the stated base SHA.
`fockResidual_norm` is an isometry, not a lower bound for a particular source
or a sign theorem. `sampled_cancellation_iff_residual_zero` explicitly retains
a positive `UniformSelbergDensity a` input and the sampled-cancellation target.
`exists_cofinal_sampling_RH_test` constructs sampling heights but still needs
the actual sampled residual energy to vanish. These are full-conductor Q
residuals, whereas the present sources use two-seed Pareto projections;
their numerical or signed estimates cannot simply be identified.

`ActualResidualSampling.sampledEnergy_signed_identity` retains its complete
signed prime-power form and literal remainder. Neither its diagonal term
nor a stronger admissible density exponent removes the required cancellation.
The context is Ford--Meng--Zaharescu, *Simultaneous distribution of fractional
parts of Riemann zeta zeros*, Bull. LMS 49 (2017), 1-9:
https://arxiv.org/abs/1511.06814 . This reference supplies sampling context,
not a residual-specific source lower bound.

The finite CRT and canonical-basis results provide exact compatibility,
periods, and finite independence. The categorical CRT energy catalog itself
retains target-specific reconstruction cost as Open. Such finite structure
does not supply a common bound on the alignment with the actual residual;
the Euclidean countermodels isolate this gap even with identity Gram.

Bettin--Conrey--Farmer's logarithmic Nyman--Beurling approximation result
assumes RH and a negative moment bound on zeta derivatives at zeros:
https://arxiv.org/abs/1211.5191 . It cannot be used as an unconditional input
here. Its error asymptotic is also not, by itself, a stagewise gain estimate.

## Precise remaining arithmetic obligation

A sufficient route using the new certificate is to establish constants
C>0 and M_0, specified scales L_M>1, and for **every** M>=M_0 a finite K_M,
with

\[
T_M>0,\qquad E_M T_M\le C\log(L_M)\,\widehat H_{M,K_M}.
\]

Alternatively, prove the corresponding lower gain for the entire correctly
specified enlarged correction space, without restricting to these two probes.
An eventual quantitative bound for S_M itself with enough strict margin can
be transferred to a finite head by the proved fixed-M convergence, but
neither that bound nor a uniform quantitative cutoff is supplied here.

To use a residual-exhaustion/RH consumer one must additionally use its actual
projection sequence and verify the nonsummability of its relative-gain
schedule. Cofinality of L_M alone does not give that nonsummability.
The new results prove no such arithmetic provider, sampled cancellation,
residual exhaustion, or RH unconditionally.

## Verification and proposed changes

The two saved modules passed Bazel/BuildBuddy import verification:
`job_5hZzRseC8Plo9wvkipwJTKXOZA_lXrLz`, 66.713 server seconds.
Receipt: https://app.buildbuddy.io/invocation/f3b7b8c1-e647-4893-9ecf-817cdac06971 .

The guarded principal axiom audit and complete project build are recorded
after their terminal results below. A full project build validates the retained
workspace, not a future integration with newer main. Publication requires a
separate approved checkpoint and any required integrated-source verification.

Proposed changes:
- Add `RH/CoupledResidualFiniteHead.lean`.
- Add `Analysis/ResidualProjectionObstruction.lean`.
- Export both modules from `RiemannResearch.lean`.
- Add this catalog; the reproducible numerical script is retained separately.
- Link this continuation from the original residual-projection catalog.

The user explicitly approved committing and pushing these five files after
review. Publication is gated by the server checkpoint's source audit and
full-project verification.


## Final acceptance before approval

- Complete final Lean source, including both exports: Bazel/BuildBuddy
  `//:RiemannResearch`, terminal success.
- Job: `job_A7B5uRma0oK8aJHT9UdspYU0OqxxZKer`.
- Server-reported full-project build time: 174.068 seconds.
- Receipt: https://app.buildbuddy.io/invocation/696dae30-efa2-4361-a983-905d2bf49d8a .
- Nine guarded principal axiom inventories passed in
  `job_9GsMmaGKjBPM1YUSOCeniTNsNABUjuWv` (20.765 server seconds).
  Each list is exactly `[propext, Classical.choice, Quot.sound]`.
- Axiom receipt: https://app.buildbuddy.io/invocation/444709c2-6d8a-4539-8832-d9dc9862cbff .
- 39 public theorems added: 27 in the actual residual module and 12 in the
  finite-dimensional obstruction module. No proof placeholders or new axioms.
- Five proposed repository files: two new Lean modules, their root exports,
  the new catalog, and the pointer in the original catalog. The computation
  script is a separate retained deliverable.
- No commit or publication occurred. This receipt validates the current
  retained workspace; later integration must pass the approved checkpoint.
