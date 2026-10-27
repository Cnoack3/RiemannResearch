# Dyadic resampling and stretched exponential moments

26 October 2026. Continuation of the attached PrimeResamplingFormalization20261027(1).md.

## Outcome and precise scope

This continuation proves new exact identities and sufficient RH criteria for the
actual inverse-square law and actual squarefree projection. It does not establish
the remaining arithmetic estimate and does not prove RH unconditionally.

Let
$$
Q(n)=\frac1{\zeta(2)n^2},\qquad
V=\overline{\operatorname{span}}\{g_d:d\ge2\text{ squarefree}\},\qquad
r=1-P_V1.
$$
The zero coordinate has zero weight. Put $e=\|r\|_Q^2$,
$b=P_VBr$, and $Bf(n)=f(n)/(n+1)$. Let $r_N=1-P_N1$ and
$b_N=P_NBr_N$ for the canonical nested stages.

All RH consumers conclude Mathlib's RiemannHypothesis via the existing
squarefree-density bridge. No RH-to-squarefree-density converse is asserted.

## Exact actual dyadic decomposition

The actual prime-two resampling is
$$
(C_2f)(n)=\frac34\sum_{k\ge0}4^{-k}f(n_{\perp2}2^k),\qquad n>0.
$$
Its formula, absolute convergence, and orthogonal-projection interpretation were
already verified in the previous development.

With $h=g_2-\frac38 1$ and $d=r-C_2r$, the arithmetic normalization and new
exact identities are
$$
C_2g_2=\frac38 1,\qquad \|h\|_Q^2=\frac3{64},\qquad
\langle d,h\rangle_Q=-\frac38 e,
$$
$$
\boxed{\|d\|_Q^2=3e^2+\|d+8eh\|_Q^2},
$$
$$
\boxed{e=4e^2+\|d+8eh\|_Q^2+\|C_2r-e1\|_Q^2}.
$$
Both norm-square remainders are retained. In particular,
$$
C_2r=r
\iff (\forall n,\ r(2n)=r(n))
\iff r=0.
$$
Also $r_N-C_2r_N\to r-C_2r$ in Q norm, and convergence of these defects
to zero is equivalent to zero limiting residual.

The reusable abstract exact identities extend
Analysis/ProjectionAveragingDefect.lean. The actual variance is proved in
RH/QPrimeProjectionSharpness.lean; the application is in
[QSquarefreeDyadicResampling.lean](QSquarefreeDyadicResampling.lean).

Principal declarations in RH.QSquarefreeDyadicResampling:

- limiting_defect_energy_exact
- limiting_residual_energy_exact
- limiting_dilation_invariant_iff_residual_zero
- riemannHypothesis_of_limiting_dilation_invariant
- stageDefect_tendsto_zero_iff

## Every positive stretched exponential moment detects zero residual

For every fixed $\alpha>0$ and $\kappa>0$:
$$
\boxed{\mathbb E_Q\exp(\kappa|b(X)|^\alpha)<\infty\iff r=0}.
$$
Thus even arbitrarily small positive stretch exponents suffice.
The expectation here is the extended nonnegative expectation. Lean states its
finiteness as Summable of the nonnegative weighted terms; no divergent
real-valued infinite sum is interpreted as infinity.

The reusable proof has two steps:
1. A finite exponential moment of a physical sequence gives a logarithmic
   pointwise envelope, because every positive integer has positive Q mass.
2. Applying that estimate to $|b|^\alpha$, choose an integer $m$ with
   $\alpha m\ge1$. This gives $|b(n)|\le D(6+\log n)^m$.

The existing complete-tail estimate and logarithmic residual-tail dichotomy
then force $r=0$. The finite moment remains an Open arithmetic obligation.

Files:

- [QExponentialMoment.lean](QExponentialMoment.lean): general sequence envelope,
  stretched-exponential-to-polylogarithmic envelope, bounded-vector moments.
- [QSquarefreeExponentialMoment.lean](QSquarefreeExponentialMoment.lean):
  actual correction equivalences and RH consumers.

Principal declarations in RH.QSquarefreeExponentialMoment:

- correction_stretchedExponentialMoment_summable_iff_residual_zero
- riemannHypothesis_of_correction_stretchedExponentialMoment_summable

## Finite tests and the exact uniformity gap

For every fixed $\kappa>0$, the ordinary exponential criterion has the
finite-test form
$$
r=0\iff
\exists M\in\mathbb R\ \forall S\subset\mathbb N\text{ finite}\
\forall N_0\ \exists N\ge N_0:
\sum_{n\in S}Q(n)e^{\kappa|b_N(n)|}\le M.
$$
Only M must be common; good stages may depend on S. Necessity uses
pointwise convergence to zero and budget M=2. Sufficiency passes each finite
sum to the limit, then uses bounded partial sums of nonnegative terms.

Every individual finite-stage correction is physically bounded, so it has
every ordinary exponential moment for every real parameter. Nevertheless:
$$
\boxed{r\ne0\ \Longrightarrow\
\mathbb E_Q e^{\kappa|b_N(X)|}\longrightarrow+\infty
\quad\text{for every }\kappa>0.}
$$
This implication is unconditional for the actual canonical stages.
It does not assert a converse saying that $r=0$ gives bounded complete-stage
moments. The finite-test formulation is the established equivalence.

See [QSquarefreeStageExponentialMoment.lean](QSquarefreeStageExponentialMoment.lean),
including moving_exponentialMoment_tendsto_atTop_of_residual_ne_zero.
The finite-test equivalence is
residual_zero_iff_frequently_exponential_finiteSum_bound in
RH.QSquarefreeExponentialMoment.

## Remaining research obligations

Any one of these actual arithmetic providers would close a sufficient
implication to RH:

1. Prove $r(2n)=r(n)$ at all positive integers.
2. Prove $r_N-C_2r_N\to0$ in Q norm.
3. Prove one finite stretched exponential moment of b, or the common ordinary
   exponential finite-test budget above.
4. Prove the original handoff's common prime-energy finite-grid budget or
   finite weighted correction Dirichlet energy.

None is established here. These are zero-residual tests, not automatic
properties of orthogonal projection.

In particular, asserting $C_2V\subseteq V$ already gives the desired target:
$g_2\in V$ and $C_2g_2=\frac38 1$. Normal equations only give $r\perp V$.
For the one-atom legal space, $\widetilde r=1_{\mathrm{even}}$ and $C_2\widetilde r=1/4$,
so generic projection structure cannot force dyadic invariance.
This illustrative calculation does not refute invariance for the complete
squarefree closure. The exact two-remainder identity yields $e\le1/4$,
not $e=0$.

Further directions remain paper-level: the zeta-mixture formula, countable
dyadic near-pole moment tests, integrable covariance-growth envelopes,
and estimates using all squarefree normal equations. These were not silently
added as hypotheses discharged by Lean.

## Provenance and verification

Source: the attached user agenda and direct Hilbert/positive-series arguments
developed in this continuation. Background for the resampling/Poincare framework:
Decreusefond and Halconruy,
[Malliavin and Dirichlet structures for independent random variables](https://arxiv.org/abs/1707.07915).
That reference does not supply the missing squarefree projection estimate.

Wolfram simplified the dyadic scalar coefficients as a diagnostic, not a
formal proof input.

Verified isolated candidate jobs (all exit 0, verified true):

- job_OSCV4fdfoa77BM4jlz2_aQ6uQH0WvTct: dyadic identities and ordinary moment criterion.
- job_qZ6JaldLImWkvpNT6T4hs5wtAHWghSSD: finite stages and moment divergence.
- job_0t2SrXJh2JVFA0AqDXMJ1uW96a10E3E4: all positive stretched exponents.

Saved-module type/axiom audit job_O4gfYgUMMXDBtriLXTmlwTDv2DCc-pvM passed
with verified true and exit code 0. Its reported server verification duration
was 54.816 seconds, excluding request and polling delays. Seven principal
theorem types and five axiom dependencies were inspected; the axiom lists are
exactly propext, Classical.choice, and Quot.sound. The RH theorem types retain
their displayed arithmetic hypotheses.

The final aggregate publication checkpoint is reported in the publication
response. Only its terminal successful result certifies the published revision.

Workspace-opening request time was not separately
instrumented. Server verification durations are distinct from request,
queue, and polling delays; no unsupported cause is assigned to those delays.
