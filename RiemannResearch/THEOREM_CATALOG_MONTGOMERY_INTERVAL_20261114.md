# Montgomery interval averages: exact signed and countable criteria

Date: 2026-11-14. Development baseline: caaf1ebef26a4adb671940f2209f01c976e60931.

## Result and boundary

This development does **not** prove Montgomery's pair correlation conjecture
(PCC) or RH. It proves exact identities, the unconditional actual zero-count
normalization, and equivalent formulations of an open interval-average target.
No arithmetic convergence assumption is discharged by renaming it.

Let the occurrence labels include every positive-height nontrivial zero up to
T with its analytic multiplicity, and write

\[
C_T=\frac{T\log T}{2\pi},\quad N(T)=\#\{i\},\quad
d_{ij}=\gamma_i-\gamma_j,\quad w(d)=\frac4{4+d^2}.
\]

The existing `MontgomeryFormFactor.formFactor` is
\[
F_T(\alpha)=\frac1{C_T}\Re\sum_{i,j}w(d_{ij})e^{i\alpha\log T\,d_{ij}}.
\]
It is nonnegative for T>1 and continuous in alpha; both are already checked
for the actual zero multiset, without RH.

## Exact identity before taking a limit

Define the explicit endpoint kernel
\[
K_{a,b}(\xi)=
\begin{cases}
b-a,&\xi=0,\\
\dfrac{\sin(b\xi)-\sin(a\xi)}\xi,&\xi\ne0.
\end{cases}
\]
Lean proves the complete equality
\[
\int_a^b F_T(\alpha)\,d\alpha
=(b-a)\frac{N(T)}{C_T}+S_T(a,b),\qquad
S_T(a,b)=\frac1{C_T}\sum_{i\ne j}w(d_{ij})K_{a,b}(\log T\,d_{ij}).
\]
The condition i != j refers to occurrence labels. Distinct labels with the
same ordinate remain in S_T, and their kernel value is b-a. No simplicity,
ordinate injectivity, or critical-line hypothesis is used. All signs remain.

## Unconditional count normalization

`ActualZeroOrdinate.tendsto_count_div_mainTerm` proves
\[
\frac{N(T)}{C_T}\longrightarrow1.
\]
The proof uses the existing actual Riemann--von Mangoldt theorem, first
obtaining every dyadic upper coefficient above 1/(2*pi), then iterating the
exact count decomposition N(T)=N(T/2)+N(T/2,T). Finite geometric accumulation
sharpens the existing coarse total upper bound. The existing sharp lower
coefficient theorem supplies the other side of the squeeze. All hypotheses
of the generic RvM step are supplied by checked actual-zero providers.

`countNormalized_interval_limit_iff` checks the passage between N(T) and C_T
normalization for every fixed interval and every finite limiting value.

## Countable exact arithmetic target

The checked equivalence is
\[
\begin{aligned}
&\forall b\ge1,\ \forall\ell>0,\quad
\frac1\ell\int_b^{b+\ell}F_T(\alpha)\,d\alpha\longrightarrow1\\
&\qquad\Longleftrightarrow\quad
\forall q\in\mathbb Q,\ q>1,\quad S_T(1,q)\longrightarrow0.
\end{aligned}
\]

The right side is `RationalSignedCancellation`. **Its truth remains Open.**
The proof passes through `RationalAnchoredLimit`, namely
integral from 1 to q tending to q-1. Positivity makes the cumulative integrals
monotone, so rational-density squeezing supplies every real endpoint; exact
subtraction supplies every interval. A further checked theorem permits
endpoints a(T), b(T) converging to real a,b>=1, provided the moving endpoints
are eventually >=1. It yields interval masses, not averages divided by a
vanishing interval length.

## Declarations and classification

| Module | Principal declarations | Status |
| --- | --- | --- |
| Analysis/ActualZeroCountNormalization.lean | eventually_count_le_log_of_lt; tendsto_count_div_mainTerm | Unconditional actual-zero theorem |
| Analysis/RationalIntervalLimits.lean | tendsto_intervalIntegral_of_rat_Ici; tendsto_intervalIntegral_of_rat_Ici_moving | Generic positivity/dense-set theorems |
| Analysis/MontgomeryIntervalIdentity.lean | integral_cosineWindow; integral_formFactor_diagonal | Unconditional exact finite identities |
| Analysis/MontgomeryIntervalCriterion.lean | rationalAnchoredLimit_iff_intervalAverageLimit; moving_interval_limit_of_rationalAnchoredLimit | Conditional research reduction |
| Analysis/MontgomerySignedIntervalCriterion.lean | countNormalized_interval_limit_iff; interval_limit_iff_signed_cancellation; intervalAverageLimit_iff_rationalSignedCancellation | Conditional research reduction; normalization transfer unconditional |

The equivalences are theorems; neither side's arithmetic truth is asserted.
The open domain-specific obligation is RationalSignedCancellation. Ordinary
foundational axioms must be distinguished from hypotheses in theorem types.

## Published input and its precise role

1. H. L. Montgomery, *The pair correlation of zeros of the zeta function*
   (1973), https://websites.umich.edu/~hlm/paircor1.pdf. Source for the form
   factor, weight, and Fourier-pairing conventions.
2. E. Carneiro, M. B. Milinovich, A. P. Ramos, *Fourier optimization and
   Montgomery's pair correlation conjecture*, arXiv:2310.01913v2,
   https://arxiv.org/html/2310.01913v2, Section 1.2, equation (1.4), citing
   Goldston (1988), Theorem 1. Under RH, the interval-average condition with
   N(T) normalization is equivalent to ordinary PCC. This published PCC
   equivalence is **external**, not formalized or assumed by these new modules.
   Their bounds 0.9303 and 1.3208 for sufficiently long intervals do not prove
   the limit 1. No pointwise F(alpha,T)->1 beyond support one is required by
   the weaker interval-average target.
3. D. A. Goldston, J. Lee, J. Schettler, A. I. Suriajaya, *Pair Correlation
   Conjecture for the zeros of the Riemann zeta-function I: simple and critical
   zeros*, https://arxiv.org/html/2503.15449v4. Theorem 1 assumes PCC to obtain
   density-one simple critical zeros without separately assuming RH. It does
   not prove PCC or exclude every exceptional off-line zero.

Web sources were checked on 2026-11-14. Wolfram independently returned the
nonzero-frequency cosine integral and its zero-frequency limit b-a. These
computations guided/cross-checked the formula; Lean proves it independently.

## Verification and next check

The final focused import and guarded axiom audit passed in server job
`job_o-C50BiIFYAhKR-4Osxy39SOU7_1hF8O` (Bazel/BuildBuddy, exit 0,
`verified=true`, server verification 53.743 seconds). Build evidence:
https://app.buildbuddy.io/invocation/e18b96c9-a26d-4ce0-b564-385a808036eb.
The count normalization, normalization-transfer equivalence, signed criterion,
and moving-endpoint theorem were each checked to depend only on `propext`,
`Classical.choice`, and `Quot.sound`. This does not discharge the open
hypotheses in the conditional theorem types.


All final source files must pass the server checkpoint's full Bazel target
`//:RiemannResearch` with `--config=buildbuddy` before publication. Focused
snippet successes alone do not certify the integrated project. The terminal
checkpoint job and exact published commit are reported in the accompanying
chat response; the commit containing this catalog identifies its source.

Canonical next arithmetic target: prove S_T(1,q)->0 for every fixed rational
q>1. No uniformity in q is required by this criterion. The fixed q=2 case is a concrete initial test, but
that one case alone is insufficient. The existing coarse absolute-value bounds do not
establish the required signed cancellation. Separately, formalizing the
published RH-conditional PCC equivalence remains an analytic transfer task.
