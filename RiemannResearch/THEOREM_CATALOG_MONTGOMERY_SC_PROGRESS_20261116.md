# Montgomery SC continuation: boundary and diagonal estimates

Date: 2026-11-16 (America/Los_Angeles).
Starting revision: 8db47ed43c4ffd5fffff3b69319f21c3a1bc0e28.
Source plan: user-provided Montgomery_SC_Proof_Plan_2026-11-16.md.

## Outcome

P1 of the source plan is now formalized: the complete boundary is uniformly
negligible below the square-root scale, and the actual prime-window diagonal
has its expected asymptotic throughout every interior polynomial range.

SC, ordinary Montgomery pair correlation, and RH are not proved.
No new theorem below assumes RH, prime-pair cancellation, or the desired
variance asymptotic.

## Lean results

All names in this table are under RiemannResearch.Analysis.

| Module | Declaration | Exact mathematical content |
| --- | --- | --- |
| Analysis/ShortIntervalBoundaryAsymptotic.lean | ShortIntervalBoundaryAsymptotic.centered_boundary_normalized_le | Explicit boundary error at most 32 H² log N / N, for N≥2, H≥2, log N≥1, H²≤N. |
| Same | ShortIntervalBoundaryAsymptotic.centered_boundary_power_bound | Explicit uniform bound 32 log N / N^(2η), whenever H≤N^(1/2−η), η>0, with the same elementary lower-size conditions. |
| Same | ShortIntervalBoundaryAsymptotic.centered_boundary_uniform_log_div | For every η>0 and δ>0, eventually in N, every integer 2≤H≤N^(1/2−η) has boundary error divided by NH log(N/H) less than δ. |
| Same | ShortIntervalBoundaryAsymptotic.centered_boundary_tendsto_of_scale | Stronger moving-window result: H(N)² log N / N→0 and eventually H(N)≥2 imply negligible normalized boundary. |
| Analysis/MangoldtSquareAsymptotic.lean | MangoldtSquareAsymptotic.squareMass_ratio_tendsto | The actual sum Σ_(n≤N) Λ(n)² divided by N log N tends to 1; all proper prime powers remain in the sum. |
| Same | MangoldtSquareAsymptotic.centeredSquareMass_ratio_tendsto | The actual sum Σ_(n≤N) (Λ(n)−1)² divided by N log N tends to 1. |
| Analysis/ShortIntervalDiagonalAsymptotic.lean | ShortIntervalDiagonalAsymptotic.baseDiagonal_ratio_tendsto | The unshifted sum Σ_(x<N) (Λ(x+2)−1)² divided by N log N tends to 1. |
| Same | ShortIntervalDiagonalAsymptotic.centeredDiagonal_shift_exact | Exact finite diagonal translation identity, retaining both endpoints. |
| Same | ShortIntervalDiagonalAsymptotic.centeredDiagonal_shift_bound | Absolute translation error at most H(H−1)(log(N+H+2)+1)²/2. |
| Same | ShortIntervalDiagonalAsymptotic.centeredDiagonal_uniform | For every ε>0 and δ>0, eventually in N, every integer 1≤H≤N^(1−ε) has absolute diagonal error divided by HN(log N−log H) less than δ. |

The cases η≥1/2 or ε>1 are allowed in the theorem types; their large-N window
ranges are empty. The useful ranges are 0<η<1/2 and 0<ε<1.

### Boundary proof and strengthened scale

Write B(N,H) for the complete boundaryCorrection from ShortIntervalBoundary.
The existing cubic estimate and H²≤N give

\[
\frac{|B(N,H)|}{HN(\log N-\log H)}
 \le 32\frac{H^2\log N}{N}.
\]

For H≤N^(1/2−η), the right side is at most 32 log N / N^(2η), which tends to zero
independently of H. The moving-window theorem removes the need for a fixed
power saving: H=o(sqrt(N/log N)) is sufficient.

### Actual squared-Mangoldt asymptotic

The proof uses the repository's unconditional PNT and Chebyshev asymptotic,
rather than introducing either as a new hypothesis. Put Q(N)=Σ_(n≤N)Λ(n)².
For 0<A≤N, the finite inequalities are

\[
\log A\,(\vartheta(N)-\vartheta(A))
 \le Q(N)\le \log N\,\sum_{n\le N}\Lambda(n).
\]

For the lower bound, retain only primes in (A,N]. For the upper bound,
use 0≤Λ(n)≤log n≤log N. Taking A=δN for fixed δ∈(0,1) gives a limiting lower
bound 1−δ after division by N log N; δ may then approach zero. The upper
bound tends to 1 by PNT. Proper prime powers have not been deleted.

The centered identity is exact:

\[
\sum_{n=0}^{N}(\Lambda(n)-1)^2
 =Q(N)-2\sum_{n=0}^{N}\Lambda(n)+(N+1).
\]

### Uniform diagonal and an explicit error envelope

Define d(N)=Σ_(x<N)(Λ(x+2)−1)² and
e(N)=|d(N)/(N log N)−1|. The proof establishes e(N)→0 and, for sufficiently
large N and 1≤H≤N^(1−ε),

\[
\frac{|D(N,H)-HN\log N|}{HN(\log N-\log H)}
 \le \frac{e(N)+8\log N/N^\varepsilon}{\varepsilon}.
\]

This is a uniform rate expressed using the actual proved unshifted error;
it is not an explicit numerical PNT constant. The finite identity preceding
the estimate is

\[
D(N,H)=Hd(N)+
 \sum_{j<H}\sum_{x<j}
 \big((\Lambda(N+x+2)-1)^2-(\Lambda(x+2)-1)^2\big).
\]

Both squared terms lie between zero and the same bound, yielding the factor
H(H−1)/2 in the translation estimate.

## The remaining arithmetic target

Retain the repository's exact identity, with M=HN(log N−log H):

\[
V(N,H)-M=(D(N,H)-HN\log N)
       +2\sum_{k<H}E_N(k)+B(N,H).
\]

For any fixed 0<η<1/2, both the diagonal error and B/M now have unconditional
uniform proofs on 2≤H≤N^(1/2−η). In that range, the missing analytic estimate is

\[
\frac{2\sum_{k<H}E_N(k)}{HN\log(N/H)}\longrightarrow0
\]

with the required uniformity. This implication follows from the displayed
identity and the new support estimates; this session has not proved the
signed-prefix estimate or added it as an axiom. In larger H ranges, keep B
inside the signed combination unless a stronger boundary estimate is supplied.

Do not replace ΣE by Σ|E| without showing that the resulting stronger budget
is adequate. The odd-gap theorem still does not provide the required
even/odd cancellation at the triangular scale.

## Prime-to-zero bridge: precise external target and unresolved adapter

Primary reference inspected:
Languasco–Perelli–Zaccagnini, *Explicit relations between pair correlation
of zeros and primes in short intervals*, J. Math. Anal. Appl. 394 (2012),
761–771, introduction, equations (1.1)–(1.2):
https://doi.org/10.1016/j.jmaa.2012.04.058

The cited classical equivalence is under RH. Its relative-window statistic is

\[
J(X,\theta)=\int_X^{2X}
  (\psi(x+\theta x)-\psi(x)-\theta x)^2\,dx,
\quad
J(X,\theta)\sim \tfrac32X^2\theta\log(1/\theta)
\]

uniformly for X^(−1)≤θ≤X^(−ε). Its pair sum is
F(X,T)=Σ_(0<γ,γ'≤T) X^(i(γ−γ')) w(γ−γ'), and the pair-correlation target is
F(X,T)∼T log T/(2π), uniformly for T≤X≤T^A for each fixed A>1.
Under matching zero conventions, the repository's raw form factor is
F(T^α,T)/(T log T/(2π)). This is a stronger uniform pointwise route than the
fixed-interval SC target.

These statements identify an external transfer target; they are not a
newly formalized or instantiated theorem. The discrete fixed-window
variance in this project is not J(X,θ). The full relative-window, dyadic,
rounding, cutoff and normalization adapter remains to be supplied.

A useful exact first adapter is available on paper for integer N,H:

\[
V(N,H)=\int_1^{N+1}
  (\psi(t+H)-\psi(t)-H)^2\,dt.
\]

On t∈[x+1,x+2), the Mangoldt difference is exactly
Σ_(j<H)Λ(x+j+2); integer endpoints have measure zero. This observation is
not yet Lean formalized here. It handles fixed integer windows only and
does not solve the relative-window comparison.

The transition α↓1 and all rational anchored endpoints must still be
controlled. An RH-based external transfer must remain explicitly conditional
on RH; it is not an unconditional SC provider.

## Finite divisor-model feasibility: paper obstruction

For the source plan's model

\[
b_R(n)=\sum_{d\le R}\mu(d)\log(R/d)
  (\mathbf1_{d\mid n}-1/d),\qquad
A_R=\sum_{d\le R}|\mu(d)|\log(R/d),
\]

counting multiples in any interval of H consecutive integers gives

\[
|W_Hb_R(x)|\le A_R,\qquad
\mathcal E(b_R)\le NA_R^2.
\]

Hence

\[
\frac{\mathcal E(b_R)}{NH\log(N/H)}
 \le \frac{A_R^2}{H\log(N/H)}.
\]

This elementary paper bound is not Lean formalized in this continuation.
For a fixed R it proves that the model energy tends to zero on any schedule
with H log(N/H)→∞. Such a cutoff cannot satisfy the proposed sufficient
condition E(b_R)=M+o(M). More generally, any growing cutoff with
A_R²=o(H log(N/H)) is too small for that condition. The crude estimate
A_R≤R log R gives one easily checked sufficient test for this failure.

This does not rule out a useful growing-cutoff model or a signed transfer
that retains the mixed and residual terms.

## Numerical diagnostics — not proof evidence

The calculations use the actual von Mangoldt sequence including proper prime
powers. They evaluate D, V, every gap correlation, the complete endpoint B,
and the signed prefix sum independently. All numbers below are floating point.

| N | H | V/M | (D−HN log N)/M | 2ΣE/M | B/M |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 10,000 | 22 | 0.616318 | −0.331278 | −0.051256 | −0.00114745 |
| 100,000 | 46 | 0.674506 | −0.261833 | −0.063514 | −0.000146773 |
| 1,000,000 | 100 | 0.745017 | −0.218367 | −0.036584 | −0.0000322124 |

At N=1,000,000 and H=100, the complete model identity gives:

| R | E(b_R)/M | 2P(b_R,a−b_R)/M | E(a−b_R)/M |
| ---: | ---: | ---: | ---: |
| 10 | 0.000292500 | 0.000840031 | 0.743884 |
| 100 | 0.00663584 | 0.00983563 | 0.728545 |
| 1,000 | 0.0779639 | 0.0844212 | 0.582632 |

In each row the three entries sum to V/M, not to an assumed asymptotic value.
The largest relative identity discrepancy in the arithmetic runs was below
1.2×10^(−14). Independent small-index checks tested proper prime powers,
divisor coefficients, window endpoints, and H=1,...,8.
These finite checks do not establish an asymptotic, a uniform error estimate,
or information about uncomputed zeros.

## Verification and continuation

Focused boundary acceptance: job_B20686wFFKCG_DeHO78MjvvCa0_PdGER,
Bazel target //RiemannResearch/Analysis:ShortIntervalBoundaryAsymptotic.

Combined source-import and axiom-audit snippet:
job_d-Z420tsVFQaloqEyiBQDuvMNwccntIJ, successful with backend bazel.
This checks the three new modules and their transitive imports.
Axiom audits distinguish ordinary foundations from substantive hypotheses;
the actual moment and boundary theorems use only propext, Classical.choice,
and Quot.sound.
Guarded axiom audit: job_XtHmTcbTgbVGNKBlqDrhTzOuxmZkrdz_, succeeded with
backend bazel. Five #guard_msgs checks require exactly propext,
Classical.choice, and Quot.sound for the two moment limits, the uniform
diagonal theorem, and both principal boundary theorems.

Publication must pass the managed full //:RiemannResearch checkpoint.
The final response records its terminal job and exact published commit.
No GitHub-hosted runner is part of this acceptance path.

Next work:

1. Formalize the exact discrete-to-continuous fixed-window identity.
2. Choose a growing divisor cutoff and formally prove its empirical formulas
   and the above window-discrepancy bound before attempting a residual estimate.
3. Prove an actual two-sided signed-prefix estimate in a nonempty interior band.
4. Supply the full conditional prime-to-zero adapter with all ranges explicit.
5. Treat α=1, larger bands and sharp cutoffs before applying the rational SC criterion.
