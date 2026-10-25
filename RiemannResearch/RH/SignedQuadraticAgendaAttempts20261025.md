# Signed quadratic correction: attempts on all seven agenda items

Date: 25 October 2026. Source: Christian Noack's attached
`Signed_Quadratic_Correction_Research_Note.pdf`, especially section 10.
The seven-item numbering here follows the PDF, rather than the differently
grouped older repository memorandum.

## Scope

This development restores the four salvaged modules, adds nine focused modules,
and distinguishes finite unconditional results, conditional actual-zero consumers,
ordinary mathematical deductions, and open obligations. No proof of RH or of
constant-target legal closure is claimed. A phase-law or density hypothesis in a
Lean theorem is not discharged by an axiom audit.

## Agenda ledger

| PDF item | Result of the attempt | Remaining acceptance obligation |
| --- | --- | --- |
| 1. Analytic phase provider | Audited the exact density premise and assembled its existing scalar band estimate into the actual quadratic sum, with multiplicity. | Open: a Lean proof supplying `UniformSelbergDensity (1/4)` and the quantitative rational-frequency provider. |
| 2. Finite arithmetic assembly | Positive prime-power indexing is injective; different pure towers have zero covariance; conjugate pairing gives the exact coefficient `-1/pi`; an actual-zero limit consumer has only `hphase` as its analytic premise. | The intended finite conditional assembly is completed; discharging `hphase` belongs to item 1. |
| 3. Moving-support budget | Exact reciprocal and inverse-square spread formulas, weighted Cauchy, geometric tower sums, and actual density-band quadratic transfer. | Open: nearest-prime-power rational logarithmic separation assembled with quantitative Landau, and a fully checked explicit growing-support asymptotic regime. |
| 4. Spectral and stability | General scalar inverse rows, both endpoints, exact Hermitian perturbation, quadratic-zero/operator-kernel distinction, and sixth-coordinate boundary effect. | Open: matrix inverse assembly, positive definiteness, congruence, normalized-path spectrum, exact inertia, prime kernel classification, and asymmetric spectral bounds. |
| 5. Arithmetic coefficients | Exact sign identity for the actual full squarefree covariance with damped Möbius coefficients, retaining composite edges; connected to the actual phase-limit consumer. | Open: sufficient uniform signed estimates for the optimized legal coefficients and their downstream closure consequences. |
| 6. Legal approximation | Complete progression-tail bounds (9.11), complete-Q bounds `F5 < 7/250` and `F7 < 1/50`, F7 legality/head, projection and parity corollaries. | Open: uniformly bounded growing exact-head costs or vanishing full projection error. |
| 7. RH-sensitive strengthening | Exact finite-sample modification bound; paper proof of a fixed-height Landau-positivity criterion. | Open: proving the requisite Landau positivity or another genuinely RH-sensitive estimate without assuming the desired closure. |

## 1. Analytic input: the hypothesis is still visible

The repository's `Analysis/ActualZeroSelbergDensity.lean` explicitly defines,
but does not supply, the classical uniform estimate

\[
N(\sigma,T)\le C T^{1-(\sigma-1/2)/4}\log T,
\qquad \tfrac12\le\sigma\le1.
\]

Ford--Zaharescu, Lemma 2, supports this unconditional classical mathematical
input. Their count with both signs of the ordinate bounds the positive-ordinate
inclusive count used by the project, with analytic multiplicity. Reflection and
layer cake give the paper estimate `E(T) <= 64 C T/log T`; this does not force
the finitely many individual horizontal displacements to vanish.

The pre-existing scalar formalization is stronger than the sufficient frequency
range displayed in the PDF. For a density exponent `a>0`, and `0<=theta<1`, it gives

\[
\left|\frac{\operatorname{Ord}_T(u)-\operatorname{Lan}_T(u)}T\right|
\le\frac{2C}{a^2(1-\theta^2)}\frac{u^2}{\log T},
\qquad |u|\le\theta a\log T.
\]

The new `ActualDirichletPolynomialDensityBand` sums this inequality with actual
coefficient magnitudes and proves

\[
\left\|\frac{\operatorname{SampledSquare}_T(a)-
\operatorname{LandauGram}_T(a)}T\right\|
\le\frac{2C}{a^2(1-\theta^2)}\frac{V(a)}{\log T}.
\]

The classical specialization on `|u|<=log T/8` has constant `128 C/3`.
Its moving-support theorem assumes eventual density and band membership and
`V(a_T)/log T -> 0`. There is no extra diagonal/cardinality error in this
phase-to-Landau comparison. It is a conditional research reduction, not a new
proof of Selberg's estimate or of the full signed arithmetic asymptotic.

## 2. Actual finite prime-tower assembly

`PrimeTowerAssembly` accepts any finite set of pairs `(p,k)` with prime `p`
and positive `k`, including nonuniform or sparse towers. It proves injectivity
of `(p,k) -> p^k`, rather than assuming it. The displayed upper-triangular sum
is expressed as a filtered double sum of index pairs, with a term only when
the prime bases agree and `k<l`:

\[
\mathcal C(a)=-\frac1\pi\sum_p\log p
\sum_{k<l}\frac{\Re(\overline{a_{p^k}}a_{p^l})}{\sqrt{p^{l-k}}}.
\]

The theorem `tower_correction_eq` identifies this with the real part of the
repository's complete arithmetic Gram pairing. The theorem
`sampledSquare_tower_signed_limit_of_phase` supplies the actual-zero limit
under exactly the explicit off-diagonal phase-limit premise. Frequency 1 is
excluded by the positive exponent condition.

## 3. Coefficient budgets and stronger paper regimes

The finite profile lemmas preserve the negative square. On one tower,
with `H_K=sum 1/k` and `H_{K,2}=sum 1/k^2`, they specialize to

\[
V_{1/k}=(\log p)^2[K(K+1)H_K-2K^2],\qquad
V_{1/k^2}=2(\log p)^2[K H_{K,2}-H_K^2].
\]

The formal statements allow arbitrary nonzero real indices; substituting
`x_k=k` and the elementary sum of integers gives these displayed forms.
The checked weighted Cauchy/geometric budget is

\[
\left(\sum_{k=1}^K w_k\sqrt{p^k}\right)^2
\le2p^K\sum_{k=1}^K w_k^2,\qquad p\ge2.
\]

**Paper deductions, not fully formalized support regimes.** Combining the
larger conditional density band with the rational Landau estimate would permit
every `K=o(log T)` for inverse-square magnitudes, rather than only the PDF's
sufficient `O(log T/loglog T)` range. For example, eventually
`K=floor(log T/logloglog T)` is admissible.

For inverse-cube magnitudes `|a_(p^k)|=k^-3`, fix `0<c<1/4` and choose
`K=floor(c log T/log p)`. Elementary integral comparisons give

\[
A_0\le2,\quad V(a)\le4(\log p)^2(1+\log K),\quad
A_{1/2}^2\le4p^K.
\]

The resulting conditional remainder is bounded by a constant times

\[
\frac{1+\log K}{\log T}+\frac{p^K\log^2T}{T}\longrightarrow0.
\]

Thus the largest frequency may reach `T^c`, uniformly in coefficient phases.
The complete rational-frequency provider, admissibility checks, and final
asymptotic specialization remain open formalization work. These are not
estimates for the optimized legal approximants in `L^2(Q)`.

## 4. Stability and the general spectral route

`HermitianQuadraticPerturbation` proves the complete identity

\[
Q_B(a+h)=Q_B(a)+2\Re(h^*Ba)+Q_B(h).
\]

The linear term disappears under `Ba=0`. A quadratic zero alone does not
remove it: `(1,-r/2,1)` has middle coordinate `2r` in `(K_r-I)a`.
For the five-coordinate kernel `(1,r,0,-r,-1)` with `2r^2=1`, the sixth row
after zero extension equals `-r`. Adding a real sixth coefficient `epsilon`
gives correction exactly `2 c r epsilon`. No quadratic remainder is omitted;
the newly added diagonal of the correction matrix is zero.

`PrimeTowerStability` also verifies the scalar rows underlying the tridiagonal
inverse, including both endpoints and every interior row. It does not package
these as a matrix-inverse theorem or claim a checked spectral classification.

The audited paper route remains

\[
K_r^{-1}-I=\frac r{1-r^2}(rD-A),\qquad
\operatorname{inertia}(I-K_r)=
\operatorname{inertia}(rI-D^{-1/2}AD^{-1/2}).
\]

Normalized-path thresholds are `cos(j pi/(K-1))`. Congruence preserves
inertia, not eigenvalues. For prime `p` and `r=1/sqrt p`, the rational
algebraic-integer argument gives `p=2`, `K=1 mod 4` for `K>=2`.
`K=1` is separately zero for every prime. The shorter determinant route

\[
\det(I-K_r)=-r^K U_{K-2}(r),\qquad K\ge2,
\]

may reduce future formalization cost for the kernel criterion. Its Chebyshev
recurrence and the algebraic-integer argument are not checked results here.

## 5. Composite squarefree edges survive

Let `W(n,m)` be the actual `primePowerCovarianceSymmetricEntry`. For
squarefree endpoints, any prime-power quotient is a prime, and

\[
W(n,m)\mu(n)\mu(m)=-W(n,m).
\]

Consequently, for any finite squarefree support `S` and any real damping `f`,

\[
\mathcal C_S(\mu f)=\frac1{2\pi}
\sum_{n,m\in S}W(n,m)f(n)f(m).
\]

It is nonnegative for nonnegative damping. The formula includes edges such
as `3--6` and every support boundary. It applies equally to `-mu f`.
`sampledSquare_squarefree_moebius_limit_of_phase` connects this exact formula
to the actual-zero consumer while retaining `hphase`.

For the nonunit divisors of a product of `k>=1` distinct primes, a paper
counting specialization gives

\[
\mathcal C_S(\mu)=\frac{2^{k-1}-1}{\pi}
\sum_p\frac{\log p}{\sqrt p},\qquad A_2=2^k-1.
\]

The counting specialization is not formalized here. Positivity of this
coefficient-space correction does not establish legal density, and the
needed uniform estimates for the actual optimized coefficients remain open.

## 6. Complete Q certificates and the remaining limit

`ProgressionSquareTailBounds.progression_square_tail_bounds` proves (9.11):
for `L>=1`, `a>0`, and `M>=0`,

\[
\frac1{L(a+ML)}\le
\sum_{j\ge M}\frac1{(a+jL)^2}
\le\frac1{L(a+ML)}+\frac1{(a+ML)^2}.
\]

The proof uses finite telescoping comparisons and a vanishing explicit
boundary, without an assumed integral theorem.

`QSignedCorrectionCertificates` proves

\[
\|1-F_5\|_Q^2<\frac7{250},\qquad
\|1-F_7\|_Q^2<\frac1{50},
\]

where

\[
F_5=g_2+g_3+g_5-\tfrac15g_6,\qquad
F_7=F_5+\tfrac47(g_7-\tfrac67g_6).
\]

F7 has explicit squarefree-span membership and matches the first five sites.
The certificates use periods 540 and 1260 (multiples of the minimal periods),
the established bound `1/zeta(2)<76/125`, and the complete periodic-tail
majorant. Rational comparisons are reduced by `decide +kernel`, not a
floating-point oracle. Every tail is included. The proofs of the numerical
certificates use this convenient existing majorant; the new (9.11) theorem is
independently available for sharper or smaller future certificates.

Any projected subspace containing `g2,g3,g5,g6,g7` inherits error `<1/50`.
Using the existing exact parity identity, its parity-leakage lower factor
improves from `21/25` to `23/25`; atom membership remains explicit.

For growing exact heads, the target-weighted inverse-Gram cost is still
uncontrolled. Physical head rows may be dependent. A consistent constrained
minimum uses `1^T(A G^-1 A^T)^+1`, not an unjustified inverse of every head
row. A uniform full-norm bound would give legal closure by weak compactness;
it does not alone prove strong convergence of the chosen exact-head sequence.
More quantitatively, with `q_H=Q(n>H)`, the paper inequality

\[
\|1-F_H\|_Q\le
\sqrt{\|F_H\|_Q^2-1+q_H}+\sqrt{q_H}
\]

shows why costs tending to 1 would suffice for strong convergence. No such
uniform or asymptotically unit cost bound is proved here.

## 7. A limitation and a sensitive target

`FinitePhaseModification` proves the exact unit-phase diagonal removal and
the finite-update estimate. Adding `m` sample ordinates changes the centered
statistic by at most

\[
\frac mT(A_0^2-A_2)\le\frac{m(|S|-1)}T A_2.
\]

Deletion has the same bound by reversing the difference; mixed edits follow
by triangle inequality. The formal theorem uses a finite index set, so
repeated ordinates may be represented by distinct indices. For `|S|=o(T)`
this vanishes relative to `A_2`. Therefore these asymptotics alone are
insensitive to finitely many altered ordinates. Artificially modified sets
are not claimed to satisfy all other zeta identities.

**Paper RH-sensitive criterion.** Fix a prime `p` and a cutoff `T`. Positivity
of all actual Landau Gram matrices on `{p,...,p^K}`, with `K` unrestricted,
is equivalent to every included zero being on the critical line. Indeed,
positive two-by-two minors force

\[
|b_k|\le N(T),\qquad b_k=\sum_{0<\gamma\le T}m(\rho)p^{k(\rho-1/2)}.
\]

An off-line zero and reflection give a positive maximal real displacement
`alpha`. After dividing `b_k` by `p^(alpha k)`, the maximal-displacement
zeros give a finite trigonometric sum plus an exponentially decaying
remainder. Grouping equal unit phases leaves positive multiplicities, so its
Cesàro mean square is positive. Thus `b_k` is unbounded on a subsequence,
a contradiction. The converse is phase-Gram positivity on the line.

This argument has not been formalized here, and its required Landau
positivity is unproved. The exact hyperbolic factorization includes negative
sinh squares, so ordinary phase-Gram positivity does not provide it. Fixing
`T` and letting `K` be unrestricted is outside the established density band.

## Verification and publication

The coherent development job `job_uYtjixg2YbE-yM_u44lzf9JJHuw6fbY7`
returned terminal `succeeded`, `verified=true`, exit code 0. Its 57 new
theorem declarations include three private helper lemmas. The restored four
modules contain another 42 theorem declarations. Source SHA-256 of the coherent
checked snippet: `6c9ae89b055c95830a5de2f2e2a2f3bf55203eb6a227ca0a3ab7f8c651cd4d5d`.

The server reported 79.577 seconds for that verification operation (79.593
seconds total job elapsed). This is not an isolated kernel timing. Workspace
opening and client polling time are not included in that measurement; no
separate precise wall-time measurement of those phases was retained.

The saved-module import and axiom-audit job
`job_mNw4sYbyMeoFqAIT-9DkNoZkdr3ZzPMH` also returned terminal
`succeeded`, `verified=true`, exit code 0 (167.445 seconds verification operation,
167.460 seconds total job elapsed). It compiled all nine new modules and
their project dependencies. Audited central declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`; their analytic hypotheses
remain visible in the theorem types.

The source is saved as individually imported modules and submitted to the
mandatory final checkpoint for changed-module/reverse-dependent validation
and publication. The final user-facing report supplies its terminal status
and published commit. Successful development verification alone does not
certify a publication checkpoint. Failed intermediate snippets are proof
development diagnostics, not accepted theorems.

## Primary references and provenance

- User attachment, *Signed quadratic corrections for finite prime-power support*, 25 October 2026: source of the agenda and finite target formulas.
- Ford--Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, Lemma 2 and (3.8), https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf : classical density and phase-comparison inputs, not formal providers in this development.
- Ford--Meng--Zaharescu, *Simultaneous distribution of fractional parts of Riemann zeta zeros*, Lemmas 1--2, https://arxiv.org/abs/1511.06814 : uniform Landau/phase estimates used in the paper deductions.
- Fikioris, *Spectral properties of Kac--Murdock--Szegő matrices with a complex parameter*, Theorem 2.1(i),(v), https://arxiv.org/abs/1804.08140 : inverse and Poisson-symbol background.

No claim of mathematical novelty is made. Kernel verification concerns the
exact declarations, not the truth of their unresolved analytic hypotheses.
