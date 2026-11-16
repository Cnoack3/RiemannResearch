# RH part 2 — research review and formalization checkpoint

Prepared 16 November 2026 for Christian Noack. Repository base inspected: `b9d28e2775cfe2f846798fb307b9460e99f6b59f`. Work began at 17:39:40 UTC; the research cutoff is 18:54:40 and the hard deadline is 19:09:40. Publication is authorized and must pass the managed full-project server checkpoint.

## Results and scope

The [RH part 2 folder](https://drive.google.com/drive/folders/1Bc0hEIxDoC1owgzNc3N3rNIJthymIIvw) contains 89 original research/source items. They comprise 50 searchable documents, 25 TeX sources, 12 handwritten scans, one cleaned-claims PDF and one original numerical-certificate script. Original file IDs and contents were preserved; files were moved without deletion or sharing changes. Added review deliverables are separate from these 89 originals.

The [individual ledger](RH_PART2_PAPER_LEDGER_20261116.md) records every selected file, its review depth, imported declarations, deferred claims, duplicate status and next obligation. Its [JSON counterpart](ResearchData/RHPart2_20261116/paper_review_ledger.json) also retains source IDs and available text/source hashes. This was a broad title/folder search followed by content triage, not an exhaustive transcription of every generic scan in Drive. Handwritten files received first-page triage only. Large manuscripts received selected-section review, not blanket proof certification.

Four new Lean modules contain 38 theorem declarations. They formalize selected exact identities and strengthen their generality. The actual arithmetic estimates needed for RH remain separate. The older first-prime numerical certificate was also audited, repaired and rerun externally. The empirical zero-phase agenda was advanced with a reproducible finite experiment.

## 1. Nyman–Beurling: attainable drift and minimum-energy extension

Source: [Best Nyman Beurling for RH — A1–A2 Audited Revision](https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view), especially sections 21 and 23.9–23.10. The final two physical PDF pages were rendered and inspected. The similarly named TeX file is an older revision and lacks the late section used here.

Module: [HeadTailDriftObstruction.lean](LinearAlgebra/HeadTailDriftObstruction.lean), namespace `RiemannResearch.LinearAlgebra.HeadTailDrift`.

Let A and B be finite-column head and tail synthesis maps into arbitrary real inner-product spaces. Assume the complete tail Gram G=B*B is invertible. Define

\[
d(h)=BG^{-1}A^*h,\qquad
\mathcal N=\{(h,t):A^*h+B^*t=0\}.
\]

The new declarations prove:

- `attainable_iff`: the drifts of targets in \(\mathcal N\) are exactly \(\operatorname{ran}(BG^{-1}A^*)\).
- `graph_normal`: every such drift is realized by the explicit target \((h,-d(h))\).
- `normal_tail_energy`: for every normal extension,
  \[
  \|t\|^2=\|d(h)\|^2+\|t+d(h)\|^2.
  \]
  Thus the residual graph gives the minimum-energy extension; equality forces the graph extension.
- `normal_completion` and `normal_minimizer_unique`: the full least-squares objective has its exact two-energy remainder and uniquely minimizes at coefficient zero.
- `tail_completion`: the stated inverse-tail-Gram coefficient really is the tail least-squares optimizer.
- `no_uniform_strict_angle`: if a nonzero direction u is accessible, then for every κ<1 there is a legitimate normal-equation target with drift=u, defeating the proposed universal strict angle bound.

The strengthening is an exact range/energy statement in arbitrary ambient inner-product spaces; completeness is unnecessary. It retains the full inverse Gram. It does **not** disprove a bound specialized to the actual arithmetic source. It proves why normal equations alone cannot supply that bound.

**Still open:** the actual curvature/nonalignment estimate in the paper's (23.29), A1 affine dispersion, A2 signed moment/admissibility control and any cofinal arithmetic provider. Current `ParetoAffineHeadTrials.lean` already retains every mixed residual-Gram term and gives a conditional RH reduction; its subpolynomial Gram-growth hypothesis is not discharged here. `QDensitySquarefreeObstruction.lean` also rules out density-image approximation by a conductor family omitting four; that obstruction must be respected when selecting legal dictionaries.


## Additional gluing audit: strict positivity does not repair the pairwise formula

Source: [Audited Cross-Route Synthesis](https://drive.google.com/file/d/1Z-FVYsCfc-gg5WPg2rLQSffi9mc0MO4W/view), proposition “Rational counterexample to the discarded formula.” The paper's example uses singular positive-semidefinite blocks. The new [ThreeBlockOptimizerObstruction.lean](LinearAlgebra/ThreeBlockOptimizerObstruction.lean) strengthens it to uniformly positive, bounded blocks:

\[
G_1=\begin{pmatrix}2&0\\0&1\end{pmatrix},\quad
G_2=\begin{pmatrix}1&0\\0&2\end{pmatrix},\quad
G_3=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad I\le G_j\le3I.
\]

With local fits \(\beta_1=(0,0)\), \(\beta_2=(0,1)\), \(\beta_3=(1,1)\), the complete Gram is \(G=\begin{pmatrix}5&1\\1&5\end{pmatrix}\) and the common optimizer is \(\beta=(5/12,11/12)\). Lean verifies both inverse identities, the normal equations and the exact positive completion of the common objective.

Nevertheless,

\[
\sum_j(\beta_j-\beta)^TG_j(\beta_j-\beta)=\frac{13}{6},
\qquad
\frac12\sum_{i,j}(\beta_i-\beta_j)^TG_iG^{-1}G_j(\beta_i-\beta_j)
=\frac{55}{24}.
\]

The missing signed defect is exactly \(-1/8\). All three blocks are symmetric, strictly positive and bounded between I and 3I, so neither singularity nor poor conditioning explains the failure. `pairwise_formula_false` rules out this formula under those stronger hypotheses. The existing two-block formula remains unaffected. The actual arithmetic gluing estimate still requires the complete noncommutative correction or a valid positive Green representation.

## 2. Harmonic analysis: the complete reciprocal-max Green matrix

Source: [growing_degree_ridge_no_go.pdf](https://drive.google.com/file/d/1p5qy1xBllrTpwe96tm6ee2fAcF36IOvK/view), section 14.2, equations (14.13)–(14.14).

Module: [ReciprocalMaxGreen.lean](LinearAlgebra/ReciprocalMaxGreen.lean). It extends the existing `WeightedGreenInverse` calculus instead of duplicating it.

For \(1\le i,j\le n\), let \(K_{ij}=1/\max(i,j)\), and let \(C_k=\sum_{i\le k}c_i\). `brownian_energy` proves the exact finite identity

\[
c^TKc=\sum_{k=1}^{n-1}\frac{C_k^2}{k(k+1)}+\frac{C_n^2}{n}.
\]

The last term is essential: truncating the infinite series at n and leaving weight \(1/(n(n+1))\) would change the matrix. The entire infinite tail for a finitely supported charge is encoded by \(C_n^2/n\).

`WeightedGreen.applyGreen_applyInverse` supplies the missing right inverse with the explicit zero right boundary. `brownian_inverse` supplies the matching left inverse, and `brownian_inverse_energy` proves

\[
y^TK^{-1}y=\sum_{k=1}^{n-1}k(k+1)(y_k-y_{k+1})^2+n y_n^2.
\]

This gives a concrete precision-energy diagnostic for actual source vectors. Wolfram independently returned the exact n=5 inverse and zero symbolic difference between its quadratic form and this expression. That computation is corroboration; the general identities are Lean proofs.

**Still open:** the Mellin interchange and actual CRT-source observability/resistance estimate needed by the paper's global agenda. The growing-degree no-go theorem was reviewed but was not imported wholesale. Large finite gains do not prove the asymptotic bound, and independently optimized Mellin blocks cannot be glued without their optimizer mismatch.

## 3. Zeta ordinates: decoding with unequal tolerances and corruptions

Sources: [Modular Phase Reconstruction](https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view) and [Empirical Phase Coding](https://drive.google.com/file/d/1quuQlmUyGYSn5E8FmkfbdOeg9fIfI_KR/view).

Module: [FiniteCoordinateDecoding.lean](Analysis/FiniteCoordinateDecoding.lean). Existing `PhaseDecoding.lean` already covers finite packing, arbitrarily far approximate collisions, ordinary nearest-neighbor uniqueness, compact two-prime inverse stability and noisy anchor reconstruction. The new result permits coordinate corruption and erasure budgets.

For a finite coordinate set and an arbitrary pseudometric space, put

\[
B_\epsilon(u,v)=\{i:d(u_i,v_i)>\epsilon\}.
\]

The exact deterministic input is

\[
B_{\epsilon+\delta}(u,v)\subseteq
B_\epsilon(u,z)\cup B_\delta(v,z).
\]

Consequently two candidate explanations of one observation, with at most r and s bad coordinates, have at most r+s coordinates separated by more than ε+δ. `unique_of_error_budgets` proves uniqueness whenever every distinct candidate pair exceeds that count. `bad_card_le_of_good_outside` turns an explicit discarded-coordinate set into a budget. Tolerances and budgets may differ between explanations; no stochastic noise model is used.

**Hypothesis retained:** separation of the actual finite code. The theorem does not produce zeta zeros from no data, prove a growing-height separation rate, or establish pair correlation.

## 4. Executed zero-phase experiment

Wolfram supplied the first 300 `ZetaZero` ordinates at machine precision; the last is approximately 541.8474371212013. The saved experiment uses primes 2,3,5,7, seed 20261116 and windows \((T,2T]\). Python 3.12.14 / NumPy 2.3.5 reproduced the retained output exactly.

| Window | Zeros | Minimum circular sup-distance | Median nearest-neighbor distance | Minimum far-coordinate count at ε=0.005 |
|---|---:|---:|---:|---:|
| (50,100] | 19 | 0.148424 | 0.234994 | 3 |
| (100,200] | 50 | 0.146410 | 0.178528 | 3 |
| (200,400] | 123 | 0.096267 | 0.160459 | 2 |

The last column counts coordinates with distance greater than 2ε, minimized over distinct pairs. The new theorem's sufficient condition for one corrupted coordinate in each candidate requires more than two. The floating-point diagnostic passes that test in the first two windows and fails it in the third. This is not an interval-certified certificate and failure of a sufficient condition is not nonuniqueness.

The empirical first Fourier coefficients show the expected negative prime bias. In (200,400], their real parts for 2,3,5,7 are approximately −0.120668, −0.157924, −0.194972, −0.186653. The classical leading prediction

\[
-\frac{T\log p}{2\pi\sqrt p\,N(T,2T]}
\]

gives −0.126840, −0.164145, −0.186266, −0.190335. The absolute centered discrepancies are 0.008490, 0.006389, 0.008709, 0.004152. This motivates subtracting the known arithmetic bias before testing a random surrogate.

The primary literature supports qualitative fixed-dimensional phase equidistribution and secondary prime bias. That is distinct from growing-dimensional coding rates, pair correlation, and the current Lean actual-prime-torus theorem: `PrimePhaseWindows.lean` still takes a `UniformSelbergDensity (1/4)` provider and a quantitative Fourier-decay hypothesis. No unconditional Lean provider was added here.

Files: [script](ResearchData/RHPart2_20261116/reproduction_sources.md#phase-diagnostics), [ordinates](ResearchData/RHPart2_20261116/phase_ordinates.json), [complete diagnostics](ResearchData/RHPart2_20261116/phase_diagnostics.json). The iid comparison is exploratory, with 100 replicates, not a calibrated hypothesis test. All distances and zeros in this experiment are floating-point data.

## 5. First-prime certificate: defect, repair and rerun

The [original certificate](https://drive.google.com/file/d/1HDzIW9Znf9g-ZcE-HuGIB8LKPUphJXFh/view) was read in full. Its claimed interval enclosure was invalid:

1. `-Decimal(...)` used the ambient 28-digit context in interval negation. A singleton containing 1.123456789012345678901234567890123456789 was mapped to a singleton at −1.123456789012345678901234568, excluding the exact negative.
2. Both square-root endpoints were computed identically. For sqrt(2), the resulting point interval lay below the exact root; its upper endpoint squared was strictly less than 2.
3. Absolute-value/remainder endpoint handling and one tail product also needed explicit outward treatment. A near-zero branch silently replaced a nonzero-frequency integral by its zero-frequency value.

The [repaired script](ResearchData/RHPart2_20261116/reproduction_sources.md#interval-certificate) uses exact sign/absolute-value copies, neighboring representable square-root endpoints, interval tail multiplication and an exact-zero-only branch. The original Drive script was preserved unchanged. [Regression checks](ResearchData/RHPart2_20261116/reproduction_sources.md#interval-regression-tests) compare against exact rational arithmetic: the original negation failure is reproduced, and 100 square-root brackets plus 800 arithmetic enclosure checks pass after repair.

The complete repaired run with J=20, four head modes and K=2001 succeeded. It returned γ9>0.919837 and four strictly positive LDL pivot intervals with approximate lower endpoints

\[
0.0838143661,\quad0.0168793553,\quad1.1433969933,\quad0.2484784747.
\]

The [raw output](ResearchData/RHPart2_20261116/reproduction_sources.md#interval-output) retains the numerical details; the [interval witness](ResearchData/RHPart2_20261116/odd_endpoint_interval_witness.json) preserves full-precision decimal endpoints for the head matrix, Schur lower matrix and pivots. Existing `RatInterval.matrixProduct_contains` and `stagedCongruence_contains` in `LinearAlgebra/RationalMatrixIntervalCertificate.lean` provide a suitable next formal-certificate interface once the analytic entry bounds are proved. Printed tables round their endpoints for display; the script's positivity assertions use the internal intervals.

**Status:** repaired external numerical evidence. This run does not kernel-verify the interval implementation, the operator reduction, monotonicity, or the analytic tail bound \(|x_{m,n}|\le63/(50n)\). It therefore does not promote the complete odd-sector operator theorem to Lean-checked status. The constrained even inequality remains open. The implementation defect invalidates the old certificate as supplied; it does not refute the claimed mathematical positivity.

## 6. Import decisions and next-check queue

| Priority | Concrete next obligation | Work completed here | Acceptance condition still missing |
|---|---|---|---|
| 1 | Actual-source NB curvature / mixed-source cross-Gram | Exact attainable range and energy; generic normal-equation shortcut excluded | Bound for the prescribed arithmetic vector, not all accessible targets |
| 2 | Reciprocal-max source energy with legal CRT constraints | Full finite kernel and inverse energy formalized | Uniform actual-source estimate with conductor compatibility and all Mellin blocks |
| 3 | C2 odd endpoint and constrained even sector | Original arithmetic implementation audited; repaired finite computation passes | Lean operator/series/tail bridge, then even constrained inequality |
| 4 | Robust phase-code separation | Deterministic corruption theorem and finite diagnostics | Certified actual-code separation or justified growing-height rate |
| 5 | F7–F11 and G85–G92 source observability | Source covector, Gram and amplitude distinctions reviewed | Complete marked-Gram transfer, legal capture budget and absolute mixed-source lower bound |
| 6 | V-Weil mixed-prime factorization | Compared against existing cutoff and approximate-factorization modules | Renormalized mixed-prime boundary and actual-direction contraction |
| 7 | Spectral determinant / Pick route | RH-equivalent acceptance condition identified; duplicates retained | Zero-independent spectralizing construction with required metric/trace control |

No conjecture was imported as an axiom. No generic Gram inversion, first-jet identity, local Euler-factor identity, finite positive matrix, or cofinal compactness assertion was counted as a proof of the actual RH-level source estimate. Several agendas remain unresolved; the ledger makes these explicit rather than marking the papers complete.

## Verification and reproducibility

All new modules are exported by `RiemannResearch.lean`. The [focused theorem catalog](THEOREM_CATALOG_RH_PART2_20261116.md) lists exact declarations and hypotheses. Ten main results were checked with guarded `#print axioms` messages, each restricted to `propext`, `Classical.choice`, and `Quot.sound`; local mathematical hypotheses remain visible in their types. No placeholder, new project axiom or unsafe declaration was added.

The final publication uses one managed checkpoint with `push=true` and Bazel/BuildBuddy `//:RiemannResearch` validation. The checkpoint's terminal record, reported with the published commit, is the evidence for whole-project and any integrated-main verification. Focused checks and the external computations above do not substitute for that gate.

## Primary references consulted

- Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733). The Drive copy was read for the weighted sequence-space formulation.
- Luis Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, [arXiv:math/0202141](https://arxiv.org/abs/math/0202141). Abstract-level corroboration of the integer-dilation criterion.
- Jean-François Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, [arXiv:math/0103058](https://arxiv.org/abs/math/0103058). Bibliographic/abstract check; no sharp constant imported from that check.
- Kevin Ford and Alexandru Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, [author PDF](https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf), especially the introduction and prime-power secondary density.
- Kevin Ford, Xianchang Meng and Alexandru Zaharescu, *Simultaneous distribution of the fractional parts of Riemann zeta zeros*, [arXiv:1511.06814](https://arxiv.org/abs/1511.06814). Fixed-dimensional distribution versus stronger quantitative agendas.
- Python's [`decimal` documentation](https://docs.python.org/3.12/library/decimal.html), for exact sign copies, context-sensitive arithmetic and numerical rounding behavior.

The source papers' own assertions are not automatically treated as established published results. The only new kernel-checked claims are the exact Lean declarations listed in the catalog, under their displayed hypotheses.
