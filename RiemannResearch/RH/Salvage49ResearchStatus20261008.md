# Independent-prime continuation: 49-theorem salvage status

Date: 2026-10-08. This note records source fidelity, successful kernel verification, and the exact mathematical scope of eight modules.

## Kernel verification and publication procedure

All **73 theorem bodies** in the eight modules pass coherent Lean checks, including all **49 previously unverified candidates**. The final comparison preserves every original candidate statement and explicit section context. The union of all 73 public axiom reports is exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorryAx` dependencies. The complete-body checks in batches B, C, and D report no warnings; all batches return `verified = true` and exit code zero.

The environment is Lean `v4.33.0-rc2` with the project's pinned Mathlib. Isolated checks used repository baseline `04db1cc3090d06e1abd30261b4a5f4d27df8e189`. Each batch includes every theorem body. Batch A's output was truncated; batch D recovers its seven missing axiom reports. Together the retrieved reports cover all 73 distinct theorem names.

| Batch | Terminal check job | Seconds | Checked source SHA-256 |
|---|---|---:|---|
| A | `job_wk41K91c4aQH2-EAPpt39Q8T4XEg3IW4` | 5.028 | `896cfa8e76eb956c930ddca896c6ccc2c5ff4f40fc46ee2f40a28a7c7934a10b` |
| B | `job_C_INejVCm7_Dqt6daXQYLVzl9gQKWwgr` | 5.035 | `32d8aa76b7d0b84edffd5b1d11b04ac1ca0c89f6bdba3920a14603028146b7ec` |
| C | `job_G85sDFx8acfOV0DwWvosDbvwmYZQ8n4L` | 4.738 | `2f630e04ff0a95ebc20d409c69818ec58136b7ac9b46c070715d2d4d2dae1015` |
| D | `job_cBsr1B2TI7BHymD_4yeLT87DI4-2CDJt` | 4.961 | `4fa6911d1574610ed513f681f53771757d87d412df1d6442eeeab6629b79d6b6` |

`Salvage49KernelVerification20261008.json` records the report for every declaration. `Salvage49StatementAudit.json` records the original and final statement hashes and the final source digests. These records distinguish kernel verification from source comparison.

The retained dependency build was recovered as interrupted. Its incremental continuation reached completion but reported errors in two candidate modules. Four elaboration/tactic issues and redundant tactic warnings were then repaired. That failed preparation build is not reported as a successful full-project build. The subsequent coherent checks verify the repaired proof bodies.

All eight native modules are exported from `RiemannResearch.lean`. Final publication uses the workspace checkpoint, which audits and validates the affected native modules and their reverse dependents before committing and pushing. Its final commit and native validation outcome are supplied in the publication response and delivered verification manifest; an isolated check alone does not assert publication.

## Exact declaration inventory

Counts include declarations prefixed by attributes such as `@[simp]`; definitions are counted separately. There are **8 modules, 73 theorems, and 20 definitions: 93 named source declarations**. There are no extra lemma/structure/abbreviation declarations in these eight files.

| Module | Theorems | Definitions | Group |
|---|---:|---:|---|
| `FinitePrimeLikelihood` | 18 | 11 | Previously isolated-check group |
| `PrimeSieveSecantAlgebra` | 6 | 0 | Previously isolated-check group |
| `FinitePrimeDivisibilityMoments` | 13 | 2 | Salvage |
| `ZetaTwoDampedEnergyTransfer` | 12 | 2 | Salvage |
| `ZetaTwoPeriodMeanBounds` | 4 | 0 | Salvage |
| `ExactHeadMeanGap` | 5 | 1 | Salvage |
| `PrimeSieveTwoCutoffHead` | 10 | 2 | Salvage |
| `PrimeSieveTwoCutoffMean` | 5 | 2 | Salvage |
| **Total** | **73** | **20** | **24 + 49 theorems** |

The salvage split is exactly **13 + 12 + 4 + 5 + 10 + 5 = 49**. The previous group is **18 + 6 = 24**. All 73 listed theorem bodies pass the current checks; 49 are newly salvaged relative to the October 7 record.

The root source comparison reports that all 49 salvage proposition statements are unchanged. This statement audit does not replace kernel validation of their proof bodies.

## Mathematical scope and assumptions

**Finite product law.** `FinitePrimeLikelihood` defines a mass on a finite Boolean cube explicitly and proves factorization, normalization, likelihood moments, and the change of success probabilities from \(p^{-2}\) to \(p^{-1}\). A probability interpretation uses parameters in \([0,1]\), for instance real parameters \(p\ge1\); rational identities impose their displayed nonzero-denominator conditions. `FinitePrimeDivisibilityMoments` adds monomial moments, the complete differentiated Gram formula, its diagonal, and likelihood orthogonality. These are identities in the defined finite product law.

**Integer-law bridge remains separate.** Neither finite module constructs the probability measure \(Q(K=k)=1/(\zeta(2)k^2)\) or proves that its actual divisibility indicators push forward to the finite Boolean mass. Interpreting subset products as squarefree conductors and unions as least common multiples additionally requires distinct actual primes. The algebraic declarations allow real parameters and do not silently provide these arithmetic or measure-theoretic identifications. They also provide no bounded discrete-integration operator and no residue-atom approximation sequence.

**Secant algebra.** `PrimeSieveSecantAlgebra` proves exact finite rational identities and affine/convex mean bounds. A signed affine combination with coefficients summing to one pays its full total variation. The prime increment interpretation and a uniform Mertens asymptotic are not proved by these finite statements.

**Damped energy transfer.** `ZetaTwoDampedEnergyTransfer` compares complete Pareto and inverse-square square-summability for any positive normalizer \(Z\). Taking \(Z=\zeta(2)\) is the intended probabilistic specialization; the file uses a positive real parameter. The unconditional damping range is \(\varepsilon\ge1/2\), with the canonical center and its uniqueness inherited from existing results. The RH consumers explicitly require summability at positive dampings tending to zero, or at arbitrarily small positive dampings. No uniform norm bound is required by these consumers, but the small-damping summability premise remains unproved.

**First-period limitation.** `ZetaTwoPeriodMeanBounds` gives

\[
\frac{\operatorname{periodMean}(u,P)^2}{ZP}
\le\sum_{k\ge1}\frac{u(k)^2}{Zk^2},\qquad Z>0,\ P>0,
\]

under the displayed summability assumption. The proof uses only the first block of length \(P\). Its residue-synthesis specialization retains both exact coefficient sums, \(\sum c_d\) and \(\sum c_d/d\), and requires every index to divide \(P\). It does not formalize the stronger bound obtained by summing every period of a periodic function. In particular, at \(Z=\zeta(2)\), it does not claim the paper's stronger \(\operatorname{periodMean}(u,P)^2/P\) lower bound. Summability is retained to avoid Lean's totalized-tsum convention masking divergence.

**Complete exact-head obstruction.** `ExactHeadMeanGap` proves that any actual Pareto Hilbert vector \(F\) with physical values \(F(k)=1\) for \(1\le k\le N\) satisfies

\[
(N+1)(1-\mathbb E_PF)^2\le\|1-F\|_P^2,
\qquad
\frac{N+1}{Z}(1-\mathbb E_PF)^2
\le\sum_{k\ge1}\frac{|1-F(k)|^2}{Zk^2}.
\]

This uses the exact full tail mass \(1/(N+1)\), not a finite-tail surrogate. It requires no legality or RH hypothesis.

**Actual two-cutoff sieves.** `PrimeSieveTwoCutoffHead` constructs the actual signed factorial-divisor sieve and its bundled Hilbert vector. Exact head interpolation requires \(Y\le W\) and distinct sieve reciprocal masses; the eventual pointwise statement retains an admissible cutoff schedule and this nondegeneracy. The complete intermediate rough count remains in the residual. `PrimeSieveTwoCutoffMean` identifies the exact Pareto mean with finite divisor-logarithmic masses and proves the secant formula. It does not identify the normalized divisor-log sum with a prime sum or prove the Mertens limit. Thus the eventual uniform linear error-growth conclusion still needs those arithmetic/asymptotic bridges to be formalized.

## Squarefree scope and RH status

The repository's existing `SquarefreeTransfer.riemannHypothesis_of_squarefreeCenteredApproximation` is the appropriate explicit squarefree approximation-to-RH theorem. Its finite witnesses carry squarefree support; it assumes no external RH-density provider. The existing comparable-weight forward consumer also implies RH from complete inverse-square approximation.

The primary mathematical reference is B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, [arXiv:math/0607733](https://arxiv.org/pdf/math/0607733). **Remark 8 on printed p.145 directly states the discrete squarefree criterion:** the constant sequence \(\gamma\) belongs to the closed linear span of \(\gamma_l\) with squarefree \(l\) if and only if RH. Theorem 1 and the comparable-weight paragraph appear on printed pp.137–138; Remark 4 on printed p.142 gives the corresponding squarefree Hardy-space restriction. These support the paper-level criterion, not a claim that the new Lean modules formalize its complete converse.

`hilbertLegalClosure A` and `legalSeedSpan A` are seed-and-dilation constructions: choosing squarefree seeds does not restrict all resulting conductor indices to squarefree integers. The new two-cutoff module states membership in `legalSeedSpan allPositiveSeeds`; this must not be relabeled as a proved squarefree-only closure equivalence. Nor should squarefree atoms be claimed total in the full Hilbert space merely because the constant-approximation criterion holds.

The full Lean reverse implication RH \(\Rightarrow\) the required approximation remains **OPEN as a formalization obligation**: existing conditional equivalences explicitly take `hBaezDuarte : RiemannHypothesis → NaturalApproximation`. The corresponding published analytic theorem is known; it is not supplied by these eight modules. The arithmetic provider needed to deduce RH unconditionally—such as admissible small-damping energy or bounded legal approximation—also remains **OPEN**. None of the salvage statements supplies that provider.

Source basis: all eight local module declarations, the existing `SquarefreeParetoTransfer`, `ParetoComparableWeights`, `BaezDuarteNaturalApproximation`, and `ThresholdRiemannHypothesis` source APIs, and the October 7 continuation's historical verification ledger. The final native validation and publication outcome must be read from the terminal checkpoint evidence.
