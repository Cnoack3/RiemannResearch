# Spectral-correction continuation of highest viability RH.pdf

Source: [highest viability RH.pdf](https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view), especially equations (32), (37), (44), (58), (68), (72), (73), and agenda G1–G5.

## Lean: exact finite-cutoff obstruction

Modules: `Analysis/ZetaFactorObstruction.lean` and `RH/ProjectedPairSpectralObstruction.lean`.

| Declaration | Exact content |
|---|---|
| `ZetaFactorObstruction.numerator_three` | H + zeta(1-3) F(3) = H |
| `ZetaFactorObstruction.no_accumulating_zeros` | For H nonzero and F entire, the numerator cannot have accumulating zeros in Re(z)>0 |
| `ZetaFactorObstruction.mellin_block_pos` | Every nonempty vertical-line interval with positive real part has strictly positive weighted block energy |
| `ZetaFactorObstruction.finite_corrected_block_pos` | Any finite entire-column correction multiplied by zeta(1-z) still leaves positive block energy, even with complex coefficients |
| `ProjectedPairSpectralObstruction.booleanKernel_entire` | The literal finite Boolean kernel in (44) is entire |
| `ProjectedPairSpectralObstruction.haarMellin_entire` | Every finite weighted-atom synthesis is entire |
| `ProjectedPairSpectralObstruction.numerator_correction` | Exact signed addition formula for an arbitrary finite-atom correction |
| `ProjectedPairSpectralObstruction.finite_cube_block_pos` | For a nontrivial prime signal, every finite-cube correction leaves positive continuous block energy; analyticity is discharged |

Namespaces are prefixed by `RiemannResearch.Analysis.` for ZetaFactorObstruction and `RiemannResearch.RH.` for ProjectedPairSpectralObstruction. The last theorem allows arbitrary real atom weights and corrections; therefore its hypotheses are weaker than the paper's specific Haar/projected-pair assumptions. Its only arithmetic nontriviality premise is that some p_i>1.

The proof uses the complex identity theorem on Re(z)>0 and the actual trivial zero zeta(-2)=0. There is no RH, zero-density, simplicity, frame, or quantitative arithmetic hypothesis.

### Consequence for G2

At each fixed finite cutoff, Gamma and the projected column factors are entire finite sums/products. The finite-rank kernel RKHS consists of finite linear combinations of its columns. Exact membership of the target would make H+zeta(1-z)F(z) vanish on the continuous block, contradicting the positive integral theorem for H≠0. Thus the source's G2 exact finite-cutoff membership is impossible. The Lean theorem concerns the literal finite synthesis and its integral; the identification of that synthesis with the source's RKHS vocabulary is a mathematical interpretation, not a separate formalized RKHS construction.

This is not a uniform lower bound as x grows. It does not refute G1, approximation, or RH. Sampled pseudoinverse interpolation can succeed while exact continuous interpolation is impossible.

## Lean: replacement by quantitative approximate sources

Module: `Analysis/PrimitiveRegularizationCertificates.lean`.
Namespace: `RiemannResearch.Analysis.PrimitiveRegularization`.
This extends the repository's existing PrimitiveRegularization normal equations and Lax–Milgram existence theorem rather than duplicating them.

Let u solve the normal equation for T, target e, multiplier μ, and a linear subspace S; put r=Tu−e and let v∈S.

| Declaration | Content |
|---|---|
| `trust_region_minimizes` | The normal equation, μ≥0, complementarity μ(‖u‖²−B)=0, and ‖v‖²≤B imply residual(u)²≤residual(v)² |
| `approximate_source_centered_identity` | 4‖r‖²+μ‖v−2u‖² = μ‖v‖²+4⟨r,Tv−e⟩ |
| `approximate_source_residual_bound` | For μ≥0, ‖r‖≤(δ+sqrt(δ²+μ‖v‖²))/2, where δ=‖Tv−e‖ |
| `exact_source_residual_le_quarter` | If Tv=e, then ‖r‖²≤μ‖v‖²/4 |
| `approximate_source_budget` | If ‖Tv−e‖²≤δ and ‖v‖²≤B, the regularized objective at u is ≤δ+μB |
| `exists_approximate_source_budget` | For a continuous linear operator between complete real Hilbert spaces and μ>0, such a normal solution and objective bound exist |

The exact signed correlation is retained before Cauchy–Schwarz. These are unconditional Hilbert-space implications/existence results; they do not supply the x-uniform arithmetic approximate witnesses. In particular the exact-source corollary must not be applied to the obstructed exact source in G2.

## External: continuous block certificates

All code, exact decimal coefficient inputs, reports, and reproduction instructions are in `ResearchData/HighestViability20261116/`. Floating-point optimization proposes coefficients only. The independent verifier uses exact rational Gram data and FLINT/Arb ball arithmetic for logarithms, verified linear solves, zeta, and continuous analytic integration.

For x=53,97,199 the verifier certifies diagonal correction energy <x²log(x). It also certifies residual <10⁻⁴x²log(x) on [1,4], and residual <10⁻²x²log(x) on each of [1,16] and [0,16], using separate fixed coefficient vectors for the three windows.

| x | Pair columns | Certified residual ratio on [0,16] |
|---:|---:|---|
| 53 | 120 | [0.0024632652 ± 7.14e-11] |
| 97 | 300 | [0.004499037 ± 1.02e-10] |
| 199 | 1035 | [0.002639813 ± 2.57e-10] |

The residual uses the positive-half-line normalization 1/(π(t²+1/4)). Real coefficients identify [0,16] with the symmetric [-16,16] contribution in the paper's 1/(2π) normalization. One correction controls the whole stated window. This makes finite-cutoff progress on both G4 and G5 without combining incompatible separately optimized blocks.

Exact full-cube regression at x=7,11,13 checks the compressed signed formula, preservation of head/first moments, correction orthogonality, energy decomposition, and diagonal majorization. It is external exact arithmetic, not Lean verification. The continuous certificates likewise depend on the numerical implementation and Arb; their trust boundary is explicit in the data README.

## Agenda and next checks

| ID | Current status | Remaining acceptance condition |
|---|---|---|
| G1 | Open; strengthened Lean regularization tools and finite witnesses | Construct approximate witnesses with energy and residual budgets uniformly in x |
| G2 | Exact finite-cutoff membership refuted | Replace it by a quantitative approximate-source condition; no exact-membership premise |
| G3 | Signed formula preserved and independently regression-tested | Prove an x-uniform bound on the actual signed head-resonance contraction |
| G4 | Certified externally for three cutoffs and continuous windows through t=16 | Extend certified cutoffs/windows or formalize a uniform analytic certificate; numerical nodes alone are insufficient |
| G5 | One common correction per cutoff controls all of [0,16] | Bound the tail |t|>16 for the same correction, with summable budgets uniform in x |

The next priority is a quantitative approximate-source construction that survives both x→∞ and enlargement of the t-window. The finite certificates neither prove uniformity nor control the high-frequency tail. The RH-level variance bound and RH remain open.

## Evidence

- Source/extraction publication: `4d3807d2589962507c5059afa1b120b47c588ee3`.
- General zeta obstruction publication: `c68fde58095b50971d67c5c97b9ba12b761a4c6b`; full Bazel checkpoint succeeded.
- Focused regularization check: [BuildBuddy](https://app.buildbuddy.io/invocation/0632e7f3-e127-4967-8a89-5da9a7835f5e).
- Focused literal-kernel check: [BuildBuddy](https://app.buildbuddy.io/invocation/d276e075-adbb-46c7-851d-40a15e64ffa7).
- `RH/SpectralCorrectionAxiomAudit.lean` prints the key declarations' axiom dependencies.
- Publication of the continuation requires the managed full Bazel/BuildBuddy checkpoint, not just the focused checks.
