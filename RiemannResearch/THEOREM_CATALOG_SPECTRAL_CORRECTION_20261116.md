# Spectral-correction continuation of highest viability RH.pdf

Source: [highest viability RH.pdf](https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view), especially equations (32), (37), (44), (58), (68), and agenda G1–G5.

## Exact finite-cutoff obstruction

Module: `Analysis/ZetaFactorObstruction.lean`.
Namespace: `RiemannResearch.Analysis.ZetaFactorObstruction`.

| Declaration | Exact content |
|---|---|
| `numerator_three` | H + zeta(1-3) F(3) = H |
| `no_accumulating_zeros` | For H nonzero and F entire, the numerator cannot have accumulating zeros in the right half-plane |
| `exists_nonzero_on_interval` | On every nonempty vertical-line interval with positive real part, the numerator is nonzero somewhere |
| `mellin_block_pos` | Its continuously weighted block integral is strictly positive |
| `expPolynomial_entire` | Every finite exponential polynomial is entire |
| `finite_corrected_block_pos` | Every finite entire-column correction multiplied by zeta(1-z) leaves strictly positive continuous block energy |

The argument uses the complex identity theorem on Re(z)>0 and the actual trivial zero zeta(-2)=0. There is no RH, zero-density, simple-zero, or quantitative arithmetic hypothesis.

## Consequence for G2

At fixed finite cutoff, the source Gamma in (32) is a finite exponential polynomial. The Boolean Mellin kernel (44), and hence each projected column factor in (58), is entire. The finite-rank kernel's RKHS consists of finite linear combinations of those columns. The theorem therefore rules out G2's exact target membership for H_x nonzero. The formal theorem is about the finite column synthesis and its actual positive integral; identification with the source's RKHS terminology is the mathematical interpretation recorded here.

This is not a uniform lower bound as x grows. It does not refute G1, projected-pair approximation, or RH. Sampled pseudoinverse interpolation is a different finite-dimensional problem and may succeed while continuous exact interpolation is impossible.

## Remaining agenda

- G1: Open. Retain approximate witnesses with simultaneous energy and residual budgets.
- G2: Exact finite-cutoff membership is obstructed under the source's entire-column representation. Replace it by quantitative approximate membership.
- G3: Open. Preserve the signed head-resonance contraction.
- G4: Open. No numerical table has become a continuous certificate merely by this analytic result.
- G5: Open. A common correction must control all blocks; separately optimized corrections do not automatically assemble.

The source and extracted text were published at `4d3807d2589962507c5059afa1b120b47c588ee3`. Lean publication is subject to the full Bazel/BuildBuddy checkpoint.
