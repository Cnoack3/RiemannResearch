# Large-sieve import provenance

Source: [ericlisg/erdos768-lean](https://github.com/ericlisg/erdos768-lean)
at commit [e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9](https://github.com/ericlisg/erdos768-lean/commit/e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9).
This source supports the statements and proofs of the copied development.
The upstream Apache 2.0 license is preserved in LICENSE.md.

## Scope and faithful adaptations

The two selected modules preserve the upstream namespace Erdos768LS and all
declaration statements. No upstream toolchain, dependency configuration, or
unrelated Erdos problem development is imported.

The umbrella Mathlib import is replaced with named analysis, integration,
finite-sum, floor, Fourier, Dirichlet-character, and tactic modules. The local
multiplicative module imports the local additive module.

For the target Lean v4.33.0-rc2 / Mathlib
51e6992efd06126df61a496bebf8f49482a4e129, proof elaboration in Additive.lean
is adapted as follows:

- The real integral norm conversion explicitly uses Real.norm_eq_abs.
- Sum differentiation names its termwise derivatives, closes definitionally
  equal goals, and uses function extensionality for the pointwise sum.
- The derivative-norm estimate spells out the same absolute-value,
  real-part-norm, and product-norm calculation.
- The two Parseval applications unfold S and Sderiv and simplify the same
  coefficient norm square; the inequalities and constants are unchanged.
- Redundant ring normalization steps are allowed to finish trivially.

For Multiplicative.lean, the target port adds the named Dirichlet-character
norm bounds and real-pi bounds imports. It expresses circle conjugation and
the standard additive character on a cast natural number explicitly, unfolds
the same Gauss-sum shift identity and double inverse, applies the same
unit-residue reindexing with an explicit function, and supplies NeZero q from
q in Icc 1 Q before using the per-modulus bound. The unit conjugate-inverse
identity is closed algebraically instead of by unrestricted automation.
These adaptations change no declaration statements, character restrictions,
normalizations, signs, or inequality constants.

Exact finite Parseval, DFT Plancherel, and character orthogonality identities
remain primary endpoints. The large-sieve estimates preserve the additive
constant delta^(-1) + 4*pi*N and the universal positive multiplicative constant
witnessed by 4*pi. This port does not provide the sharper classical constant
displayed in RH/RawMobiusFarTailLargeSieve20260924.md.

## Source manifest

| Local file | Upstream file | Upstream blob |
| --- | --- | --- |
| Additive.lean | RequestProject/LargeSieve.lean | d3244cec13b58e1f26fb44ed2f645857f13bbfdf |
| Multiplicative.lean | RequestProject/LargeSieveMult.lean | 784de8d27fa346949e6e2eee3532d121b42115ec |
| LICENSE.md | LICENSE | d645695673349e3947e8e5ae42332d0ac3164cd7 |

## RH application obligations

The finite CRT frequency expansions and conductor-averaged square energies
are concrete intended consumers. Duality, the exact CRT Fourier
identification, and weighted-tail transfer remain separate obligations.
An absolute-value bound does not supply the signed arithmetic cancellation
required by the repository's RH reductions.
