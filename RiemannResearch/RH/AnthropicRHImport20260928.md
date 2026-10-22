# Anthropic RH import — 28 September 2026

## Scope

This completes the useful proof-library import from
[anthropics/formal-math](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23),
pinned to commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
The baseline already contained 140 modules. This extension adds 171, for
311 imported proof modules under `RH/WeilExplicitFormula/`.
Lean and Mathlib pins are unchanged. Existing namespaces such as
`Zeta23` and `RHLinalg` are preserved.

This is an import of upstream mathematics, not a new proof of RH.
The source supports the mathematical statements and proofs. The selection
and the proposed applications below are a local research assessment.

## Available mathematics and intended consumers

| Added group | Modules | Content and concrete RH use |
|---|---:|---|
| XiPrime | 108 | Zeros of the completed zeta derivative; real-part partial fractions for xi'/xi; explicit formulas, zero counts, coefficient expansions, prime moments, quartic windows; Hardy Z and its stationary points. Supports spectral, zero-detection and Mellin/Weil comparisons. |
| ThmE | 37 | Primitive Dirichlet L-functions: functional-equation seam, explicit formula, Riemann-von Mangoldt, local counts, prime-side traces and zero proportions. Supplies character-twisted comparisons relevant to arithmetic/CRT decompositions. |
| ThmDE | 9 | Montgomery-Taylor optimization for primitive Dirichlet characters, including multiplicity-aware counts. |
| PairCeiling | 11 | General Abel and twice-integrated discrepancy identities, stability and signed-edge inequalities, integer certificate checks, and law-specific bounds with explicit enclosure and validity premises. Useful for testing the limits of two-moment spectral arguments. |
| Taper | 3 | Gevrey ramps and test-function construction. Supports smooth localization in explicit-formula and frequency-window arguments. |
| WeilEF | 2 | Effective explicit-formula bounds and general zero-summability machinery. |
| ZeroSide | 1 | Sharpness examples for the multiplicity-aware rank-trace inequality. |

The earlier 140 modules already provide the zeta explicit formula,
Riemann-von Mangoldt, Montgomery-Vaughan, prime-sum estimates, linear-algebra
inertia tools, and the zeta proportion results. They are reused, not duplicated.

## Entry imports

Use the narrowest applicable module:

```lean
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Final
import RiemannResearch.RH.WeilExplicitFormula.ThmE.Mult
import RiemannResearch.RH.WeilExplicitFormula.ThmDE.Mult
import RiemannResearch.RH.WeilExplicitFormula.PairCeiling.Stability
import RiemannResearch.RH.WeilExplicitFormula.PairCeiling.Signed
import RiemannResearch.RH.WeilExplicitFormula.ZeroSide.TightMult
```

All imported modules are also exported by `RiemannResearch.lean`.

Key upstream endpoints include:

- `Zeta23.XiPrime.xiDeriv_simple_on_line` and
  `xiDeriv_simple_on_line_quartic_std`: actual xi' zero proportions,
  with constants 0.85838/0.92919 and 0.86864/0.93432 respectively.
- `Zeta23.XiPrime.hardyW_simple_on_line` and
  `hardyZ_simple_stationary_points_quartic`: the W-function and actual
  Hardy-Z stationary-point conclusions, with their exact counting definitions.
- `Zeta23.ThmE.thmE_B₀_mult` and `thmE_C₀_mult`:
  primitive-character simple-critical and distinct zero proportions.
- `Zeta23.ThmDE.thmE_D₀_simple_mult` and `thmE_D₀_dist_mult`:
  optimized primitive-character versions.
- `Zeta23.ZeroSide.TightMult.lemmaR_tight`: rank-trace sharpness.
- `Zeta23.PairCeiling.ceiling_stability`:
  general discrepancy inequality under its explicit regularity/validity conditions.
- `Zeta23.PairCeiling.ceiling_law256_signed`:
  the law-specific signed bound, retaining `EnclOK` and `hvalid`.

## Verification and assumptions

The 171 new source files were compared to the pinned upstream files after
removing nested comments and string literals and normalizing whitespace:
only import paths change in executable source. Original license headers remain.
The source scan found no proof holes, new axioms, unsafe declarations,
native proof evaluation, or external proof-evaluation hooks.
No new file contains a blanket Mathlib import.

The publication checkpoint compiles the added modules and affected dependents.
The source scan is not a substitute for compilation. The upstream audit
snapshot records upstream verification and is not a claim that Comparator or
an independent kernel was rerun locally.

Axiom inspection must be combined with reading theorem types. The law-specific
ceiling requires `EnclOK` for the chosen form-factor function and certificate
validity; this import supplies no provider identifying the actual periodic law
with those enclosures. Its integer row checks and general analytic estimates
are separately proved. Primitive-character results retain modulus and
primitivity conditions. Abstract intermediate theorems retain their displayed
analytic hypotheses.

The proportion theorems do not exclude an exceptional off-line zero.
No theorem here proves the project's signed correction pairing tends to zero,
identifies the Mellin DPP with the zeta-zero process, or supplies a Hilbert-Polya
operator. Each such application still requires an explicit checked bridge.

## Research reading retained as source references

| Source | Status and use |
|---|---|
| [Main paper, arXiv:2608.13637](https://arxiv.org/abs/2608.13637) | Published research source for the imported proof package. |
| [Five-page expert note](https://www-cdn.anthropic.com/23455459f8832d06bb175cc0f88d019aed962ef8.pdf) | Concise Weil-form, trace and inertia argument. |
| [95-page discovery account](https://www-cdn.anthropic.com/d7f3ecf1d01392d887f8bc974ca187e2a121b1ed.pdf) | Exploratory source; its opening disclaims independent verification of intermediate mathematics. Covers negative-index attempts, compression visibility and research failures. |
| [116-page annotated transcripts](https://www-cdn.anthropic.com/8a0d1add3c637b858a9a181e98c40e9548c3f44f.pdf) | Working history of E2 and E2-pairs, not an additional theorem provider. |
| [Anthropic announcement](https://www.anthropic.com/research/riemann-zeta) | Provenance and links to the research package. |
| [Fermat repository](https://github.com/anthropics/fermats-last-theorem) | Indirect modular/automorphic reference only; not added as a dependency. Its different toolchain and lack of an identified direct RH consumer make wholesale import inappropriate here. |

Discovery-account page 14 mentions finite-support Weil positivity and
narrow-interval zero-density improvements. These remain exploratory leads:
the account says the positivity certificate was not independently rerun or
refereed in the session, and the zero-density note was not drafted.
They have not been promoted to Lean theorems or assumptions.

## Exclusions and reproducibility

Challenge files contain deliberate proof placeholders and are not imported.
Solution wrappers and the alias-only Unconditional entry point add no needed
mathematics. Four unused FromPNTPlus files outside the selected closure are
excluded; the existing PrimeNumberTheoremAnd dependency remains unchanged.
No third-party pull request or fork is silently treated as Anthropic source.

`WeilExplicitFormula/SOURCE_MANIFEST.json` records all 311 source paths and
upstream Git blob identities. `PROVENANCE.md` records transformations.
`UPSTREAM_README.md` and `UPSTREAM_AUDIT.md` retain the upstream documentation
at the pinned revision, with local snapshot notices.

For an endpoint audit after building, run the following through `lake env lean`:

```lean
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Final
import RiemannResearch.RH.WeilExplicitFormula.ThmDE.Mult
import RiemannResearch.RH.WeilExplicitFormula.ThmE.Mult
import RiemannResearch.RH.WeilExplicitFormula.ZeroSide.TightMult
import RiemannResearch.RH.WeilExplicitFormula.PairCeiling.Signed

#check Zeta23.XiPrime.xiDeriv_simple_on_line
#check Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
#check Zeta23.ThmE.thmE_B₀_mult
#check Zeta23.ThmDE.thmE_D₀_simple_mult
#print axioms Zeta23.XiPrime.xiDeriv_simple_on_line
#print axioms Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std
#print axioms Zeta23.XiPrime.hardyW_simple_on_line
#print axioms Zeta23.XiPrime.hardyZ_simple_stationary_points_quartic
#print axioms Zeta23.ThmE.thmE_B₀_mult
#print axioms Zeta23.ThmDE.thmE_D₀_simple_mult
#print axioms Zeta23.ZeroSide.TightMult.lemmaR_tight
#check Zeta23.PairCeiling.ceiling_law256_signed
#print axioms Zeta23.PairCeiling.ceiling_stability
#print axioms Zeta23.PairCeiling.ceiling_law256_signed
#print axioms Zeta23.PairCeiling.LawN256_edge
```
