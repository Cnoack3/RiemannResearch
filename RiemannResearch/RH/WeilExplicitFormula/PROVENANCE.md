# Weil explicit formula and zero-proportion proofs: source and scope

Upstream: [anthropics/formal-math, zeta23](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23).

Pinned upstream commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
The earlier `anthropics/zeta-23-lean` repository URL redirects to this repository.

Lean: `leanprover/lean4:v4.33.0-rc2`.
Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.
Both match the existing RiemannResearch project exactly.

## Scope

The original compact-formula import contained 57 upstream project modules
transitively imported by `Zeta23.WeilEF.Main`, totaling 18,105 source lines.

The 28 September 2026 extension adds 83 modules from the same pinned revision,
for 140 upstream modules in total. The added source has 29,488 lines when
terminal empty split lines are excluded. The union is the transitive closure
of `Zeta23.WeilEF.Main`, `Zeta23.FinalMult`, and `Zeta23.ThmD.Mult`.
The plain `Zeta23.Final` endpoint needs 60 new modules; the multiplicity-aware
endpoint needs 78, and the optimized multiplicity endpoint needs 83.
All declarations retain their original namespaces. No trusted Challenge
placeholder, Solution, Dirichlet, XiPrime, or PairCeiling module is imported. The linear-algebra and tail modules present here are imported by
the upstream `Hypotheses`/`Tail` dependency chain. They are import-reachable;
no claim is made that every declaration in each imported module occurs in
the final theorem's kernel dependency graph.

The exposed upstream theorem is
`Zeta23.WeilEF.EF_lit_zetaZeroConfig : Zeta23.EF.EF_lit Zeta23.zetaZeroConfig`.
It has no hypotheses. The compact test hypotheses appear when the proposition
`EF_lit` is expanded: `ContDiff ℝ 2 k` and `HasCompactSupport k`.

The carrier is exactly `riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`, and the
multiplicity is `(analyticOrderAt riemannZeta ρ).toNat`. Positivity and
finiteness of the multiplicities and the necessary symmetries are proved
in the imported seam; no seam hypothesis remains in the exposed theorem.

The formula includes absolute convergence of the zero sum, every von
Mangoldt prime-power term, the two pole terms, and the digamma integral.
It also supplies the unconditional inverse-square zero-sum majorant and
the unit-window zero-count bound. The full dyadic Riemann--von Mangoldt theorem and completed GammaFacts
package are now included. Their zero-count growth, together with the
unconditional on-line simple-zero proportion, supports the project module
`RH/CriticalLineZeros.lean`. Its consumer
`RH/ProjectedDualMassObstructionUnconditional.lean` discharges the
critical-zero premise of the strict-margin mass obstruction.

Additional upstream endpoints include `Zeta23.MV.mv_hilbert`,
`Zeta23.PrimeSide.thm_traces`, `Zeta23.thmA₀`,
`Zeta23.thmB₀_mult`, `Zeta23.thmC₀_mult`, and the multiplicity-aware
Montgomery--Taylor results in `Zeta23.ThmD`. See
`RH/Zeta23ImportCompletion20260928.md` for their exact scope.

## Mechanical changes

Each file retains its original copyright and license notices. A new header
records this relocation. Every command of the form `import Zeta23.X` has
been changed to `import RiemannResearch.RH.WeilExplicitFormula.X`. No theorem,
definition, proof body, namespace, attribute, or option has been changed.
For the original 57 modules, only whitespace and the documented prose
corrections below accompany import relocation.

Six added modules previously used a blanket Mathlib import:
Taper/Norms, Taper/Fourier, Taper/Decay, MV/Spacing, ThmD/Functional,
and PrimeSideA/Defs. Those imports are replaced by specific analysis,
measure-theory, matrix, and tactic modules. The publication build checks
the resulting proof elaboration. All other added-file changes are the
provenance header, intra-project import relocation, whitespace normalization,
and the two documentation-only corrections recorded below.

The closure contains no exact `import Mathlib` command. Its imports are
specific Mathlib modules (including tactic support) and the existing
standard dependency module `Batteries.Tactic.Lemma` in the original closure.
Lean, Mathlib, Lake configuration, and dependency pins are unchanged.

The upstream `Prelude/InstancePriorities.lean` demotes
`LieAlgebra.toModule` to instance priority 10. This existing upstream
attribute is retained; it does not alter theorem statements, but can
affect instance elaboration in importers.

## Audit boundary

The original source was scanned with nested Lean block comments, line
comments, and string literals excluded. The complete imported closure
contains no executable `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`,
`implemented_by`, `extern`, `mkSorry`, `ofReduceBool`, or `addDecl` token.
Documentation corrections (7 September 2026): the publication audit identified
postulated-constant examples inside the additive-combination documentation,
a line beginning with the corresponding declaration keyword in Hypotheses,
and a proof-status word in StrongPNTPrefix. The example now uses explicit
parameters and hypotheses; the two prose descriptions were reworded. A
nested-comment-aware comparison confirms that executable source is unchanged
in all three files. Copyright and license text is unchanged.

Documentation corrections (28 September 2026): the first extension checkpoint
flagged proof-status words in the FromPNTPlus/Mertens provenance comment and
a declaration keyword at the start of a line in the PrimeSideB/PP module
description. These comments now say explicitly that unfinished upstream
material was excluded and the taper conditions are proved. No executable
source, copyright notice, or license text was changed by this correction.

The relocated compact formula passed this project's `efcore1` compiler check.
The combined completion check `job_Krj1svNf3MBDoFYei95fp6xuWVuq_WxM` also passed
and audited the exposed compact formula and downstream endpoints: their only
axioms are propext, Classical.choice, and Quot.sound. The subsequent native
publication checkpoint validates the normal module imports. A source scan
alone is not used as compilation evidence.

The conversion of the Fourier/digamma integral to the spatial subtracted gamma
kernel is supplied by the separate WeilGammaFourierAdapter module. The dominated
extension to noncompact superexponential tests is supplied by
WeilNoncompactExplicitFormula. Both passed the combined completion check; this
compact adapter itself exposes only the compact formula and its majorants.

## License and attribution

Apache License 2.0; see `LICENSE.md` and `NOTICE.md` in this directory.
Copyright 2026 Anthropic, PBC. The `FromPNTPlus` modules preserve notices
for the PrimeNumberTheoremAnd and Mathlib contributors, including original
authors and upstream commit references. The included `NOTICE.md` is copied
unchanged from the upstream zeta23 project.

Whitespace normalization: trailing whitespace and terminal blank lines removed; proof tokens unchanged.

Verification of the 28 September extension: the full project build
`job_6aCSTLypXtTRqZE5upxJwCctqH4-K7CS` succeeded. The exact-type and
13-endpoint axiom audit `job_fNxyjrlIIb81oC2E24O0GitQLce2N8lh` succeeded;
all endpoints report only propext, Classical.choice, and Quot.sound.
The critical-zero and existential mass-obstruction specializations have
no premises. Publication uses the affected-module checkpoint gate.

## Complete RH-relevant extension (28 September 2026)

The subsequent comprehensive import adds 171 modules from the same pinned
revision, bringing this directory to 311 proof modules. The earlier exclusions
of Dirichlet, XiPrime and PairCeiling above describe the historical 140-module
stage, not the current scope.

Added groups: XiPrime (108), ThmE (37), ThmDE (9), PairCeiling (11),
Taper (3), WeilEF (2), and ZeroSide (1). This includes Hardy's Z derivative
and W-function development, primitive Dirichlet L-functions, Gevrey tapers,
rank-trace sharpness, and conditional certificate stability.

The new files preserve executable source exactly after import relocation
and whitespace normalization, verified by a nested-comment/string-aware
comparison with the fetched pinned sources. No new file uses a blanket
Mathlib import. The NumericCert documentation replaces the phrase naming
a native evaluation tactic with "native evaluation"; proof tokens are unchanged.
The executable-source scan found no proof holes, added axioms, unsafe
declarations, native evaluation, or external proof-evaluation hooks.

The source and upstream Git blob identity of every imported module are recorded
in SOURCE_MANIFEST.json. All new modules are exported from RiemannResearch.lean.
UPSTREAM_README.md and UPSTREAM_AUDIT.md are snapshots of upstream documentation;
their build claims describe upstream runs, not a new local comparator run.

Theorem assumptions remain part of their types. In particular, law-specific
PairCeiling bounds require both form-factor enclosures (EnclOK) and certificate
validity, along with their regularity conditions. No enclosure provider for the
actual periodic law is added. Pure integer checks and general stability lemmas
are separately proved. No RH assumption or new proof of RH is introduced.

The unused Unconditional module only repeats existing endpoints as aliases.
The four unused FromPNTPlus files are outside this dependency closure.
Challenge placeholders and Solution wrappers remain excluded.
See ../AnthropicRHImport20260928.md for concrete consumers and reading material.
