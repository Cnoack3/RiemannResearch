# V-space synthesis and retained-work recovery

Review date: 14 November 2026 Pacific (15 November UTC).
Starting published main: `c8374f82a71e51af647074d8d6087fa557d5788a`.

## Exact scope

This change recovers the unpublished source deltas recorded by the research Sites
and adds `RH/QDensityLeakageSeries.lean`. The recovery inventory and complete
declaration list are in `THEOREM_CATALOG_RETAINED_RECOVERY_20261115.md`.
Newer main developments are preserved; old aggregate files are not substituted
for current main. The later prime-subtype budget package supersedes the earlier
prime-specific draft. Seven generic continuous-synthesis results are separated
into `QCRTContinuousSynthesis.lean`, preserving the newer actual CRT coordinate
assembly.

The recovery adds 65 modules. The new leakage-series module adds eleven theorems
and five definitions. Recovered declarations include exact Gram interpolation,
complete rational progression certificates, signed CRT energy identities,
Möbius head repairs, hyperplane countermodels, relative-variation reductions,
and unconditional higher-prime-power arithmetic budgets.

## The V-space result added here

Work in the actual real Hilbert space with physical weights
`Q(n) = 1 / (zeta(2) n^2)`, n >= 1. Let V be the closed span of all residues
g_k, k >= 2. Define

```text
r = 1 - projection_V(1)
h_k = B g_k - projection_V(B g_k)
S_N = sum_{k=2}^{N+1} h_k
H_N = sum_{k=2}^{N+1} 1 / (zeta(2) k)
E_N = sum_{k=2}^{N+1} (h_k - r / (zeta(2) k)).
```

Here B is the density multiplier (n+1)/(zeta(2)n).
D is multiplication by 1/n. The reciprocal multiplier 1/(n+1), sometimes
locally called B in older physical-response modules, is a different operator.

The exact signed identity is

```text
S_N = H_N r + E_N.
```

The existing centered-leakage theorem gives the finite complete bound
`M = sum_k ||h_k - r/(zeta(2)k)|| < infinity`. Therefore

```text
||E_N|| <= M
H_N ||r|| <= ||S_N|| + M
H_N -> infinity.
```

Consequently `1 not in V` implies `||S_N|| -> infinity`. This is divergence
of the norm of the vector sum, stronger than divergence of the sum of norms.
It excludes conditional convergence through cancellation for this specific
arithmetic leakage series.

The following conditions are equivalent in Lean:

- There is one real C such that for every J there exists N >= J with ||S_N|| <= C.
- The leakage vector series is summable.
- The leakage norms are summable.
- 1 belongs to V.
- V is the complete Q Hilbert space.

Every one of these conditions implies RH through the existing target bridge.
The existence of the common bound is **Open**. No analytic RH-to-density
converse is assumed in this chain, and no unconditional RH proof is claimed.

All declarations below are in `RiemannResearch.RH.QDensityLeakageSeries`:

| Declaration | Exact role |
|---|---|
| `partialLeakage_exact` | Signed harmonic residual identity |
| `centeredPartial_norm_le` | Uniform complete bound for the centered remainder |
| `harmonicMass_nonneg` | Positivity of the finite harmonic mass |
| `harmonicMass_tendsto_atTop` | Unconditional harmonic divergence |
| `partialLeakage_lower` | Lower bound retaining the full centered budget |
| `partialLeakage_norm_tendsto_atTop` | Escape if the constant target is absent |
| `frequently_bounded_partialLeakage_iff` | Cofinal boundedness iff constant-target membership |
| `summable_residue_leakage_iff` | Vector summability iff constant-target membership |
| `summable_residue_leakage_iff_summable_norm` | No conditional-only summability |
| `frequently_bounded_partialLeakage_iff_totality` | Cofinal boundedness iff V is the full space |
| `riemannHypothesis_of_frequently_bounded_partialLeakage` | Conditional RH reduction |

## Recent V-space progress retained from main

- Augmented density concerns both g_k and B g_k, or the damped generators.
  It does not establish density of g_k alone.
- The Q/P coupling has dense range and injective adjoint.
  Surjectivity is equivalent to finite dimensionality of the complement;
  neither property is supplied unconditionally.
- Distinct actual zeta zeros right of the critical line give independent
  functionals on the Q complement. Finite dimensionality would force only
  finitely many such zeros. Finiteness is not itself a proof that there are none.
- The normalized leakage tends to the actual constant residual.
- The finite provider criterion requires cofinal k_j and finite legal a_j with
  k_j ||B g_{k_j} - a_j|| -> 0. The arithmetic small-o estimate remains open.
- At the starting main, every prescribed-coefficient positive single-cutoff
  primorial lift has divergent P and Q source norms, while its D-image tends
  to D1 without a cofinality requirement on the cutoff. Uniformly bounded
  scalar rescaling loses the target and tends to zero after D.
- Even freely optimized single coefficients cannot repair eventually small
  cutoffs. These results leave signed multiscale corrections open.

## Recovered arithmetic versus open providers

The complete higher-prime-power weight is summable and at most one:
`sum_p sum_{k>=2} p^(-k) <= 1`. Finite distinct prime/depth admissions obey an
explicit logarithmic budget, and a sequence satisfying the stated one-step
energy bound obeys the corresponding polylogarithmic estimate.

The actual canonical one-step inequality `hstep` is an explicit hypothesis.
The recovered package does not prove it for the canonical CRT family.
The positive-relative-variation small-o premise, complete repair-budget times
residual-tail decay, and uniform physical half-head/screened-diagonal bounds
also remain **Open**.

Finite exact head interpolation and certified complete finite-conductor
energies establish finite statements. They do not supply a constant uniform
over every stage and physical site.

## Verification and provenance

The coherent eleven-theorem leakage candidate passed focused Bazel/BuildBuddy
verification in `job_mj8jc7NZr0UJRkczXtbs1dazYn3RsLHT`, with server elapsed
81.374 seconds:
https://app.buildbuddy.io/invocation/617dd8b6-09fd-4572-adc1-5e5773d052cb.

The retained sources are from
`ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_` and
`ws_cFM0TMufSAwwe3E2c9erVSCyB7rRsKaS`.
Three other Site-linked workspaces were inspected and were clean/published:
`ws_moPuhDmz30n2XrpD90BOu5Bo4rW7q6bg`,
`ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj`, and
`ws_yZDc-iUQ0cmg2dhNO2C_SkmCwnCTQu4k`.
Original retained workspaces are preserved.

The saved-module import audit and guarded transitive-axiom checks precede
the final managed full-project checkpoint. Publication requires successful
Bazel/BuildBuddy validation of `//:RiemannResearch`, including downstream
consumers and all source packages. Exact final checkpoint and publication
receipts are recorded in the synchronized Sites.

## Saved-source acceptance

All recovered modules and the saved leakage-series module passed the combined
Bazel/BuildBuddy import check in `job_7UICCHa6QtEF8hIGAoUMqkE-Un_vP6Km` (91.777 seconds).
The same successful run guarded the transitive axiom output of 40 declarations:
all eleven new leakage theorems and 29 recovered endpoints. Each reported only
`propext`, `Classical.choice`, and `Quot.sound`.

https://app.buildbuddy.io/invocation/6e80a2c2-8de3-4739-8165-5a28659d37af

The recovered proofs were repaired for the current import locations, explicit
matrix types and casts, finite enumeration, and elaboration of limits. Their
mathematical hypotheses were preserved. This checked recovery discharges the
paper-only gcd-cell mass/innovation formulas, noncanonical depth example,
oblique-lift example, and positive-relative-variation comparison recorded on
the research Sites. The rational energy enclosures retain their explicit
normal-equation hypotheses; further comparisons must retain their own scope.
