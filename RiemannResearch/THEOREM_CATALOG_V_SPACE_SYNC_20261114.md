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

## Cofinal subharmonic strengthening (15 November 2026)

The exact identity gives `abs (||S_N|| - H_N ||r||) <= M` at every N.
The common boundedness provider can be weakened to
`forall epsilon > 0, forall J, exists N >= J, ||S_N|| <= epsilon H_N`.
This allows candidate envelopes growing sublinearly relative to harmonic mass.
It is equivalent to `1 in V` and to full Q-space totality, and implies RH.
The actual arithmetic cofinal smallness premise remains **Open**.

Four new declarations in `RiemannResearch.RH.QDensityLeakageSeries`:

- `partialLeakage_norm_gap_le`: the two-sided norm error, keeping the full budget.
- `cofinal_subharmonic_partialLeakage_iff`: exact cofinal provider equivalence.
- `cofinal_subharmonic_partialLeakage_iff_totality`: full-space equivalence.
- `riemannHypothesis_of_cofinal_subharmonic_partialLeakage`: conditional RH consumer.

Source: user-requested triage continuation, 15 November 2026; deduction from
this module's signed identity. No analytic RH-to-density converse is used.
The coherent candidate passed Bazel/BuildBuddy job
`job_ku4WYfE-1eam1U8l0irVBMKxnylS4vcJ` in 52.32 server seconds:
https://app.buildbuddy.io/invocation/3c0b1f8a-584e-46f3-81e7-2b5209bc15ab.
This is a snippet receipt; saved-source axiom checks and full-project checkpoint
provide the separate publication gate. The synchronized triage Site retains
final commit and checkpoint evidence.


## Actual signed sums: partial progress and remaining gap (16 November 2026)

**The requested unconditional cofinal subharmonic bound remains Open.**
No target-membership premise was discharged. The following new results identify
the exact limit and prove a concrete unconditional range of slopes.

For N > 0, with all definitions and full Q tails unchanged,

```text
H_N^(-1) S_N - r = H_N^(-1) E_N
||H_N^(-1) S_N - r|| <= M/H_N
S_N/H_N -> r
||S_N||/H_N -> ||r||
<1,S_N>/H_N -> ||r||^2.
```

The complete energy equality is

```text
||S_N||^2 = H_N^2 ||r||^2 + 2 H_N <r,E_N> + ||E_N||^2.
```

Consequently a bounded centered remainder does not itself give a zero normalized
limit. The possible leading residual remains. Passing to a cofinal subsequence
does not change that limit.

There is genuine unconditional arithmetic partial progress: the finite legal
competitor qOdd = 2*g_2 has complete error norm 1/2, because the Q mass of positive
even integers is exactly 1/4. Therefore, at every N,

```text
||S_N|| <= H_N/2 + M.
```

For every epsilon > 1/2, the requested bound holds at every sufficiently large
stage, with threshold H_N >= M/(epsilon - 1/2). This does not establish the
quantifier over ALL epsilon > 0. The number 1/2 is a proved upper bound from
one competitor; it is not asserted to be optimal.

A more focused arithmetic target is now equivalent to the requested vector
condition:

```text
forall epsilon > 0, forall J, exists N >= J,
  <1,S_N> <= epsilon*H_N.
```

This is a one-sided signed bound, without an absolute value. Its equivalence is
proved; its actual arithmetic provider remains **Open**. It uses the fixed test
vector 1, rather than requiring a bound against every vector in the annihilator.

All new declarations are in RiemannResearch.RH.QDensityLeakageSeries:

| Declaration | Content |
|---|---|
| harmonicMass_pos | Positive normalization for N > 0 |
| normalized_partialLeakage_error_eq | Exact normalized error |
| normalized_partialLeakage_error_norm_le | Complete M/H_N error bound |
| normalized_partialLeakage_tendsto | Vector limit equals r |
| normalized_partialLeakage_norm_tendsto | Norm ratio limit equals ||r|| |
| partialLeakage_norm_sq_exact | Full signed energy expansion |
| qOne_inner_residual | Constant pairing equals residual energy |
| partialLeakage_mean_exact | Exact signed mean decomposition |
| partialLeakage_mean_gap_le | Mean error at most M |
| normalized_partialLeakage_mean_tendsto | Signed mean ratio tends to ||r||^2 |
| cofinal_subharmonic_partialLeakage_mean_iff | Conditional scalar criterion |
| cofinal_subharmonic_partialLeakage_iff_mean | Vector/scalar criterion equivalence |
| partialLeakage_norm_le_legal_certificate | Bound from any legal competitor |
| partialLeakage_norm_le_half_harmonic_add_budget | Unconditional parity bound |
| eventually_partialLeakage_norm_le_of_half_lt | Unconditional slopes > 1/2 |

The coherent fifteen-theorem candidate passed Bazel/BuildBuddy in
job_QgPWva4j-zGDEQsBC3qAh-Nc-2DCV-C5 (55.914 server seconds):
https://app.buildbuddy.io/invocation/f8b9b6dc-3142-495d-bce2-99a8ffc0c1bf.
Saved-source guarded axiom checks and the managed full-project checkpoint are
separate publication evidence recorded on the triage Site.

Source: user-requested continuation, 16 November 2026; deductions from the exact
leakage identity and complete parity mass. Bagchi, arXiv:math/0607733,
Theorem 1 and its equivalent-weight observation, support the classical
RH/density interpretation. No external estimate is imported as an axiom.

Next check: prove the displayed one-sided signed-mean smallness from the actual
arithmetic data, or construct finite legal competitors whose complete errors
approach zero with justified uniform tail bounds. Increasing a finite table,
using a bounded centered remainder, or assuming that the projection preserves
physical positivity does not supply that estimate.

## Finite rational certificate continuation (16 November 2026)

See [the finite-certificate catalog](THEOREM_CATALOG_LEAKAGE_RATIONAL_CERTIFICATES_20261116.md).
The leakage condition is now equivalent to a countable family of entirely finite
rational inequalities with complete tail budgets. The unconditional slope improves
to 19/100, including the eventual endpoint. The universal certificate provider is Open.
