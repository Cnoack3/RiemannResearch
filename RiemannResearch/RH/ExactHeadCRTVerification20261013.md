# CRT proof recovery and Lean verification — 2026-10-13

## Verification

Recovered workspace: `ws_8mGWZfvEgM4mkcQCUvjzqZ-f3Ex2LutN`.
Base commit: `d01390749cf05f9481b868ba242d58bf06945dd7`.

The old queued job `job_e5PYFoNAU3e2gY8cb4SxO0aupoxBFpH5`
terminated as interrupted: its owner exited before compilation began.
The saved four-module source and aggregate exports remained intact.

Fresh combined import and axiom audit:
`job_CfF-ItEXLk9irhbBIdf40jU-kB3HtFhC`.
Result: succeeded, exit code 0, verified true, 19.168 seconds execution.
Submitted code SHA-256:
`1798e363fb178118056b5bc250deb68dfd9f76a0cd725af8165f97c04f71038c`.

Imported modules:
- RiemannResearch.Analysis.AffineObservationProjection
- RiemannResearch.RH.ExactHeadTailMoment
- RiemannResearch.RH.ExactHeadCRTExample
- RiemannResearch.RH.CanonicalMobiusErrorEnergy

All ten selected transitive axiom checks reported exactly the ordinary
foundations: propext, Classical.choice, Quot.sound. They covered the general
square completion, scalar prefix equivalence, finite legality, attained
minimum, full remainder, conditional RH consumer, all three explicit
M=1 example formulas, and PNT-backed normalized complete error limit.
The build produced style warnings but no compiler errors.

## Precise mathematical scope

With g_d(n)=(n mod d)/d, beta_M=sum_(d=1)^M mu(d)/d, M>0, and
a finite tail dictionary S of conductors d>M, put
F=-sum_(d=1)^M mu(d)g_d+sum_(d in S)c_d g_d.
The checked scalar characterization states:
F(n)=1 for 1<=n<=M iff sum_(d in S)c_d/d=beta_M.

In the complete Pareto Hilbert space, let T be the finite tail span,
z=1+sum_(d=1)^M mu(d)g_d, e the first-coordinate representer,
p=P_T z, and q=P_T e. For nonempty S, ||q||^2>0. The optimizer is
x*=p+((beta_M-<e,p>)/||q||^2)q, and every feasible x satisfies

    ||z-x||^2 = ||z-p||^2
                 + (beta_M-<e,p>)^2/||q||^2
                 + ||x-x*||^2.

No physical tail is truncated. The candidate has literal finite legal
support with an explicit conductor cap. Enlarging the dictionary cannot
increase the attained minimum.

## Open arithmetic premise

The exact type of riemannHypothesis_of_cofinally_bounded_tailMinimum
retains a nonempty finite dictionary schedule s, a real C, and the premise

    forall M, exists N, M <= N and tailMinimum (N+1) (s N) <= C.

This premise is Open. The unconditional canonical error-energy limit
E_N/N -> 0 does not prove this uniform bound or E_N -> 0.

The manuscript's specific constant-12 estimate, literal determinant,
fixed-anchor representation, and packaged unrestricted-infimum dichotomy
are not newly formalized here. The published RH-to-density theorem is
still an explicit analytic provider in the existing converse assembly.
It is not an axiom or hypothesis of the new finite optimization or its
bounded-minimum-to-RH implication.

## Publication gate — completed

The final server checkpoint was recovered and its terminal record inspected
on 2026-10-13:

- Job: `job_E8SG2DV7UeuZtjtHgYh3lbPhsF5Krxan`, kind `checkpoint`.
- Workspace: `ws_ZA4GigtIG0nd5-s_SNgoG3aOTA9irjqY`.
- Submitted: 2026-10-13 07:26:48.218 UTC.
- Finished: 2026-10-13 07:27:49.673 UTC.
- Terminal result: `state: succeeded`, `terminal: true`,
  `committed: true`, `pushed: true`.
- Both `commit` and `source_commit`:
  `85f1a6f673381dbde48f418a8b532e11d95b9c9b`.
- Request SHA-256:
  `ed614f99f62a4306ab3d07151b39c7d0371d4b35d55ae1fd8aaa62fcc52db579`.
- Build scope: `full`; reason: `the aggregate project module changed`.
- Recorded command: `lake build +RiemannResearch <4 changed module(s)> --quiet`.
- Targets: `RiemannResearch` and the four modules listed above.
  The target list is complete (`target_count: 5`, `targets_truncated: false`).
- Build elapsed time: 58.617 seconds; whole checkpoint: 61.454 seconds.
  Existing dependency and native project artifacts were reused. The
  `lake exe cache get` preflight completed with no files to download.
- `integrated_with_newer_main: false`: no additional integration occurred
  inside this final checkpoint; its input already contained the recovered
  modules on the newer published parent, as explained below.

This terminal result establishes successful server validation before
publication of [the exact commit](https://github.com/Cnoack3/RiemannResearch/commit/85f1a6f673381dbde48f418a8b532e11d95b9c9b).
The required gate was satisfied. The old pending wording recorded a
pre-publication state and is superseded by this result.

The earlier combined import/axiom audit and this aggregate checkpoint are
different evidence: the former checked ten selected transitive axiom
dependencies; the latter validated the integrated aggregate and all four
explicit changed-module targets before pushing. Full scope here means an
incremental aggregate-project validation with cached artifacts, not a clean
rebuild or a claim about every unexported file or later main revision.
The terminal checkpoint schema has no separate numeric build exit-code
field; its successful result and publication fields are the evidence.
The numeric exit code 0 above belongs to the earlier import/axiom job.

An empty GitHub combined-status list is not evidence either for or against
this server gate. GitHub-hosted CI is not the repository's verification path.

## Integration recovery

The original checkpoint job_XC6GGr4zcK9KAcoiTm7S6xu9jlPcuOZM
created local commit 3df946d873ac3de4140cc49ca945abdf755780ab, then
failed while integrating newer main because both the aggregate imports
and theorem catalog had concurrent edits. Nothing was pushed by that job.
The original workspace and commit remain preserved.

The same four modules were carried into workspace
`ws_ZA4GigtIG0nd5-s_SNgoG3aOTA9irjqY`, based on published commit
`c7306f6dabafe0cf7ede9250f5f8775f507fcb08`. Existing newer exports and
catalog entries were retained. The successful final checkpoint above
validated and published this combined source.

## Source and integration comparison — 2026-10-13

The retained original workspace is clean at local commit
`3df946d873ac3de4140cc49ca945abdf755780ab`. Its complete four source files
were compared with the complete added-file patches and blob identities in
published commit `85f1a6f673381dbde48f418a8b532e11d95b9c9b`.
All four contents are identical, including imports and proof bodies.

Paths below are relative to `RiemannResearch/`.

| Module | Lines | Published Git blob SHA-1 | Comparison |
| --- | ---: | --- | --- |
| `Analysis/AffineObservationProjection.lean` | 119 | `d5d673fa75d2ec63dc6ab7764a5f3fa579811e34` | Identical |
| `RH/CanonicalMobiusErrorEnergy.lean` | 45 | `d8d806ada0af800cef29529509850bdf6f4dd45f` | Identical |
| `RH/ExactHeadCRTExample.lean` | 106 | `c54f7004c5f59293b7d03a9a9d5cbbcb8cc8cc53` | Identical |
| `RH/ExactHeadTailMoment.lean` | 403 | `85671bd4120528fd9eb2bc28a1c779c949ff2db0` | Identical |

The [comparison between the original and recovery bases](https://github.com/Cnoack3/RiemannResearch/compare/d01390749cf05f9481b868ba242d58bf06945dd7...c7306f6dabafe0cf7ede9250f5f8775f507fcb08)
contains three commits. It adds fifteen Lean modules and their fifteen
aggregate imports, two reports, and catalog entries. It modifies no
pre-existing child Lean module or dependency configuration. Consequently,
there is no intervening edit to an existing dependency of the four recovered
proofs. The expanded aggregate import environment was an integration change
requiring validation, and the final full-scope checkpoint supplied it.

Relative to its recovery parent, publication adds the four recovered Lean
files, four aggregate imports, this report, and the relevant catalog entry;
it removes no lines. GitHub records the parent as
`c7306f6dabafe0cf7ede9250f5f8775f507fcb08` and the published tree as
`950ad7717f0c60e4db7433c9bd4f8ecb9fda5401`.
There is no additional unvalidated integration step in the successful
checkpoint record.

## Reconciliation outcome

No further Lean compilation is required to establish the historical
verification gate. This reconciliation changes documentation only; it
preserves all Lean sources and the open arithmetic premise above. Its
documentation-only publication must not be described as a new mathematical
verification. The original failed checkpoint, successful module/axiom audit,
and successful integrated publication remain separately identified.
