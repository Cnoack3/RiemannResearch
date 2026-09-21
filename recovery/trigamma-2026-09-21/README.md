# Trigamma Lean recovery — verification evidence

This recovery branch preserves the work from the trigamma mean-point and DPP midpoint discussion. At the user's request, this update records verification evidence only. The recovered Lean sources, restoration patch, and ZIP archive are unchanged; no module integration or successful publication checkpoint is claimed.

The original archive was committed at `d857b9afd54c613636d1203e83d48d8d5aac919c`. The subsequent evidence note was committed at `26c2cf68af87924c39e3c7f4ec09c0d5402f4d35`. This record supersedes the earlier verification-status statements, including those preserved inside the unchanged archive.

`RH_Lean_Recovery_2026-09-21.zip` contains:

- Four Lean proof-candidate modules as originally recovered.
- The research note, including the signed Mobius trial and unresolved tail estimate.
- A restoration patch, source hashes, verification history, and recovery instructions.

The recovered workspace is based on commit `8f9bec2691b96631b046ea2791943ca5a2dfd358`, whose declared toolchain is `leanprover/lean4:v4.33.0-rc2`. The checks below used that resumed workspace and its dependencies. The three full-file checks reported source hashes identical to the archive manifest.

## Current status — 21 September 2026

**Only `FiniteMatrixInverseComparison` receives a new promotion among the three previously unverified modules. Its status is file-verified, not checkpoint-verified.**

| Module | Supported status | Evidence and limits |
| --- | --- | --- |
| `FiniteMatrixInverseComparison` | **File-verified: unchanged recovered source.** | Full-file check succeeded with exit code 0 and `verified: true`. All eight theorem declarations also passed an axiom audit using only standard Lean axioms. |
| `CRTTrigammaMeanValue` | **Draft: compiler errors confirmed.** | Full-file check returned `compiler_error`, exit code 1, `verified: false`. Its mathematical statements are not refuted by these compiler errors. |
| `ProgressionMidpointInverse` | **Draft: compiler errors confirmed.** | Full-file check returned `compiler_error`, exit code 1, `verified: false`. Its mathematical statements are not refuted by these compiler errors. |
| `NonnegativeResidueObstruction` | **Prior successful module build reported; two endpoint declarations axiom-audited.** | The old checkpoint recorded a successful module build. This audit additionally checked the axioms of two imported endpoint declarations. No fresh full-file rebuild of this module was performed. |

The old checkpoint is now known to be **terminal and interrupted**. No successful final checkpoint audit, integration, or verification publication was recovered. The entire bundle must not be called verified.

## Exact source and check evidence

These are the full SHA-256 values returned by the new full-file checks; each matches its recovery-manifest entry.

| Project-relative source | Checked SHA-256 |
| --- | --- |
| `RiemannResearch/LinearAlgebra/FiniteMatrixInverseComparison.lean` | `0ca43b32bd48286ce1cc837e35197257b952a323a0b6216f96ec2730e209be2a` |
| `RiemannResearch/RH/CRTTrigammaMeanValue.lean` | `3018f8270efe67d90897c240416cf76b458ddb06ce4636ab6a632d5e93624fbb` |
| `RiemannResearch/RH/ProgressionMidpointInverse.lean` | `9e097ffa5f5ae843a45424565e694e48cdbb332bb5b109f9d2478cdaec5feb57` |

The archived `RH/NonnegativeResidueObstruction.lean` manifest hash is `4218c163883d6a4f34e89fe4fd315de72ff18d5f260dae7d310a2157353b1662`. This manifest hash is not presented as a new full-file check result.

All three new file checks reached terminal states:

| Source | Job ID | Terminal state / classification | Exit code | Check duration | Finished (UTC) |
| --- | --- | --- | --- | --- | --- |
| `FiniteMatrixInverseComparison.lean` | `job_0PpnOvB_iWhVrBPX4ZlmCL7kADAB1Xvh` | `succeeded` / `success` | 0 | 41.523 s | 2026-09-21T04:36:58.683Z |
| `CRTTrigammaMeanValue.lean` | `job_5_2O2jfAHh_HfJrjaXIERjSuHs_n6XiX` | `failed` / `compiler_error` | 1 | 3.026 s | 2026-09-21T04:38:51.995Z |
| `ProgressionMidpointInverse.lean` | `job_L5_GtVbeO3pUspj9wuh-T04s_-GlHGZf` | `failed` / `compiler_error` | 1 | 6.464 s | 2026-09-21T04:38:10.999Z |

Each used a 300-second timeout. The finite inverse check returned no diagnostics. The two failed checks returned compiler diagnostics rather than HTTP 504 or wall-timeout results. Verification submissions were serialized after establishing that the old checkpoint had terminated.

## Compiler failures preserved without repairs

`CRTTrigammaMeanValue.lean`:

- Lines 38–50: the `HasSum` conversion generated an equality between real additive-monoid instances; `funext` and `unfold digammaSlope` then targeted incompatible goals, with an unsolved sum-value equality.
- Lines 60–63: positivity obligations were not discharged.
- Line 218: `positivity` was applied to a goal it did not recognize as a positivity goal.
- Lines 247 and 250: tactics were invoked after all goals had been solved.
- Lines 299 and 316: the reciprocal-limit and square-root-limit expressions did not elaborate to the required `Tendsto` statements.

`ProgressionMidpointInverse.lean`:

- Line 45: `simp` made no progress.
- Line 89: `PosDef` field lookup on an unannotated function failed with `Function.PosDef`.
- Line 102: the `Finset.single_le_sum` expression did not elaborate to the required dot-product summand.
- Line 109: `mul_le_mul_left hp` resolved to an incompatible theorem/type; field lookup for `mp` also failed.
- Line 138: Lean emitted a downstream "declaration uses sorry" warning after the errors. The recovered source contains no literal `sorry`; this warning is not accepted as verification and is not evidence of a placeholder written into the archive.

No repairs were applied. The original diagnostics remain associated with the terminal jobs above.

## Axiom audit

Job `job_Hnu03iEt9WXfhb_D4mJBFphWwsToqUhG` completed at 2026-09-21T04:39:57.108Z with `state: succeeded`, `classification: success`, exit code 0, and `verified: true` after 18.208 seconds.

The ephemeral audit re-elaborated the unchanged `FiniteMatrixInverseComparison` source, imported `NonnegativeResidueObstruction`, and requested `#print axioms` for these declarations:

Under `RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix`:

- `gramQuadratic_nonneg`
- `inverseQuadratic_eq_energy`
- `inverseQuadratic_nonneg`
- `quadratic_objective_le_inverse`
- `gramQuadratic_smul`
- `inverseQuadratic_antitone`
- `inverseQuadratic_relative`
- `inverseQuadratic_eq_matrix_inverse`

Under `RiemannResearch.RH.CRTBlock`:

- `normalizedResidueSynthesis_nonnegative_tail_lower_bound`
- `normalizedResidueSynthesis_nonnegative_occupation_cap`

Every report listed exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or project-local axiom appeared in those dependency reports. The audit snippet SHA-256 was `c8a19907b2e952b9eddf88de813c6634d2c7fdcb4b99d5a95d35e04768debdfe`.

This audits the named declarations' axiom dependencies; it does not discharge hypotheses appearing in their theorem types. In particular, the finite inverse comparison retains positive-definiteness and quadratic-form-comparison hypotheses. The obstruction endpoints retain their nonnegative-coefficient and normalization hypotheses.

## Checkpoint and transport history

The earlier checkpoint `job_kn3SXMzhgaXJhGaWaKgVYiDYqoOT-DYh` had reported:

```text
state: running
current: 4152
total: 4153
detail: Built RiemannResearch.RH.NonnegativeResidueObstruction (7547s)
terminal: false
```

After that response, workspace resume, checkpoint-status retrieval, and job-list retrieval returned HTTP 504. No competing verification was submitted while the checkpoint's state was unknown.

On restoring access, its terminal result was recovered:

```text
state: interrupted
terminal: true
error: The job owner exited while this job was pending.
       Inspect workspace and Git status before submitting it again;
       it was not replayed.
```

The separate earlier `CRTTrigammaMeanValue` file check, `job_atBoGXboFTzpOYX80Z-yR-iS-AaHqywk`, had ended with `classification: wall_timeout`, exit code -9, `verified: false`, and no output after 600.102 seconds. That older timeout neither proved nor refuted the source. The later compiler-error result above now provides concrete diagnostics.

The original workspace token remains `ws_vtvPqH8WM2fKnuH5YO2on9FV4dl2GLnn`. No new checkpoint was submitted during this audit or evidence-only update. The source changes in that workspace were preserved.

## Mathematical scope

The verified finite inverse comparison proves its exact finite-dimensional statements under their explicit hypotheses. It does not establish arithmetic saturation.

The drafted midpoint comparison would transfer occupation convergence between exact and midpoint models; it would not itself prove either convergence. The drafted trigamma asymptotic is a fixed-residue statement, not a uniform growing-residue saturation theorem.

Capacity divergence, zero limiting vacancy, saturation, and RH remain unproved by this recovery work. Future promotion of either failed module requires a successful check of its actual revised source; the present user-directed action preserves the sources unchanged.

ZIP size: 28,486 bytes. Git blob SHA-1: `4b90b14a88eeb75790f788c4cedaea312b28d45f`.
