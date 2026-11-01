# Conditional-iid Pareto / Cesàro agenda: Lean continuation

Date: 1 November 2026.
Source: user-provided `Conditional_IID_Pareto_Cesaro_Research_Agenda_2026-11-01.md`.
Baseline inspected: `5041fdee7f073fcfa3d3c5377b1c235cf6bbeeb8`.

## Mathematical scope

The continuation connects the agenda's normalized lower-growth condition to the
existing actual-zeta obstruction. It also extends the explicit Möbius head to an
arbitrary repair conductor beyond the head, proves literal squarefree membership
when that conductor is squarefree, and retains deterministic signed averaging.

The physical quantities are
\[
q_t=2/((t+1)(t+2)),\qquad
E_j=\sum_{t\ge1}q_t|(CF_j)(t)|^2/|c_j|^2.
\]
The hypotheses require deterministic finite legal functions, exact positive heads
\(F_j(n)=c_j\ne0\) for \(1\le n\le H_j\), and \(H_j\to\infty\).
There is no bound away from zero on the sequence \(|c_j|\).

## Added declarations

- `Analysis/LowerLogGrowth.lean`: `lowerLogGrowth`,
  `lowerLogGrowth_eq_zero_iff`, and
  `no_positive_power_floor_of_lowerLogGrowth_zero`.
  The lower limit uses extended nonnegative reals, retaining +∞.
  It equals zero precisely when arbitrarily small positive growth thresholds
  occur cofinally. For nonnegative energies and cofinal heads, the ratios are
  eventually nonnegative, so this implements the ordinary extended lower limit
  in the manuscript without a real-valued unbounded-infimum convention.
- `RH/ConditionalMeanNormalization.lean`:
  `conditionalMeanSquare_mul` and `conditionalMeanSquare_normalize`.
  The latter is the exact scaling identity
  `conditionalMeanSquare(F/c) = conditionalMeanSquare(F)/|c|²`. Legal membership supplies summability in applications.
- `RH/ConditionalMeanLowerGrowth.lean`:
  `riemannHypothesis_of_cofinally_small_conditionalMean_heads`,
  `normalized_exact_head_polynomial_obstruction_eventually`,
  `riemannHypothesis_of_cofinally_small_normalized_conditionalMean`, and
  `riemannHypothesis_of_lowerLogGrowth_normalized_conditionalMean_zero`.
  The conclusions use Mathlib's actual `RiemannHypothesis`.
- `RH/SquarefreeMobiusCesaroHeads.lean`:
  `squarefreeMobiusHead_exact`,
  `squarefreeMobiusHead_mem_divisorSpan`,
  `exists_squarefreeMobiusHead`,
  `squarefree_mobius_prefix_coefficient_ne_zero`,
  `squarefreeMobiusHead_average_exact`,
  `squarefreeMobiusHead_mem_legal`,
  `squarefreeMobiusHead_prefix_exhaustion`, and
  `riemannHypothesis_of_mobiusHead_lower_growth`.

For the explicit family, the exact formula is
\[
F_{H,D}(n)=-\sum_{d=1}^{H}\mu(d)g_d(n)
             +D\left(\sum_{d=1}^{H}\frac{\mu(d)}d\right)g_D(n).
\]
The conductor-one term vanishes. If \(H<D\), the head is exactly one.
If \(D\) is squarefree, the function lies in the literal finite residue span of
a squarefree common primorial period. Composite squarefree terms are included.
The sufficient RH consumer also works with arbitrary positive repair conductors;
squarefreeness is an additional established property of the designated family.

## Existing agenda coverage inspected

The following are existing declarations, not newly authored results:

| Agenda component | Existing source |
|---|---|
| Finite summation by parts, terminal boundary, inversion | `Analysis/CesaroFiniteCalculus.lean` |
| Actual weighted contraction | `Analysis/CesaroWeightedContraction.lean` |
| Actual continuous dual functional | `Analysis/ConditionalMellinFunctional.lean` |
| Normalized generator pairing and removable value at one | `Analysis/MellinNormalizedResidue.lean` |
| Exact head/tail obstruction and polynomial lower bound | `RH/ConditionalMeanHeadObstruction.lean`, `RH/ConditionalMeanTailObstruction.lean`, `RH/ConditionalMeanSubpolynomial.lean` |
| Finite residue means | `RH/CesaroResidueMean.lean` |
| Conditional-iid moment criterion and sample-error limit | `RH/ConditionalIIDNymanCriterion.lean` |
| Probability, operator, and matrix continuation manifest | `RH/Conditional_IID_Cesaro_Lean_Continuation_2026-09-17.md` |

The existing September continuation records the common mixture, conditional
independence, exchangeability, endpoint recovery, strong law, and finite
optimization infrastructure. This continuation does not freshly reverify every
probability module or assert that every sentence of the new agenda is covered.

## Conditional research reductions and Open providers

The growth-based RH endpoints are **conditional research reductions**.

- **Open:** construct a deterministic legal cofinal family with zero lower
  logarithmic growth exponent in its normalized complete Cesàro energy.
- **Open:** prove that the explicit Möbius family or a deterministic finite
  repair average meets that condition.
- **Open in this continuation:** formalize and provide the localized dyadic
  estimate of agenda Section 8.3 for an actual legal family.
- **Not supplied here:** a new Lean proof of the classical RH-to-density
  direction. The new sufficient criteria do not assume that converse.

Exact heads, complete finite squarefree support, sampling variance reduction,
and finite computations do not discharge any of the growth providers.
No signed cross term is dropped in the new energy identities.

## Verification history

All three queued development jobs terminated with a wall timeout and exit code -9.
They returned build/import output, not a successful proof receipt:

| Job | Scope | Server-reported wall duration |
|---|---|---:|
| `job_b8Icw4eIc4O72OfZqBApkS0K95Vfw7KH` | First combined candidate | 300.062 s |
| `job_ptPl42RcLf0ws2eVgEIO8sguU3V3uvtm` | Assembled normalized criterion | 600.050 s |
| `job_2FR_Yom_UquRchtxhBnbubEGPpsyfeX4` | Saved LowerLogGrowth module | 300.099 s |

A subsequent diagnostics call returned `partial: true`, `timed_out: true`,
and `still_elaborating_lines: [[1,61]]`, with no diagnostic items.
Its follow-up returned a network timeout. A later job inventory confirmed
all three queued jobs terminal, with no queued job left over.

These durations are whole verification-job wall times, including dependency
preparation; they are not measurements of kernel proof checking alone.
The initial workspace-opening request also incurred a separate delay, which
was not instrumented precisely. Queued jobs were admitted at queue position
one and reported starting almost immediately; polling delays are separate.

The final saved-project checkpoint receipt, if successful, is the publication
gate and supersedes these failed development attempts as certification of the
published files. Without that receipt, the added declarations remain
unverified candidates. No successful result is inferred from these timeouts.

### Successful saved-module development validation

After the timeouts, checkpoint `job_OGJvmAmcB6y2x-m9PvF5TAV2J3BYTeEB`
returned actionable compiler diagnostics in 69.267 seconds. Two function-space
scalar coercions were repaired using `Pi.smul_def`. The subsequent saved-file
check `job_-EElyiO__xTOLJKbFUMVpInXYRdCda5a` compiled the RH consumer and
identified one remaining conductor-one simplification, repaired using
`Nat.mod_one`.

The complete saved-module import and axiom audit then **succeeded**:

- Job: `job_oy3RLG6hGNnxMZvHpQUWjSOBlmq6CoQ-`.
- Result: `classification: success`, `exit_code: 0`, `verified: true`.
- Server-reported whole-job duration: 11.698 seconds.
- Scope: import of `RH/SquarefreeMobiusCesaroHeads.lean`, its three new
  module dependencies, and the following five principal axiom inspections:
  `riemannHypothesis_of_lowerLogGrowth_normalized_conditionalMean_zero`,
  `exists_squarefreeMobiusHead`,
  `squarefreeMobiusHead_prefix_exhaustion`,
  `riemannHypothesis_of_mobiusHead_lower_growth`, and
  `conditionalMeanSquare_normalize`.
- Every inspected endpoint depends only on `propext`, `Classical.choice`,
  and `Quot.sound`. No admitted proof or project-local axiom is present.

This supersedes the earlier development timeouts. The separate successful
publication checkpoint is still the required certificate for the final saved
project and published commit; its receipt accompanies the published revision.
