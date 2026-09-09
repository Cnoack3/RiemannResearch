# RH chat formalization audit — 8 September 2026

## Verified continuation — 9 September 2026

The five preserved candidates in RH_Lean_Continuation_2026-09-09.zip have now
passed serialized Lean verification after repairs. They supply 41 public
theorems in six new modules. The combined packaging and representative axiom
check succeeded as job_nExKbVWLTN-2hCeKRL3FgNdi9MNwbOyZ, exit code 0,
verified true (6.720 seconds). All six representative axiom reports list only
propext, Classical.choice, and Quot.sound.

| Module | Theorems | Exact scope |
|---|---:|---|
| RH/ConductorBoundedReciprocal | 6 | Actual conductor-symbol lower bound, positive gap, uniform reciprocal bound, and convergent exact geometric reciprocal series for n>1 and Re(s)<1. No L² operator/support theorem. |
| RH/ParetoApproximationRatio | 3 | Complete Pareto error decomposition, exact mean normalization, and equivalence of arbitrarily small approximation error and noise/signal ratio in a scalar-closed bounded-function class. Neither approximation property is asserted to hold. |
| RH/ParetoFiniteSchur | 20 | Actual complete Pareto Gram optimizer, mean preservation, exact signed covariance remainder, Schur value, and joint coefficient/scale optimum. The Gram linear equivalence and its coordinate identification remain explicit hypotheses. |
| Analysis/CountableLaplaceDetector | 10 | Countable entire zero set, a real tilt avoiding it at a specified countable spectrum, actual normalized bump and transform shift, and existence of a smooth compact detector. |
| RH/CountableTiltDetector | 1 | A nonzero smooth compact test annihilating 0 and 1 and detecting every member of a specified countable set excluding 0 and 1. Does not claim a whole-strip zero-free transform. |
| RH/SingleZetaDetectorCriterion | 1 | Conditional actual RH criterion requiring detection only at actual strip zeta zeros; tail L², support, exact transform cancellation, and subpower growth remain explicit. |

The countable-detector construction supersedes only the detector-existence
gap for a specified countable spectrum. The actual-zeta-zero countability
specialization and its connection to the criterion remain Open here. The
original infinite-convolution whole-strip detector remains unformalized.
The Nyman–Beurling equivalence, the genuine L² conductor inverse/support
realization, and the mixed optimizer's analytic providers remain Open.
Subpower growth and all-scale variance/signal convergence remain
mathematically unproved. No unconditional RH result is claimed.

Recovery preserved the retained workspace and verified all nine package
checksums. The initial workspace was clean at 454a2ef, while GitHub main was
126b563 (one newer commit). Workspace sync restored the saved publication
commit; it did not advance HEAD. The checkpoint containing this report must
fetch origin/main, integrate in a clean clone, revalidate affected modules,
and publish without force-push. Its terminal result is the authority for
project integration/publication; the snippet result alone does not certify
the newer GitHub tree. Existing unrelated work is not replaced.

Repairs corrected an import from Analysis/PoleCancellationTransform to its
actual RH location, restricted logarithm simplification, used explicit
function equalities for HasSum, unfolded finite combinations/let-bound
residuals, and specified the scalar function in HasCompactSupport.smul_left.
The last change eliminated the detector elaboration timeout at the normal
heartbeat allowance. HTTP 504 on a source read was distinct from successful
verification jobs.

---

This report covers the user-provided discussion and
`RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md`.
It supersedes the earlier interrupted verification audit.

**The discussion is not completely Lean formalized.** This change adds 39
public proved theorems in ten Lean modules (nine new modules and one extended
module). The selected proofs have passed remote Lean snippet verification.
Repository validation and publication are recorded by the checkpoint containing
this report. No unconditional proof of RH, detector-existence theorem, or
subpower-growth theorem is claimed.

## Verification evidence

Base commit: `36ff009985eb1d16298b6c47c63aa29f378dee49`.

Successful serialized verification jobs:
- `job_vfvocA45RYwi3pB0texQM8iR1lnSxn-I`: pointwise bridge, binary error,
  general means, forced Möbius head, finite and infinite Green identities.
- `job_oXntbBawiEy7nTThutuRvBlK3MtHrU8D`: reciprocal-moment cancellation,
  Ramanujan gcd formula, general subpower-tail obstruction.
- `job_4e6ET0KNRGwnzBIQfHfjPFHClFexBS-l`: actual uniform law, finite norm
  identity and finiteness bounds, standard RH/strip bridge and final conditional
  RH criterion.

All returned `verified: true`, exit code 0. Representative `#print axioms`
checks for each group reported only `propext`, `Classical.choice`, and
`Quot.sound`. The new proofs contain no `sorry`, `admit`, project axioms,
or unsafe proof shortcuts. Standard axioms do not discharge explicit
hypotheses. Fresh checks of these additions do not by themselves constitute
an independent re-audit of every older module.

## Claim-by-claim status

| Discussion claim | Status and exact scope |
|---|---|
| `K=floor(1/U)` has probabilities `1/(k(k+1))` | Newly proved for the actual Lebesgue probability measure restricted to `(0,1]`, all natural `k`, including zero mass at `k=0`. This has the same law as uniform `(0,1)`. |
| Fractional-part Nyman function equals `(K mod n)/n` | Newly proved pointwise for `u>0`, `n>0`. |
| Nyman and Pareto squared errors coincide | Newly proved for every finite positive-conductor combination, using the actual nonnegative Lebesgue integral and complete infinite Pareto series, including all cross terms. An explicit finite upper bound is also proved. |
| `E(K mod n)=log n` | Newly proved for every `n>0`, by an exact finite harmonic identity and its limit. |
| `E J_q = vonMangoldt(q)` | Newly proved for every natural `q`; prime powers and non-prime-powers are specialized. Thus mixed conductors have zero mean. |
| Packet increments are negatives of Ramanujan sums | Newly proved for `q>1` and positive increment index; also identified with the gcd-divisor formula. The `q=1` increment formula is excluded. |
| Green Gram formula | Newly proved with exact finite boundary subtraction `1/(N+1)`; the full infinite inner product equals this finite expression plus the genuine summable Pareto tail. |
| Mixed two/three exact head matching forces `e_m=mu(m)` | Newly proved for the actual arithmetic synthesis from two coefficient sequences and the stated head constraints. Finite-divisor uniqueness is also proved. |
| Synthesized coefficients have support through `3M` and `A_M(1)=0` | Newly proved under finite input-support assumptions, including explicit reciprocal-sum cancellation. |
| Binary optimum is `1-log 2` | Newly proved over the complete Pareto measure, with exact quadratic error and minimizer. The displayed decimal is not an interval certificate. |
| Remote tail energy lower bound | Existing actual analytic providers were source inspected: `Analysis/RemoteLaplaceTail`, `RH/NymanActualTailEnergy`, and `RH/NymanCompletionAdmissibility`. The actual one-conductor family has proved L², support and signature providers under the stated smooth compact seed assumptions. |
| Single-test subpower criterion implies RH | Newly proved conditionally for an arbitrary actual tail family. It concludes Mathlib's `RiemannHypothesis`, using the newly proved equivalence with the actual open-strip formulation and existing zeta reflection. All five substantive hypotheses below remain explicit. |
| A smooth compact fixed test detecting the whole strip exists | Not yet formally connected to the infinite-convolution construction in the supplied note. The criterion assumes transform nonvanishing and does not construct this test. |
| Classical integer-dilation Nyman approximation criterion is equivalent to RH | Not yet formalized or located by this audit. This is a known mathematical theorem requiring formalization; the new exact norm transfer does not establish that equivalence. |
| Complete returns preserve the signed Weil obstruction | Existing source-confirmed providers include `NymanFullReturnWeilNullity`, `NymanActualTailWeilAccounting`, `ActualArithmeticTailExistence`, and `WeilSpectralPairing`. Their actual analytic hypotheses and full signed arithmetic terms are retained. |
| Prime-square compensation and its limits | Existing source-confirmed providers in `NymanBroadPrimeSquareCompensation`, `NymanBroadSquareAsymptotic`, and `NymanBroadPrimeAsymptotic`; no independent positivity theorem follows just from compensation. |
| Optimal scaling gives `V/(S²+V)` | Existing source-confirmed `ParetoNoiseSignal` proves the actual infinite-measure identities for bounded functions with nonzero mean. |
| Covariance and residue-weight calculations retain all terms | Existing source-confirmed `ParetoCovariance`, `ParetoFiniteGram`, and `ParetoPeriodicRegrouping` provide scalar covariance optimization, full finite Gram expansion, and exact periodic weighted regrouping. A general block Schur-complement optimizer must still be identified for any particular packet space. |
| CRT coordinates are not independent under the Pareto law | Existing exact progression weights, positivity, normalization and compatibility were source inspected. The leading-atom bound specializes to `W_Q(1)>=1/2`; replacing these weights by uniform product measure is not justified. |
| Larger decimal examples `0.095748`, `0.078293` | Floating numerical illustrations; not interval certified here. |
| Bounded conductor inversion, spectral norm identity, and leftward support argument | Not fully audited/formalized as a connected result here. The new finite reciprocal identity is a distinct algebraic result. |
| Subpower growth, or optimized variance/signal² tending to zero | Mathematically unproved research targets in the original discussion. No such unconditional assertion is added. |

## Exact conditional RH obligations

`RiemannResearch.RH.riemannHypothesis_of_single_subpower_tail_test` uses a fixed
function `f : Real -> Complex`, actual tails `tau M : Real -> Complex`, and
a real support origin `a`. Its assumptions are:

1. Each actual tail belongs to Lebesgue L².
2. Each tail vanishes before `a+log(M+1)`.
3. At every actual zeta zero in the open strip, the tail's actual centered
   transform equals the negative transform of `f`.
4. The centered transform of this one `f` is nonzero everywhere in the strip.
5. For every positive epsilon, tail energy multiplied by
   `exp(-epsilon*log(M+1))` tends to zero.

The analytic helper proves that (1), (2), (3), and (5) force a fixed transform
signature at any right-of-line point to vanish. Assumption (4) then excludes
such zeros, and actual zeta reflection excludes left-of-line zeros. The
standard RH/strip bridge discharges boundary and trivial-zero formulation
differences using existing actual completed-zeta and Gamma-factor providers.

This is a proof of an implication. It supplies none of the five hypotheses
for the particular mixed optimizer. Existing one-conductor tail providers
must not be silently used as identification of the two-conductor optimizer.
No converse from RH to that optimizer's growth estimate is proved.

The compact detector still needs a connected formal construction of its
limiting distribution, smooth compact density, convergent product transform,
nonvanishing, tilt, and pole-annihilating differential operation. The paper's
specific detector also sees artificial nonreal zeros of a single conductor
on `Re(s)=1`; a canonical single-conductor subpower hypothesis is therefore
not substituted for the mixed-conductor target. This last observation has
not been packaged as a Lean no-go theorem for the unformalized detector.

## New declaration inventory

Counts exclude definitions, instances, and private helper lemmas.

| Module | Public theorems | Declarations |
|---|---:|---|
| `Analysis/SubpowerTailObstruction` | 1 | `signature_eq_zero_of_supported_subpower_tail` |
| `RH/NymanInverseMobius` | 8 | `finite_divisor_sums_force_moebius`; `nymanConductorSynthesis_apply`; `nymanConductorSynthesis_eq_moebius_return`; `nymanTwoThreeSynthesis_forced_moebius_head`; `nymanConductorSynthesis_zero_above`; `nymanTwoThreeSynthesis_zero_above`; `nymanConductorSynthesis_reciprocal_sum`; `nymanTwoThreeSynthesis_reciprocal_sum` |
| `RH/ParetoBinaryApproximation` | 3 | `paretoError_scale_residue_two`; `paretoError_residue_two`; `paretoError_residue_two_minimizes` |
| `RH/ParetoNymanPointwise` | 2 | `fract_div_sub_fract_div_eq_floor_mod`; `pareto_nyman_pointwise` |
| `RH/ParetoPacketGreenGram` | 5 | `ramanujanPacket_increment`; `ramanujanPacket_prefix`; `ramanujanPacket_green_gram`; `ramanujanPacket_green_gram_with_tail`; `ramanujanSum_gcd_divisors` |
| `RH/ParetoResidueMean` | 5 | `residue_partial_sum_harmonic`; `paretoMean_residue`; `paretoMean_ramanujanPacket`; `paretoMean_ramanujanPacket_of_not_isPrimePow`; `paretoMean_ramanujanPacket_of_isPrimePow` |
| `RH/SingleTestTailCriterion` | 1 | `riemannHypothesis_of_single_subpower_tail_test` |
| `RH/ParetoUniformLaw` | 10 | `reciprocalFloor_measurable`; `uniformUnit_univ`; `reciprocalFloor_fiber`; `uniformUnit_reciprocalFloor_mass`; `reciprocalFloor_map_mass`; `reciprocalFloor_zero_fiber`; `reciprocalFloor_map_zero_mass`; `reciprocalFloor_map_mass_all`; `uniformUnit_lintegral_reciprocalFloor`; `uniformUnit_lintegral_square` |
| `RH/ParetoNymanNorm` | 3 | `nyman_finite_lintegral_error`; `nyman_finite_lintegral_error_le`; `nyman_finite_lintegral_error_lt_top` |
| `RH/RiemannHypothesisStrip` | 1 | `riemannHypothesis_iff_strip_zeros_on_line` |

All modules are exported by `RiemannResearch.lean`. Pareto theorem names
use namespace `RiemannResearch.RH.Pareto`; the analytic helper uses
`MeasureTheory.RemoteLaplaceTail`; the RH formulation and criterion use
`RiemannResearch.RH`. The extended Nyman declarations remain in their
existing module namespace.
