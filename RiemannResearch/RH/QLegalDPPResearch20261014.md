# Legal-residue projection DPPs and the remaining arithmetic convergence problem

Date: 14 October 2026. Source: the user's proposal to construct DPPs from legal
residue projections, use CRT, and investigate floors of zero ordinates times
prime logarithms.

## Checked construction and exact probabilities

Write H = L²(Q) in the project's actual weighted sequence realization,
g_d = qResidue d, and e_r = normalizedDivisorWavelet r. The complete arithmetic
Hilbert basis is reused; e_1 = qOne and ||qOne||² = 1.

For any orthogonally projectable subspace S, define

    L_S(r,s) = <P_S e_r, P_S e_s>.

Both every finite principal matrix and its complement are positive
semidefinite, by the existing projection Gram identities. The existing
positive-contraction/projective-limit constructor therefore supplies an
actual probability measure modeLaw S on positive divisor labels -> Bool.
No DPP, coupling, RH, or legal-density hypothesis is assumed.

The full legal stage is span{g_2,...,g_(n+1)}. The squarefree stage is the
existing squarefreeAtom walk: nonsquarefree conductors contribute zero atoms.
Both finite stages have orthogonal projections. Their laws fullLaw n and
squarefreeLaw n are constructed unconditionally.

The DPP sites are wavelet labels. Site 1 is the target constant mode, not the
physical integer 1 in the earlier counting-coordinate DPP.

For either legal stage, put p_n = Prob(site 1 occupied). The exact identity is

    1-p_n = Prob(site 1 vacant) = ||qOne-P_n qOne||².

For every F in the same stage the complete signed-error decomposition is

    ||qOne-F||² = Prob(site 1 vacant) + ||P_n qOne-F||².

Thus any proved full-Q trial-error estimate controls the vacancy. The theorem
fullOccupation_tendsto_one_of_trial_error formalizes this implication. A
pointwise head estimate is not its norm hypothesis.

For the full stage let b_i = <qOne,g_(i+2)>,
C_ij = <g_(i+2),g_(j+2)> - b_i b_j, and I_n = b^T C^(-1)b.
The genuine inverse and its invertibility are reused, giving exactly

    p_n = I_n/(1+I_n).

For the possibly redundant masked squarefree dictionary, the existing
projection-based capacity is used, rather than a singular matrix inverse:

    p_n = capacity_n/(1+capacity_n).

Both occupation sequences are monotone. The full sequence converges
unconditionally to ||P_closure qOne||². Both p_n -> 1 assertions are equivalent
to membership of qOne in the corresponding literal legal closure, and are
sufficient for Mathlib's RiemannHypothesis via the existing Mellin obstruction.
No RH-to-Q-density converse is claimed.

## An exact single-entry target

Any stage containing g_2 obeys the existing parity-wavelet identity

    e_2 = (3 qOne - 8 g_2)/sqrt(3).

Its complementary residual is sqrt(3) times the constant residual. Therefore
the complete constant-parity kernel block is

    [ p,                  -sqrt(3)(1-p) ]
    [ -sqrt(3)(1-p),       3p-2          ].

The actual probability that both labels are occupied is 4p-3. This implies
p >= 3/4 whenever g_2 is present. For both finite legal families p_n < 1,
because their full residual energy is strictly positive at every finite stage.

For both families the formal equivalence is

    L_n(1,2) -> 0  <->  p_n -> 1.

The two named consumers
riemannHypothesis_of_full_parity_kernel_tendsto_zero and
riemannHypothesis_of_squarefree_parity_kernel_tendsto_zero prove Mathlib RH
from the respective zero-limit hypothesis. These are conditional research
reductions. Establishing either actual arithmetic zero limit remains Open.

The earlier absolute-overlap theorem concerns diagonal complete-basis
cutoffs, finite subsets and diagonal tapers in physical counting coordinates.
A legal-residue projection is generally a dense operator in wavelet
coordinates. The earlier moving-physical-site bound does not prove this new
fixed-wavelet-label entry tends to zero.

## What the CRT route must actually prove

The checked squarefree equivalence is

    squarefree p_n -> 1
      <-> capacity_n -> infinity
      <-> SquarefreeExactHeadTailBound.

The final condition means there is one real C such that, for every M, there
are a squarefree common period L and F in the literal divisorResidueSpan L
with F(n)=1 for 1 <= n <= M and

    sum_(a=M+1,...,L) |1-F(a)|²/a² <= C.

The uniform bound, not simply CRT solvability on each finite head, is the
substantive Open obligation. Existing periodic estimates and weak closure
machinery convert this bound to legal density and hence to p_n -> 1. The
condition does not require an imposed period schedule or a decay rate.

The inspected concrete attempts retain the following checked obstructions:

- QPrimeSieve.primeConductor_fullError_ge_quarter gives a positive uniform
  lower bound 1/(4 zetaTwo) for the canonical uncorrected primorial sieve.
  Its fullError_not_tendsto_zero theorem already refutes that trial family.
- QCRTDivisorHead.candidate_exact_head supplies a density-repaired legal
  exact head, but candidate_fullError_lower retains the reflection term

      (1-L divisorDensity(L)/2)² / (zetaTwo L).

  Exact heads do not remove this term. No uniform-tail provider for this
  candidate was established in this continuation.
- QExactHeadEscape already supplies exact legal heads with escaping norm
  energy, showing why a pointwise construction cannot replace the norm bound.

These concern particular candidates and insufficient hypotheses. They do not
refute a different CRT construction or the legal-projection convergence target.

## Zero ordinates, floors, and equidistribution

The checked floor identity holds for arbitrary real inputs. For a prime p and
any assigned ordinate gamma(p), put x = gamma(p) log(p)/(2 pi). Then

    exp(-i gamma(p) log(p)) = exp(-2 pi i fract(x)).

The integer part cancels exactly from this phase. The relevant period is
2 pi; the unnormalized floor of gamma log(p) is not the unit-circle phase.

AtomSpanReweighting.span_range_smul_eq proves over any division ring that
independently multiplying every dictionary atom by a nonzero scalar preserves
its span. QLegalResidueDPP.reweighted_modeLaw_eq proves that nonzero real
column weights preserve the actual full legal DPP law. In a complex module,
PrimeOrdinateTwist.primePhase_span_eq proves span invariance even for arbitrary
primewise assigned ordinates, because all phase weights are nonzero.
This complex-span statement is not a construction of a complex-valued kernel
on the original real Hilbert space.

Thus phase reweighting of a fixed dictionary cannot increase its optimal
occupation. This does not preclude phase data selecting a different conductor
family or explicit trial coefficients. Such a construction must still prove
legality and one of the full-energy/CRT-tail/information-divergence estimates.

Even granting finite-prime equidistribution, a uniform estimate for growing
prime sets and complete arithmetic tails is not supplied by fixed-test
equidistribution. The inspected actual finite-prime FMZ continuous-test
consumer in ActualPrimeTorusFMZContinuous exposes
UniformSelbergDensity(1/4); its classical analytic provider is not formalized
there. No zero-sampled convergence or growing-prime estimate was silently
assumed in the new unconditional DPP and floor identities.

Open: a quantitative bridge from zero-phase statistics to the actual legal
Gram capacity or a uniformly controlled legal trial family.

## Source and verification scope

The five exported modules contain 53 new theorems:

| Module | Theorems | Scope |
| --- | ---: | --- |
| RH/QDivisorProjectionDPP.lean | 13 | Actual arbitrary Q-subspace law, constant occupation/vacancy and exact trial error |
| RH/QDivisorProjectionParity.lean | 6 | Exact normalized parity residual, kernel block and joint probability |
| RH/QLegalResidueDPP.lean | 30 | Full/squarefree laws, monotonicity, information, CRT equivalence, conditional RH and reweighting |
| Analysis/AtomSpanReweighting.lean | 1 | General nonzero coordinate-weight span invariance |
| Analysis/PrimeOrdinateFloorPhase.lean | 3 | Exact normalized fractional phases and complex-span invariance |

The proof-candidate batch passed job_jaOEjMEKUCViJt7F8YFyMjSUvuPA8LzO
(exit code 0, verified true, 8.038 seconds). All five saved source modules and
the 16 central-declaration axiom audit passed
job_ckDopHaizfaW5vhguVHyDNs2Q-emhH2S (exit code 0, verified true,
11.578 seconds). Every inspected declaration uses only propext,
Classical.choice, and Quot.sound. The zero-limit hypotheses remain explicit
in the conditional RH theorem types; an axiom audit does not discharge them.
Publication requires the separate final checkpoint audit and
aggregate-plus-changed-module server validation.

No p_n -> 1 estimate, RH proof, zero-spectrum identification, or Hilbert-Polya
operator was produced. The excluded positive-density unit-lattice sine regime
from the earlier physical-window modules remains distinct from unresolved
continuum unfoldings and the unresolved spectral identification problem.
