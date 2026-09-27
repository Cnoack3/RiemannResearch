# Nyman–Beurling: centered damping and finite-energy Mellin continuation

Working date: 2026-09-26 (America/New_York).
Base: 234497e34671b4a893d8f0642f38fce8d9ab4463.

Status reconciled on 2026-09-27 with endpoint commit
`d4e06595e09075250bc2c2c49399dcd0b3cd6767`. The verification record below
describes the original continuation development; the subsequently verified
half-damping endpoint is recorded under the remaining arithmetic obligation.

Combined candidate verification: succeeded, `verified=true`, exit code 0.
Job: `job_eQxijapPHngZmALTfhH0na2Ig0UC8RTM`; elapsed 3.673 seconds.
The five principal axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, `admit`, project axiom, or unsafe declaration
is used. Explicit hypotheses in theorem types remain substantive obligations.
The publication checkpoint separately validates the integrated modules and
their reverse dependents; the commit containing this note records publication.

## Exact arithmetic family

For real epsilon and a nonnegative integer n define

A_epsilon(n) = sum_{d=1}^n mu(d) d^(-epsilon) floor(n/d).

This is the existing `dampedMobiusPrefix epsilon n`, not a surrogate sequence.
Its first-difference coefficients are the existing
`dampedDivisorCoefficient epsilon n = sum_{d|n} mu(d)d^(-epsilon)`.
For epsilon >= 0 these coefficients lie in [0,1], as previously proved.

The `DampedDivisorLSeries` module identifies their actual Dirichlet
series as zeta(s)/zeta(s+epsilon) wherever both real parts exceed one.
The common-domain theorem even allows negative damping; the nonnegative
specialization requires only Re(s)>1. Absolute Dirichlet convolution supplies
the proof; no PNT or RH is assumed.

## Actual Mellin identity

Let f be a vector of the existing Pareto Hilbert space with physical
coordinates f(n)=A_epsilon(n)-n*C, where C is any real constant. The actual
Mellin functional is

M_f(s) = integral_1^infinity f(floor(x)) x^(-s-1) dx.

For epsilon >= 0 and Re(s)>1 the exact arithmetic identity is

s M_f(s) = zeta(s)/zeta(s+epsilon) - C zeta(s).

`DampedMobiusMellinArithmetic` obtains it from Mathlib's Abel summation
identity for L-series, retaining the complete integer-floor correction.
The positivity bounds provide the required linear absolute-coefficient
partial-sum bound. No exchange of a merely conditionally convergent series
with an integral is assumed.

## Finite energy supplies holomorphy

`ParetoMellinFiniteEnergy` extends the existing bounded-coordinate theorem
to every vector f of the complete Pareto Hilbert space. Finite coordinate
truncations converge in Hilbert norm. The previously verified sharp Mellin
Cauchy bound makes their transforms converge uniformly on every half-plane
Re(s)>sigma>1/2. Mathlib's locally uniform limit theorem proves holomorphy
on Re(s)>1/2. No boundedness of the physical coordinates is required.

The same proof gives a reusable norm-convergence to uniform-Mellin-convergence
theorem. Its constants depend on the distance to the critical boundary;
it makes no assertion of uniform convergence on Re(s)=1/2.

## Entire continuation and normalization

Set a(s)=1/2-2^(-s), and let Z_2 be the existing entire continuation of
zeta(s)a(s). Multiplying the arithmetic identity by the conductor factors
produces the entire identity

s Z_2(s+epsilon) a(s) M_f(s)
  = Z_2(s) [a(s+epsilon)-C Z_2(s+epsilon)].

Both sides are holomorphic throughout Re(s)>1/2, including the former zeta
poles. The identity theorem extends equality from a neighborhood of 2.
At s=1, for positive epsilon, this forces

C zeta(1+epsilon) = 1.

Thus C is uniquely determined by finite energy and the arithmetic identity;
its value need not be a separate premise.

At a zeta zero rho with 1/2+epsilon<Re(rho)<1, evaluate at s=rho-epsilon.
The conductor factors there and at rho are nonzero because their real parts
are below one. The identity forces zeta(rho-epsilon)=0, without division
by a vanishing zeta value. The existing isolated-zero theorem then excludes
all right-half-strip zeros if positive admissible epsilon values tend to zero.

## Exact remaining arithmetic obligation

The assembled sufficient condition is:

There exists a positive sequence epsilon_j -> 0 such that, for every j,
there is a real C_j with

sum_{n=1}^infinity
  (A_{epsilon_j}(n)-n*C_j)^2 / [n(n+1)] < infinity.

There is no uniform bound on these sums, and no monotonicity requirement on
epsilon_j. The formal statement uses `Summable` of the actual weighted-square
terms, not Lean's totalized `tsum` value without a convergence hypothesis.
The theorem constructs the Hilbert vectors from that summability.

**Open:** proving this summability for the actual family at positive damping
approaching zero. It is not supplied by the Dirichlet identity, the Euler
product positivity, or holomorphy conditional on membership.

At epsilon=0 the existing Möbius floor identity gives A_0(n)=1 for n>=1.
This endpoint fact does not establish positive-damping membership.

No unconditional RH proof is claimed. The reverse implication from RH to
this particular finite-energy formulation is not formalized by these modules.

Burnol's Lemma 4.1 establishes square-integrability for epsilon >= 1/2,
including the endpoint, unconditionally. For x in [n,n+1), his function
satisfies -f_epsilon(1/x)=A_epsilon(n)-C*n-C*(x-n). The rounding term is
bounded and has finite Pareto energy, so his membership statement transfers
to the centered discrete sequence. The discrete endpoint is now established
unconditionally in `RH/DampedMobiusHalfEndpoint.lean` at commit
`d4e06595e09075250bc2c2c49399dcd0b3cd6767`:
`dampedMobius_half_endpoint` proves the actual centered weighted-square
summability at epsilon=1/2, together with a quantitative discrepancy bound.
`centered_dampedMobius_square_summable_iff_of_half_le` proves, for every
epsilon >= 1/2 and every real C, that this energy is finite if and only if
C = Re(1/zeta(1+epsilon)). See
[`BurnolHalfEndpointFormalization20260927.md`](BurnolHalfEndpointFormalization20260927.md)
for the arithmetic proof and verification record. Thus the endpoint is no
longer merely a literature finding. The inclusive range epsilon >= 1/2
does not supply positive damping parameters tending to zero; finite energy
along such a sequence remains **Open**.

## Provenance

J.-F. Burnol, “On an analytic estimate in the theory of the Riemann zeta
function and a theorem of Baez-Duarte,” arXiv:math/0202166, Lemma 4.3 and
Theorem 4.2: https://arxiv.org/pdf/math/0202166.
This supports the arithmetic Mellin and zero-propagation strategy. The
paper's critical-line ratio estimate is conditional on RH and is not used
as an unconditional premise. The arbitrary centering, entire-conductor
pole removal, and general Pareto-Hilbert implementation are the present
formalization choices; no claim of mathematical novelty is made.

Wolfram symbolically confirmed the elementary kernel integrals
integral_1^infinity x^(-2 sigma) dx = 1/(2 sigma-1) and
integral_1^infinity log(x)^2 x^(-2 sigma) dx = 2/(2 sigma-1)^3,
for real sigma>1/2. These computations are ancillary; Lean verification
supplies the proof evidence for the declarations above.


## Module and declaration map

| Module | Principal declarations |
|---|---|
| `DampedDivisorLSeries` | `dampedMobiusWeight_LSeriesHasSum`, `dampedDivisorCoefficient_LSeriesHasSum`, `dampedDivisorCoefficient_LSeries` |
| `DampedMobiusMellinArithmetic` | `dampedMobiusPrefix_centered_mellin`, `paretoMellin_of_centered_dampedMobiusPrefix` |
| `ParetoMellinFiniteEnergy` | `paretoMellin_tendstoUniformlyOn_of_tendsto`, `paretoMellin_differentiableAt`, `paretoMellin_analyticOnNhd` |
| `BurnolMellinContinuation` | `damped_mellin_conductor_identity`, `normalization_of_mellin_identity`, `zero_propagation_of_mellin_identity` |
| `BurnolFiniteEnergyReduction` | `centered_dampedMobius_mellin_cross_identity`, `riemannHypothesis_of_centered_damped_finiteEnergy_sequence`, `riemannHypothesis_of_centered_damped_square_summable` |
| `DampedMobiusHalfEndpoint` (subsequent endpoint development) | `dampedMobius_half_endpoint`, `centered_dampedMobius_square_summable_iff_of_half_le` |

The existing `BurnolDampingZeroShift` keeps its statements and uses the
already verified conductor regularization lemma for finite zeta zero order,
removing an unnecessary dependency on the full explicit-formula assembly.
This avoids rebuilding that unrelated dependency chain for the new bridge.

## Verification recovery

The fresh workspace lacked project object files. The baseline rebuild
`job_zRAJz4y9Kq8UNGBkerKWhinmM3UpOUXo` ended in `interrupted` with the server
message “The job owner exited while this job was pending.” It was not an
RH refutation or a proof failure. The repository stayed clean. Its partial
build artifacts plus reduced module dependencies allowed the focused proof
candidate above to pass. Publication uses the targeted checkpoint rather
than claiming that this interrupted full-project build succeeded.
