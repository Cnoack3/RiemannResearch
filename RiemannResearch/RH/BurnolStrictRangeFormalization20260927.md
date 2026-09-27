# Published-source finite energy and quantitative Nyman–Beurling formalization

Date: 2026-09-27. Repository: Cnoack3/RiemannResearch.
Base commit: 70ef2e5183ccd61e4096cf6366ecc0070224ef72.

Status reconciled with endpoint commit
`d4e06595e09075250bc2c2c49399dcd0b3cd6767`. The original strict-range
construction and its quantitative truncation bound retain their hypotheses;
the current finite-energy status includes the subsequently verified endpoint.

## Source and exact scope

J.-F. Burnol, *On an analytic estimate in the theory of the Riemann zeta
function and a theorem of Báez-Duarte*, Acta Cientifica Venezolana **54**
(2003), 210–215.
The author's record verifies the publication:
https://arxiv.org/abs/math/0202166.
The proof and numbering used here are from the author's manuscript:
https://arxiv.org/pdf/math/0202166, Section 4, Lemma 4.1.

Burnol proves square integrability for epsilon >= 1/2. Its strict range
epsilon > 1/2 follows by an absolutely convergent Hilbert series.
The endpoint epsilon = 1/2 uses additional estimates for zeta and its inverse.

This development formalizes the **discrete counterpart of the strict-range
argument**, using the repository's actual Pareto Hilbert space and genuine
Mathlib Mobius function. The discrete endpoint is now formalized separately
in `RH/DampedMobiusHalfEndpoint.lean`, using quantitative PNT, Abel summation,
and an exact hyperbola decomposition. See
[`BurnolHalfEndpointFormalization20260927.md`](BurnolHalfEndpointFormalization20260927.md).
The full continuous Mellin–Plancherel theorem is outside this development.
The arithmetic weight
generalization and explicit truncation rate are standard consequences
of the proof mechanism, not claimed as new mathematics.

## Exact objects

For real weights w, define

- A_w(k) = sum over 0 <= n <= k of w(n)*floor(k/n), with Lean's n=0 term zero.
- C_w = sum over n >= 1 of w(n)/n.
- H consists of zero-anchored real sequences f with
  sum over k >= 1 of f(k)^2/[k(k+1)] finite.

The new constructor is the signed Hilbert series

F_w = -sum over n >= 1 of (w(n)/n) * (k -> k mod n).

For Mobius damping, w(n)=mu(n)*n^(-epsilon), and
A_w is exactly the existing `dampedMobiusPrefix epsilon`.
The finite approximation F_w,N truncates this residue series at n=N.
It centers its floor sum by the corresponding finite density; its error
estimate is for this precisely defined approximation.

## Generalization proved

Assume only

S_w = sum over n >= 1 of |w(n)|/sqrt(n) < infinity.

Then C_w converges absolutely, F_w is a genuine Hilbert vector,

F_w(k) = A_w(k) - k*C_w,

and its norm is at most sqrt(2)*S_w.
The construction permits arbitrary signs and arbitrary real weights.
There is no multiplicativity assumption or cancellation hypothesis.

The complete signed error is the infinite tail of the Hilbert series, and

norm(F_w-F_w,N) <= sqrt(2) *
  sum over n>N of |w(n)|/sqrt(n).

A separate elementary theorem proves uniqueness of the linear centering
for any real sequence having finite weighted square energy.

These statements live in `RH/ArithmeticFloorHilbertSeries.lean`.
They reuse `hilbertResidue_norm_sq_le_twice`; the residue estimate is
not a new result in this development.

## Actual unconditional arithmetic provider

The original strict-range provider covers epsilon > 1/2. With
`centered_dampedMobius_square_summable_iff_of_half_le` in
`RH/DampedMobiusHalfEndpoint.lean`, Lean now proves the inclusive statement
for **every epsilon >= 1/2**:

Summable (k -> positiveWeight(k) *
  (dampedMobiusPrefix(epsilon,k)-k*C)^2)

if and only if

C = Re(1/zeta(1+epsilon)).

The cast-and-real-part formulation is the exact Lean statement because
Mathlib's Riemann zeta function is complex-valued.

For every epsilon > 0, **if** the centered prefix has finite energy,
Lean proves the forced normalization

(C : complex) * zeta(1+epsilon) = 1.

The latter theorem is conditional on actual energy, even though its proof
contains no new axioms. It assembles the previously checked arithmetic
Mellin identity, finite-energy holomorphy, and Burnol continuation.

Principal declarations in `RH/DampedMobiusFiniteEnergy.lean`:

- `dampedMobius_half_weight_le`
- `dampedMobius_half_weight_summable`
- `centered_dampedMobius_normalization`
- `centered_dampedMobius_square_summable_of_half_lt`
- `centered_dampedMobius_square_summable_iff`
- `dampedMobius_finiteEnergy_with_bound`
- `dampedMobius_finiteEnergy_tail_bound`

Subsequent endpoint declarations in `RH/DampedMobiusHalfEndpoint.lean`:

- `dampedMobius_half_endpoint`: unconditional centered weighted-square
  summability at epsilon=1/2, together with a quantitative discrepancy bound.
- `centered_dampedMobius_square_summable_iff_of_half_le`: the unique-centering
  characterization above for every epsilon >= 1/2.

## Quantitative refinement proved

For epsilon > 1/2 and integer N >= 1,

norm(F_epsilon-F_epsilon,N)
  <= sqrt(2)*N^(1/2-epsilon)/(epsilon-1/2).

The proof combines |mu(n)|<=1 with the full residue norm estimate and
the exact p-series tail bound

sum over k>=0 of (k+N+1)^(-p) <= N^(1-p)/(p-1), for p>1.

The latter is `Real.tsum_nat_rpow_tail_le` in
`Analysis/PSeriesTail.lean`, proved from Mathlib's integral comparison
and improper power integral.

Wolfram independently checked the exponent simplification and power
integrals. Wolfram output is supporting symbolic evidence only; the
theorems are proved by Lean from their displayed assumptions.

## Verification

The combined candidate succeeded in Lean with verified=true and exit code 0.
Verification job: job_4ZVJIOaFzCptVP0oiD48-oJ302AM3zEl.
Lean elapsed time: 14.648 seconds.
The five principal axiom reports contain only propext, Classical.choice,
and Quot.sound. The general centering-uniqueness proof was also checked
separately with the same foundational axioms.
There are no sorry/admit placeholders, added project axioms, or unsafe declarations.

The project publication checkpoint validates the actual split modules
and their affected dependents before commit and push.
A kernel check verifies each declaration's exact hypotheses; it does not
establish a premise such as small-damping energy.

## Remaining obligations toward RH

| Obligation | Current status after endpoint reconciliation |
| --- | --- |
| Arithmetic centered Mellin identity and half-plane holomorphy | Previously established |
| Finite energy of actual centered prefixes for every epsilon>1/2 | Established here |
| General real-weight synthesis, unique centering, explicit truncation error | Established here |
| Burnol discrete endpoint epsilon=1/2 | Established in `DampedMobiusHalfEndpoint.lean` by `dampedMobius_half_endpoint` (commit `d4e06595e09075250bc2c2c49399dcd0b3cd6767`) |
| Unique-centering characterization for every epsilon>=1/2 | Established by `centered_dampedMobius_square_summable_iff_of_half_le` |
| Finite energy for positive epsilon_j tending to zero | Open |
| RH implies the small-damping membership premise | Not formalized here |
| Unconditional RH | Not proved |

The existing `riemannHypothesis_of_centered_damped_square_summable`
needs finite energy along positive damping parameters tending to zero.
The current unconditional providers cover epsilon>=1/2, so they cannot
discharge that premise. Finite energy at positive dampings tending to zero
remains **Open**, and no unconditional RH proof is claimed.
The strict-range truncation majorant still loses control as epsilon
decreases to 1/2; the separate endpoint proof does not extend that bound.
Descending below 1/2 requires additional input; substituting an
RH-conditional published bound would retain RH as a hypothesis and would
not prove RH unconditionally.
