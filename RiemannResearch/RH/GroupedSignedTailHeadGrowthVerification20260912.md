# RH grouped signed tails and exact-head growth — 2026-09-12

RH has not been proved. This continuation proves two concrete advances:
unconditional grouped signed-tail identities under actual weighted L2
membership, and a quantitative obstruction to legal exact-head approximation
at a hypothetical right-half-strip zeta zero.

## 1. Actual signed tails: the summability requirement is reduced

Write
```
w(n) = 1/(n(n+1)) for n>0, w(0)=0,
A(n) = sum_{k>=n} w(k)h(k) for n>0, A(0)=0.
```
Assume only `Summable (fun n => positiveWeight n * h n ^ 2)`.
The signed coefficients are absolutely summable, so all tails are genuine.
For every m>0, both sequences
```
G₂,m(j) = A(m(2j+1)) - A(m(2j+2)),
G₃,m(j) = A(m(3j+1)) + A(m(3j+2)) - 2 A(m(3j+3))
```
are absolutely summable. No summability of A itself is assumed.

The exact identities are
```
paretoInner h (dilation m (residue 2)) = m * tsum G₂,m,
paretoInner h (dilation m (residue 3)) = m * tsum G₃,m.
```
Thus an actual two-seed legal annihilator has both grouped sums equal to zero
at every positive integer dilation.

The proof first retains the finite Abel boundary term:
```
sum_{n<N} A(n)(g(n)-g(n-1))
 = sum_{n<N}(A(n)-A(n+1))g(n) + A(N)g(N-1).
```
For bounded tests the boundary vanishes because A(N) tends to zero.
Finite divisor-mask reindexing and exact binary/triadic block identities then
identify the two grouped limits. Each fixed-width tail difference is summable
because it is a finite sum of injectively sampled signed coefficients.

Main file: `RH/ParetoGroupedSignedTails.lean`.
Supporting files: `Analysis/SummableDiscreteAbel.lean`,
`Analysis/SummableMultiples.lean`, and `RH/ParetoSignedTails.lean`.

## 2. A hypothetical off-line zero forces polynomial full energy

Let s be an actual zeta zero with sigma=Re(s)>1/2 and s!=1.
For every legal f with physical sequence equal to one through N>=3:
```
norm(f)^2 >= (2*sigma-1)/(4*norm(s)^2) * (N+1)^(2*sigma-1).
```
This uses the actual Mellin-nullity provider, the established complete
head-tail energy inequality, and a uniform bound on the residual Mellin mode.
No comparison-vector, independent-channel, or truncated-energy estimate
replaces the full norm.

Consequently an exact-head legal family has full energy tending to infinity
at such a zero. Moreover, if its full squared norm is o((N+1)^p) for every p>0,
then Mathlib's actual `RiemannHypothesis` follows.

Endpoints:
- `paretoMellin_exact_head_power_lower` in `RH/ParetoMellinHeadObstruction.lean`.
- `legal_exactHead_power_lower_of_zeta`,
  `legal_exactHead_energy_tendsto_atTop_of_zeta`, and
  `riemannHypothesis_of_legal_exactHead_subpower` in
  `RH/ParetoLegalHeadGrowth.lean`.

The RH theorem is a conditional research reduction. It does not construct
the required subpolynomial-energy witnesses. The stronger assumption of a
uniform norm bound is unnecessary for this sufficient criterion.

## 3. Exact remaining proof tasks

1. Invert the simultaneous binary and triadic grouped equations using their
actual weighted difference energy, without separating divergent channels.
Absolute summability of the grouped differences does not itself justify the
summable-multiples inversion theorem.
2. Alternatively, construct legal exact-head witnesses with complete squared
norm o(N^p) for every p>0, retaining all mixed terms. Finite interpolation
alone does not prove this energy bound.
3. Canonical-residual signed-tail summability remains another open route.
The earlier summable-tail uniqueness theorem remains valid and unchanged.

Do not infer zero from dyadic scaling and finite difference energy alone:
A(n)=1/n for n>0 has both properties and is nonzero. This simple analytical
obstruction is a scope check, not a newly formalized counterexample here.

## 4. Verification and continuation

Twenty new public lemmas/theorems and one private cutoff lemma are included.
The mathematical candidates passed serialized Lean checks, including actual
grouped-equation endpoints and the exact-head subpower RH criterion.
Their printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
These audits do not discharge hypotheses appearing in theorem types.

Candidate jobs:
- Grouped equations: `job_qXH4uxkAnCg6K_5HmgtwZ3ER0-FE7YkX`,
  verified true, exit code 0.
- Exact-head growth and RH criterion: `job_v8XaWPUhXB4ycXZtdCgz_CuHAU9BRm4n`,
  verified true, exit code 0.

The publication checkpoint containing this note is the authority for final
module integration and publication. Its commit contains the complete source
and updated theorem catalog.

Workspace token: `ws_5_b1WRw2Rk548lJWXAhwvIfo4hXv6KWp`.
Base commit: `c38a4d9c90ae79f3670b0243117bc0fb05b0943d`.
Keep mathematical development parallel and serialize all verification jobs.
