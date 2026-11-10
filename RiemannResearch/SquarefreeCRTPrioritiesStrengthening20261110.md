# Squarefree CRT priorities: strengthened certificates (10 November 2026)

Source: the attached *Squarefree projection displacement and infinite CRT carries:
Definitions, proved reductions, and a research program toward d = 0*
(9 November 2026), Sections 6, 10--13.

## Mathematical status

The final arithmetic acceptance conditions in Priorities 1--5 remain **Open**.
The changes below prove stronger estimates and exact identities for the actual
canonical primorial projections. They do not prove that the displacement
vanishes, that the constant target belongs to the squarefree closure, or RH.

The original structural agenda is already implemented in
`QPrimorialMatchedDisplacement`, `QPrimorialMatchedGram`,
`QPrimorialPrimeCarry`, `QPrimorialRayAssembly`, and
`QSquarefreeWitnessHead`. These results are extended, not assumed to close
their own remaining arithmetic hypotheses.

## Notation and exact objects

Let `V_n = primorialStage n` use every divisor greater than one of
`primorialPeriod n = primorial (n+3)`. Its Q and Pareto fits use the same
physical dictionary. Write

- `d_n = stageDisplacement n = f_n^Q - f_n^P`;
- `E_n = pError n = ||1-f_n^P||_P^2`;
- `a(n,m) = normalizedPairing n m = zeta(2) m <g_m,d_n>_Q`;
- `W_n = primeStage n`, `K_n = V_n intersect W_n^perp_Q`;
- `x_n = primeComponent n = P^Q_{W_n} d_n`;
- `L_n x = schurLift n x = x-P^P_{K_n}x`;
- `F_n = selfForcing n = schurForcing n x_n`.

The shift multiplier `B` in these modules divides physical values by
`k+1`. The Q and Pareto metrics and the prime and carry subspaces are
kept distinct.

## Priority 1: uniform little-o and finite certificates

In `QPrimorialPairingRefinement.lean`:

```
normalizedPairing_energy_bound
pError_le_of_normalizedPairing_nonpos
pError_le_twice_pairing_add_inv
normalizedPairing_scaled_tail_bound
normalizedPairing_uniform_scaled_defect
normalizedPairing_scaled_defect_tendsto
```

For every included positive conductor m:

```
|E_n-a(n,m)| <= sqrt(1/m) ||1-f_n^P||_P,
sqrt(m)|E_n-a(n,m)| <= ||tail_(m-1)(1-f_n^P)||_P.
```

The second right-hand side tends to zero uniformly over *all* stages n
as m grows. Thus the error is uniformly `o(m^(-1/2))`, not merely
`O(m^(-1/2))`. The proof uses uniform complete-tail tightness of a
norm-convergent family; it assumes no rate for projection convergence.

For any arbitrary stage selection N(j), included conductors m(j) tending
to infinity give

```
sqrt(m(j)) |E_(N(j))-a(N(j),m(j))| -> 0.
```

Cofinality of N(j) is unnecessary for this *defect* conclusion. Cofinality
is still used in the existing theorem identifying the limit of a(N(j),m(j))
with the limiting residual energy.

Two useful finite consequences are

```
a(n,m) <= 0  ==>  E_n <= 1/m,
E_n <= 2 a(n,m) + 1/m.
```

The signed complete Gram row is retained. No nonpositive or vanishing
cofinal upper bound for that row has been proved here.

## Priorities 2 and 4: scalar Schur energy and exact metric gap

In `QPrimorialSchurEnergy.lean`:

```
schurForm_upper
schurForm_coercive_arithmetic
selfForcing_exact
selfForcing_bounds
displacement_zero_of_cofinal_selfForcing
selfForcing_tendsto_zero_iff
displacement_sub_schurLift_mem_carry
metricGap_schur_exact
riemannHypothesis_of_cofinal_selfForcing
```

The existing four-site certificate bounds `<u,Bu>_Q <= (29/59)||u||_Q^2`
on the squarefree closure. It improves Schur coercivity to

```
(30/59) zeta(2) ||x||_Q^2 <= schurForm_n(x,x)
                                  <= zeta(2) ||x||_Q^2,   x in W_n.
```

The new scalar is an exact nonnegative energy:

```
F_n = ||L_n x_n||_P^2,
(30/59) zeta(2) ||x_n||_Q^2 <= F_n <= zeta(2) ||x_n||_Q^2.
```

Consequently `F_n -> 0 <=> d=0`. For a sufficient RH certificate,
full convergence can be weakened to

```
for every epsilon > 0, frequently n: F_n <= epsilon.
```

This replaces a bound uniform over all prime test vectors by a single
scalar test on the *actual canonical prime component*. Supplying these
arithmetic upper bounds remains **Open**.


### A posteriori certificate for an approximate Schur solve

In `QPrimorialSchurCertificate.lean`, choose any trial v in W_n and define

```
J_n(v) = 2 schurForcing_n(v) - schurForm_n(v,v),
r_n(v;y) = schurForcing_n(y) - schurForm_n(v,y).
```

The signed identity is

```
F_n = J_n(v) + schurForm_n(x_n-v,x_n-v).
```

If a complete dual residual certificate establishes

```
r_n(v;y) <= zeta(2) eta ||y||_Q   for every y in W_n,  eta>=0,
```

then the actual canonical energy lies in the rigorous interval

```
J_n(v) <= F_n <= J_n(v) + (59/30) zeta(2) eta^2.
```

Thus one can use approximate trial coefficients together with a certified
solve-residual bound. There is no need to identify the trial with the exact
unknown solution. `riemannHypothesis_of_cofinal_schurCertificate` proves
the RH implication when these *upper endpoints* are arbitrarily small
cofinally. Producing that cofinal arithmetic certificate remains **Open**.

Set `k_n = d_n-L_n x_n`. The theorem proves `k_n in K_n` and the
complete gap identity

```
G_n = F_n + ||k_n||_P^2 + metricCorrection(1-f_n^Q).
```

Both nonnegative remainders are retained. In particular, the carry
contribution has not been set to zero by a Q/Pareto orthogonality substitution.

## Priority 3: actual branches and arbitrarily growing normalized tests

In `QPrimorialRayProjection.lean`:

```
assembledPrime_exact
assembledCarry_exact
assembledPrime_tendsto
assembledCarry_tendsto
assembledPrime_tendsto_zero_iff
normalized_test_bound
exists_normalized_diagonal
branchPairing_exact
exists_diagonal_energy_detection
```

Each ray is weighted by `displacementCoefficients n`, the difference of
the two complete inverse-Gram solves. If A_n, T_n, and B_n denote the
weighted prime sum, carry sum, and boundary, the exact identities are

```
A_n + P_W T_n = P_W(d_n-B_n),
P_(W^perp) T_n = P_(W^perp)(d_n-B_n).
```

For any depths for which B_n tends to zero, these expressions tend to
d_W and d_K, respectively. Moreover, the first tends to zero if and only
if d=0. No separate convergence of the raw A_n and T_n is assumed.

For any prescribed conductor sequence m(n), a diagonal depth choice gives
both

```
||B_n||_Q < 2^(-n),
|zeta(2) m(n) <g_(m(n)),B_n>_Q| < 2^(-n),  if m(n)>=2.
```

The second conclusion is stronger than ordinary boundary norm decay:
the normalization can grow arbitrarily fast. This applies to the entire
primorial period, as well as a prime. For included m(n) tending to infinity,
the normalized signed pairing with A_n+T_n converges to the limiting
Pareto residual energy.

**Open:** force that signed limit, or the projected prime combination, to
vanish. The theorem supplies the actual coefficients and negligible
normalized boundary; it does not supply the remaining cancellation.

## Priority 5: exact heads and growth

The existing `QSquarefreeWitnessHead.prime_anchor_exact` and
`prime_anchor_witness_tail` give the legal prime-anchor interpolant and
its exact signed tail pairing with the faithful witness. The existing
`residual_zero_of_prime_anchor_witness_tail` assumes the complete
defect-norm times witness-tail-norm tends to zero.

That product bound remains **Open**. No estimate on the actual displacement's
growth, no prime-only representation for it, and no vanishing witness mean
has been inferred from head interpolation or branch convergence.

## Priority 6: reproducibility

All four new modules are exported from `RiemannResearch.lean`. They use
the complete Q/Pareto norms and preserve the signed canonical terms.
The final publication uses the server's Bazel/BuildBuddy full-project
checkpoint. The focused verification additionally checks the exact transitive axiom lists
for the new uniform defect theorem, exact gap identity, conditional RH
consumer, normalized branch construction, and existing prime-anchor identity.

The proof-development snippet `job_ca0ImF7J-s-37PHiXsUizdgmOgGRKx-8`
verified the pairing and Schur/gap proofs with Bazel (exit 0; server-reported
verification time 176.471 seconds). A snippet check is distinct from the
final full-project publication gate.

The approximate-solve proof snippet `job_flHvOPQz7IGpchFoaKq09zzKk_nUIByo`
also passed Bazel (exit 0; server-reported verification time 97.540 seconds).
The three initial modules and existing witness-head module passed the
combined focused check `job_HX5XzynaRaxgH4bn_LLWklULuwLFxk27`
(exit 0; 191.071 seconds). These durations exclude workspace setup and
subsequent polling delay.

The next mathematical obligation is a provider for the cofinal upper bound
on `selfForcing` or the complete canonical normalized Gram row. These are
stated as open hypotheses, not added axioms.

The final focused axiom audit `job_8QznPILuYeSkM0KXdj9Kk8WWTIp5xUXv`
passed Bazel with exit 0 (53.842 seconds of reported verification time).
Five explicit `#guard_msgs` checks required the complete axiom lists to be
exactly `[propext, Classical.choice, Quot.sound]`, covering the uniform
defect theorem, exact gap, approximate-certificate RH consumer, normalized
branch construction, and existing prime-anchor witness identity.
The domain-specific bounds in conditional theorem types remain hypotheses;
an axiom audit does not discharge those bounds.
