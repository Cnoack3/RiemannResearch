# Quantitative endpoint convergence and the enlarged moving band

**Status update, 2026-09-27:** the quarter-logarithmic estimates below
record the earlier result at `ba20efab`. They remain valid, but are
superseded in strength by the direct MediumPNT stretched-exponential
Mertens and complete endpoint profile exp(-a*(L*log L)^(1/11)). The
supported moving band has width c*L^(-10/11)*(log L)^(1/11), for fixed
c below the endpoint coefficient. See `MertensStretchedContinuation20260927.md`
for the checked provider chain, finite-bootstrap audit, and remaining RH gap.

Continuation of `b6f6c5a8eaf653c3e5b95368d0f7a82fbeb47787`, 2026-09-27.

Write `F_{epsilon,M}` for the complete arithmetic Hilbert cutoff and `f` for
`dampedMobiusHalfRangeLimit (1/2) le_rfl`. Put `L(M)=6+log(M+1)`.
Every norm below is the full Pareto Hilbert norm, including all physical
coordinates and all signed Gram terms.

## Endpoint rate and finite-head audit

The quantitative result is a single unconditional constant `C>=0` with

```math
\|F_{1/2,M}-f\|_P\le C L(M)^{-1/4}.
```

The infinite-tail envelope alone does not establish this statement. The
finite head is controlled by the exact density-tail identity already
verified in `DampedMobiusJointHeadLimits`. If
`tau_M=1/zeta(3/2)-sum_{d<=M}mu(d)d^(-3/2)`, then for `n<M` the error is
`n*tau_M`, and

```math
\sum_{n<M}\frac{|F_{1/2,M}(n)-f(n)|^2}{n(n+1)}
=|\tau_M|^2\sum_{n<M}\frac{n}{n+1}
\le D(6+\log M)^{-3}.
```

The existing conductor-uniform physical envelope passes to the coordinate
limit. Thus for all sufficiently large `n` and every `M`,

```math
|F_{1/2,M}(n)-f(n)|
\le 2K\sqrt n\,(6+\log n)^{-3/4}.
```

The required quantitative tail estimate follows from the exact integral

```math
\int_M^\infty\frac{dx}{x(6+\log x)^{3/2}}
=2(6+\log M)^{-1/2}.
```

Including the first summand gives the bound `3(6+log M)^(-1/2)`. Consequently

```math
\|F_{1/2,M}-f\|_P^2
\le D(6+\log M)^{-3}+12K^2(6+\log M)^{-1/2}.
```

Taking square roots gives exponent `1/4`. Enlarging the constant handles
the finitely many small cutoffs and changes `log M` to `log(M+1)`.
The head is substantially smaller than the tail; it causes no exponent loss.

## Quantitative increasing Abel transfer

Let `S_m=sum_{n<m}u_n`, `e_m=S_m-f`, and `w_n=(n+1)^delta`, with `delta>=0`.
For `M=N+1` the exact centered finite Abel identity is

```math
\sum_{n<M}w_nu_n-f
=w_N e_M-\sum_{n<N}(w_{n+1}-w_n)e_{n+1}.
```

Norms are taken only after each complete signed prefix. For
`0<alpha<1`, the scalar primitive

```math
P(t)=\frac{(e^{\delta t}-1)(c+t)^{-\alpha}}{1-\alpha}
```

satisfies `P'(t)>=delta*exp(delta*t)*(c+t)^(-alpha)` for `t>=0,c>0`.
Indeed `exp(delta*t)-1<=delta*t*exp(delta*t)` and `t<=c+t`.
Integrating over successive logarithmic intervals bounds the complete
Abel variation by a constant times the terminal amplified rate.
This yields an unconditional constant `C'` such that

```math
\|F_{1/2-\delta,M}-f\|_P
\le C'(M+1)^\delta L(M)^{-1/4}\qquad(\delta\ge0).
```

The assertion concerns finite conductor cutoffs, even when the damping is
below one half. It asserts no existence of an infinite Hilbert vector at
such a damping.

## Widest generic band supported by this rate

For `M_j->infinity` and `delta_j=1/2-epsilon_j>=0`, the supported condition is

```math
(M_j+1)^{\delta_j}L(M_j)^{-1/4}\longrightarrow0,
```

equivalently

```math
\delta_j\log(M_j+1)-\tfrac14\log L(M_j)\longrightarrow-\infty.
```

Under this condition the complete cutoff vectors tend to `f` and their
squared norms tend to the canonical half-damped energy. In particular,
for each fixed `0<=c<1/4`, convergence is uniform in

```math
0\le\tfrac12-\varepsilon
\le c\,\frac{\log(6+\log(M+1))}{\log(M+1)}.
```

At the critical coefficient `1/4`, an arbitrary diverging subtractive
margin is permitted in the numerator. A fixed subtractive margin gives
only a bounded majorant by this argument, not convergence.
More quantitatively, the fixed `c` band has the uniform error bound
`C' L(M)^(c-1/4)`, and a slack `omega(M)` has error at most
`C' exp(-omega(M))`.

There is also an unconditional bound on the full cutoff norms and signed
energies throughout the larger critical boundary band

```math
\delta\log(M+1)\le\tfrac14\log L(M)+A,
```

for each fixed finite `A`. Here the amplified majorant is at most `exp(A)`.
This boundedness statement includes the critical coefficient itself; the
convergence statement requires the margin to tend to negative infinity.

For a fixed subhalf damping, the same quantitative estimate gives
`||F_{epsilon,M}||<=||f||+C'(M+1)^(1/2-epsilon)L(M)^(-1/4)`.
The residual power growth is not removed.

The word "widest" refers to transfer from the displayed norm envelope
alone, not arithmetic optimality. An abstract Hilbert sequence with
orthogonal residuals `e_m=L(m)^(-1/4)v_m` has a terminal weighted component
of norm `M^delta L(M)^(-1/4)` orthogonal to all preceding residuals.
This explanatory example shows why a universal envelope-only transfer
cannot discard the terminal amplification condition.
Neither this example nor the positive tail majorant supplies a lower
bound on the actual arithmetic approximation error.
The orthogonal-model comparison is explanatory; it is not a separately
formalized lower-bound theorem.

## Remaining gap and provenance

No fixed `epsilon<1/2` has newly established finite energy. The moving
band shrinks toward `1/2`; every fixed positive `delta` eventually leaves
it. Finite energy at positive dampings tending to zero remains Open.

The endpoint coordinate and head providers are the existing checked
repository declarations. The new tail and Abel arguments use elementary
integral comparison, the fundamental theorem of calculus, and finite
summation by parts. No new arithmetic cancellation premise is inserted,
and no mathematical novelty claim is made.

The audited provider chain ends at `M_shiftedLog_threeHalves_bound`,
assembled from `M_mul_sqrt_log_cube_eventual_of_inverseLogFourth`.
The weighted Mertens transfer and tail modules use the fixed exponent
`3/2`. A stronger Chebyshev-error PNT provider exists, but the audit found
no already assembled stronger Mertens logarithmic provider that would
automatically replace the present endpoint envelope. That assembly has now been strengthened in
`NumberTheory/PrimeNumberTheorem/MertensAllLogPowers.lean` to every fixed
logarithmic exponent, with all-logarithmic weighted, endpoint, and
moving-band consumers. The paragraph above describes the earlier audit;
see the status update and continuation linked at the start of this file.

## Principal declarations

| Declaration | Content |
|---|---|
| `dampedMobius_half_cutoffs_log_rate` | Unconditional endpoint norm rate, every cutoff |
| `signedVector_increasing_weight_residual_le` | Exact signed-prefix error budget |
| `increasingPower_logProfile_sum_le` | Uniform scalar Abel multiplier |
| `dampedMobius_subhalf_quantitative_bound` | Endpoint rate times conductor amplification |
| `dampedMobius_loglog_band_error_le` | Explicit rate throughout each coefficient-c band |
| `dampedMobius_moving_subhalf_margin_tendsto` | Convergence under the exact vanishing-margin condition |
| `dampedMobius_sharp_margin_subhalf_band_uniform` | Uniform convergence with any divergent slack |
| `dampedMobius_critical_loglog_band_signed_bounds` | Uniform signed bounds at the critical coefficient |
| `dampedMobius_moving_subhalf_margin_energy_tendsto` | Complete squared-norm convergence |
| `dampedMobius_subhalf_log_improved_growth` | Quarter-logarithmic gain in fixed-subhalf cutoff growth |

## Verification record

The isolated endpoint and scalar-support check
`job_Ft7w7Bvc_rQG3y13YDn7Oz_5CzshjQWV` completed with `exit_code=0`,
`verified=true`, and no warnings. The endpoint rate and scalar Abel kernel
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The general centered Abel transfer passed
`job_p1GafrWvNid4dUwIojUDTe4DfycSxfIY`, also with standard foundations only.
The complete arithmetic assembly passed
`job_sChaFpma8XtltTH-T5TxqZzz9FXceRsL` with `exit_code=0` and
`verified=true`. Its quantitative subhalf norm bound, uniform sharp-margin
convergence, and critical-band signed bounds likewise have only the three
standard foundations above. No unproved arithmetic premise or project-local
axiom is introduced. The publication checkpoint validates the changed
modules and their affected local dependents before pushing.
