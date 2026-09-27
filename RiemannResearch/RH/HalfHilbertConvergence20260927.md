# Full Hilbert convergence at the half-damping endpoint

Date: 2026-09-27. Project: RiemannResearch, Lean 4 / Mathlib.

## Established result

The missing full-tail convergence dependency is discharged. For every fixed
epsilon >= 1/2, the naturally ordered arithmetic Hilbert cutoffs converge
in norm to a vector with the canonical centered coordinates.

Write, for n >= 1,

```math
F_{\varepsilon,M}(n)
=-\sum_{d=1}^{M}\frac{\mu(d)}{d^{1+\varepsilon}}(n\bmod d),
\qquad
g_\varepsilon(n)
=\sum_{d\le n}\frac{\mu(d)}{d^\varepsilon}\lfloor n/d\rfloor
-\frac{n}{\zeta(1+\varepsilon)}.
```

The real part of the reciprocal zeta is used in the Lean real-valued
definition. The theorem `dampedMobius_cutoffs_converge_of_half_le` proves

```math
\lim_{M\to\infty}\sum_{n\ge1}
\frac{|F_{\varepsilon,M}(n)-g_\varepsilon(n)|^2}{n(n+1)}=0
\qquad (\varepsilon\ge1/2).
```

In particular, `dampedMobius_half_cutoffs_converge` proves the critical
endpoint. No RH, uniform norm bound, or unproved arithmetic estimate
occurs in its hypotheses.

## Proof of the missing uniform envelope

Let L(x)=6+log x, and set w(d)=mu(d)/sqrt(d). Existing PNT and signed Abel
providers give nonnegative constants B and D such that, for t>=1,

```math
|P(t)|:=\left|\sum_{d\le t}w(d)\right|
\le \frac{B\sqrt t}{L(t)^{3/2}},
\qquad
\left|c-\sum_{d\le t}\frac{w(d)}d\right|
\le \frac{D}{\sqrt t\,L(t)^{3/2}},
\quad c=\frac1{\zeta(3/2)}.
```

Truncate w at an arbitrary conductor M, and center by its finite density
c_M=sum_{d<=M} w(d)/d. The truncated prefix is exactly P(min(M,t)).
The function h(x)=sqrt(x)/L(x)^(3/2) is increasing on x>=1, since

```math
h'(x)=\frac{1}{\sqrt x\,L(x)^{3/2}}
\left(\frac12-\frac{3}{2L(x)}\right)\ge0.
```

Thus the same prefix constant B works for every M. The truncated density
tail is zero when M<=t. When M>t it is exactly the difference of the
original density tails at t and M. Their common decreasing majorant
bounds it by 2D/(sqrt(t)*L(t)^(3/2)).

Apply the existing hyperbola estimate to these truncated signed weights.
For every M and every positive n with log(n)>=200,

```math
|F_{1/2,M}(n)|
\le \frac{K\sqrt n}{L(n)^{3/4}},
\qquad K=2+24B+16D.
```

This is `dampedMobius_half_partial_uniform_log_bound`. There is no
restriction relating n and M. In particular, it controls the entire
physical tail beyond the conductor cutoff.

The squared envelope has summable Pareto energy:

```math
\sum_{n\ge1}\frac{K^2 n/L(n)^{3/2}}{n(n+1)}
=K^2\sum_{n\ge1}\frac1{(n+1)L(n)^{3/2}}<\infty.
```

The previously proved coordinate limit identifies g. Coordinate
convergence also bounds the finitely many coordinates below the
logarithmic threshold. Tannery's theorem applied to the full weighted
square error now proves norm convergence. The general transfer is
`pareto_tendsto_of_eventual_dominated_coordinates`.

## Stronger signed consequences

Let E_epsilon be the actual centered energy, Delta_epsilon the sum of
squared residue-atom norms, Omega_epsilon(M) the complete finite Gram
off-diagonal, and O_epsilon(H,M) its physical-head version.

1. `dampedMobius_full_offDiagonal_tendsto_of_half_le` proves
   Omega_epsilon(M) -> E_epsilon - Delta_epsilon.
   This follows from the exact identity
   ||F_epsilon,M||^2=Delta_epsilon(M)+Omega_epsilon(M).
2. `dampedMobius_offDiagonal_unrestricted_joint_tendsto` proves
   O_epsilon(H(j),M(j)) -> E_epsilon - Delta_epsilon for **any** two
   diverging cutoffs. The former H(j)<=M(j) restriction is removed.
   The head square error is bounded by the complete norm square error.
3. `dampedMobius_signed_bounds_of_half_le` supplies a single finite B
   bounding every full off-diagonal Omega_epsilon(M) and every signed
   head O_epsilon(H,M), independently of H and M.

Every result in this section assumes only epsilon>=1/2 (and the stated
cutoff divergence for the limit statements). Constants may depend on epsilon.

## Files and status

- `Analysis/WeightedMertensTransfer.lean`: monotonicity and the exact
  square-root expression for the logarithmic profile.
- `RH/DampedMobiusHalfEndpoint.lean`: reusable unconditional half-damped
  prefix estimate and coefficient bound.
- `RH/ArithmeticFloorTruncationBounds.lean`: exact truncation identities
  and the generic uniform physical envelope.
- `RH/ParetoDominatedConvergence.lean`: full Hilbert convergence from
  eventual uniform coordinate domination.
- `RH/DampedMobiusHalfHilbertConvergence.lean`: arithmetic specialization,
  full norm convergence, and the three signed consequences.

**Open:** actual subhalf energy and the signed bounds at positive dampings
approaching zero. These results do not descend below one half or prove RH.
The endpoint assertion is convergence in the natural conductor order.
It does not identify an unordered Hilbert `tsum` at the endpoint or assert
absolute convergence of the off-diagonal double series.

## Provenance and verification

Burnol, *On an analytic estimate in the theory of the Riemann zeta function
and a theorem of Baez-Duarte*, Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166, supports the underlying endpoint
membership statement. The uniform truncation argument above is supplied
explicitly from the repository's checked PNT, Abel, and hyperbola
providers; no mathematical novelty claim is made.

The complete source and main axiom checks passed with exit_code=0,
verified=true, and no warnings (job_YzFLhsGg5Nt5YF4Pt6Rx6pWzwGrAZmMj).
The endpoint convergence, unrestricted joint limit, and uniform signed
bounds depend only on propext, Classical.choice, and Quot.sound.
No sorry, admit, project-local axiom, or unsafe declaration is used.
Final publication checks the changed modules and their local reverse
dependents. The exact theorem hypotheses, not an axiom report alone,
establish that the endpoint arithmetic premises have been discharged.
