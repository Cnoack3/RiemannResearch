# Normalized signed cancellation below half damping

Date: 2026-09-27. Project: RiemannResearch, Lean 4 / Mathlib.

## Established result

Full natural-order Hilbert convergence at half damping now supplies an
unconditional normalized theorem for **every real epsilon<1/2**.
Write

```math
F_{\varepsilon,M}(n)
=-\sum_{d=1}^{M}\frac{\mu(d)}{d^{1+\varepsilon}}(n\bmod d),
\qquad
\|h\|_P^2=\sum_{n\ge1}\frac{|h(n)|^2}{n(n+1)}.
```

The new results prove the exact limits

```math
\lim_{M\to\infty}
\frac{\|F_{\varepsilon,M}\|_P}{(M+1)^{1/2-\varepsilon}}=0,
\qquad
\lim_{M\to\infty}
\frac{\|F_{\varepsilon,M}\|_P^2}{(M+1)^{1-2\varepsilon}}=0.
```

The vector itself tends to zero after multiplication by
(M+1)^(epsilon-1/2). These are full Hilbert norms, including the entire
infinite physical tail. There is no RH, arithmetic cancellation, or
bounded-energy premise in the specialized statements.

At zero damping this gives

```math
\lim_{M\to\infty}\frac{\|F_{0,M}\|_P}{\sqrt{M+1}}=0,
\qquad
\lim_{M\to\infty}\frac{\|F_{0,M}\|_P^2}{M+1}=0.
```

## Exact signed Gram consequences

Let Delta_epsilon(M) be the finite diagonal and Omega_epsilon(M) the
full finite off-diagonal, retaining both orientations of every pair.
The existing exact identity is

```math
\|F_{\varepsilon,M}\|_P^2
=\Delta_\varepsilon(M)+\Omega_\varepsilon(M).
```

The new proof establishes separately

```math
\lim_{M\to\infty}
\frac{\Delta_\varepsilon(M)}{(M+1)^{1-2\varepsilon}}=0,
\qquad
\lim_{M\to\infty}
\frac{\Omega_\varepsilon(M)}{(M+1)^{1-2\varepsilon}}=0.
```

No finite unnormalized infinite diagonal is assumed at epsilon=0
or negative epsilon.

For the signed physical head O_epsilon(H,M), the conclusion is uniform
in the head cutoff:

```math
\forall\eta>0\;\exists M_0\;\forall M\ge M_0\;\forall H\ge0,
\qquad
\frac{|O_\varepsilon(H,M)|}{(M+1)^{1-2\varepsilon}}\le\eta.
```

Thus any M_j->infinity and any H_j give a vanishing normalized absolute
signed-head limit. H_j need not diverge or satisfy a relative-rate condition.
The absolute value is taken after the full signed off-diagonal sum;
this is not a bound on the sum of absolute individual pairings.

## Proof of the analytic transfer

Let u_n be vectors with naturally ordered prefixes S_N=sum_{n<N}u_n
converging in norm. Let w_n>0 be increasing and tend to infinity.
Finite Abel summation gives, for N>=1,

```math
\sum_{n<N}w_nu_n
=w_{N-1}S_N+
\sum_{n<N-1}(w_n-w_{n+1})S_{n+1}.
```

A common signed-prefix norm bound C therefore bounds the weighted sum
by 2*w_N*C. Apply this same estimate to shifted prefixes

```math
\sum_{n<r}u_{K+n}=S_{K+r}-S_K.
```

For any eta>0, convergence supplies K for which all these tail norms
are at most eta. The normalized weighted tail then has norm at most
2*eta, independently of N>=K. The fixed finite head divided by w_N
tends to zero. This proves the vector Kronecker conclusion

```math
\frac1{w_N}\sum_{n<N}w_nu_n\longrightarrow0.
```

The proof requires neither absolute summability of u nor completeness
of the ambient space when its natural-order limit is supplied.

For the arithmetic application, take
u_n=-arithmeticResidueTerm(dampedMobiusWeight(1/2),n) and
w_n=(n+1)^(1/2-epsilon). The exact atom factorization turns the weighted
sum into F_epsilon,N. The base convergence is supplied by the already
checked unconditional half-endpoint theorem.

For the diagonal, apply the scalar version to
||arithmeticResidueTerm(dampedMobiusWeight(1/2),n)||^2, whose series is
already proved summable, with weights (n+1)^(1-2*epsilon).
Subtract the diagonal limit from the energy limit to obtain the full
signed off-diagonal limit.

Finally, the finite signed head obeys

```math
|O_\varepsilon(H,M)|
\le \|F_{\varepsilon,M}\|_P^2+\Delta_\varepsilon(M).
```

This estimate is uniform in H and proves the claimed head limits.

## Exact remaining gap

**Open:** bounded unnormalized signed norms or a suitable bounded signed
head criterion at positive dampings approaching zero. The normalizing
power grows when epsilon<1/2; its vanishing ratio does not bound the
unnormalized energy or establish subhalf Hilbert membership.

For the existing signed-growth route, a bound on the raw norm by
C*M^theta for M>=1, with a fixed theta<1/2, would imply finite energy at
every positive epsilon>theta through
`dampedMobius_energy_of_raw_signed_growth`.
The new limit at exponent 1/2 does not supply such a smaller exponent.
Arbitrarily small positive exponents would be sufficient to reach the
existing RH reductions, and remain open.

These theorems give unconditional normalized cancellation below one half,
including zero damping. They do not assert convergence of the
unnormalized subhalf Hilbert vectors, unordered Hilbert summability,
absolute off-diagonal summability, a new zero-free region, or RH.

## Files, provenance, and verification

- `Analysis/VectorKronecker.lean`: increasing-weight prefix and tail
  bounds, the vector Kronecker lemma, and its power specialization.
- `RH/DampedMobiusSubhalfNormalization.lean`: actual normalized
  vectors, norms, energies, diagonals, signed off-diagonals, uniform
  physical heads, and the zero-damping specializations.

The analytic proof is the classical Kronecker argument via finite Abel
summation, supplied explicitly here. The arithmetic input is the
repository's verified half-endpoint natural-order convergence.
Burnol, *On an analytic estimate in the theory of the Riemann zeta
function and a theorem of Baez-Duarte*, Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166, is the source for the underlying
endpoint membership statement. No mathematical novelty is claimed.

The complete combined source passed with exit_code=0 and verified=true,
without warnings (job_5xaqh9z9ZJGyO8_zlgwwe2kKsNECfhGj).
The principal axiom reports contain only propext, Classical.choice,
and Quot.sound. No sorry, admit, project-local axiom, or unsafe declaration
is used. Final publication validates the changed modules and their
affected local dependents.
