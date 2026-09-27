# Centered finite-head growth below half damping

Date: 2026-09-27. Project: RiemannResearch, Lean 4 / Mathlib.

## Established result

For every fixed real damping 0 < epsilon < 1/2, write

```math
g_\varepsilon(n)
=\operatorname{dampedMobiusPrefix}(\varepsilon,n)
-n\operatorname{Re}\frac{1}{\zeta(1+\varepsilon)},
\qquad
E_\varepsilon(H)=\sum_{n<H}\operatorname{positiveWeight}(n)
                    g_\varepsilon(n)^2.
```

The new unconditional theorem is

```math
\lim_{H\to\infty}\frac{E_\varepsilon(H)}
 {(H+1)^{1-2\varepsilon}}=0.
```

This is the energy of the actual centered arithmetic sequence on a finite
physical head. The conductor has already been completed in its definition.
It is a further consequence of the previously proved normalized Hilbert
cutoff estimates, not an assumption of total centered energy.

Let Delta_epsilon(H) be the completed nonnegative head diagonal and let
L_epsilon(H) be the full signed conductor limit on that head. The existing
exact identity is L_epsilon(H)=E_epsilon(H)-Delta_epsilon(H). We also prove

```math
\frac{\Delta_\varepsilon(H)}{(H+1)^{1-2\varepsilon}}\longrightarrow0,
\qquad
\frac{|L_\varepsilon(H)|}{(H+1)^{1-2\varepsilon}}\longrightarrow0.
```

The absolute value follows the complete signed sum.

## Two-scale proof

The checked signed density-tail estimate and finite weighted energy
comparison give, whenever H <= M and M >= 1,

```math
E_\varepsilon(H)\le
2\|F_{\varepsilon,M}\|_P^2+
\frac{2}{\varepsilon^2}H M^{-2\varepsilon}.
```

The prior theorem says ||F_epsilon,M||_P^2/(M+1)^(1-2*epsilon) tends to zero.
To transfer this fact, fix an integer k >= 1 and choose

```math
M=k(H+1)+H,\qquad M+1=(k+1)(H+1).
```

For fixed k, the normalized first term tends to zero exactly by this affine
identity. The normalized second term is at most
(2/epsilon^2)*k^(-2*epsilon), since H <= H+1 and M >= k(H+1).
First make this bound small by choosing k, then take H sufficiently large.
This avoids requiring any unproved quantitative convergence modulus or
letting k vary inside the fixed-k convergence theorem.

The generic theorem uses only q>0, C>=0, E(H)>=0, the comparison

```math
E(H)\le A(M)+CHM^{-q},
```

and A(M)/(M+1)^(1-q)->0. It concludes E(H)/(H+1)^(1-q)->0.
Neither q<1 nor nonnegativity of A is needed for that analytic transfer.
The arithmetic specialization supplies q=2*epsilon and A(M)=2||F_epsilon,M||^2.

The completed diagonal already tends to the finite exact diagonal for
every epsilon>0. Multiplication by the decaying inverse normalization
therefore proves its normalized limit. Subtraction and continuity of
absolute value prove the signed limit.

## Dependencies discharged and remaining

**Established:** the transfer from normalized finite-conductor Hilbert
energy to normalized actual centered physical-head energy, throughout
0<epsilon<1/2. The completed diagonal and signed-head consequences have
no unresolved arithmetic hypotheses.

**Open:** a bound on the unnormalized E_epsilon(H), uniformly in H, below
half damping; suitable bounded-energy providers at positive dampings
approaching zero; and the corresponding remaining RH reduction premises.
A vanishing ratio with a growing denominator permits unbounded energy.
The new theorem therefore does not prove subhalf Hilbert membership,
a fixed power saving, a new zero-free region, or RH. It does not extend
the completed density formula to epsilon=0.

## Lean declarations

In `Analysis/TwoScaleEnergyTransfer.lean`:

- `linear_inverse_power_normalization`
- `affine_cutoff_normalized_tendsto`
- `two_scale_energy_tendsto_zero`

In `RH/DampedMobiusCenteredHeadGrowth.lean`:

- `dampedMobiusCenteredHeadEnergy`
- `dampedMobiusCenteredHeadEnergy_nonneg`
- `dampedMobius_centered_head_energy_le`
- `dampedMobius_centered_head_energy_normalized_tendsto`
- `dampedMobius_completed_head_diagonal_normalized_tendsto`
- `dampedMobius_signed_head_limit_normalized_tendsto`

## Provenance and verification

Source: the two-scale argument developed explicitly in this session,
using the repository's previously checked signed head approximation,
finite weighted energy comparison, vector Kronecker specialization,
and exact diagonal limit. No mathematical novelty claim is made.

The coherent candidate was checked by Lean. Axiom inspection of the
generic transfer and main arithmetic conclusions reports only ordinary
Mathlib foundations, with no project-local axiom or unresolved arithmetic
premise. Final publication is gated by the workspace checkpoint's source
audit and affected-module validation. No placeholder proof is persisted.
