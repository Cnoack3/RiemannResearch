# Pareto capacity formalization — 21 September 2026

Source: user-provided argument in
`RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`.
This report records the precise declarations and their assumptions.

## Stage convention

The repository's stage `n` uses generators g_2,...,g_(n+1).
Thus the source note's N equals n+1.
The original weights are 1/[j(j+1)] at physical site j>=1.
New shape weights are a^(-alpha)-(a+1)^(-alpha); the physical tail starts at a=2.

## Original Pareto(1) capacity

The existing `ParetoTailCapacity.pointError_eq_inv_capacity` proves
pointError(n)=1/(tailCapacity(n)+2). Existing finite Gram and
`TailCapacityJointCorrections` declarations give the exact constrained
minimum 1/tailCapacity(n) for nonempty dictionaries.

`FirstCoordinateTailGap.tailCapacity_bounded_iff_not_RH` now states the
requested bounded-capacity equivalence directly. It takes the explicit
argument

```lean
hDensity : RiemannHypothesis → closedSpace = ⊤
```

This is the classical RH-to-density direction in Bagchi, Theorem 1:
https://arxiv.org/pdf/math/0607733.
The provider has not been proved in this addition. No project axiom is
introduced. The already-established direction from not RH to positive gap
does not require that argument. No positive or zero limiting gap is proved.

## Concrete rough-integer certificates

Module: `RH/ParetoRoughTailCertificates.lean`.

- `differenceCertificate` is the actual two-point Hilbert vector
  p(p+1)e_p-p(p-1)e_(p-1), with p=k+2.
- `differenceCertificate_norm_sq` proves its exact squared norm 2p^2.
- `differenceCertificate_inner_residue` retains the signed divisor term:
  its pairing with g_d is 1/d minus the indicator of d dividing p.
- `differenceCertificate_observation` proves actual finite-dictionary
  feasibility when p avoids all dictionary moduli.
- `tailCapacity_le_rough_certificate` and
  `tailCapacity_le_prime_certificate` bound the existing full-tail capacity.
- `differenceCertificate_sum_norm_sq` proves orthogonal finite averaging.
- `averagedRoughCertificate_norm_sq` and its observation theorem construct
  an actual feasible vector with squared norm the reciprocal of the
  finite inverse-energy mass.
- `roughCertificate_affine_energy_completion` proves exact finite-family
  optimality for every signed coefficient vector with sum one:
  energy=1/mass + squared distance from the inverse-square average.
  The corresponding lower-bound and equality-characterization theorems
  prove that this average uniquely minimizes energy within the family.
- `tailCapacity_mul_coprimeMass_le` passes to the entire infinite coprime
  sum using the proved summability of the actual reciprocal-square terms.
- `tailCapacity_le_eulerProduct` proves the full finite Euler-product bound
  for any nonzero even common multiple P of the dictionary moduli.
- `tailCapacity_le_factorial_eulerProduct` uses P=(n+1)! explicitly.
  Its prime factors are precisely the primes at most n+1.

The Euler-product identity is supplied by the existing
`ParetoEulerProduct.coprimeReciprocalSquareMass_eulerProduct`; it is not
assumed. All full-tail mixed terms remain in the actual Gram capacity.

The new finite-stage helpers in `ParetoTailCapacityDuality` prove
`finiteTailCertificate_energy_completion` and
`finiteTailCertificate_capacity_le`. In particular a feasible trial z has
exact energy C_n + ||z-tailMinimum(n)||^2. Infinite-dictionary observations
are not required for these finite conclusions.

These upper bounds are not uniform in the growing dictionary. They do not
prove either boundedness or divergence of the optimal capacities.

## General Pareto shapes and the critical boundary

Module: `RH/ParetoShapeMellinEnergy.lean`.

The definitions use the actual complex power difference and the actual
Pareto cell mass. Theorems establish:

- Positivity and the exact integral identity for `shapeCellWeight`.
- Weighted cell Cauchy–Schwarz.
- Summability of actual Mellin cell energy whenever
  0<alpha<2 Re(s).
- The full tail bound
  ||s||^2 a^(alpha-2 Re(s))/(alpha(2 Re(s)-alpha)).
- For the normalized coefficient
  m_s(a)=(a^(-s)-(a+1)^(-s))/s, the corresponding bound without ||s||^2.
- `criticalNormalizedTailEnergy_le`: the exact displayed upper-bound
  constant 2^(alpha-1)/(alpha(1-alpha)) for 0<alpha<1.
- `criticalShapeMellinCellEnergy_lower`: a harmonic lower bound at alpha=1.
- `criticalNormalizedTailEnergy_not_summable`: genuine nonsummability of
  the normalized critical-line certificate at alpha=1.

These analytic theorems are unconditional and do not assume zeta vanishing.
The boundary proofs reuse the existing critical-mode energy obstruction.

## Full finite legal combinations for the new shapes

Module: `RH/ParetoShapeCapacity.lean`.

`shapeLegalCombination` is the actual finite complex combination of all
residues in the indicated dictionary. `shapeLegalTailEnergy` is its entire
infinite weighted tail. Its summability is proved from boundedness of finite
residue combinations and summability of the actual shape weights.

`zero_shapeLegal_tail_hasSum` proves the exact signed arithmetic zero
pairing, using the existing Mellin residue formula.
`zero_shapeLegal_capacity_bound` then proves the uniform coefficient
inequality with the explicit tail constant.
`shapeFiniteCapacity` is the actual supremum of the squared head value
divided by the full tail energy, over every finite coefficient vector.
`zero_shapeFiniteCapacity_le` bounds this supremum.
`critical_shapeFiniteCapacities_bddAbove` bounds all stages for 0<alpha<1.

The last critical-line theorem explicitly assumes

```lean
hz : riemannZeta (MellinFrequency.criticalPoint t) = 0
```

It assumes neither RH nor not RH. Classical existence of critical-line
zeros is known, but a kernel-checked existence provider is not added here.
Thus the proof in Lean is parameterized by any actual critical-line zero;
the analytic energy threshold itself needs no such input.

## Certificates whose support escapes into the tail

Module: `RH/ParetoTailCertificateEscape.lean`.

`residue_two_tail_norm_sq_le` bounds the actual g_2 tail energy by
1/[4(N+1)]. With the actual normalization <g_2,z>=1/2 and physical
support at sites j>=M, `normalized_certificate_support_energy_lower`
proves ||z||^2>=M. The accompanying
`normalized_certificate_escaping_support_energy_tendsto` proves that
the squared norms of any such family tend to infinity. These results
have no RH or zeta-zero hypotheses and use the complete infinite tail.

## Scope and acceptance

The original note's continuous ambient-space caution is explanatory:
these arithmetic generators are unit-cell step functions. Non-step
annihilators in a larger continuous space do not automatically obstruct
either the constant or first-cell target.

The capacity, Euler-product, shape-energy, critical-boundary,
finite-family optimality, and general moving-support lower bound are
formalized above. The full Euler bound is obtained by finite exhaustion;
this addition does not separately construct the infinite averaged Hilbert
vector or prove its infinite-family equality characterization.

Development candidates were checked in serialized Lean jobs. Final
acceptance is the repository checkpoint, which audits the source, builds
changed modules and their local reverse dependents, and publishes only
after successful validation. The publication commit is recorded in Git.
No sorry, admit, local axiom, or unsafe declaration is introduced.

## Continuation: critical-line zero search and numerical first zero

Date: 21 September 2026. Starting published commit:
`82c4ba162d52a3be7d83f3dfc1823d969e99e7c1`.

### What the installed Lean dependency supplies

The pinned Mathlib revision is
`51e6992efd06126df61a496bebf8f49482a4e129` (`v4.33.0-rc2`).
It includes `Mathlib.NumberTheory.LSeries.ZetaZeros`.
Its relevant declarations are:

- `riemannZetaZeros`: the set of all zeros.
- `mem_riemannZetaZeros`: membership is equivalent to actual zeta vanishing.
- `isClosed_riemannZetaZeros` and `isDiscrete_riemannZetaZeros`.
- `IsCompact.inter_riemannZetaZeros_finite`: compact sets contain finitely many zeros.
- `tendsto_riemannZeta_cofinite_cocompact`.

These results do not exhibit a zero with real part one half. Bounded
declaration searches in both this project and the pinned Mathlib dependency
did not locate Hardy's theorem or a checked first-positive-zero provider.
This is a report about the inspected dependency, not a claim about every
external Lean project.

Source for the package's statements:
[Mathlib ZetaZeros source at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/NumberTheory/LSeries/ZetaZeros.lean).

### Numerical computation

Using Python 3.12.14 and mpmath 1.4.1 at 120 decimal digits of working
precision, `zetazero(1)` returned the approximation

\[
\rho_1=\frac12+i\gamma_1,\qquad
\gamma_1\approx
14.13472514173469379045725198356247027078425711569924317568556746014996342980925676494901039317156101.
\]

At the internal, unrounded approximation, the computed residual was

\[
|\zeta(\rho_{1,\mathrm{num}})|\approx 2.163980592834693\times10^{-121}.
\]

This residual is not an error bound for the displayed decimal and is not a
proof that any finite decimal is an exact zero.

For the real Hardy function
\(Z(t)=e^{i\theta(t)}\zeta(\tfrac12+it)\), mpmath returned

\[
Z(14)\approx-0.10562626777988261013891075576194791686188797004733,
\]
\[
Z(15)\approx 0.71994239134213713351661016594703005117787734307689.
\]

Its numerical zero-count routine returned \(N(14)=0\) and \(N(15)=1\).
A tighter numerical sign bracket is

\[
\begin{aligned}
a&=14.13472514173469379045725198356247027078425711569924,\\
b&=14.13472514173469379045725198356247027078425711569925,\\
Z(a)&\approx-2.5188281408906945825755300209075938413782932954927
           \times10^{-51},\\
Z(b)&\approx 5.4127761926743665775634456318359273000806357550502
           \times10^{-51}.
\end{aligned}
\]

These are floating-point computations. Neither the signs nor the zero
counts are certified in Lean by this continuation. A formally proved
real-valued continuous Hardy function and certified endpoint signs would
suffice for existence by the intermediate value theorem. Proving that the
root is the *first* positive root additionally requires excluding earlier
zeros. The Pareto capacity application only needs existence of one
critical-line zero; it does not need firstness.

The numerical result agrees with the first-zero example in
[mpmath's documentation](https://mpmath.readthedocs.io/en/latest/functions/zeta.html).
The [LMFDB zeta-zero database](https://www.lmfdb.org/zeros/zeta/) separately
documents high-precision initial critical-line zeros; those external
certificates are not Lean declarations in this project.

### Consequence for the explicit Pareto constant

For an actual critical-line zero \(\rho=\tfrac12+it\), retain the exact
constant

\[
A(\rho)=\frac{|\rho|^2}{|1-2^{-\rho}|^2}.
\]

The existing coefficient and supremum theorems give, for \(0<\alpha<1\)
and every finite stage \(n\),

\[
\operatorname{shapeFiniteCapacity}(\alpha,n)
\le
A(\rho)\frac{2^{\alpha-1}}{\alpha(1-\alpha)}.
\]

Evaluating the exact expression at the numerical first-zero approximation
gives

\[
A(\rho_1)\approx
71.00831118873284247475329639853726496100261170179239583445514975815115.
\]

For example, at \(\alpha=\tfrac12\), the exact bound is
\(2\sqrt2\,A(\rho_1)\), whose numerical value is approximately

\[
200.84183344863035350178306739698427811488073023143.
\]

The displayed rounded constants are numerical evaluations, not certified
upper bounds substituted into Lean. This does not address the original
\(\alpha=1\) capacity, whose Mellin certificate has nonsummable energy.

### Reproduction

Run the following with mpmath 1.4.1 installed. It needs no Lean process.

```python
import mpmath as mp

mp.mp.dps = 120
rho = mp.zetazero(1)
A = abs(rho)**2 / abs(1 - mp.power(2, -rho))**2

print("mpmath:", mp.__version__)
print("working decimal digits:", mp.mp.dps)
print("rho:", mp.nstr(rho, 100))
print("abs(zeta(rho)):", mp.nstr(abs(mp.zeta(rho)), 16))
print("A(rho):", mp.nstr(A, 70))
print("C_bound_alpha_half:", mp.nstr(A * 2 * mp.sqrt(2), 50))

for x in (mp.mpf(14), mp.mpf(15)):
    print("Hardy_Z(%s):" % x, mp.nstr(mp.siegelz(x), 50))
    print("N(%s):" % x, mp.nzeros(x))

lo = mp.mpf("14.13472514173469379045725198356247027078425711569924")
hi = mp.mpf("14.13472514173469379045725198356247027078425711569925")
print("Hardy_Z(lo):", mp.nstr(mp.siegelz(lo), 50))
print("Hardy_Z(hi):", mp.nstr(mp.siegelz(hi), 50))
```

### Formal status and stopping point

The continuation records the package audit and numerical computation; it
does not add or change a Lean theorem. A serialized Lean check completed
successfully (exit code 0), confirming the package declarations and the
exact type of `critical_shapeFiniteCapacities_bddAbove`. Its axiom audit
reported only `[propext, Classical.choice, Quot.sound]`. That audit does not
discharge the theorem's explicit local hypotheses. The substantive input

```lean
hz : riemannZeta (MellinFrequency.criticalPoint t) = 0
```

remains explicit. No decimal approximation is asserted to satisfy it, and
no axiom is introduced. The RH-to-density input attributed to Bagchi also
remains explicit and untouched. Work stops after publishing this record,
pending the user's exact Bagchi equation.

## Continuation: infinite coprime average and exact capacity gap

Date: 21 September 2026. Starting published commit:
`dde42cb74277ded4075568dbab09abebaa6c891c`.

This continuation completes the infinite-vector construction and
infinite-family equality characterization explicitly left open in the
original scope section. It resumes the project after the numerical-zero
record above. It does not use a new zeta-zero existence provider or a
Bagchi-density provider.

### Exact construction

Keep the original Pareto weights \(w_j=1/[j(j+1)]\). For a nonzero even
integer \(P\), let

\[
\mathcal R_P=\{p\in\mathbb N:p\ge3,\ p\text{ odd},\ \gcd(p,P)=1\},
\qquad
S_P=\sum_{p\in\mathcal R_P}\frac1{p^2},
\qquad M_P=\frac{S_P}{2}.
\]

The arithmetic series defining \(S_P\) is summable, and \(S_P>0\).
For \(p\in\mathcal R_P\), set

\[
u_p=p(p+1)e_p-p(p-1)e_{p-1}.
\]

The original module proves \(\|u_p\|^2=2p^2\); distinct vectors in this
odd-indexed family are orthogonal. The new construction is the genuine
Hilbert-norm sum

\[
z_P=\frac1{M_P}\sum_{p\in\mathcal R_P}\frac{u_p}{2p^2}
    =\sum_{p\in\mathcal R_P}\frac{u_p}{S_Pp^2}.
\]

Lean proves the `HasSum` statement for this vector series, not just
convergence of the scalar masses. Its coefficients have `HasSum` one.
The squared norm is exactly

\[
\boxed{\|z_P\|^2=\frac1{M_P}
=\frac2{S_P}
=\frac{2}{
(\pi^2/6)\prod_{\ell\mid P,\ \ell\ {\rm prime}}(1-\ell^{-2})-1}.}
\]

The construction uses summability of squared norms of the orthogonal
summands. It does not assume absolute summability of their vector norms.

### Actual tail feasibility

If every dictionary modulus \(d=2,\ldots,n+1\) divides \(P\), then

\[
\langle g_d^{\rm tail},z_P\rangle=\frac1d.
\]

The new theorem also proves \(\langle z_P,e_1\rangle=0\), retaining the
absence of a first-coordinate component after infinite summation.
These are statements in the original infinite Pareto Hilbert space, with
the entire weighted tail and all the finite-dictionary observations.

### Infinite-family optimality with signed coefficients

Let \(a_p\) be arbitrary real coefficients such that
\(\sum_{p\in\mathcal R_P}a_pu_p\) has Hilbert sum \(z\). The general theorem
first proves that the scalar coefficients themselves are summable. Thus
the normalization \(\sum_p a_p=1\) is not being imposed on an undefined or
totalized divergent series.

Under that normalization, Lean proves

\[
\boxed{\|z\|^2=\frac2{S_P}+\|z-z_P\|^2.}
\]

Consequently \(\|z\|^2\ge 2/S_P\), with equality exactly when \(z=z_P\).
The normalized inverse-square coefficients attain the minimum. This
extends the finite-family theorem to every convergent signed combination
of the whole infinite coprime family.

### Exact gap to the unrestricted capacity

Let \(C_n=\operatorname{tailCapacity}(n)\) and
\(z_n^{\min}=\operatorname{tailMinimum}(n)\). The existing finite-dictionary
energy completion now applies to the constructed infinite vector:

\[
\boxed{
\frac2{S_P}=C_n+\|z_P-z_n^{\min}\|^2.
}
\]

The Euler-product form is also proved directly:

\[
\boxed{
\frac{2}{
(\pi^2/6)\prod_{\ell\mid P,\ \ell\ {\rm prime}}(1-\ell^{-2})-1}
=C_n+\|z_P-z_n^{\min}\|^2.
}
\]

Thus the earlier Euler bound has an explicit feasible Hilbert vector,
and its entire slack is identified exactly. Optimality inside the coprime
family does not assert that this vector minimizes over all feasible
vectors. Equality with the unrestricted capacity holds precisely when
the displayed Hilbert distance vanishes.

A growing value of the left-hand side does not alone force \(C_n\) to
diverge: the squared-distance term is still present. This continuation
does not prove either boundedness or divergence of the capacities.

### Declarations and assumptions

New general module: `Analysis/OrthogonalAffineSeries.lean`.

The namespace is
`RiemannResearch.Analysis.OrthogonalAffineSeries`.
Its reusable declarations include:

- `summable_iff_sq_norm_summable`: orthogonal Hilbert summability.
- `reciprocalEnergy_summable`, `reciprocalEnergyVector_inner`,
  and `reciprocalEnergyVector_norm_sq`: the actual infinite vector,
  its unit pairings, and exact energy.
- `coefficient_hasSum`: scalar coefficient summability for every
  convergent signed vector series in this family.
- `affineMinimum_hasSum` and
  `affineMinimum_coefficients_hasSum`: attainment and normalization.
- `affine_energy_completion` and `affine_energy_eq_iff`:
  exact infinite affine energy and uniqueness.

New arithmetic module: `RH/ParetoInfiniteRoughTailCertificates.lean`.

The namespace is the existing
`RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity`.
Its main declarations are:

- `coprimeCertificate_reciprocalEnergy_summable` and
  `coprimeCertificate_reciprocalEnergyMass`.
- `infiniteCoprimeCertificate_hasSum` and
  `infiniteCoprimeCertificate_coefficients_hasSum`.
- `infiniteCoprimeCertificate_inner_firstPoint`,
  `infiniteCoprimeCertificate_norm_sq`, and
  `infiniteCoprimeCertificate_observation`.
- `infiniteCoprimeCertificate_affine_energy_completion` and
  `infiniteCoprimeCertificate_affine_energy_eq_iff`.
- `infiniteCoprimeCertificate_capacity_gap` and
  `infiniteCoprimeCertificate_eulerProduct_capacity_gap`.

The arithmetic hypotheses are \(P\ne0\), \(2\mid P\), and, for the finite
dictionary assertions, \(d\mid P\) for every \(2\le d\le n+1\).
Signed-series optimality additionally specifies the Hilbert convergence
and scalar normalization of the trial combination. The arithmetic
construction proves its own reciprocal-energy summability.
No theorem in this addition assumes RH, not RH, a critical-line zero,
or RH-to-density.

### Verification and remaining frontier

The proof candidates were checked serially. The key axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`.
Both modules are exported from `RiemannResearch.lean`; the theorem
catalog records their established status and separates the open capacity
limit from the completed certificate construction.

Final project acceptance is the single publishing checkpoint containing
this section, which audits the source and builds the changed modules and
their local reverse dependents. Its publication commit is recorded in Git.

The following remain open in this record:

1. Boundedness or divergence of the unrestricted \(\alpha=1\) capacities.
2. A kernel-checked provider of an actual critical-line zeta zero for the
   previously conditional \(0<\alpha<1\) application.
3. The explicitly retained Bagchi RH-to-density input.

The floating-point first-zero calculation recorded earlier is unchanged.
