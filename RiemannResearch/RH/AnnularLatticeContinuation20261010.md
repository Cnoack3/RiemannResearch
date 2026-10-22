# Exact annular lattice correction and arithmetic energy transfer

Continuation of **RH_Annular_Lean_Chat_Record_20261009** — 10 October 2026 UTC.

The lattice-decay obligation in Sections 2, 8, and 9 of the supplied record
is discharged. Quantitative weighted membership and a bounded convergent
correction between the two actual critical energies are also proved.
**RH and the actual signed residual estimate remain open.**

## Actual signals and exact correction

Retain the original annular weight
\[
W(u)=(1-u)_+^2-\frac74(1-2u)_+^2+
       \frac78(1-4u)_+^2-\frac18(1-8u)_+^2.
\]
The actual signals are
\[
A(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)W(n/x)-\frac7{64}x,\qquad
U(x)=\sum_{1\le n\le\lfloor x\rfloor}(\Lambda(n)-1)W(n/x).
\]
The exact difference is \(\delta=A-U\). All prime powers, singleton
coefficients, fractional cutoffs, and endpoint terms are retained.

Let \(B_3(t)=t^3-\frac32t^2+\frac12t\). Lean proves the finite Riesz sum
\[
\sum_{1\le n\le\lfloor y\rfloor}(1-n/y)^2
=\frac y3-\frac12+\frac1{6y}-\frac{B_3(\{y\})}{3y^2},\qquad y>0.
\]
Induction proves the finite polynomial identity. The four dilations cancel
the constant and reciprocal terms exactly, giving
\[
\boxed{\delta(x)=
\frac{-B_3(\{x\})+7B_3(\{x/2\})-14B_3(\{x/4\})+8B_3(\{x/8\})}
{3x^2}\quad(x>0).}
\]

## Sharp all-cutoff decay

The signed numerator \(P(x)\) reduces to eight exact cubic pieces on
\(y=8\{x/8\}\in[0,8)\). Rational Bernstein certificates bound the coarse
pieces. On the decisive piece \(y=2+t\), \(0\le t\le1\),
\[
\frac{10}{9}-P(2+t)=
\frac{(3t-2)^2(106+21t)}{576}\ge0.
\]
Lean proves
\[
\boxed{|P(x)|\le10/9,\qquad |\delta(x)|\le\frac{10}{27x^2}\quad(x>0).}
\]
At \(x=8/3\), \(\delta(x)=5/96\) and \(x^2|\delta(x)|=10/27\).
A theorem quantifies over every possible replacement coefficient and proves
that no smaller global coefficient works. ActualLatticeDecay now has the
unconditional provider AnnularCriticalEnergy.actualLatticeDecay.

## Actual weighted membership and Mellin control

In the project normalization \(H_a=L^2((1,\infty),x^{-2a-1}dx)\), Lean proves
global measurability of the actual correction, using the exact Bernoulli
quotient above 1 and the empty-cutoff formula \(\delta(x)=-7x/64\) below 1.
It then proves, for every \(a>-2\),
\[
\boxed{\delta\in H_a,\qquad
\|\delta\|_{H_a}^2\le\frac{100}{729(2a+4)},\qquad
A\in H_a\iff U\in H_a.}
\]
The equivalence does not establish membership of either infinite prime
signal at an RH-sensitive weight.

For \(\mathcal M\delta(z)=\int_1^\infty\delta(x)x^{-z-1}dx\), the proven
weighted Mellin APIs imply analyticity on \(\Re z>-2\).
Optimizing the point-evaluation estimate gives
\[
\boxed{|\mathcal M\delta(z)|^2\le
\frac{100}{729(\Re z+2)^2}\quad(\Re z>-2).}
\]
The new uniform corollary gives the bound \(25/729\) at every coordinate
with positive real part. It applies at full nontrivial zero coordinates
once their ordinary strip data is supplied, independently of RH.

## Complete signed critical-energy transfer

Define \(E_f(X)=\int_{[1,X]}f(x)^2/x^2\,dx\), with the empty-set value
for \(X<1\). For every real cutoff Lean proves
\[
\boxed{E_A(X)=E_U(X)+D(X),\quad
D(X)=\int_{[1,X]}\frac{2U(x)\delta(x)+\delta(x)^2}{x^2}\,dx.}
\]
The signed cross term and lattice square are explicitly retained.

The elementary \(\Lambda(n)\le\log n\) estimate gives
\[
|U(x)|\le\frac7{24}x(1+\log x)\qquad(x\ge1).
\]
For \(C=10/27\), the absolute correction density is dominated by
\(2(7/24)C(1+\log x)x^{-3}+C^2x^{-6}\).
Its exact integral is \(7C/16+C^2/5\). Thus Lean proves
\[
\boxed{|E_A(X)-E_U(X)|\le1105/5832\quad\text{for every real }X,}
\]
and
\[
\boxed{E_A(X)-E_U(X)\longrightarrow
\int_1^\infty\frac{2U(x)\delta(x)+\delta(x)^2}{x^2}\,dx.}
\]
The limiting integral is absolutely convergent; its value and sign are
not asserted. The energy-difference envelope is not claimed sharp.

Using \(\log X\ge\log2>0\) for \(X\ge2\), the bounded correction gives the
unconditional equivalence ActualPrimeEnergyUpperBound iff
ActualEnergyUpperBound. The signed-residual equivalence still explicitly
requires ActualModelLogBound. The RH equivalence still explicitly requires
ActualRHEnergyCriterion. Neither premise is supplied by this continuation.

## Formalization and verification scope

Five new exported modules contain 49 public theorems:

| Module | Responsibility |
|---|---|
| RH/AnnularLatticeCorrection.lean | Finite polynomial sum and exact signed Bernoulli formula |
| RH/AnnularLatticeBounds.lean | Rational cubic certificates and optimal decay constant |
| Analysis/SignedLatticeEnergy.lean | Reusable signed energy identity, integrability, bound, and convergence |
| RH/AnnularCriticalEnergyTransfer.lean | Actual growth, lattice provider, energy transfer, and conditional reductions |
| Analysis/ActualAnnularLatticeWeighted.lean | Actual measurability, weighted norms, membership equivalence, and analytic correction |

Decisive theorem names include annularLatticeFinite_eq_bernoulli,
annularLatticeFinite_abs_le, annularLatticeFinite_constant_optimal,
AnnularCriticalEnergy.actualLatticeDecay,
AnnularCriticalEnergy.actualPrimeSignal_energy_difference_abs_le,
AnnularCriticalEnergy.actualPrimeSignal_energy_difference_tendsto,
AnnularCriticalEnergy.actualPrimeEnergyUpperBound_iff_actualEnergyUpperBound,
WeightedMellinTopology.actualAnnularLatticeVector_Ha,
WeightedMellinTopology.actualCentered_Ha_iff_actualPrimeSignal_Ha, and
WeightedMellinTopology.actualAnnularLatticeVector_transform_analyticAt.

The successful combined server source check was
**job_v-E2dHkADCWD2WP9QI-AS2-XcEUhWBWP**, with
state succeeded, classification success, exit code 0, and verified true.
Its checker SHA-256 was
**392461eba86530415ab45d722b51be3afe454913781abc544932d4d47f5c1cdf**.
The checker requested axiom inspection of every public continuation theorem.
The returned log was bounded. The earlier decisive sharp-lattice audit,
job_-IkB5pfjtotNOJpB3RGsdfNLc_y-svBs, reported only propext,
Classical.choice, and Quot.sound.

The baseline was 6fd4c413ad6189bed30bdfd8678779f9249aff74.
The recorded Lean 4.33.0-rc2 and pinned mathlib environment were retained.
No added axiom, unproved placeholder, unsafe declaration, or dependency
upgrade is part of the continuation. Final repository acceptance is the
server checkpoint introducing these modules, which separately validates
the module sources and required dependencies before publication.
The source check itself does not certify a full repository build.

## Remaining RH target

The lattice term is now controlled. The arithmetic task remains quantitative
infinite-tail control of \(U\), equivalently \(A\), at the required weights.
The signed prime-pair target is still \(R_X\le C\log X\) for every \(X\ge2\),
with the complete signed decomposition. The model estimate and analytic
RH-energy bridge remain explicit obligations.

The next analytic target is the RH implication from the actual all-cutoff
prime-energy bound, using the initial Mellin identity, holomorphic
continuation, and the nonzero annular zero-pole multiplier. It must discharge
the local identity bridge, rather than assume it as a provider.
The new bounded energy correction supplies no prime-pair cancellation.

## Sources and small computations

- [NIST DLMF 2.10(i)](https://dlmf.nist.gov/2.10): classical remainder strategy.
- [NIST DLMF 24.2](https://dlmf.nist.gov/24.2): periodic Bernoulli definitions.
- [NIST DLMF 24.4(ii),(iii)](https://dlmf.nist.gov/24.4): classical symmetry and
  polynomial power sums.
- Existing project modules AnnularArithmeticWeight, ActualAnnularKernel,
  WeightedMellinEnergy, and WeightedMellinLogarithmicKernel provide the actual
  definitions and proved analytic APIs.
- Wolfram checked the rational factor certificate and a few exact sample
  values. Lean supplies the all-cutoff proof evidence.
  No mathematical novelty claim follows solely from this formalization.
