# Dyadic CRT schedules, complete errors, and the Pareto comparison

Continuation of the epsilon formulation in commit 024c2f6. Earlier fixed-stage
minimizers, conductor-gap obstructions, and finite certificates remain intact.

## Concrete choice and precise theorem

Choose
\[
\varepsilon_n=2^{-n},\qquad H_n=5\cdot4^n,\qquad
\delta_n=\varepsilon_n^2/8.
\]
The tolerances strictly decrease to zero, the heads strictly increase to
infinity, and \(H_n\varepsilon_n^2=5\). Since \(5>608/125\), the complete
Q-tail estimate gives
\[
\tau_Q(H_n)\le\frac{76}{625}\varepsilon_n^2<\frac{\varepsilon_n^2}{8}.
\]

The explicit arithmetic input, named DyadicMinimumProvider, is
\[
\forall n\in\mathbb N\;\exists j:\quad
H_n\le j+1,\qquad E(j,H_n)\le1+\delta_n.
\]
Here E(j,H) is the squared complete Q norm of minimumAt j H, with period
primorial(j+2), the product of primes at most j+2.

The new Lean theorem dyadicProvider_iff_minimum_energy_witnesses proves
equivalence with the previous all-real-epsilon energy provider. Thus the
dyadic choice makes the problem countable and explicit without strengthening
that provider. It does not prove that the provider holds.

Given these witnesses j(n), define
\[
J_0=j(0),\qquad J_{n+1}=\max\{j(n+1),J_n+1\}.
\]
The indices J are strictly increasing and tend to infinity. Enlargement of
the primorial period preserves each successful energy bound. The actual
vectors
\[
F_n=\operatorname{minimumAt}(J_n,H_n)
\]
are legal, retain the exact heads, and satisfy
\[
\|F_n\|_Q^2\le1+\delta_n\le9/8,\qquad
\|1-F_n\|_Q<\varepsilon_n,\qquad F_n\longrightarrow1
\]
in the complete Q Hilbert norm. These conclusions, including the literal
norm convergence, are formalized in exists_cofinal_minimum_schedule.
They remain conditional on DyadicMinimumProvider.

The sharper checked estimate dyadic_error_sq_bound is
\[
\|1-F_n\|_Q^2
\le\left(\frac14+\frac{304}{625}\right)\varepsilon_n^2
=\frac{1841}{2500}\varepsilon_n^2.
\]
The starting point is the complete signed head/tail identity from
QExactHeadEpsilonBounds, with its mixed tail term retained before estimation.

## Certified initial stages and the first unresolved test

| n | epsilon | head | allowed energy | achieved result | status |
|---|---:|---:|---:|---|---|
| 0 | 1 | 5 | 9/8 | period 30, energy at most 1 | Lean kernel theorem |
| 1 | 1/2 | 20 | 33/32 | period 9699690, energy at most 311254353881/312500000000 | Lean kernel theorem |
| 2 | 1/4 | 80 | 129/128 | primorial through 79, energy at most 13222897792897/13159200000000 | external exact-rational certificate |
| 3 | 1/8 | 320 | 513/512 | no qualifying certificate found | Open |

The first two statements are specialized to the actual minima by the new
dyadic_zero_certificate and dyadic_one_certificate. The head-20 minimum is
minimumAt 19 20; its primorial period is still 9699690.

The new head-80 period is exactly
\[
L=\prod_{p\le79}p=3217644767340672907899084554130.
\]
Its rational witness uses 126 squarefree conductors d at most 300 dividing L.
Every head equation through 80 is checked exactly. The certificate proves
\[
\|F\|_Q^2
\le \frac{13222897792897}{13159200000000}
=1.0048405520774059\ldots
<\frac{129}{128}.
\]
Consequently the constrained minimum at this full divisor period also obeys
the same upper bound; no claim is made that the restricted witness is that
full-dictionary minimizer.

Its complete error satisfies
\[
\|1-F\|_Q^2
\le \frac{263717632897}{6579600000000}
<\left(\frac{201}{1000}\right)^2
<\left(\frac14\right)^2.
\]
The head-80 result is an external integer/rational computation, not a Lean
theorem about this vector. The universal analytic error estimate is checked
in Lean, but the numerical witness has not been connected to that theorem
inside the kernel.

For head 320, restricted numerical searches with conductors at most 1000
and 1500 gave approximate best trial energies 1.00855921 and 1.00696195.
These exceed the target 513/512 = 1.001953125. They do not bound below the
minimum over larger dictionaries, so they do not refute the proposed schedule.

The [reproducibility packet](CofinalScheduleHead80Certificate20261028.md)
contains the immutable witness, exact verifier, complete Gram calculation,
and exploratory numerical scripts and outputs. The independent verifier
passed with exit code 0. Wolfram confirmed the rational error comparison
and the dyadic constants.

## How Pareto helps

Let T be the actual physical-coordinate map to the Pareto Hilbert space.
The existing shifted-reciprocal operator B has multiplier 1/(n+1) at physical
site n. The new module QExactHeadMeasureComparison first proves
\[
\|Tf\|_P^2=\zeta(2)\bigl(\|f\|_Q^2-\langle f,Bf\rangle_Q\bigr).
\]
For any error e vanishing at physical sites 1 through H, it then proves
\[
0\le\zeta(2)\|e\|_Q^2-\|Te\|_P^2
\le\frac{\zeta(2)}{H+2}\|e\|_Q^2,
\]
and therefore
\[
\boxed{\quad
\zeta(2)\frac{H+1}{H+2}\|e\|_Q^2
\le\|Te\|_P^2
\le\zeta(2)\|e\|_Q^2.
\quad}
\]
This comparison applies to F-1 for exact-head vectors, or to two vectors
with the same head. The complete metrics become asymptotically proportional
on these errors, regardless of the coefficients.

Pareto also has the exact target-tail formula
\[
\tau_P(H)=\frac1{H+1},
\]
already checked as Pareto.paretoTail_norm_sq in ParetoHeadMeanEnergy.
For a Pareto version of the energy argument, H_n=8*4^n-1 makes
tau_P(H_n)=epsilon_n^2/8 exactly. The corresponding near-unit Pareto-energy
certificates still have to be supplied. Changing the measure does not supply
them. In particular, comparisons of raw full energies must not be substituted
for comparisons of errors, and the two metrics' minimizers need not coincide.

## What Ramanujan coordinates preserve

The existing RamanujanCanonicalOptimizer and QRamanujanCanonicalOptimizer
modules identify packet-coordinate solutions with the same finite residue
vectors. This can simplify the constraint matrix and numerical conditioning.

The objective remains the complete signed weighted Gram form.
ParetoCRTGramTransfer.centeredResidue_paretoInner_eq_uniform_add_defect
explicitly retains the correction to uniform CRT covariance. Increasing the
period does not authorize deleting that correction. The head-80 computation
retains all cross terms; it independently evaluates the complete pairwise-LCM
Gram entries and separately verifies the rational witness using a finite
ceiling sum plus a rigorous bound for the entire infinite tail.

No all-stage energy provider was obtained from the Ramanujan coordinate change.

## What is proved and what remains open

The new saved Lean modules are:

- QCRTDyadicEpsilonSchedule.lean: the explicit head/tolerance sequence, the
  equivalence of arithmetic providers, increasing cofinal period indices,
  conditional convergence of actual minima, and the first two finite stages.
- QExactHeadMeasureComparison.lean: the exact complete metric identity and
  the sharper Q/Pareto comparison for matching-head errors.

The saved modules built and nine main declarations passed axiom audits in
job_jJO_3uclTGzQ4CXLwrNO-qLgk6VJa4Mk (exit code 0). The audits report only
propext, Classical.choice, and Quot.sound. Publication additionally validates
the aggregate project and the changed modules.

Unconditionally, the existing QSquarefreePrimorialCofinality module proves
that the full primorial projections converge to the projection of 1 onto
the closed legal span S. Reindexing cofinally preserves that limit.
Identifying it with 1 remains the unresolved residual-zero statement.

Open: establish DyadicMinimumProvider for every n, equivalently prove
termination of the period/dictionary search at every tolerance. The first
unresolved test in this particular schedule is head 320. The head-80 success
and conditional convergence theorem do not establish an infinite cofinal
family, a uniform bound for such a family, or RH.
