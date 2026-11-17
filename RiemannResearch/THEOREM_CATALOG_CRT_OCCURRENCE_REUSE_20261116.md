# CRT occurrence relaxation, atom reuse, and corrected research targets

Source: Christian Noack, **Chinese-Remainder and Profinite Structure in the
Nyman–Beurling–Báez-Duarte Hilbert Space**, `sdf_modified.pdf`, dated July 21, 2026.
[Drive source](https://drive.google.com/file/d/1RWvDfQdERH8uDRS9PwGhK2eOKJxyfvO6/view).
The current browser selection identified this source. Baseline repository:
`420f72df97d2295badda3b623aa19eef4463dd56`.

This continuation addresses sections 14.9, 14.13, and 14.14 and the remaining
atom-reuse agenda. It does not prove RH or the uniform arithmetic bound.
The existing `ExactHeadGcdAtoms` and `ExactHeadAtomOptimizer` modules already
supply the upper-ideal atom/floor span identity and identify the actual
finite optimizer. They are reused, without adding a second optimizer model.

## Exact finite results

The main namespace is
`RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection`.

Write `F = {n : 1 <= n < P, x < gcd(n,P)}`. On `1,...,P-1`, use the actual
infinite progression weights, target `atom P 1 r - 1`, and steps
`Y_n(r) = 1[n <= r]`. The selected occurrence coefficients are actual
finite normal-equation solutions supplied by the existing existence theorem.
They are not numerical oracles.

| Declaration | Result |
|---|---|
| `atom_eq_sum_steps` | Exact expansion of a free gcd atom into its occurrence steps. |
| `lift_synthesis` | A shared atom coefficient is exactly the corresponding repeated occurrence coefficient. |
| `atomEnergy_eq_occurrence_add_reuse` | `atomEnergy = occurrenceEnergy + reuseEnergy`, including every nonnegative square. |
| `reuse_trial_identity` | Every trial atom vector has energy `reuseEnergy` plus the squared norm of its difference from the actual atom fit. |
| `fit_energy_eq_green` | Exact signed quadratic Green expansion, including both off-diagonal directions. |
| `reuse_green_identity` | Equation (127) with an explicit exact excess term for every candidate. |

These identities hold for arbitrary natural periods and cutoffs. The
quantitative bound below needs only `0 < P`; neither squarefreeness nor
independence is used.

## A certified coefficient bound and its limitations

`Analysis/DiscretePrefixHardy.lean` proves the finite forward Hardy inequality
with squared constant four by duality from the existing finite adjoint bound.

`RH/ExactHeadOccurrenceDispersion.lean` proves

\[
 A(P,x) \le 5\sum_{n\in F}|c_n^*-u_{\gcd(n,P)}|^2
\]

for every shared atom vector `u`. The first progression is controlled by
Hardy, and all later progressions are bounded using the existing exact
progression-tail enclosure. This is a checked rational constant; it does not
claim to sharpen the manuscript's smaller informal constant in (143).

The coefficient-loss minimizer is explicit: use the arithmetic mean of `c*`
on every complete atom fiber. `Analysis/FiniteAtomDispersion.lean` proves the
full completion

\[
 \sum_n|c_n-u_{d(n)}|^2
 = D + \sum_d N_d|\bar c_d-u_d|^2,
 \qquad
 D=\sum_d\frac{1}{2N_d}\sum_{n,m\in F_d}(c_n-c_m)^2.
\]

Only nonempty fibers appear. Hence `reuseEnergy_le_five_returnDispersion`
supplies `A <= 5 D`. These means minimize the coefficient loss, not the
Green energy. The distinction matters: the numerical experiment below finds
the coefficient bound very loose.

## Corrections to proposed proof steps

### Lemma 14.6: the aggregate concentration inference loses a scale factor

The first per-fiber Cauchy–Schwarz inequality is valid. However,
`V_d <= E^2 H` for each atom and `sum N_d <= C H` do not by themselves imply
`S <= O(sqrt(H) E)`.

`no_uniform_dyadic_inference` gives an unbounded dyadic counterfamily to this
inference. One atom with `H=2^j` unit errors has `N=H`, `V=H`, `E=1`, and
`S=H`. Thus `S^2/(H E^2)=H` is unbounded. This refutes the stated algebraic
inference; it does not assert a counterexample for the special unknown
occurrence-optimal sequence without supplying that specialization.

The corrected aggregate estimate is

\[
 S^2\le \#F\,\sum_n|c_n-u_{d(n)}|^2.
\]

Consequently a **total** squared error at most `E^2`, together with
`#F <= C H`, gives `S^2 <= C H E^2`. Both statements are proved in Lean.

### Hypothesis 14.9: unit returns retain an exact character bias

`NumberTheory/DivisorReturnCoordinates.lean` proves, for every `d>0`,

\[
 \gcd(n,dQ)=d\iff n=dm\text{ for some }m\text{ with }\gcd(m,Q)=1.
\]

No squarefreeness is required. For even `Q`, every such reduced coordinate
is odd. The nontrivial parity character `(-1)^m` therefore has average `-1`
on **every nonempty return sample**, including any nonempty shell. Its
Haar average over an even modulus is zero. `parity_return_bias` proves that
the normalized discrepancy has absolute value exactly one.

Thus Hypothesis 14.9, interpreted as comparison against uniform translates
on the whole residue group, cannot hold for all additive characters with
decaying error. The constant character must also be excluded in any such
formulation. A comparison against the unit measure, or against suitably
centered specific observables, is a different target and remains open.

## Stronger sufficient RH criteria

`RH/ExactHeadOccurrenceCriterion.lean` connects the exact decomposition to
the repository's established bounded exact-head closure theorem.

For the repository's `greenPeriod x = primorial (x+1)`, each of the following
is sufficient, for one real `B` and arbitrarily large **common** stages `x`:

1. `occurrenceEnergy + reuseEnergy <= B`.
2. `occurrenceEnergy + 5 * returnDispersion <= B`.
3. For explicit stage-dependent shared atom coefficients `u`,
   `occurrenceEnergy + GreenTrialEnergy(u) <= B`.

Declarations:

- `riemannHypothesis_of_cofinal_bounded_occurrence_reuse`
- `riemannHypothesis_of_cofinal_bounded_returnDispersion`
- `riemannHypothesis_of_cofinal_bounded_green_trial`

The third route preserves the signed cumulative error and can avoid the
severe loss in the unweighted coefficient bound. These are **conditional
research reductions**. They remove the need to prove vanishing at every
cutoff but do not supply the boundedness premises.

The exact terminal progression contribution is retained through
`MobiusHeadGreen.actual_energy_split`; it is bounded by total probability
one in the closure argument. No cofinality among all divisibility moduli is
assumed. No reverse implication from RH to this constrained primorial
exact-head family is claimed.

## Research experiment: signed versus unweighted dispersion

The retained reproduction source and JSON are in
`ResearchData/OccurrenceReuse20261116/`. They use float64, the digamma
progression weights, and direct summation within each free-to-free block.
Direct block sums avoid severe cancellation from subtracting two almost
equal cumulative masses late in a large period. These are diagnostics, not
interval certificates, Lean evaluations, or asymptotic evidence.

| x | P | occurrence energy | unweighted D | Green trial with ordinary fiber means |
|---:|---:|---:|---:|---:|
| 5 | 30 | 0.0342368 | 0.187414 | 0.00993376 |
| 7 | 210 | 0.0340320 | 0.741714 | 0.00173732 |
| 11 | 2310 | 0.0290720 | 52.6370 | 0.0143138 |
| 13 | 30030 | 0.0211878 | 971.428 | 0.0180824 |
| 17 | 510510 | 0.0144125 | 22265.1 | 0.0727672 |

The simple unweighted proxy grows sharply in this range, while its signed
Green energy stays much smaller. This does not prove divergence or
boundedness. It does show why an absolute-error proof can discard the
cancellation that the actual target needs.

We also tried weighted fiber means with weights `n^(-p)` for
`p = 0, 1/2, 1, 3/2, 2`, with and without a global zero-total-increment
constraint. The constrained `p=3/2` candidate has Green trial energy about
`0.0534874` at `x=17`, below the unweighted trial's `0.0727672`, but the
finite rows show no uniform cofinal estimate. No candidate is declared a
solution of the agenda.

The data directory's `reproduction.md` contains the complete executed Python
source. Save its code block as `occurrence_diagnostics.py` and run it there.
Runtime versions are recorded in the JSON. The charge constraint is enforced
in floating point; small nonzero residuals are reported, not hidden.

## Remaining obligations and next checks

| Obligation | Status and acceptance condition |
|---|---|
| Exact occurrence/atom split and Green trial accounting | Supplied by this continuation. |
| Corrected fiber concentration | Supplied as an exact finite identity and bound; decay remains open. |
| Haar-uniform return pseudorandomness | Invalid in the all-character form, by the parity obstruction. |
| Uniform signed Green trial bound | **Open.** Construct actual shared atom coefficients with the common cofinal bound in the new criterion. |
| Occurrence compression estimate | **Not formalized here.** The paper's squarefree smooth-gap adaptation and its analytic providers must still be supplied in Lean. |
| Signal-direction Ramanujan–Green estimate (81) | **Open**, independent of the atom-reuse route. |
| Walsh/subset-lattice decay | **Open.** Basis changes alone do not provide the required weighted estimate. |
| Markov-chain comparison | **Open after correction.** Respect unit support and retain the signed Green geometry. |

Heath-Brown's [2018 paper](https://arxiv.org/abs/1808.02947) proves smooth-number
gap moments. The squarefree restriction in Lemma 14.14 is an additional
adaptation in the supplied manuscript; the original reference alone is not
a Lean provider for it. The translated sieve claims also need correctly
normalized providers. In particular, the arbitrary-divisor version of
Proposition 14.7(i) cannot uniformly inherit full-primorial sifting density:
`Q=1` leaves every integer unsifted. This last observation is an informal
source audit, separate from the two Lean-checked counterarguments above.

The next useful numerical work is a rigorously enclosed signed Green trial,
followed by an analytic construction valid on unbounded common stages.
Testing increasingly large finite cutoffs does not close the cofinal gap.
