# Noor regularity completed in the real Pareto model

Date: 2026-09-23.
Development base: ee21cb7330c328b9ce00478057ca2c0af423b636.

## Completed theorem

In namespace `RiemannResearch.RH.Pareto.CoefficientStabilization`:

```lean
theorem eq_zero_of_orthogonal_tailRegular
    (f : ThresholdHilbert)
    (hf : f ∈ closedSpaceᗮ)
    (hreg : TailRegular f) : f = 0
```

There is no shifted-density assumption. The proof uses the newly proved
`RiemannResearch.RH.Pareto.Noor.shiftedResidue_density`.

The project already proves that `TailRegular f` is equivalent to the
local-Dirichlet coefficient condition on `hardyCoordinates f`.
Thus this is the real coefficient/Pareto form of Noor's regularity theorem.
The new work does not construct the complex holomorphic Hardy space or an
integral definition of the local Dirichlet energy.

## Proof and normalization

Write `L_k(n) = k/n` when k divides n and zero otherwise, with zeroth
coefficient zero. Each L_k belongs to real square-summable coefficient space,
and for k>0 all these vectors have the same norm.

For k>0 define the finite sum

```math
S_{N,k}=\sum_{d\mid N!}\frac{\mu(d)}d L_{kd}.
```

The Möbius divisor identity gives the exact coefficient formula

```math
S_{N,k}(n)=
\begin{cases}
 k/n,&n>0,\ k\mid n,\ \gcd(n/k,N!)=1,\\
 0,&\text{otherwise}.
\end{cases}
```

For each fixed n this eventually equals the kth coordinate vector.
The squared error is bounded by the summable sequence L_k(n)^2.
Dominated convergence proves norm convergence to that coordinate vector.
Consequently the L_k are total among vectors with zeroth coefficient zero.

For `k=i+2`, the checked actual-coordinate identity is

```math
k (I-S)\,\mathrm{hardyCoordinates}(\mathrm{residueAtom}(i))
 =-\log(k)e_0+L_1-L_k.
```

The L_k converge weakly to zero: their norms are bounded and their support
escapes each fixed initial segment. If w is orthogonal to all shifted
residue vectors, division by log(k) first forces w(0)=0. Weak convergence
then forces its pairing with L_1, and hence every L_k, to vanish.
The finite-sieve totality proves w=0. Therefore the shifted span is dense.

Finally the adjoint relation between forward and backward coefficient
differences proves that a regular vector in the original orthogonal
complement is zero. No inverse of I-S is applied to a norm limit.

The density proof uses neither PNT nor RH, and no infinite Möbius series
is exchanged with a norm limit.

## Files and resulting interfaces

- `Analysis/NoorLogarithmDensity.lean`: square-summable logarithmic vectors,
  the finite divisor identity, exact eventual coefficients, norm convergence,
  and totality.
- `RH/NoorShiftedResidueDensity.lean`: exact residue-coordinate
  normalization, weak convergence, and shifted density.
- `RH/ParetoTailAverageCriterion.lean`: completed regularity theorem
  and its updated residual criteria.

The public root imports both new modules. The obsolete proposition
`ShiftedResidueDensity` has been removed; the proved density theorem is
used directly. The following declarations no longer require hdense:

```lean
limitResidual_zero_iff_tailRegular :
  limitResidual = 0 ↔ TailRegular limitResidual

riemannHypothesis_of_tailRegular
  (hreg : TailRegular limitResidual) : RiemannHypothesis
```

The explicit infinite tail-average summability equivalence is updated too.
The theorem does not supply `TailRegular limitResidual`.
That assertion remains an open sufficient condition for RH.

## Verification

The combined source, all downstream criterion declarations, and axiom
queries passed in job `job_s8FdOojIupE4N46HELk2JB9xfmB2OoWB`:
verified=true, exit code 0, elapsed 7.218 seconds.
The sole diagnostic was an unused simp argument, removed before publication.

Axiom queries for `sieveVector_tendsto`, `shiftedResidue_density`,
`eq_zero_of_orthogonal_tailRegular`, and
`riemannHypothesis_of_tailRegular` returned only
`propext`, `Classical.choice`, and `Quot.sound`.
No sorry, custom axiom, or unsafe declaration is used.
Final integration is validated by the project's change-aware checkpoint.

## Source

S. Waleed Noor, *A Hardy space analysis of the Báez-Duarte criterion for
the RH*, Advances in Mathematics 350 (2019), 242–255.
Theorems 9 and 12, with the local-Dirichlet coefficient characterization
in Theorem 2:
https://arxiv.org/html/1809.09577v4.

The source supplies the shifted-density and regularity statements, the
logarithmic generators, and the adjoint proof strategy.
The Lean density proof above uses the finite factorial-divisor sieve.
