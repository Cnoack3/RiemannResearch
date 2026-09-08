# Repair of the false normalized Bessel route

This note continues `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf` and
`ParetoNoiseSignalReport.md`. The verifier is operational. The mathematical
obstruction is the already proved negation of `RepairBesselBound` for the
actual least `3,5`-smooth scales. That refutation remains valid.

## Exact shared-scale cancellation

Write `U(p,E) = arithmeticRepair 2 p E` and use the complete Pareto inner
product. For positive p and q, pointwise at every integer coordinate,

    U(p,E) - (q/p) U(q,E) = U(p,q).

For p<q this preserves every coordinate below p and the defect -1 at p.
For p<q<2p, the compensating defect at q is exactly q/p. It has moved, not
vanished. With q=p+h and 0<h<=p, the already verified full variance estimate
applies to the difference, independently of E:

    Var[U(p,E) - (q/p)U(q,E)] <= 8(h/p^2)(1+log(p/h)).

For a finite cluster, the exact decomposition retains the collective term
`(sum_p a_p q/p) U(q,E)`. Removing it requires the explicit balance condition
`sum_p a_p/p=0`. This is different from `sum_p a_p=0`.

An ordered-chain version writes the original combination as adjacent repairs
with cumulative reciprocal coefficients, plus the final anchor. Thus shorter
gaps can improve individual costs, but the cumulative coefficients and final
anchor are still present in the exact formula.

## Reverse orthogonalization

For bounded sequences define

    V = f - (<f,g>/<g,g>) g.

When g has positive squared norm, the complete infinite sums satisfy

    <V,g> = 0,
    ||f||^2 = ||V||^2 + <f,g>^2/||g||^2.

If g vanishes through coordinate p, V agrees with f through p and preserves
the Möbius defect at p. For an actual repair with anchor value -1, every such
elimination leaves squared norm at least `1/(p(p+1))`, certifying a positive
pivot. Mean zero and previously established orthogonality are preserved.

The exact coefficient transformation is

    a f + b g = a V + (b + a<f,g>/<g,g>) g.

Consequently this is a change of generators, not permission to keep the old
coefficients after altering the directions. Descending through a finite
ordered repair family supplies the reverse Gram--Schmidt construction. The
formal modules provide the elimination operations, simultaneous finite tail
projection, and exact finite Gram / orthogonal-energy identities. The finite
projection theorem assumes an already orthogonal tail family and supplies the
next constructive step. A packaged recursive existence theorem for every
family is not claimed here. Any orthogonal family satisfies Parseval with
its own coefficients and squared norms. Projection preserves packet legality
when the input vectors are finite combinations of the allowed packets.

## A valid general coefficient bound

For every finite bounded family, all signed cross terms first appear in the
exact Gram identity. Cauchy--Schwarz then gives the separate valid bound

    ||sum_i a_i f_i||^2 <= (sum_i a_i^2)(sum_i ||f_i||^2).

If the diagonal energies are summable, their full sum gives a single constant
for the unweighted coefficient-square sum. This does not prove the refuted
estimate with `sum_i a_i^2 ||f_i||^2` on its right side. In particular, it
does not justify the infinite coefficient choice `a_i=1`.

## What remains open

The quantitative `3,5`-smooth gap input is still an explicit unformalized
hypothesis of the earlier summability theorem. These covariance repairs do
not supply that theorem.

Orthogonalization within the existing repair span preserves its binary
composite invariant. That span still cannot approximate the constant target.
A successful enlargement must address composite defects as well as primes.
For an infinite construction, the transformed coefficients, final anchor,
and convergence must be controlled. No RH conclusion is asserted.

The original Bessel refutation is retained as a theorem. Its false statement
is not replaced with an axiom, and the remaining arithmetic hypotheses are
not presented as proved.

## Formal declarations

| Module | Principal declarations |
|---|---|
| `ParetoRepairAnchorCancellation` | `arithmeticRepair_common_anchor_cancel`, `arithmeticRepair_adjacent_chain`, `arithmeticRepair_common_anchor_variance_bound` |
| `ParetoTailOrthogonalization` | `tailOrthogonalize_energy_split`, `tailOrthogonalize_preserves_defect`, `arithmeticRepair_tail_elimination` |
| `ParetoFiniteGram` | `paretoInner_finsetCombination`, `paretoInner_finsetCombination_of_orthogonal`, `paretoInner_finsetCombination_le_tsum_energy` |
| `ParetoFiniteTailProjection` | `finiteTailProjection_orthogonal`, `finiteTailProjection_energy_split`, `finiteTailProjection_preserves_head`, `finiteTailProjection_pos_of_anchor` |

All declarations are in `RiemannResearch.RH.Pareto`. General results expose
their boundedness, orthogonality, and nonzero-pivot hypotheses. The actual
repair application supplies boundedness and the anchored positive pivot.
