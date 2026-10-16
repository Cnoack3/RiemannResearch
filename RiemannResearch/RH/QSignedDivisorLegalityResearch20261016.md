# Finite Signed Divisor Combinations: Exact Squarefree Legality

**Date:** 16 October 2026
**Handoff:** QDivisorLegality_Research_2026-10-16, research agenda item 3
**Development base:** 03de4d50b46a5907aa9aecfd28ccef2e19325e34

## Result

Let \(Q(n)=1/(\zeta(2)n^2)\) for positive integers, let
\(g_d(n)=(n\bmod d)/d\), and let \(I_m(n)=\mathbf1_{\{m\mid n\}}\).
Write
\[
A_{\rm sf}=\operatorname{span}_{\mathbb R}\{g_d:d\ge2,\ d\text{ squarefree}\},
\qquad H_{\rm sf}=\overline{A_{\rm sf}}^{\,L^2(Q)}.
\]
For any finite set \(s\) of positive integers and arbitrary real coefficients,
put \(F=\sum_{m\in s}b_m I_m\). All coefficient signs are allowed.

The new checked classification is
\[
\boxed{
F\in H_{\rm sf}
\iff
\left[\forall n\ge1,\ F(n+2)=F(n)\right]
\ \land\
\left[F(2)=0\ \lor\ 1\in H_{\rm sf}\right].
}
\]
Whenever the periodicity condition holds, the complete identity is
\[
\boxed{F=F(2)\,1+2\bigl(F(1)-F(2)\bigr)g_2.}
\]
No norm-square remainder, signed coefficient, or exceptional positive
coordinate is dropped in this identity.

The finite algebraic span has the sharper unconditional classification
\[
\boxed{
F\in A_{\rm sf}
\iff
\left[\forall n\ge1,\ F(n+2)=F(n)\right]\land[F(2)=0].
}
\]
Thus among finite signed divisor sums, the finite squarefree legal vectors
are precisely the scalar multiples of \(g_2\).

These results do not prove \(1\in H_{\rm sf}\) or RH.

## Why arbitrary signed cancellation still forces parity

The integer extension
\[
f(z)=\sum_{m\in s}b_m\,\mathbf1_{\{m\mid z\}},
\qquad z\in\mathbb Z,
\]
is even and invariant modulo \(L=\prod_{m\in s}m>0\).
Its zero value is used only in the integer argument. At positive integers,
it agrees exactly with the physical Q-Hilbert sequence.

Suppose all square-jump tests vanish:
\[
f(n^2)-f(n^2-1)=f(n)-f(n-1)\qquad(n\ge2).
\]
Fix \(n\ge2\), set \(t=2(n+1)\), and set \(a=Lt-n\).
Then \(a\ge2\), \(a\equiv-n\pmod L\), and \(a^2\equiv n^2\pmod L\).
Evenness and modular invariance give
\[
f(a)=f(n),\quad f(a-1)=f(n+1),\quad
f(a^2)=f(n^2),\quad f(a^2-1)=f(n^2-1).
\]
The square-jump identity at \(a\) therefore reads
\[
f(n^2)-f(n^2-1)=f(n)-f(n+1).
\]
Subtracting the complete identity at \(n\) gives
\(f(n+1)=f(n-1)\). Hence \(F(n+2)=F(n)\) for all \(n\ge1\).

Conversely, the parity decomposition above shows that every such
two-periodic \(F\) passes all square-jump tests. The constant passes
because its jumps are zero at positive sites at least two, and \(g_2\)
passes because it is itself a squarefree legal atom.

Consequently, within the finite signed divisor dictionary, the entire
family of square-jump tests is equivalent to parity dependence. This
is a sufficiency theorem for passing those tests in this restricted
dictionary, not a sufficiency theorem for membership in \(H_{\rm sf}\).

## Exact closure and finite-span membership

Since \(g_2\in A_{\rm sf}\), the parity identity implies
\[
F\in H_{\rm sf}\iff F(2)\,1\in H_{\rm sf}.
\]
For a real scalar \(\alpha\), the subspace property gives
\[
\alpha\,1\in H_{\rm sf}\iff
\alpha=0\ \lor\ 1\in H_{\rm sf}.
\]
This proves the closure classification.

If in addition \(F\in A_{\rm sf}\), the existing common-multiple theorem
supplies \(J>0\) with \(F(kJ)=0\) at every positive multiple.
At the even multiple \(2J\), two-periodicity gives
\(F(2)=F(2J)=0\). Conversely, any two-periodic \(F\) with \(F(2)=0\)
is exactly \(2F(1)g_2\), a finite legal vector.

There are two explicit conditional specializations:

* If \(1\in H_{\rm sf}\), a finite signed divisor sum belongs to the
  closure exactly when it depends only on parity.
* If \(1\notin H_{\rm sf}\), closure membership and finite-span
  membership coincide on all finite signed divisor sums.

Neither hypothesis is asserted. Both specializations are checked as
implications with that hypothesis visible in their types.

## Lean modules and declaration map

There are sixteen new public theorem declarations.

### Analysis/EvenPeriodicSquareJump.lean

Namespace: RiemannResearch.Analysis.EvenPeriodicSquareJump.

* even_periodic_square_jump_two_periodic:
  the integer evenness/modular-invariance rigidity theorem.
* values_of_two_periodic:
  recovery of a positive sequence from its values at one and two.

### RH/QParityGeometry.lean

Namespace: RiemannResearch.RH.ZetaTwoHilbert.

* qHilbert_eq_parity_of_two_periodic:
  exact Q-Hilbert-vector reconstruction from the physical parity values,
  including the auxiliary zero coordinate.

### RH/QSignedDivisorLegality.lean

Namespace: RiemannResearch.RH.QSignedDivisorLegality.

The definition integerDivisorSum is the integer extension of a finite
signed sum. Its value at the auxiliary zero is not used as a physical
Hilbert coordinate.

* integerDivisorSum_even.
* integerDivisorSum_modular.
* qSequence_sum_divisors_integer.
* square_jump_integer_of_identities.
* signed_divisor_two_periodic_of_square_jumps.
* signed_divisor_closure_two_periodic.
* signed_divisor_square_jumps_iff_two_periodic.
* signed_divisor_closure_eq_parity.
* scalar_qOne_mem_squarefreeClosure_iff.
* signed_divisor_mem_squarefreeClosure_iff.
* signed_divisor_mem_squarefreeSpan_iff.
* signed_divisor_mem_squarefreeClosure_iff_of_qOne_mem.
* signed_divisor_mem_closure_iff_mem_span_of_qOne_not_mem.

All three modules are exported by RiemannResearch.lean.

## Verification

The targeted server job job_X5Uctd1ftojmh6BIsDvln3dQGj9m4S5B succeeded:
all three modules built and the representative axiom checks for the
closure criterion, finite-span criterion, and integer rigidity theorem
returned only propext, Classical.choice, and Quot.sound.

The source contains no sorry, admit, project-local axiom, or unsafe
declaration. Publication uses the mandatory server checkpoint gate,
which audits the complete delta and validates the aggregate project
and changed child modules before pushing. The terminal checkpoint job
and published commit are reported in the task completion record.

## RH-facing interpretation and remaining work

The quantitative obstruction item in the original handoff was already
implemented in QSquarefreeJumpDistance.lean at the development base.
The present continuation addresses the signed-combination classification
item. Its nontrivial point is that cancellations cannot produce a
finite non-parity divisor sum passing every square-jump test.

A proposed coordinate truncation that is a finite signed divisor sum
must satisfy this classification to remain squarefree legal. Having
coordinates in the complete divisor dictionary alone does not supply
legal residue approximants.

The constant remains a parity function that passes all the jump tests.
Its closure membership is exactly the unresolved alternative retained
in the criterion, so this development supplies no new proof of RH.

Next research targets:

1. Prove a global norm, tail, inverse-capacity, or target-dual estimate
   for actual finite squarefree residue candidates approaching the
   constant. This is the central unresolved approximation step.
2. Formalize the external RH-to-squarefree-density bridge without an
   axiom, separately from the unconditional legality results.
3. Use complete multi-witness Gram matrices to quantify distance from
   the squarefree legal closure for non-parity signed combinations.
4. Transfer the classification through the actual complete Parseval
   isometry and characterize which concrete coordinate truncations
   preserve legality. No such new coordinate-map declaration is
   asserted here.

Provenance: the user-provided handoff supplies the square-jump
obstruction and the signed-combination question. The periodic-reflection
proof and the finite-span classification were developed in this
continuation. No claim of external mathematical novelty is made.
