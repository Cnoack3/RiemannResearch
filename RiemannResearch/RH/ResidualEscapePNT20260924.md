# Residual tails and the full inverse source energy

24 September 2026. Research baseline: commit `874f5ee`.

## Status

This update does **not** prove unconditional RH. It proves seventeen additional
Lean theorems, including an explicit residual-tail lower bound, escape of the
raw Möbius residual norms, and escape of the full inverse source quadratic form
under positive limiting residual energy. It also closes a historical target
that was still labeled open.

The qualitative tail reduction was already present in
`ParetoSublinearResidualTail.lean`. The later checked PNT provider now
discharges its arithmetic premise. This is a formal integration of existing
results, with quantitative and raw-source consequences; no mathematical novelty
claim is made.

## Definitions and normalization

Let \(V_n=\operatorname{span}(g_2,\ldots,g_{n+1})\), let \(P_n\) denote its
orthogonal projection in the complete Pareto Hilbert space, and put
\[
r=1-P_{\overline{\bigcup_n V_n}}1,\qquad
E=\|r\|^2,\qquad e_n=\|1-P_n1\|^2.
\]
Thus Lean stage \(n\) corresponds to physical modulus cutoff \(n+1\).
Write
\[
A_n=1+\sum_{j=2}^{n+1}\mu(j)g_j,\quad
s_n=b_n+G_n\mu_n,\quad
\mathcal I_n=s_n^T G_n^{-1}s_n.
\]
The new definition `GramMobiusCorrection.inverseSourceEnergy` is exactly
\(\mathcal I_n\). All Gram entries and norms include the infinite physical tail.

For an independent physical cutoff \(N\), write
\[
T_N=\sum_{k>N}\frac{|r(k)|^2}{k(k+1)}
=\texttt{residualTailEnergy}(N).
\]
The established weighted-tail identity justifies this notation.

## 1. Exact inverse source energy and escape

Let \(Q_n\) be the orthogonal projection onto the first \(n\) coefficient
Riesz vectors. Their union is dense, as already proved in
`MobiusResidualEscape.lean`; this is density of the **dual** dictionary.
The raw residual annihilates every present dual. Its finite legal part is
orthogonal to \(r\), while \(\langle1,r\rangle=E\). Therefore
\[
\boxed{\langle A_n,r-Q_nr\rangle=E}.
\]
Since \(Q_nr\to r\), Cauchy–Schwarz gives
\[
\boxed{E^2\le\|A_n\|^2\,\|r-Q_nr\|^2}.
\]
Consequently,
\[
E>0\quad\Longrightarrow\quad\|A_n\|\longrightarrow+\infty.
\]

The finite normal equations identify \(P_nA_n\) with the synthesis of
\(G_n^{-1}s_n\), and the full projection error is still \(1-P_n1\). Hence
\[
\boxed{\|A_n\|^2=e_n+\mathcal I_n},
\qquad
\mathcal I_n=\|P_nA_n\|^2.
\]
The sequence \(e_n\) is bounded by \(e_0\). It follows that
\[
\boxed{E>0\quad\Longrightarrow\quad
s_n^TG_n^{-1}s_n\longrightarrow+\infty.}
\]
No PNT premise is needed for these identities or implications.

The project proves \(\neg\mathrm{RH}\Rightarrow E>0\). Thus a bounded cofinal
subsequence of \(\mathcal I_n\) would imply RH. This scalar criterion does not
require a bound for all entries or for the operator norm of \(G_n^{-1}\).
Its boundedness premise is **OPEN**. The same statement with \(\|A_n\|\) in
place of \(\mathcal I_n\) is also proved.

These are sufficient criteria, not claims that RH would force bounded raw
Möbius residual norms.

Main declarations in `NaturalMobiusResidualEscape.lean`:

- `naturalResidual_dual_error_pairing`
- `naturalResidual_dual_error_bound`
- `naturalResidual_norm_tendsto_atTop`
- `inverseSourceEnergy_eq_projection_norm_sq`
- `naturalResidual_norm_sq_eq_energy_add`
- `inverseSourceEnergy_tendsto_atTop`
- `riemannHypothesis_of_frequently_bounded_naturalResidual`
- `riemannHypothesis_of_frequently_bounded_inverseSourceEnergy`

## 2. Actual residual tails and the quantitative PNT ceiling

The existing canonical exact-head approximant \(F_N\) is legal and equals
one at physical coordinates \(1,\ldots,N\). Exact orthogonality gives
\[
E^2\le T_N\|1-F_N\|^2.
\]
The checked classical PNT provider proves \(\|F_N\|^2/N\to0\), and therefore
\(\|1-F_N\|^2/N\to0\). Applying the existing positive-product limit lemma yields
\[
\boxed{E>0\Longrightarrow N T_N\longrightarrow+\infty.}
\]
Moreover \(T_N>0\) at every cutoff when \(E>0\).

This gives the exact characterization
\[
\boxed{r=0\quad\Longleftrightarrow\quad
\exists C\in\mathbb R\;\exists^\infty N:\;NT_N\le C.}
\]
Here \(\exists^\infty\) means frequently at the natural-number atTop filter,
equivalently at arbitrarily large cutoffs. In particular, the displayed
boundedness premise implies RH. The premise is **OPEN**.

The already proved quantitative arithmetic ceiling supplies one \(C\ge0\).
For \(N\) sufficiently large, set
\[
x_N=\frac{1+\log(\log N+3)}{\log N},\quad a_C=2+4C,
\]
\[
B_C(N)=\frac3N+(4+2a_C^2)x_N+4a_C^2x_N^2,\qquad
q_C(N)=2B_C(N)+\frac3N.
\]
The provider proves \(q_C(N)\to0\), eventual positivity, and
\(\|1-F_N\|^2\le(N+1)q_C(N)\). The new theorem is
\[
\boxed{\exists C\ge0,\quad\text{eventually}\quad
0<q_C(N)\quad\text{and}\quad
(N+1)T_N\ge\frac{E^2}{q_C(N)}.}
\]
This has no unproved arithmetic premise.

Main declarations in `ResidualTailPNT.lean`:

- `residualTailEnergy_pos_of_limitEnergy_pos`
- `normalized_residual_tail_tendsto_atTop`
- `limitResidual_eq_zero_iff_frequently_bounded_normalized_tail`
- `riemannHypothesis_of_frequently_bounded_residual_tail`
- `residual_tail_eventual_explicit_lower`

The new `residualTailLinearFloor` in
`ResidualEnergyHistoricalTargets.lean` proves the historical
`ResidualTailLinearFloorTarget`. Its proposed linear upper witness is
unnecessary: the stronger divergence theorem supplies every fixed lower
threshold, including \(E^2/4\). The separate upper-witness target is unchanged.

## 3. What this does and does not say about inversion

The previous commit proves, for every fixed \(m\ge2\),
\[
[G_n^{-1}s_n]_m\longrightarrow-\langle r,u_m\rangle.
\]
The PNT argument recorded at commit `21e52c8` gives fixed source decay
before inversion. Its full summation-by-parts limit proof is a written
mathematical argument; this update does not relabel it as a Lean theorem.

The new escape theorem identifies a compatible obstruction: if \(E>0\),
the full inverse quadratic form diverges, although each fixed correction
has a finite limit. Neither coordinatewise source decay nor existing relative
quadratic inverse bounds prevent this behavior.

Tail decay \(T_N\to0\) is also compatible with \(NT_N\to\infty\).
For a rate illustration, physical sequences \(f(k)=k^\alpha\) with
\(0<\alpha<1/2\) belong to the Pareto Hilbert space and have
\(T_N\) of order \(N^{2\alpha-1}\). They are **not** being proposed as the
actual arithmetic residual; they demonstrate why these rate statements alone
are not contradictory. Divergent approximant energy can still be \(o(N)\).
Improving a PNT estimate by logarithmic or subpower factors alone does not
eliminate this possibility.

The remaining concrete tasks include proving one of the bounded cofinal
providers above, controlling the signed growing inverse source pairing, or
obtaining another arithmetic argument forcing \(r=0\). None is silently
assumed in these results.

## 4. Literature and computational audit

Primary references used to check the mathematical context:

- Michel Balazard, *An arithmetical function related to Báez-Duarte's criterion
  for the Riemann hypothesis* (2018),
  <https://arxiv.org/abs/1812.04309>.
  Its coefficient-limit framework and RH equivalence support treating
  coefficient identification as the substantive unresolved step.
- Luis Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable
  Reformulation of the Riemann Hypothesis* (2000),
  <https://arxiv.org/abs/math/0011254>.
  Its analysis of natural approximants supports keeping pointwise and
  full Hilbert-norm convergence distinct.

An exploratory Wolfram calculation checked an exact finite dual Gram/Schur
identity at physical cutoff four. It was not used to infer an infinite limit
or as a premise in any Lean theorem. Independent mathematical review also
examined shifted-density and stronger-PNT approaches; neither supplied the
missing boundedness provider.

## Verification

The coherent tail and raw-source proof batches passed Lean. The displayed
axiom checks for the main lower-bound, escape, historical-target and RH-reduction
theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
Their substantive hypotheses are stated above; an axiom report alone does not
discharge a local hypothesis.

The publication checkpoint performs the source audit and validates the changed
modules and local reverse dependencies before committing and pushing. No
admitted proof, new project axiom, unsafe declaration, or claim of unconditional
RH is included.
