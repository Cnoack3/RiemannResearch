# Infinite squarefree CRT continuation: Q limits and the subpolynomial consumer

Source: Christian Noack's supplied
`Squarefree_Infinite_CRT_Continuation_2026-10-16 (1).md`, especially Sections
4--8 and research priorities 1, 3, and 5. The attachment supports the statements
and proof strategies. The analytic zero witness is the repository's existing
localized Mellin theorem. No mathematical novelty claim is made.

## Complete-energy consumer

`QExactHeadSubpolynomial.lean` treats finite squarefree legal trials in the
actual inverse-square Q Hilbert space. For an exact head `1 ≤ k < n` and a
hypothetical zero `s` with `1/2 < Re(s)` and `s ≠ 1`, it proves

\[
\frac{2\operatorname{Re}s-1}{\zeta(2)|s|^2}
n^{2\operatorname{Re}s-1}\leq\|1-F\|_Q^2.
\]

The proof transfers the same full physical residual to the Pareto space and
uses its established Mellin lower bound. The complete weighted-series identity
is retained separately as `residual_energy_exact`; no signed cross term or
infinite physical tail is omitted. In the attachment's notation, one may set
`n = H + 1`.

`riemannHypothesis_of_cofinal_exact_head_subpolynomial` concludes Mathlib's
actual `RiemannHypothesis` from the following explicit hypotheses:

- Each `F i` is a finite squarefree legal trial.
- The physical cutoff `n i` tends to infinity.
- `F i` equals one at every positive integer below `n i`.
- `E i ≥ 0` and the complete squared error is at most `E i + 1`.
- `log(1 + E i) / log(n i)` tends to zero.

`riemannHypothesis_of_subpolynomial_affine_minima` specializes this consumer
to the existing exhaustive affine optimizer with exact head through `N + 1`,
allowing independent squarefree periods `L N` and normalization anchors `r N`.
Its only asymptotic energy premise concerns the actual complete optimized
errors. The period-coverage and anchor-feasibility conditions are explicit.

Status: **conditional research reductions**. The subpolynomial energy
provider is **Open**. This is weaker than a uniform error bound, but its
existence is not proved. The external RH-to-squarefree-density implication
from Bagchi is not newly formalized, so these declarations are not reported
as a Lean-verified RH equivalence.

## Infinite-conductor limits

`QConductorLimits.lean` proves dominated convergence in the full Q norm for
uniformly bounded physical sequences. It applies this to prove

\[
g_{d_j}\longrightarrow0,\qquad I_{d_j}\longrightarrow0,\qquad
R_{d_j}=1-g_{d_j}-I_{d_j}\longrightarrow1
\]

whenever `d_j → ∞`. Squarefreeness is unnecessary. These are limits under the
atomic Q law; no Haar-norm inference or legality assumption is introduced.
The explicit `O(1/d)` atom norm bound in the attachment is not newly proved.

`QConductorEscape.lean` proves that a bounded family of finite combinations
with every conductor above a cofinal cutoff converges weakly to zero against
every Q Hilbert test vector. There is no bound on the number, sizes, or signs
of its coefficients. The cutoff is assumed positive at each stage; this is
automatic after discarding a finite prefix of any cutoff tending to infinity.

The proof first retains the exact physical head energy

\[
\sum_{k=1}^{H}Q(k)|F(k)|^2
=\frac{H}{\zeta(2)}|F(1)|^2
\]

when `F(k)=kF(1)` on that head. Comparison with the complete norm forces the
slope to zero; dense single-site tests then give full weak convergence.

## Exact legality obstructions and the reflected-distance criterion

`QSquarefreeJumpApplications.lean` applies the existing four-site Riesz
witness. It retains complete norm-square remainders and proves, for every
legal-closure vector `F`,

\[
\|e_1-F\|_Q^2\geq\frac1{30\zeta(2)},\qquad
\|g_3^2-F\|_Q^2\geq\frac2{1215\zeta(2)}.
\]

Thus the singleton cannot be approximated by the original squarefree legal
atoms, and their closed span is not closed under pointwise multiplication.
This does not concern the distinct derivative closure.

For squarefree `d ≥ 3`, the reflected vector has jump defect exactly one at
`a = d - 1`; it is individually outside the closed legal span, with the
attachment's explicit positive squared-error lower bound.

Finally continuity of distance proves, for every `d_j → ∞`,

\[
1\in\overline{\mathcal V}_{Q}
\quad\Longleftrightarrow\quad
\operatorname{dist}(R_{d_j},\mathcal V)\longrightarrow0.
\]

The infimum distance over the algebraic legal span equals the distance to
its closure. This is a geometric equivalence. Neither distance decay nor
constant closure membership is supplied unconditionally.

## Next research obligations

1. **Open:** bound the actual exhaustive affine minimum subpolynomially in
   the exact-head length. Retain its full signed Gram objective and allow
   the squarefree period to grow independently of the head.
2. **Open:** construct quantitative legal approximations to the reflected
   atoms; their ambient strong limit alone does not discharge legality.
3. **Not newly formalized:** the explicit complete-energy `O(H)` benchmark,
   the bounded fixed-Mobius-coordinate converse, and the external
   RH-to-squarefree-density implication. Existing finite exact-head baseline
   results are reused rather than duplicated.

## Verification workflow

Development uses serialized server snippets, followed by one final
`agent_workspace_checkpoint` with push enabled. The checkpoint's terminal
result is the evidence for project integration and publication. A snippet
check alone does not certify the final exported modules. The final chat
report records the checkpoint job, validation scope, and published commit.
