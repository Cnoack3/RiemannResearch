# Green–Pareto–Schur: four stronger conditional reductions

6 October 2026. Source: the supplied continuation, especially Sections 17–28.
These results weaken particular provider requirements. They do not prove an
arithmetic cancellation or growth provider, and do not prove RH.

## Moving signed absorption gap

Keep the actual identity `D_N = H_N + L_N`, where `L_N` is the complete signed
trial/optimizer tail pairing and `|H_N| <= sqrt(134) E_N`. For a selected
cofinal sequence, allow a positive stage-dependent gap `a_k`:

\[
L_{N_k}\le(1-a_k)D_{N_k}+Z_k,
\qquad E_{N_k}/a_k\to0,\quad Z_k/a_k\to0.
\]

Then RH follows. The exact signed inequality is
\[
D_{N_k}\le\frac{H_{N_k}+Z_k}{a_k},
\]
and the usable upper bound is
\[
D_{N_k}\le\sqrt{134}\,E_{N_k}/a_k+Z_k/a_k\to0.
\]
No fixed positive lower bound on `a_k` is needed. For example, a gap of order
`1/log N_k` permits errors that are `o(1/log N_k)`. The head term and the
entire signed tail are retained before estimation. No optimizer-tail norm
estimate is a premise.

Declarations:

- `Analysis/MovingSignedGap.lean`: `signed_moving_gap_bound`,
  `limit_eq_zero_of_signed_moving_gap`, `limit_eq_zero_of_head_error_moving_gap`.
- `RH/ParetoMovingSignedGap.lean`:
  `riemannHypothesis_of_cofinal_signed_trial_moving_gap`.

Open: construct the legal trials and prove the eventual signed budget and
relative-error limits. Fixed-gap results are recovered by a constant `a_k`.

## Double-logarithmic source growth

For the finite nonnegative spectral data already used in the continuation,
put
\[
\Phi_2(\lambda)=\log(1+\log(1+\lambda)),\qquad
M_{2,N}=\sum_i w_{N,i}\Phi_2(\lambda_{N,i}).
\]
Let `T_N` be the correction and `S_N` the optimizer-tail energy. If
`0 < sigma < 1` and `S_N <= sigma`, the proved finite bound is
\[
T_N\le\sigma+\sqrt\sigma+
\frac{2M_{2,N}}{\log(1+\log(1/\sigma))}.
\]
It follows that cofinally
\[
\sigma_k\to0,\quad S_{N_k}\le\sigma_k,\qquad
M_{2,N_k}=o\!\left(\log(1+\log(1/\sigma_k))\right)
\]
forces the limiting correction to be zero. The proof uses the same
`1/sqrt sigma` threshold, with local monotonicity only at nonnegative
spectral points. It retains every finite source weight.

This condition allows finite source families whose old logarithmic quotient
diverges. For example, take eigenvalues `exp(-k), exp(k^3)`, weights `1,1/k`,
and envelope `exp(-k)+exp(-k^3)/k`. The optimizer-tail sum is bounded by the
envelope, the correction tends to zero, the old logarithmic quotient is
asymptotic to `k`, and the new quotient is asymptotic to `3/k`. This is an
abstract separation example, not the actual arithmetic spectrum.

The old condition implies the new one: write `z=log(1+lambda)` and
`L=log(1/sigma)`. For `L >= e-1`,
\[
\frac{\log(1+z)}{\log(1+L)}
\le 2\frac{\lambda}{1+\lambda}+\frac zL.
\]
For `z<=L`, split `lambda<=1` and `lambda>=1`; for `z>L`, use that
`log(1+z)/z` decreases. Summing gives the new normalized moment at most
`2 T + M_1/L`, which tends to zero under the old verified criterion.
This ordering and the asymptotic example are paper arguments; the new
finite bound and limiting consumer are Lean-verified.

Declarations in `Analysis/FiniteSpectralDoubleLog.lean`:
`correction_le_relative_doubleLog_envelope` and
`limit_eq_zero_of_cofinal_relative_doubleLog_envelope`.

Open: realize the finite source as the actual full-conductor whitened Pareto
matrix data in Lean, and prove its arithmetic double-logarithmic estimate.
The finite-source theorem concludes defect zero; it is not an assembled
actual RH theorem without that realization.

## Mixed affine Möbius trials

Take finitely many legal trials `u_i` sharing an exact head through sites
`j<h`, and real weights with `sum a_i=1`. Negative weights are permitted.
For `F=sum a_i u_i`, the checked complete identities are
\[
1-F=\sum_i a_i(1-u_i),\qquad
\|1-F\|^2=\sum_{i,j}a_i a_j\langle1-u_i,1-u_j\rangle.
\]
The combined trial is legal and has the same exact head. Thus subpolynomial
growth of this complete mixed Gram form relative to a cofinal common head
`h_k` implies RH. No bound on each constituent's energy is required.

The actual canonical Möbius specialization proves legality and head matching
from the existing arithmetic construction. Its only cutoff requirement is
`h_k <= Y_{k,i}+1` for every constituent. Crossings are unnecessary for this
consumer. Without crossings, the squarefree-support and boundary-coefficient
caps of the crossing family must not be inferred.

Declarations in `RH/ParetoAffineHeadTrials.lean`:
`affine_residual_norm_sq_eq_gram`,
`riemannHypothesis_of_cofinal_affine_exact_head_gram_subpolynomial`, and
`riemannHypothesis_of_cofinal_canonicalMobius_affine_gram_subpolynomial`.

Open: find normalized weights giving the required upper growth of the complete
mixed form. All same-stage and cross-stage signed interactions remain.

For convex mixtures of crossing trials only, an elementary paper version
keeps the finite certificate. Let `h` be a common head cutoff and `M` the
largest conductor. The mixed residual window is `h <= j < M^2`; the entire
farther-tail energy is at most one, because each combined atom coefficient
has magnitude at most one and `|1-F(j)| <= M`. Therefore its subpolynomial
growth relative to `h` suffices. Use the common head, not the largest
conductor, in the denominator. This finite-window assembly is not among the
new Lean declarations.

## Approximate heads with subpolynomial complete energy

Exact interpolation can be dropped altogether. Let `f_k` belong to the legal
closed space, let `n_k` tend to infinity, and put `e_k=1-f_k`. The checked
actual RH theorem assumes only
\[
\|Q_{n_k-1}e_k\|\to0,\quad
\|e_k\|^2\le C_k+1,\quad C_k\ge0,\qquad
\frac{\log(1+C_k)}{\log n_k}\to0.
\]
These imply RH. The cutoff may be chosen independently of conductor support.

At a hypothetical zero `s=beta+i gamma` with `beta>1/2`, the legal residual
has actual Mellin value `1/s`. Splitting into its physical head and tail is
an exact linear identity; the tail has zero head through `n_k-1` and
\[
\|e_k\|^2=\|Q_{n_k-1}e_k\|^2+
\|(I-Q_{n_k-1})e_k\|^2.
\]
If
\[
\|Q_{n-1}(1-f)\|/\sqrt{2\beta-1}\le1/(2|s|),
\]
the proved finite detector is
\[
\boxed{\frac{2\beta-1}{4|s|^2}n^{2\beta-1}
\le\|1-f\|^2.}
\]
Every fixed off-line zero eventually meets the small-head condition. The
positive power floor contradicts the subpolynomial complete-energy bound.

Declarations in `RH/LegalApproximateHeadSubpolynomial.lean`:
`legal_approximate_head_residual_power_lower` and
`riemannHypothesis_of_cofinal_legal_approximate_head_subpolynomial`.

Open: prove the head approximation and complete-energy growth estimates for
a concrete arithmetic family. The full infinite norm, including its entire
farther tail, is the budget premise.

## Literature and exact diagnostics

Primary sources checked:

- Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable Reformulation
  of the Riemann Hypothesis*, [math/0011254](https://arxiv.org/abs/math/0011254):
  explains why natural pointwise and L1 approximants can fail in L2.
- Báez-Duarte, *A strengthening of the Nyman–Beurling criterion …, 2*,
  [math/0205003](https://arxiv.org/abs/math/0205003): its quantitative damped
  Möbius convergence result assumes RH. It supplies no unconditional provider
  for the new criteria.
- Burnol, *A lower bound in an approximation problem involving the zeros of
  the Riemann zeta function*, [math/0103058](https://arxiv.org/abs/math/0103058):
  context for zero-induced approximation lower bounds. Its theorem is not
  being asserted to be the new localized approximate-head theorem.

Wolfram checked the square-root/head coefficient algebra and the two-point
spectral separation numerically. At `k=10,30,100`, the old normalized moments
were approximately `10,30,100`, while the new ones were
`0.288136,0.0990455,0.0299353`.

It also evaluated the complete mixed finite residual window for the crossing
trials `U_6,U_7`, using the common window `6<=j<49`. The two diagonal energies
were `0.037396949648` and `0.030567943989`. The optimal convex coefficient of
`U_6` was exactly
\[
a=\frac{3475845019570215}{9133303148931104},
\]
and the combined window energy was `0.026427254414`. This retains the
cross term and shows a finite improvement. It does not establish a cofinal
growth estimate or control a growing sequence of such optimizations.

No mathematical-priority claim is made. All new actual RH implications remain
conditional research reductions, and every arithmetic provider remains Open.
