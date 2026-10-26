# Raw positive variation: exact comparison, an equivalent criterion, and the remaining arithmetic bound

26 October 2026. Continuation of `RawSourceBoundsResearch20261026.md`.

**Status.** This development does not prove RH or the requested uniform bound
for the actual squarefree corrections. It proves a sharp unconditional
comparison, an exact characterization of zero squarefree residual, and
conditional RH implications. The missing estimate is stated below without
being promoted to a theorem. No claim of mathematical novelty is made.

## Definitions and retained exact identities

For positive integers let
\[
Q(n)=\frac1{\zeta(2)n^2},\qquad
a(n)=\frac{n}{(8+\log n)^2},\qquad a(0)=0.
\]
The repository's masked squarefree stages are \(V_N\), with Q-orthogonal
projections \(P_N\). Set
\[
r_N=1-P_N1,\quad e_N=\|r_N\|_Q^2\le1,\quad
s_N=Br_N,\quad Bf(n)=f(n)/(n+1),\quad b_N=P_Ns_N.
\]
Let \(r=1-P_V1\) and \(b=P_VBr\). The existing repository proves
\(r_N\to r\), \(b_N\to b\) in Q and \(r=0\Longrightarrow\mathrm{RH}\).
We do not assume or newly establish the reverse implication RH implies
squarefree target membership.

For the physical tail \(T_t\), define
\[
M_N(t)=\sum_{n\le t}Q(n)b_N(n)(s_N(n)-b_N(n)),\qquad
\Phi_N^\pm(H)=\sum_{t<H}\Delta a(t)\max(\pm M_N(t),0),
\]
\[
X_H(f)=\sum_{t<H}\Delta a(t)\|T_tf\|_Q^2,
\qquad E(H,f)=\sum_{n\le H}a(n)Q(n)f(n)^2.
\]
These are raw-source moments. No assertion here is silently substituted for
the CRT-conditioned source moments.

The earlier full identities remain primary:
\[
M_N(t)=\|T_tb_N\|^2-\langle T_tb_N,T_ts_N\rangle,
\qquad X_H(f)=E(H,f)+a(H)\|T_Hf\|^2,
\]
\[
X_H(b_N)=2(\Phi_N^+(H)-\Phi_N^-(H))+X_H(s_N)-X_H(b_N-s_N).
\]
In particular, the endpoint tail, negative variation, and nonnegative square
remainder have not been discarded from the formal identities.

## 1. Sharp unconditional comparison

For arbitrary Q vectors \(b,u\) with \(\langle b,u-b\rangle=0\), every
nonnegative integer profile exponent \(k\), and every finite head \(H\),
\[
\boxed{(\Phi^+(H)-X_H(b))^2\le X_H(b)X_H(u).}
\]
No weighted summability is needed for this finite statement. Here the profile
for general \(k\) is the repository's \(n/(k+6+\log n)^k\).

The proof first establishes the entire family of quadratic inequalities
\[
2c(\Phi^+(H)-X_H(b))\le c^2X_H(b)+X_H(u)\quad(c\in\mathbb R),
\]
then minimizes in \(c\), treating \(X_H(b)=0\) separately. Termwise, this
comes from the exact tail-moment identity and the nonnegative norm square
\(\|cT_tb+T_tu\|^2\); when the positive part vanishes, the same bound follows
from \(\|T_tb\|^2\le\|T_tu\|^2\). This avoids an assumed weighted
orthogonality.

The raw source budget specializes the comparison to
\[
\boxed{(\Phi_N^+(H)-X_H(b_N))^2
\le\frac{e_N}{256}X_H(b_N).}
\]
Equivalently,
\[
|\Phi_N^+(H)-X_H(b_N)|\le\frac{\sqrt{e_NX_H(b_N)}}{16}.
\]
Thus the positive variation is quantitatively the same obstruction as the
weighted correction energy. It cannot be made small through cancellation
while that energy grows without bound. In particular, along any sequence
with \(X_H(b_N)\to\infty\), the displayed estimate gives
\(\Phi_N^+(H)/X_H(b_N)\to1\). This last limit is a paper corollary of the
checked inequality, not a separately named Lean declaration in this change.

Formal declarations in `RH/QHeadTailLayerEnergy.lean`:

- `positiveCrossVariation_sub_layer_quadratic`
- `positiveCrossVariation_sub_layer_sq_le`
- `positiveCrossVariation_le_layer_add_source`
- `weightedEnergy_summable_iff_frequently_positiveCrossVariation_bounded`
- `uniform_cappedTailEnergy_iff_positiveCrossVariation`
- `cappedTailEnergy_le_profile_norm_sq`

The fourth theorem says that, for a source of finite weighted energy,
the correction has finite weighted energy iff its positive variation is
bounded along arbitrarily large heads. The fifth gives a uniform-family
version when source layer energies have a common bound.

## 2. Exact characterization using fixed heads

The actual residual satisfies
\[
\boxed{r=0\iff
\exists C\in\mathbb R\ \forall H\in\mathbb N\
\forall N_0\in\mathbb N\ \exists N\ge N_0:
\Phi_N^+(H)\le C.}
\]
The same finite constant works for every head, but the late stages may depend
on the head. There is no simultaneous all-stage estimate in this premise.

For necessity, \(r=0\) gives \(b_N\to0\) and \(r_N\to0\). For each fixed
\(H\),
\[
0\le\Phi_N^+(H)\le\tfrac32a(H)\|b_N\|^2+e_N/512\longrightarrow0.
\]
Thus \(C=1\) works. For sufficiency, pass the cofinal bound to each fixed
head of the limiting correction using finite-coordinate continuity. This
gives \(E(H,b)\le2C+1/256\) for every \(H\), hence finite complete weighted
energy. The existing squarefree logarithmic-tail dichotomy forces \(r=0\).

Formal declarations in `RH/QSquarefreeRawMomentCriterion.lean`:

- `raw_positive_variation_fixed_head_tendsto_zero`
- `residual_zero_iff_fixed_head_frequently_positive_variation_bounded`

This is an equivalence with zero squarefree residual, whose forward bridge to
Mathlib's `RiemannHypothesis` is already established. It is not an unconditional
proof of either side of the equivalence.

## 3. Cofinal and relative-gap RH implications

For any \(H(N)\to\infty\), a common bound
\(\Phi_N^+(H(N))\le C\) at arbitrarily late stages forces \(r=0\), and
therefore RH. Conversely, if \(r\ne0\), then
\[
\Phi_N^+(H(N))\longrightarrow\infty
\]
for **every** such expanding head schedule, however slowly it grows.

One may replace the absolute bound by a relative-gap hypothesis. If fixed
\(\theta<1\) and \(C\in\mathbb R\) satisfy, cofinally,
\[
\Phi_N^+(H(N))\le\theta X_{H(N)}(b_N)+C,
\]
then the quadratic comparison, with \(\delta=1-\theta>0\), gives
\[
\boxed{X_{H(N)}(b_N)\le
\frac{2\delta C+1/256}{\delta^2},}
\]
and hence RH. No nonnegativity premise on \(\theta\) or \(C\) is needed.
This condition permits a growing quantity on the right, but still requires
an unproved uniform strict gap below coefficient one.

Formal declarations in `RH/QSquarefreeRawMomentCriterion.lean`:

- `raw_source_layer_le`
- `raw_positiveCrossVariation_sub_layer_sq_le`
- `residual_zero_of_frequently_raw_positive_bound`
- `riemannHypothesis_of_frequently_raw_positive_bound`
- `raw_positive_tendsto_atTop_of_residual_ne_zero`
- `raw_layer_bound_of_relative_gap`
- `riemannHypothesis_of_frequently_raw_relative_gap`

**Open obligations:** a provider for the fixed-head common bound, cofinal
moving-head bound, or strict relative gap for the actual arithmetic stages.
These implications are conditional research reductions.

## 4. Why projection coupling alone cannot prove the bound

`Analysis/CoupledProjectionWeightedObstruction.lean` gives an explicit
two-coordinate model. With sites \(1,m\), target \(x_m=(1,1/m)\), reciprocal
multiplier \(D_m=\operatorname{diag}(1/2,1/(m+1))\), and averaging orthogonal
projection \(P(x,y)=((x+y)/2,(x+y)/2)\), let
\(r_m=(I-P)x_m\), \(s_m=D_mr_m\), and \(b_m=Ps_m\). Exactly,
\[
b_m=(c_m,c_m),\qquad
c_m=\tfrac14(\tfrac12-\tfrac1{m+1})(1-\tfrac1m),
\]
\[
E_m(b_m)=(a(1)+a(m))c_m^2.
\]
For every \(m\ge2\), Lean proves
\[
E_m(s_m)\le1/512,\qquad c_m\ge1/48,\qquad
E_m(b_m)\ge a(m)/2304\longrightarrow\infty.
\]
Projection idempotence and orthogonality are proved, as are the exact
coefficient and energy formulas. This is a finite Euclidean model, with
targets equal to the two-coordinate restrictions of the same reciprocal
sequence. The infinite-dimensional embedding is not separately formalized.
These projection ranges are **not** the actual squarefree stages. The example
rules out a proof based only on abstract coupling and the source budget; it
does not refute the arithmetic conjecture.

## 5. Arithmetic direction that survives the obstruction

The companion paper note `OneAtomSmoothingAndParityObstruction20261026.md`
proves, for projection \(P_d\) onto one legal atom and every \(d\ge2\),
\[
\sup_n|P_dBf(n)|\le\sqrt{\zeta(2)(\zeta(2)-1)}\|f\|_Q,
\]
\[
\mathcal E(P_dBf)\le\frac{9(\zeta(2)-1)}{64}\|f\|_Q^2.
\]
These are paper results, not Lean declarations in this change. The proof
uses \(\|Bg_d\|^2\le(\zeta(2)-1)/(\zeta(2)d^2)\), the exact first
\(d-1\) contributions to \(\|g_d\|^2\), and Cauchy--Schwarz. It explains
how smoothing compensates for the bad weighted/unweighted ratio of an
individual atom. Extending this to many correlated atoms needs inverse-Gram
control on the actual forcing.

The companion note also proves a paper counterexample preserving the
constant Q target and parity orthogonality. It is explicitly outside the
squarefree stages and outside a nested exhaustion.

## 6. Continuation agenda

1. Formalize the uniform one-atom smoothed projection bound, then test whether
   its cancellation survives a Schur-complement addition of one squarefree
   atom. Preserve the signed forcing and the exact Gram denominator.
2. Seek a structural bound specifically for
   \(y_N=\nu_N-J_NG_N^{-1}\mu_N\). A bound for all legal coefficient vectors
   is already obstructed and is not the right target.
3. Try to prove a fixed fraction gap
   \(\Phi_N^+\le\theta X_N+C\), with \(\theta<1\), using actual squarefree
   arithmetic. The new theorem supplies the RH implication immediately if
   such a provider is verified. Repackaging the quadratic comparison alone
   cannot supply that gap.
4. Alternatively prove the common bound with the weaker quantifier order
   \(\exists C\,\forall H\,\forall N_0\,\exists N\ge N_0\). Constants
   depending on \(H\) are insufficient.
5. For CRT conditioning, retain the existing exact identity connecting the
   conditioned source's legal projection to \(b_N\). Existing infinite-modulus
   convergence controls the source; it does not control its weighted legal
   projection. A new signed/Gram estimate is still required after conditioning.

## Literature, diagnostics, and verification scope

Alouges, Darses and Hillion, *Polynomial approximations in a generalized
Nyman–Beurling criterion*, JTNB 34 (2022), 767–785,
https://numdam.org/articles/10.5802/jtnb.1227/ separates unconditional
approximation from additional coefficient/Gram control in a different
generalized criterion. It supports the methodological distinction only;
it is not used as a proof of the squarefree bounds above.

Wolfram returned `True` for
`Abs[Max[x-c,0]-x] <= Abs[c]` under `x>=0` and real `x,c`. This is a
diagnostic of the scalar positive-part step, not a proof certificate.
Lean checked the general and actual-stage candidates, including the exact
fixed-head equivalence and relative-gap implication. The publication
checkpoint validates the persisted source and its affected dependencies.
The single-atom result, parity-preserving infinite-dimensional example,
and asymptotic ratio corollary remain explicitly paper-level in this update.
