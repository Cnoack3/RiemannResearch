# Squarefree conductor gaps improve actual minimum-energy costs

29 October 2026. Continuation of the attached minimum-energy remaining-obligations
handoff, whose baseline is e0784ecfaf37819aa6feccebf67a66e53472ec53.

## Outcome and scope

This continuation proves a new unconditional complete-Q estimate for compensated
residue directions and applies it to the actual dense-schedule minimum-norm
vectors. It constructs the least squarefree anchor, retains every enlargement
gain, and defines a literal improved prediction budget that never exceeds the
previous cost majorant.

It does not prove the required bound on moving predictions or their weighted
budget. RH, constant membership, and bounded cofinal optimizer energy remain
unproved. The external squarefree-gap applications below are paper-level.

## 1. Complete-energy conductor-gap theorem

For integers 2 <= n < r <= 2n, put delta = r-n and

  v = g_n - (r/n) g_r.

The new Lean declaration
QCompensatedResidueGap.compensatedResidue_gap_log_bound proves

\[
 \boxed{\|v\|_Q^2\le
 \frac{\delta}{\zeta(2)n^2}\left(7+\log\frac n\delta\right).}
\]

There is no squarefreeness, prime-gap, optimizer, or RH hypothesis in this
theorem. The norm includes all positive physical sites.

The stronger finite-cutoff interface
compensatedResidue_gap_energy proves, for every integer J >= 1,

\[
 \zeta(2)\|v\|_Q^2\le
 \frac{\delta}{n^2}H_J+
 \frac{(Jn+1)\delta^2}{n^2r^2}
 +\frac{(r/n)^2}{Jn}.
\]

Here H_J is the harmonic number; the Lean statement uses the equal sum
sum_{j=0}^J 1/j, with real division making the j=0 term zero.

### Ordinary proof, including the signed identity

At physical site k write a=floor(k/n), b=floor(k/r), D=a-b and t=delta*b/n.
The exact identities are

\[
 v(k)=t-D,\qquad
 v(k)^2=D+t^2-D(1+2t-D).
\]

We have D >= 0. If b=0, then k<r<=2n and D<=1. If b>=1,
na<=k<r(b+1) gives D<1+t+delta/n<=1+2t.
Thus the last displayed remainder is nonnegative.

For k < (J+1)n, the exact counting identity is

\[
 D=\sum_{j=1}^{J}\mathbf1_{\{jn\le k<jr\}}.
\]

The intervals are allowed to overlap; every multiplicity is retained.
Each interval contains j*delta integers and its inverse-square mass is at
most delta/(j*n^2). Therefore the D contribution through k=Jn is at most
delta*H_J/n^2. Since b<=k/r, the t contribution is at most
(Jn+1)*delta^2/(n^2*r^2), harmlessly counting k=0 too.
Finally, |v(k)|<=r/n and sum_{k>Jn} k^(-2)<=1/(Jn), proving the finite bound.

Choose J=floor(n/delta)+1. Then n<=J*delta<=r, J<=2n/delta and

\[
 H_J\le2+\log(n/\delta),\qquad
 (Jn+1)\delta\le r^2,\qquad
 \frac{(r/n)^2}{Jn}\le\frac{4\delta}{n^2}.
\]

The three contributions are bounded by 2+log(n/delta), 1, and 4,
respectively, in units delta/n^2. This proves the rational constant 7.

## 2. Application to the actual optimizers

Keep the exact handoff definitions

\[
 F_i=\operatorname{minimumAt}(2i,i+1),\quad
 Z_i=\operatorname{minimumAt}(2i+2,i+1),\quad
 b_i=1-Z_i(i+2),
\]
\[
 E_i=\|F_i\|_Q^2,\quad
 C_i=\|F_{i+1}-Z_i\|_Q^2,\quad
 G_i=\|F_i-Z_i\|_Q^2.
\]

For n=i+2 and any squarefree r with n<r<=2n, the actual dictionary is the
divisor dictionary of primorial(2n), so r belongs to it. When n is squarefree,
n also belongs. The vector -b_i*v is an admissible correction of the next
site, and the existing exact capacity formula yields

\[
 \boxed{C_i\le b_i^2\,w(n,r),\qquad
 w(n,r)=\frac{r-n}{\zeta(2)n^2}
       \left(7+\log\frac n{r-n}\right).}
\]

When n is nonsquarefree, b_i=C_i=0, so the same inequality holds.
The checked declaration is QSquarefreeGapHeadCost.dense_headCost_gap_bound.
The generic minimumAt_single_head_gap_bound also applies to any larger
primorial dictionary satisfying its explicit membership hypotheses.

This uses the actual old-head minimum after enlargement. It neither substitutes
canonical Mobius coefficients nor transfers equations between the norm-minimum
and approximation-error-minimum problems.

## 3. A completely specified improved budget

Let rho_i be the least squarefree integer strictly larger than i+2.
The Lean definition squarefreeAnchor uses Nat.find, and the following are
checked: existence, squarefreeness, strict lower bound, minimality among all
squarefree successors, and rho_i<=2(i+2). Bertrand supplies the last bound
without an external short-interval assumption.

Define the literal gapBudget T_N by

\[
 T_N=\sum_{i<N}\min\left\{
 \frac{4b_i^2}{\zeta(2)(i+1)},\
 b_i^2w(i+2,\rho_i)\right\}.
\]

Lean proves

\[
 0\le T_N\le\frac4{\zeta(2)}\mathcal B_N,\qquad
 \boxed{E_N\le E_0+T_N-\sum_{i<N}G_i},
\]
\[
 \|1-F_N\|_Q^2\le2+2E_0+2T_N.
\]

The minimum matters: the conductor-gap estimate alone is not always smaller
than the previous estimate when the gap is a large fraction of n.
This combined majorant is never worse at any stage.

The checked conditional consumer is

  QSquarefreeGapHeadCost.riemannHypothesis_of_subpolynomial_gapBudget

with the sole new arithmetic hypothesis

\[
 \lim_{N\to\infty}\frac{\log(1+T_N)}{\log(N+2)}=0.
\]

That hypothesis remains **Open**. The consumer proves the actual
RiemannHypothesis proposition only after the hypothesis is supplied.
The signed gain-retaining bound allows further cancellation arguments.

## 4. Paper-level arithmetic consequences

### Published squarefree gaps

Kumchev, McCormick, McNew, Park, Scherr and Ziehr,
*Explicit bounds for large gaps between squarefree integers*,
Journal of Number Theory 254 (2024), Theorem 1, states a squarefree integer in

\[
 (x,\ x+11x^{1/5}\log x]\qquad(x\ge2).
\]

Primary sources: https://arxiv.org/abs/2211.09975 and
https://www.nathanmcnew.com/Explicit2.pdf (Theorem 1, page 2);
DOI https://doi.org/10.1016/j.jnt.2023.07.003.

The citation supports the squarefree-gap input only. It does not state a result
about these optimizers. This external theorem is not formalized or assumed
as a custom axiom in the new Lean modules.

Follow-up audit: [SquarefreeGapFormalizationAudit20261029.md](SquarefreeGapFormalizationAudit20261029.md).
Lean verifies that the reciprocal inference in the cited proof's equation (4.3)
fails under its displayed numerical premises. A corrected local spacing
constant and rational repair certificates are now checked. The full interval
theorem is still not proved in Lean; its analytic and finite-range providers
remain open. The following application is conditional on that external input.

By minimality of rho_i, delta_i=rho_i-n is at most that gap bound.
For sufficiently large n, the bound is <=n. Since delta_i>=1, the new
complete-energy estimate gives

\[
 C_i\le\frac{11}{\zeta(2)}b_i^2n^{-9/5}
             \log n\,(7+\log n),\qquad n=i+2.
\]

Consequently an eventual estimate |b_i|<=B*n^(2/5) would give
T_N=O(1+log^3(N+2)) and hence RH by the checked subpolynomial consumer.
For any fixed epsilon>0, a bound O(n^(2/5-epsilon)) makes the head costs
summable, bounds E_N, and forces the fixed residual to vanish.
Neither moving prediction estimate is proved.

More generally, a limsup of log(1+|b_i|)/log(i+2) at most 2/5 suffices
on paper: every small exponent loss in b_i gives an arbitrarily small
power majorant for the cumulative energy.

### Elementary squarefree gaps

An elementary alternative avoids invoking the published short-interval theorem.
For n>=256 let m=ceil(sqrt n), h=8m. Every nonsquarefree integer in
(n,n+h] is divisible by d^2 for some 2<=d<=m+4. The union bound gives at most

\[
 \sum_{d=2}^{m+4}(h/d^2+1)
 \le \tfrac34h+(m+3)=7m+3<h,
\]

because sum_{d>=2} d^(-2)<=1/4+sum_{d>=3}1/[d(d-1)]<=3/4.
Thus a squarefree successor satisfies delta<=8ceil(sqrt n)<=16sqrt n,
and n>=256 also ensures this chosen interval lies below 2n.
Therefore, on paper,

\[
 C_i\le\frac{16}{\zeta(2)}b_i^2n^{-3/2}(7+\log n).
\]

The sufficient prediction threshold becomes O(n^(1/4)) for polylogarithmic
energy, or O(n^(1/4-epsilon)) for bounded energy.
This counting argument and its asymptotic consumers are not yet Lean declarations.

## 5. Remaining research obligations

The main unresolved problem is still an estimate on the **actual moving**
b_i, or enough cancellation from the actual G_i. This work improves the
weight multiplying b_i^2; it does not bound b_i.

Useful next targets:

1. Prove subpolynomial growth of the literal T_N, keeping the minimum and
   the actual nearest-squarefree anchors.
2. Use the actual normal equations to bound weighted moving coefficients
   b_i=a_{i+2}+mu(i+2). A fixed-conductor limit remains insufficient.
3. Retain gains in the signed sum if an absolute prediction bound is too weak.
4. Continue the requested fifth-power squarefree-gap formalization using
   the corrected spacing argument and explicit remaining obligations in
   the follow-up audit.
5. The handoff's 17H repair-operator estimate remains paper-level and unchanged.

Pointwise convergence, complete energy finite at each individual stage,
optimizer coalescence, and isolated finite certificates still do not supply
a cofinal energy bound. No assumption needed for RH has been silently discharged.

## Verification and provenance

The elementary conductor-gap argument is developed in this continuation from
the user-provided handoff; no mathematical novelty claim is made.
Wolfram checked the scalar expansion and rational algebra exactly.
The complete theorems are checked through Lean rather than those algebra checks.

The source is split by responsibility:
- Analysis/DiscreteFloorGap.lean: exact multiplicity count and weighted band sums.
- RH/QCompensatedResidueGap.lean: full Q norm and logarithmic conductor-gap bound.
- RH/QSquarefreeGapHeadCost.lean: actual optimizer costs, deterministic anchors,
  improved signed budget, and conditional RH consumer.

The saved-module import and six-declaration axiom audit succeeded in
job_mC2Mc6Nbui2A0eCAkSEVGXSNjfbXHSGq, with server elapsed time 22.219 seconds.
Every audited declaration uses only propext, Classical.choice, and Quot.sound.
The six audited declarations include the complete logarithmic bound, actual
head-cost application, old-budget comparison, signed energy estimate, and RH
consumer. The consumer's local subpolynomial-budget hypothesis remains Open.

The final server checkpoint, validation scope, and commit are reported with the
completion message. Workspace-opening and intermediate polling round trips were
not separately instrumented; server verification durations are separate from
those request delays.
