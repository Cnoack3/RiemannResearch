# Moving Gram predictions, gain cancellation, and a sharper gap bound

29 October 2026. Continuation of a4911d47; workspace baseline fcd1dd3652625bc33b7f7f8bdb3d4039e6189866.

## Outcome and status

This continuation proves a smaller unconditional complete-Q conductor-gap
majorant, exact inverse-Gram formulas for actual moving predictions, an exact
gain decomposition, and a new cumulative cancellation budget no larger than
the previous gapBudget.

The required subpolynomial growth estimate remains **Open**. Neither RH nor
a sufficient bound on the actual moving predictions is proved. The new RH
consumer is explicitly a **conditional research reduction**.

The complete algebra and optimizer applications are Lean statements. The block
Schur-complement interpretation, discussion of its limitations, and external
short-interval consequences below are paper arguments. No external analytic
result is installed as an axiom.

## 1. Stronger complete-Q conductor-gap bound

For integers 2 <= n < r <= 2n and delta = r-n, the existing declaration
QCompensatedResidueGap.compensatedResidue_gap_log_bound is strengthened to

\[
 \|g_n-(r/n)g_r\|_Q^2
 \le \frac{\delta}{\zeta(2)n^2}
       \left(\frac{21}{4}+\log\frac n\delta\right).
\]

The additive constant was 7. The full infinite tail is still included.

Set J = floor(n/delta)+1. Besides n <= J delta <= r, the integer cutoff
satisfies J >= 2. The improved tail estimate is

\[
 \frac{(r/n)^2}{Jn}\le\frac94\,\frac{\delta}{n^2}.
\]

To prove it, show r^2 <= (9/4)n J delta. If r <= 3n/2, use J delta >= n.
Otherwise delta >= n/2, J >= 2, and
(delta-n/2)(n-delta) >= 0 give r^2 <= (9/2)n delta.
The previous argument bounded this tail by 4 delta/n^2.
The harmonic contribution is at most (2+log(n/delta)) delta/n^2 and
the middle term at most delta/n^2, yielding 2+1+9/4 = 21/4.

Analysis.DiscreteFloorGap.gap_tail_sharp is the new scalar lemma.
The stronger gap_majorant_log uses J >= 2; the actual integer cutoff proves
this premise. No new assumption is added to the complete-Q theorem or actual
optimizer application.

QSquarefreeGapHeadCost.gapWeight now uses 21/4. Consequently all its existing
actual head-cost, gain-retaining energy, and conditional RH statements use
this smaller weight. The original memorandum remains a record of the
historical 7-bound, with a link to this strengthening.

## 2. Actual optimizer and inverse-Gram prediction

Use the same dense schedule as before:
\[
 F_i=\operatorname{minimumAt}(2i,i+1),\quad
 Z_i=\operatorname{minimumAt}(2i+2,i+1),\quad n=i+2.
\]
Define
\[
 a_i=1-F_i(n),\qquad b_i=1-Z_i(n),\qquad D_i=F_i-Z_i.
\]
The new oldMismatch is a_i; nextMismatch remains b_i.

Let L=primorial(2i+4), r be the nearest squarefree successor of n, and let
v_d=g_d-(r/d)g_r range over all free conductors d>n-1 dividing L, except r.
This is a linearly independent basis of the full enlarged zero-head tangent.
Write
\[
 \Gamma_{de}=\langle v_d,v_e\rangle_Q,\qquad
 z_d=\langle v_d,F_i\rangle_Q,\qquad \gamma=\Gamma^{-1}z.
\]
The checked identity is
\[
 Z_i=F_i-\sum_d\gamma_d v_d,\qquad
 b_i=a_i+\sum_d\gamma_d\,v_d(n).
\]
At a squarefree n, v_n(n)=-1 and every other basis value is zero. Therefore
\[
 \boxed{b_i=a_i-(\Gamma^{-1}z)_n.}
\]

The generic declarations minimumAt_enlargement_inverseGram,
minimumAt_enlargement_prediction, and
minimumAt_enlargement_prediction_coefficient express these facts in Lean.
The inverse is the existing actual Gram linear equivalence, whose
invertibility follows from linear independence. The coefficients are those
of the actual displacement projection; they are not substituted Mobius
coefficients or the coefficients of an approximation-error minimizer.

## 3. Scalar Schur-complement interpretation (paper)

Separate conductor n from the other free conductors:
\[
 \Gamma=\begin{pmatrix}\alpha&h^\mathsf T\\h&B\end{pmatrix},
 \qquad z=\binom{u}{v},\qquad
 s=\alpha-h^\mathsf T B^{-1}h>0,\quad
 t=u-h^\mathsf T B^{-1}v.
\]
The empty remaining block has the usual zero-dimensional convention.
Solving the two block normal equations gives
\[
 \gamma_n=t/s,\quad
 \boxed{b_i=a_i-t/s},\quad
 \kappa_i=(\Gamma^{-1})_{nn}=1/s.
\]
Here kappa_i is exactly stepCapacity, the squared norm of the next-site
evaluation representer on the full enlarged tangent.

This is an exact formula, but positivity of s alone gives no useful uniform
bound for t/s. A small conductor-gap trial bounds s from above, not below;
it improves the repair cost without controlling the moving coefficient.
The actual correlations in t still require arithmetic information.

## 4. Exact cancellation and its norm-square remainder

Let k_i be stepNormal, so k_i(n)=kappa_i and ||k_i||_Q^2=kappa_i.
At a squarefree n define
\[
 R_i=D_i-\frac{b_i-a_i}{\kappa_i}k_i.
\]
The complete gain decomposition is
\[
 \boxed{G_i=\|D_i\|_Q^2
 =\frac{(b_i-a_i)^2}{\kappa_i}+\|R_i\|_Q^2.}
\]
In particular,
\[
 (b_i-a_i)^2\le \kappa_i G_i.
\]
The exact extension cost C_i=b_i^2/kappa_i now gives
\[
 \boxed{E_{i+1}-E_i=C_i-G_i
 =\frac{a_i(2b_i-a_i)}{\kappa_i}-\|R_i\|_Q^2.}
\]

These are checked by minimumAt_enlargement_gain_completion,
minimumAt_prediction_shift_sq_le_gain,
minimumAt_signed_prediction_transition, and the actual dense specialization
dense_signed_prediction_transition. The latter explicitly assumes n is
squarefree. At nonsquarefree sites the existing radical-compatibility
theorem gives b_i=C_i=0, so the net change is -G_i.

In the block notation above, ordinary block algebra additionally gives
\[
 \|R_i\|_Q^2=v^\mathsf T B^{-1}v,\qquad
 E_{i+1}-E_i=s a_i^2-2a_it-v^\mathsf T B^{-1}v.
\]
This block reformulation is paper-level; the complete Hilbert identity with
the literal norm-square remainder is the checked result.

Wolfram independently verified the scalar cancellation
b^2/k-((b-a)^2/k+R)=a(2b-a)/k-R and the refined tail inequality.
Lean, rather than Wolfram, verifies the optimizer claims.

## 5. A smaller explicit cumulative budget

Put
\[
 p_i=\max\{0,a_i(2b_i-a_i)\}.
\]
Completing the scalar square yields
\[
 0\le p_i\le b_i^2,
 \qquad a_i(2b_i-a_i)=b_i^2-(b_i-a_i)^2.
\]
With w_i=gapWeight(n,r), define
\[
 S_N=\sum_{i<N}\min\left\{
       \frac{4b_i^2}{\zeta(2)(i+1)},\ p_iw_i\right\}.
\]

QCRTCancellationBudget checks
\[
 0\le S_N\le T_N,\qquad
 C_i-G_i\le p_iw_i,\qquad
 E_N\le E_0+S_N,
\]
and
\[
 \|1-F_N\|_Q^2\le 2+2E_0+2S_N.
\]
Here T_N is the now-strengthened gapBudget with constant 21/4.
Thus S_N is also no larger than the original 7-bound budget.

For the signed gap bound, first retain the exact norm-square remainder.
Then replace a_i(2b_i-a_i) by its nonnegative part and use
1/kappa_i <= w_i. Negative signed contributions are bounded above by zero;
they are not mistakenly multiplied by an upper bound for 1/kappa_i.

The new conditional consumer is
\[
 \frac{\log(1+S_N)}{\log(N+2)}\longrightarrow0
 \quad\Longrightarrow\quad \mathrm{RH}.
\]
Declaration: riemannHypothesis_of_subpolynomial_cancellationBudget.
Its displayed growth hypothesis remains **Open**.

S_N can exploit observed cancellation even when b_i is large. The exact
identities still retain the further unobserved gain ||R_i||^2.
Neither S_N nor the old gain-retaining bound T_N-sum G_i is claimed to
dominate the other. Both are valid energy bounds.

## 6. What the normal equations do and do not establish

Radical compatibility completely eliminates nonsquarefree next sites.
At squarefree next sites it leaves the new increment free; it supplies no
bound on the inverse-Gram coordinate by itself.

An abstract finite-dimensional example illustrates why controlling b alone
can miss cancellation. In R^2 take old dictionary span{(1,1)}, enlarged
dictionary R^2, old head x=1, and next observation (1+t)x-ty, where t>0.
Then F=(1,1), Z=(1,0), a=0, b=-t, kappa=t^2, and C=G=1.
The next head minimum is again F. Thus b is arbitrarily large while the
net energy change and p are zero. This is a paper-level Hilbert-space example,
not a claim about the actual CRT dictionaries and not evidence for RH.

For the actual arithmetic system, none of the checked normal equations
proves the needed all-stage cancellation or prediction bound.
No convergence at a fixed conductor is used to bound the moving conductor.

## 7. External gap input and revised thresholds (paper)

Kumchev et al., Journal of Number Theory 254 (2024), Theorem 1:
https://arxiv.org/abs/2211.09975 .
Using their stated delta=O(n^(1/5) log n) bound gives
w_i=O(n^(-9/5) log^2 n). Hence the new sufficient condition is
\[
 p_i=O(n^{4/5}),
\]
which makes S_N=O(log^3(N+2)). This is weaker than requiring
b_i^2=O(n^(4/5)); a signed cross term may cancel.

A newer primary source is Mayank Pandey, *Squarefree numbers in short
intervals*, arXiv:2401.13981v3, revised 7 August 2026, Theorem 1.1:
https://arxiv.org/html/2401.13981v3 .
It states a short-interval asymptotic at exponent 1/5-eta for some eta>0,
left inexplicit. Taking the interval starting at n+1 ensures a strictly
larger squarefree successor. On paper this gives
w_i=O(n^(-9/5-eta) log n).

Consequently p_i=O(n^(4/5+eta)) suffices for S_N=O(log^2(N+2));
p_i=O(n^(4/5)) even makes the signed majorants summable.
For the older absolute prediction route the threshold becomes
|b_i|=O(n^(2/5+eta/2)) for a polylogarithmic budget, while
O(n^(2/5)) suffices for bounded cumulative head costs.

These are deductions from an external theorem, not new Lean results.
Neither external gap theorem nor any stated prediction/cancellation
hypothesis is a checked provider in this continuation. The previous
Kumchev proof audit and its unresolved formalization obligations remain
in force; this work does not resolve them.

## 8. Precise remaining research targets

1. **Open:** prove subpolynomial growth of the literal S_N, or a stronger
   signed bound retaining the norm-square remainders.
2. **Open:** estimate the actual Schur numerator t relative to s and the
   old mismatch a_i; positivity of the Gram matrix is insufficient.
3. **Open:** establish a sufficient bound on p_i, potentially in weighted
   average rather than pointwise. It is not necessary to control |b_i|
   separately if observed cancellation can be proved.
4. **Paper-level:** formalize the external short-interval input and its
   asymptotic consequences, if using that route.
5. Do not replace F_i or Z_i with canonical Mobius approximants, omit the
   infinite tail, or interpret the conditional RH consumer as an RH proof.

## Verification record

The strengthened gap/cost modules passed targeted server job
job_x-PMvNkn5HWhcYCxeoaxCtjJNaZXIVee (reported elapsed 22.549 seconds).
The moving prediction/gain module and cancellation-budget application
passed targeted server job job_NQCY1okuvoQc59BSxWGVaR8ssWlkYwgV
(reported elapsed 16.598 seconds). These are targeted checks, not an
entire-project certification. Final saved-source axiom audit and the
single publication checkpoint are reported in the completion message.
