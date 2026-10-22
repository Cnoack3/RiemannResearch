# Finite-rank control of the offsite vacancy budget — 2026-09-30

Base: Cnoack3/RiemannResearch commit c7c09ab40cb4da1f400471aa6616eb5784c9a088.
Scope: quantitative continuation of the certificate-cutoff bridge, independent
of its separate audit. No RH-strength arithmetic provider is constructed.

## Main unconditional upper bound

Stage n uses g_2,...,g_(n+1). Physical site j has weight
w_j = 1/(j(j+1)); counting coordinate i represents j=i+1.

For any finite tail trial c with positive complete tail energy, put

\[
 E=\left\|\sum_{d=2}^{n+1}c_d\,t_d\right\|^2,\qquad
 S=\sum_{d=2}^{n+1}\frac{c_d}{d},\qquad
 B=\frac{E}{S^2+2E},\qquad s=\mathrm{finiteTrialVacancySlack}(n,c).
\]

These energies contain every signed Gram cross term and the entire physical
tail. The full residue trial energy is E+S^2/2. The existing bridge supplies
the exact nonnegative square slack. The new result uses

\[
 \Delta=B-s=\frac{\mathrm{vacancy}(n)}2
 =\|p_0-P_n p_0\|^2>0.
\]

Define

\[
 q=2^{-1/2},\qquad
 a_{K+1}=\frac{1-q^{K+1}}{1-q},\qquad
 A_M=\sum_{j=2}^{M+1}
 \left(\frac1{\sqrt j}+\frac1{\sqrt{j+1}}\right)^2.
\]

If

\[
 N+1\ge (M+2)\,2^K(n+1),
\]

then the newly verified theorem
offsiteWeightedVacancyPrefix_le_rank_trial_budget proves

\[
 \boxed{\quad
 O_{N,M}+\frac1{M+2}
 \le A_M\bigl(q^{K+1}+a_{K+1}\sqrt\Delta\bigr)^2+\frac1{M+2}.
 \quad}
\]

Here O_(N,M) is offsiteWeightedVacancyPrefix N M, covering physical sites
2,...,M+1. The displayed tail is the complete existing physical tail allowance.
The Lean declaration bounds O_(N,M); adding the identical tail to both sides
gives the boxed statement.

Kernel monotonicity also gives the full cutoff bound, formalized as
weightedVacancyCutoff_le_rank_trial_budget:

\[
 C_{N,M+1}
 \le \Delta+
 A_M\bigl(q^{K+1}+a_{K+1}\sqrt\Delta\bigr)^2+\frac1{M+2}.
\]

The hypotheses are only the displayed finite rank inequality and E>0.
There is no assumed RH, zero residual, density, inverse-Gram bound, or
asymptotic certificate provider in these inequality statements.

## Exact identities underlying the estimate

Let T_m f(j)=f(floor(j/m)). It is the existing
CoefficientStabilization.unscaledResidueDilation, with

\[
 \|T_m f\|^2=\frac{\|f\|^2}{m},\qquad
 T_m g_d=g_{md}-\frac1d g_m.
\]

The repository already provides unscaledResidueDilation_mem_finiteSpace and
PointTargetDilationSynthesis. Those declarations are reused.

Individual site targets obey p_i=T_(i+1)1-T_(i+2)1. Thus, for a legal trial f,
the site trial y_i=T_(i+1)f-T_(i+2)f is legal at the enlarged rank, and

\[
 \|p_i-y_i\|^2=
 \left(\frac1{i+1}+\frac1{i+2}\right)\|1-f\|^2
 -2\langle T_{i+1}(1-f),T_{i+2}(1-f)\rangle.
\]

The complete projection identity is

\[
 w_{i+1}(1-K_N(i,i))
 =\|p_i-y_i\|^2-\|P_Np_i-y_i\|^2.
\]

The second square is retained by weightedVacancyTerm_eq_trial_energy,
weightedVacancyTerm_eq_dilation_energy, and
offsiteWeightedVacancyPrefix_eq_trial_squares.
Only the upper-bound theorem discards that explicitly nonnegative square.
It estimates the signed dilation inner product by Cauchy–Schwarz after the
full equality has been recorded.

The arbitrary coefficient identity weightedVacancyTerm_eq_fullGram_trial is

\[
 w_{i+1}(1-K_N(i,i))
 =w_{i+1}-2\sum_d c_d\langle g_d,p_i\rangle
  +\sum_{d,e}c_dc_eG_N(d,e)
  -\left\|P_Np_i-\sum_d c_dg_d\right\|^2.
\]

No Gram mixed term is dropped.

For y=P_n p_0, the existing finite geometric synthesis
f=pointDilationSynthesis y (K+1) has maximal conductor 2^K(n+1), and

\[
 \|1-f\|\le q^{K+1}+a_{K+1}\|p_0-y\|.
\]

Its existing residual-step identity retains the signed error before taking
norms. The final site dilations require conductors at most
(M+2)2^K(n+1). This accounts for every rank enlargement in the main bound.

## Exact Gram-trace form of the barrier

Let B_off=windowFeatures N M (fun i => i.val+1), and let D_off have diagonal
paretoWeight(i.val+1). The new theorem
offsiteWeightedVacancyCutoff_eq_gram_trace proves

\[
 \boxed{\quad O_{N,M}+\frac1{M+2}
   =\frac12-\operatorname{tr}
      (D_{\rm off}B_{\rm off}G_N^{-1}B_{\rm off}^{T}).\quad}
\]

The matrix G_N is the full Gram matrix, not a window truncation.
This uses integerKernel_window_matrix, keeping all inverse-Gram correlations.
The pointwise upper bounds alone replace the trace by zero and return 1/2.

## What remains open, and how little is needed

The bound transfers arbitrarily small first-site errors to full cutoff
certificates after explicit conductor enlargement. It needs no additional
offsite provider once that first-site provider is available.

The remaining estimate can be written exactly as

\[
 \forall\eta>0\ \exists n:\quad
 \Delta_n=\frac1{\mathrm{tailCapacity}(n)+2}<\eta.
\]

Equivalently, the already established bridge asks for arbitrarily large finite
ratios S^2/E. No rate in n and no uniform inverse-Gram estimate are required for
the existential cutoff criterion. This is still the substantive open
RH-strength provider.

To see sufficiency quantitatively, let C=(1-q)^(-1). The established bound
A_M <= 2 sum_(j=2)^(M+1)(1/j+1/(j+1)) gives A_M=O(log M), and

\[
 C_{N,M+1}\le
 \Delta_n(1+2A_MC^2)+2A_Mq^{2(K+1)}+\frac1{M+2}.
\]

This last displayed estimate and the following parameter choice are elementary
consequences of the verified sharper inequality; they are explanatory
calculations, not separately named Lean declarations.
Choose M to make the physical tail small, then K to make the geometric
remainder small, then n using the open first-site provider. Every cutoff is
finite. No limit is exchanged with an optimization or an inverse.

At a fixed rank, the exact weakest scalar condition for offsite smallness is
trace(D_off B_off G_N^(-1) B_off^T)>1/2-epsilon. The rank-enlarged bound gives
a sufficient way to obtain it from the original first-site provider.
No same-rank vanishing assertion is made.

## Trigamma: exact evaluation, not a saturation provider

For a positive conductor L and positive progression representative r, define
alpha_(L,r)=sum_(k>=0)w_(r+kL) and beta_(L,r)=sum_(k>=0)w_(r+kL)^2. Then

\[
 \alpha_{L,r}
 =\frac{\psi((r+1)/L)-\psi(r/L)}{L},
\]

\[
 \beta_{L,r}
 =\frac{\psi_1(r/L)+\psi_1((r+1)/L)}{L^2}
 -\frac{2}{L}\bigl(\psi((r+1)/L)-\psi(r/L)\bigr).
\]

These follow from
1/(x^2(x+1)^2)=1/x^2+1/(x+1)^2-2/x+2/(x+1)
and the standard digamma difference and trigamma series.
Primary reference: NIST DLMF §5.15, https://dlmf.nist.gov/5.15.E1.
Wolfram Language symbolically checked the beta identity, returning zero
for the difference under L>0,r>0. These progression formulas are explanatory
analytic identities, not new Lean-verified declarations in this change.

Grouping complete periodic features v_r gives
G_N=sum_r alpha_(L,r) v_r v_r^T and occupied weighted mass
sum_r beta_(L,r) v_r^T G_N^(-1) v_r. The grouping keeps every conductor class
and every mixed Gram entry. Evaluating alpha and beta does not establish the
missing trace-saturation or first-site provider.

## Formalization and verification

New modules:
- Analysis/ProjectionTrialEnergy.lean — the exact general Pythagorean trial square.
- RH/IntegerDPPOffsiteTrialBounds.lean — exact site, Gram and offsite identities,
  arithmetic conductor transfer, and the two finite-rank trial bounds.

The final combined candidate passed Lean with exit code 0.
Axiom checks on the main bounds and exact Gram identities reported only
propext, Classical.choice and Quot.sound.
Final acceptance uses the change-aware project checkpoint, validating the new
modules and their reverse dependents. This is not an independent audit or a
fresh full-project rebuild of c7c09ab.
