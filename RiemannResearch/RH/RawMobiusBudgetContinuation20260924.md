# Raw Möbius budget: quantitative continuation
Date: 2026-09-24

## Status

Unconditional RH is not proved. This continuation follows
NymanBeurlingSubpowerAudit20260924.md and strengthens the unconditional
information about its actual signed finite budget. It does not replace
the Möbius sums by unsigned sums inside the definition of the budget.

The new modules are:
- RawMobiusBudgetQuantitative.lean: exact norm comparison and an explicit
  unconditional logarithmic ceiling.
- RawMobiusBudgetZeroFree.lean: the precise zero-free consequence of one
  fixed power estimate, including a boundary version.

## Exact arithmetic quantity and full norm

Retain the audit's definitions
\[
m_N=\sum_{d=1}^N\frac{\mu(d)}d,\quad
U_N(k)=1+\sum_{d=1}^N\mu(d)\frac{k\bmod d}{d},
\quad
B_N=Nm_N^2+\sum_{k=N+1}^{N^2}\frac{U_N(k)^2}{k(k+1)}.
\]
Let
\[
T_N=\sum_{k>N^2}\frac{U_N(k)^2}{k(k+1)},\qquad
H_j=\sum_{k=1}^j\frac1k.
\]
The new exact identity is
\[
\boxed{B_N+T_N=\|U_N\|_P^2+m_N^2(H_{N+1}-1).}
\]
It follows by evaluating the head sum:
\(\sum_{k=1}^N k/(k+1)=N+1-H_{N+1}\).
The complete tail is present.

The head also satisfies
\[
\frac N2m_N^2\le
m_N^2\sum_{k=1}^N\frac{k}{k+1}.
\]
Consequently the new reverse comparison and the existing forward comparison give,
for \(N\ge1\),
\[
\boxed{B_N\le2\|U_N\|_P^2,\qquad \|U_N\|_P^2\le B_N+1.}
\]
Thus the finite budget and the full physical energy have comparable growth.

## Stronger unconditional quantitative provider

Put
\[
x_N=\frac{1+\log(\log N+3)}{\log N}.
\]
The new theorem proves that there exists a real \(C\ge0\) such that, for all
sufficiently large \(N\),
\[
\boxed{
\frac{B_N}{N}\le
\frac{16}{N}+
\bigl(25+8(2+4C)^2\bigr)x_N+
16(2+4C)^2x_N^2.
}
\]
The right-hand side is also proved to tend to zero.

This uses two already formalized unconditional arithmetic providers:
1. canonicalMobiusHilbert_eventual_optimized_energy;
2. mobiusReciprocalSum_sq_mul_log_tendsto_zero.

The second implies eventually \(m_N^2\log N\le1\), hence \(m_N^2\le x_N\).
Substitution into the existing
\(B_N/N\le4\|F_N\|_P^2/N+4/N+9m_N^2\) gives the displayed constants.
Neither \(C\) nor the onset cutoff is numerically computed by this existential
theorem.

This is stronger quantitative information than merely \(B_N/N\to0\).
It does not yield any fixed positive power saving from the linear exponent.
For every \(\delta>0\), \(N^\delta x_N\to\infty\); the displayed ceiling therefore
does not supply \(B_N\le C_\delta N^{1-\delta}\).
This comparison describes the ceiling, not a lower bound on the actual budget.

## Exact consequence of a power saving

For \(\alpha\ge0\), the new conditional theorem proves:
\[
\left[\exists C,\ \text{cofinally many }N:
 B_N\le C(N+1)^\alpha\right]
\Longrightarrow
\zeta(s)\ne0\quad\left(\Re s>\frac{1+\alpha}{2},\ s\ne1\right).
\]
A stronger boundary statement holds for \(\alpha>0\):
\[
\left[\forall C>0,\ \text{cofinally many }N:
 B_N\le C(N+1)^\alpha\right]
\Longrightarrow
\zeta(s)\ne0\quad\left(\Re s\ge\frac{1+\alpha}{2},\ s\ne1\right).
\]
Whole-sequence convergence \(B_N/(N+1)^\alpha\to0\) supplies the boundary
hypothesis and has a separate Lean theorem.

These are conditional research reductions. The original estimate at every
positive exponent remains Open. The unconditional logarithmic ceiling above
does not discharge it.

## Literature connection: converse not yet formalized in Lean

Báez-Duarte, *Arithmetical aspects of Beurling's real variable reformulation of
the Riemann hypothesis*, arXiv:math/0011254, Remark 4.5, records the
Balazard–Saias implication: absence of zeros in \(\Re s>1/p\) implies
convergence of the raw arithmetic approximants to \(-\mathbf1_{(0,1]}\)
in every \(L^r(0,\infty)\), \(1<r<p\).
Source: https://arxiv.org/pdf/math/0011254, printed page 17.
This supplies a conditional input under RH, not an unconditional estimate.

Here is an independently derived bridge from that input to the present budget.
Define
\[
R_N(x)=\mathbf1_{(0,1]}(x)+\sum_{d\le N}\mu(d)\{1/(dx)\},
\qquad E_N=\int_0^\infty |R_N(x)|^2\,dx.
\]
For \(N\ge1\),
\[
B_N\le(1+1/N)E_N,\qquad
E_N\le(N+1)^{2-p}\int_0^\infty |R_N(x)|^p\,dx
\quad(1<p<2).
\]
For the first comparison, substitute \(y=1/x\).
The exact head contributes \(Nm_N^2\) on \(0<y<N\).
On every relevant unit cell, \(R_N(1/y)=U_N(k)+(y-k)m_N\).
For real \(a,b\) and \(0\le t\le1\),
\[
a^2+\frac{(a+(N+1)bt)^2}{N}
=(1+1/N)(a+bt)^2+(N+1)b^2t^2.
\]
Integrating over cells \(k=N+1,\ldots,N^2\) with weight \(y^{-2}\)
bounds the correction by \(m_N^2\); the exact head absorbs it.
The second comparison uses \(|R_N|\le N+1\).

Under RH, the cited theorem makes the \(L^p\) integral tend to zero for every
\(1<p<2\). Choosing \(2-p<\varepsilon\) therefore gives
\[
\mathrm{RH}\Longrightarrow
\forall\varepsilon>0,\quad B_N/(N+1)^\varepsilon\longrightarrow0.
\]
Together with the already verified sufficient implication, this is a
paper-level equivalence between RH and the audit's cofinal subpower criterion.
The continuous arithmetic bridge and the external \(L^p\) convergence provider
have NOT been formalized in this batch and are not imported as axioms.

## Next arithmetic target

The remaining work is cancellation in the actual middle window on suitable
cofinal cutoffs. Optimizing the existing unsigned harmonic-window bound only
adjusts its logarithmic ceiling. A complete-period CRT average also cannot be
substituted for the distinguished short interval \((N,N^2]\) without a
separate localization theorem.

A useful next formalization is the continuous-to-discrete energy bridge above.
A substantive route toward RH still requires a new unconditional provider for
the actual signed subpower energy, or a genuinely weaker sufficient criterion
with its own proved arithmetic provider.

## Verification record

The new declarations were checked in serialized Lean snippets.
Their printed dependencies contain only propext, Classical.choice, and
Quot.sound. The fixed-power zero-free declarations retain their explicit
arithmetic hypotheses. No sorry, project-local axiom, or RH assumption is used
in the unconditional quantitative declarations.

Final project acceptance and publication are performed by the single
checkpoint for this continuation; its commit is reported in the conversation.
