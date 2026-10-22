# Signed divisor sampling after the Anthropic bridge

## Status

Source: the user's `AnthropicRHBridges20260928.md` and the published
RiemannResearch base `427ea60d50ebd842570c59af8cfb429fb4f9c7af`.
The three modules named in that attachment were absent from this base.
They have been reconstructed and formalized in Lean, with a further
common-period cancellation argument. All six modules are exported from
`RiemannResearch.lean`. No novelty claim is made.

The repaired source, including all 16 principal manuscript declarations,
passes a combined Lean check in the unchanged pinned environment. Its
SHA-256 is `8ec59eca9f2f6f072325c4a1777da7c16f4e97c599c0a027042c6dfca9cde88f`.
The 11 audited endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The source contains no proof placeholders or new axioms.
The publication checkpoint additionally checks the modules with their actual
imports and affected reverse dependencies.

The foundation audit does not discharge hypotheses in theorem types.
Weil positivity explicitly assumes RH, and the cofinal signed arithmetic
cancellation condition below remains **Open**. No RH proof is claimed.

## Actual arithmetic objects

Fix a stage n and an old coordinate 1<d≤n. Put p=n+1,
u=P_n h_d, and write its unique finite residue synthesis as

\[
 b(j)=u(j)=\sum_{e=2}^{n+1}q_e\,g_e(j),\qquad
 g_e(j)=\frac{j\bmod e}{e}.
\]

Here q_e are the actual projected-dual coefficients, hence the relevant
inverse-Gram column, not independently chosen test coefficients. Let
T_n be the repository's complete canonical arithmetic tail and

\[
 a_k=\frac{T_n(p+k)}{(p+k)(p+k+1)},\quad
 A_m=\sum_{k<m}a_k,\quad
 S_M=\sum_{k<M}a_k b(p+k).
\]

The existing exact correction identity is

\[
 \kappa_{n,d}=S_M+\langle\operatorname{tail}_{n+M}u,
                         \operatorname{tail}_{n+M}T_n\rangle.
\]

Both later tails are entire Hilbert-space tails.

## Exact divisibility differences

For every e>0, increasing j by one either crosses a multiple of e or does
not. In the first case the residue drops by e-1; in the second it rises by 1.
Thus

\[
 g_e(j+1)-g_e(j)=\frac1e-\mathbf1_{e\mid j+1}.
\]

Set \(\lambda=\sum_e q_e/e\) and
\(D(j)=\sum_e q_e\mathbf1_{e\mid j}\). Finite linearity gives

\[
 \Delta b(j)=\lambda-D(j+1),\qquad
 \Delta^2b(j)=D(j+1)-D(j+2).
\]

The constant drift cancels exactly from the second difference. All q_e
remain signed. In particular, since g_e(1)=1/e,
\(\lambda=b(1)\). The first physical coordinate has Pareto weight 1/2, so

\[
 \lambda^2\le2\|P_nh_d\|^2\le2\|h_d\|^2.
\]

This is a dimension-independent bound on a signed reciprocal inverse-column
sum. It does not bound the absolute column mass or the full Abel pairing.

## Removing the Abel boundary exactly

Define the centered progression sample

\[
 E_e(M)=\sum_{k<M}A_{k+1}
       \left(\mathbf1_{e\mid p+k+1}-\frac1e\right).
\]

Finite summation by parts and the preceding first-difference formula give

\[
 S_M=A_M b(p+M)+\sum_{e=2}^{n+1}q_eE_e(M).
\]

Indeed, substituting \(a_k=A_{k+1}-A_k\) and telescoping yields
\(S_M=A_M b(p+M)-\sum_{k<M}A_{k+1}\Delta b(p+k)\);
interchanging two finite sums gives the displayed expression.

If every e≤n+1 divides p+M, all g_e(p+M) vanish, hence b(p+M)=0. Therefore

\[
 \boxed{S_M=\sum_{e=2}^{n+1}q_eE_e(M).}
\]

This step removes a boundary term rather than estimating it separately.
The primitive and progression sums are not assumed positive or small.

## A certified common-period cutoff

Let \(B=\sum_e|q_e|\). The existing atom bound gives
\(\|\operatorname{tail}_K u\|^2\le B^2/(K+1)\).
Cauchy--Schwarz and contraction of the other tail therefore give

\[
 |\kappa_{n,d}-S_M|^2
 \le\frac{B^2\|T_n\|^2}{n+M+1}.
\]

The existing complete canonical norm bound is
\(\|C_n\|^2<4n\) for n>0. Since \(T_n=1-C_n\),
\(\|T_n\|^2\le2\|1\|^2+2\|C_n\|^2\le8n+2\).
Set

\[
 M_0=\lceil (n+1)B^2(8n+2)\rceil,\qquad
 L=(n+1)!,\qquad
 M=L(M_0+n+1)-(n+1).
\]

Since L≥1, M≥M_0≥0. Also p+M=L(M_0+p), so every legal conductor divides
the terminal physical site. Finally
\((n+1)B^2(8n+2)\le M_0\le M\le n+M+1\), whence

\[
 \boxed{\left|\kappa_{n,d}-\sum_e q_eE_e(M)\right|^2
          \le\frac1{n+1}.}
\]

The factorial cutoff is deliberately crude. This is a mathematical finite
accuracy certificate, not an efficiency or floating-point certification claim.
The absolute mass is used only to certify the omitted tail; it is never used
to replace the signed interior pairing by a sum of absolute values.

## Exact remaining RH obligation

The existing correction sequence converges unconditionally to
\(\ell_d=\operatorname{mobiusDifferenceCLM}(d)(\operatorname{limitResidual})\).
The error certificate implies that the pure signed progression values
converge to this same, possibly nonzero, limit.

Consequently it suffices to show, separately for every fixed d>1,

\[
 \forall\varepsilon>0\ \forall N\ \exists n\ge N:
 \left|\sum_{e=2}^{n+1}q_{n,d,e}E_{n,e}(M_{n,d})\right|<\varepsilon.
\]

If \(\ell_d\ne0\), convergence would force these absolute values to exceed
\(|\ell_d|/2\) eventually, contradicting cofinal smallness. Hence all
\(\ell_d=0\), and the repository's correction-limit implication gives RH.
This is a **conditional research reduction**. The displayed signed arithmetic
cancellation remains **Open**; no provider has been found or assumed.

## Formalized modules

- `Analysis/SignedAbel.lean`: first and second finite signed Abel identities.
- `RH/ResidueCorrectionAbel.lean`: actual physical-shell specialization.
- `RH/ResidueCorrectionAbelLimits.lean`: complete truncation bounds, arbitrary
  later cutoffs, explicit linear majorant, factorial cutoff and limit transfer.
  It also exports the manuscript names `correction_sub_abel_sq_le`,
  `correction_sub_abelCutoff_sq_le`, `abelCutoff_value_tendsto`, and
  `riemannHypothesis_of_cofinal_abelCutoff`, with their original hypotheses.
- `RH/ResidueDualDifferences.lean`: actual dual synthesis, exact divisor jumps,
  signed reciprocal-charge bound and common-multiple vanishing.
- `RH/ResidueCorrectionDivisorAbel.lean`: pure progression pairing at the
  certified cutoff and its conditional RH endpoint.
- `RH/SmoothWeilMatrix.lean`: reconstructed finite actual-zero Weil identities,
  Hermitian symmetry, explicitly RH-conditional positivity and completed-Nyman
  nullity. The null family supplies no coercive comparison with the Pareto Gram.

Wolfram checked the proposed difference and CRT-energy algebra symbolically
at conductor bound 8; this was only a finite sanity check. No Wolfram output
is used as a Lean premise. The optional full-period CRT energy formulas are
not included as Lean theorems in this patch.
