# Quantitative squarefree jump obstructions

Date: 16 October 2026.

Implementation: `RH/ZetaTwoCoordinateDual.lean` and `RH/QSquarefreeJumpDistance.lean`.

This continues the uploaded *Divisibility Indicators and Squarefree Residue Legality* handoff. The source for the initial obstruction and research target is the user-provided argument. The quantitative development uses the standard Hilbert-space decomposition along an explicitly constructed vector. It makes no novelty claim.

## Exact objects and identities

Write \(Q(n)=1/(\zeta(2)n^2)\), \(g_d(n)=(n\bmod d)/d\), and
\[
H_{\rm sf}=\overline{\operatorname{span}\{g_d:d\ge2,\ d\text{ squarefree}\}}^{L^2(Q)}.
\]
All physical sequences have value zero at the auxiliary coordinate zero; their values on the positive integers have the meanings above.

For \(a\ge2\), set
\[
\Lambda_a(x)=x(a^2)-x(a^2-1)-x(a)+x(a-1).
\]
Define the finite-support physical vector
\[
h_a(n)=\zeta(2)n^2\big(
 \mathbf1_{\{n=a^2\}}-\mathbf1_{\{n=a^2-1\}}
 -\mathbf1_{\{n=a\}}+\mathbf1_{\{n=a-1\}}\big).
\]
The four sites are distinct. The actual Hilbert encoding satisfies
\[
\langle h_a,x\rangle_Q=\Lambda_a(x),\qquad
D_a:=\|h_a\|_Q^2
=\zeta(2)\big(a^4+(a^2-1)^2+a^2+(a-1)^2\big)
=2\zeta(2)(a^4-a+1)>0.
\]
Thus \(\Lambda_a\) is a continuous linear functional with squared operator norm \(D_a\).
Every \(F\in H_{\rm sf}\) satisfies \(\langle h_a,F\rangle_Q=0\).

For every target \(x\) and every \(F\in H_{\rm sf}\), the complete exact equality is
\[
\boxed{\quad
\|x-F\|_Q^2
=\frac{\Lambda_a(x)^2}{D_a}
+\left\|x-F-\frac{\Lambda_a(x)}{D_a}h_a\right\|_Q^2 .
\quad}
\]
The remainder is retained in the theorem. Its nonnegativity gives a lower bound, with no asymptotic error term.

For \(m\ge3\), put \(a=m-1\). The existing checked arithmetic identity is \(\Lambda_{m-1}(I_m)=-1\), where \(I_m(n)=\mathbf1_{\{m\mid n\}}\). Consequently
\[
\boxed{\quad
\|I_m-F\|_Q^2
=\frac1{D_{m-1}}
+\left\|I_m-F+\frac{h_{m-1}}{D_{m-1}}\right\|_Q^2
\ge\frac1{2\zeta(2)((m-1)^4-(m-1)+1)} .
\quad}
\]
In particular, \(\|I_3-F\|_Q^2\ge1/(30\zeta(2))\).
This is a proved lower bound for distance to \(H_{\rm sf}\); equality with the actual distance to that subspace is not asserted. The displayed decomposition isolates one annihilator, and the corrected vector need not lie in \(H_{\rm sf}\).

## Signed combinations and the constant target

For any finite set \(S\) and real coefficients \(b_m\),
\[
\Lambda_a\!\left(\sum_{m\in S}b_m I_m\right)
=\sum_{m\in S}b_m\big(
 I_m(a^2)-I_m(a^2-1)-I_m(a)+I_m(a-1)\big).
\]
All signs are retained. Vanishing of each summand separately is not required, and cancellation between different indicators is allowed.

For \(m\ge3\) and real \(\alpha,\beta\), the strengthened membership classification is
\[
\alpha\,1+\beta I_m\in H_{\rm sf}
\iff
\big(\beta=0\ \text{and}\ \alpha\,1\in H_{\rm sf}\big).
\]
The constant cannot cancel the indicator's jump obstruction.

The constant passes every test: \(\Lambda_a(1)=0\). The exact error identity therefore gives zero extracted energy for this target. No positive obstruction to approximating \(1\), and no proof of its closure membership, follows from these rows.

## Research obligations

1. Combine several annihilators using their complete Gram matrix. Account for overlapping supports and all cross terms; adding independent one-row lower bounds without proving orthogonality is invalid.
2. Transfer the explicit vectors and functionals through the complete divisibility-coordinate isometry. A truncated divisibility expansion must still be checked for legality.
3. Classify signed finite indicator combinations satisfying every necessary radical-jump condition. The present signed-row identity is a certificate formula, not a complete classification.
4. To advance the RH approximation problem, supply an arithmetic norm, tail, or inverse-capacity estimate for actual squarefree legal approximants to \(1\). Local jump constraints alone have no proved sufficiency theorem.
5. The external RH-to-squarefree-density bridge is not supplied here. No unresolved domain-specific hypothesis is used in the quantitative obstruction theorems, and RH is not claimed.
