# Canonical one-conductor tail obstruction — 9 September 2026

This note records an attempted Lean-assisted continuation toward RH. It does not prove RH.
The standard countability of zeta zeros is bookkeeping, not the analytic advance.

## Formal scope

The accompanying Lean development proves:

- Countability of the actual open-strip zeta zeros and existence of one smooth compact polar-annihilating detector for that set.
- Exact transform cancellation at any zero of the entire conductor-zeta multiplier.
- The actual canonical-tail bound
  \[
  E(\tau_M)\ge e^a(M+1)|F(s_0)|^2
  \]
  when \(P_n(s_0)=0\), \(s_0\ne1\), and \(F\) is the head transform.
  Nonzero \(F(s_0)\) therefore rules out subpower energy.
- For each \(n\ge2\), existence of a genuine compact potential whose head detects every actual nontrivial zeta zero and whose canonical tails obey a strictly positive linear lower bound.
- The exact ordinary-\(L^2\) translation identity and conductor-operator bounds below.

No RH assumption is used in these obstruction results. The formal theorem with a nonzero artificial-zero signature does not apply to every detector merely because it detects the zeta zeros.

## Exact energy retained by conductor cancellation

Write \(T_tu(y)=u(y-t)\), \(E(u)=\int_{\mathbb R}|u(y)|^2\,dy\).
For real \(A,B\), translation invariance gives
\[
E(Au-BT_tu)=(A-B)^2E(u)+AB\,E(u-T_tu).
\]
All covariance is retained in the difference energy. This is an equality before any positivity consequence.

The spatial conductor operator is
\[
L_nu=\frac1n u-\frac1{\sqrt n}T_{\log n}u.
\]
Consequently
\[
E(L_nu)=
\left(\frac1n-\frac1{\sqrt n}\right)^2E(u)
+\frac1{n\sqrt n}E(u-T_{\log n}u).
\]
Its norm is bounded below by
\[
\|L_nu\|_2\ge
\left(\frac1{\sqrt n}-\frac1n\right)\|u\|_2,
\qquad n\ge2.
\]
Applying this fixed operator to a tail cannot turn a linear energy lower bound into subpower energy. The Lean identity concerns the literal spatial operator; a claim about commutation with the whole canonical construction needs its own formal assembly.

## Stronger finite-jet argument — written proof, not yet formalized

The following proof has been checked algebraically in this session, but the general derivative-signature and projection steps have NOT been checked by Lean. They are the next formalization target, not an established Lean theorem.

Fix \(n\ge2\), a compact smooth potential \(v\), and the nonzero entire transform
\[
F(s)=\mathcal L_c[(D^2-\tfrac14)v](s).
\]
Assume explicitly that \(F\) is not identically zero. For a nonzero continuous compact head this follows from Fourier uniqueness; the explicit detector construction also provides nonzero transform witnesses.

Let \(b_n(k)\) denote the existing conductor-inverse coefficients and define the finite entire function
\[
B_M(s)=\sum_{k=1}^M\frac{b_n(k)}{\sqrt k}
  e^{-(s-1/2)\log k}
=\sum_{k=1}^M b_n(k)e^{-s\log k}.
\]
Finite integral linearity and the exact translation formula give
\(\mathcal L_c[v_M]=B_M\mathcal L_c[v]\).
The existing full arithmetic transform formula then gives exactly
\[
T_M(s):=\mathcal L_c[\tau_M](s)
=\bigl(C_n(s)B_M(s)-1\bigr)F(s),
\]
where \(C_n\) is the entire removable continuation of
\(\zeta(s)P_n(s)\) and \(P_n(s)=1/n-e^{-s\log n}\).

Choose an artificial zero
\[
s_0=1+\frac{2\pi i}{\log n}.
\]
It is distinct from \(1\), has real part \(1\), and satisfies \(C_n(s_0)=0\).
Since \(F\) is entire and not identically zero, it has a finite vanishing order \(r\ge0\) at \(s_0\):
\[
F^{(j)}(s_0)=0\ (j<r),\qquad F^{(r)}(s_0)\ne0.
\]
Leibniz's formula now yields, for every \(M\),
\[
T_M^{(j)}(s_0)=0\ (j<r),\qquad
T_M^{(r)}(s_0)=-F^{(r)}(s_0).
\]
The finite inverse and all its \(M\)-dependent derivatives drop out because they multiply lower derivatives of \(F\).

Put \(Y=a+\log(M+1)\), where \(v\) vanishes below \(a\). The actual tail has support in \([Y,\infty)\) and smooth superexponential decay. Differentiation under the Laplace integral is therefore justified for each finite derivative. The zero lower moments imply
\[
\int_Y^\infty (y-Y)^r\tau_M(y)e^{-(s_0-1/2)y}\,dy
=(-1)^{r+1}F^{(r)}(s_0)=:d.
\]
Let
\[
k_{r,Y}(y)=\mathbf1_{[Y,\infty)}(y)(y-Y)^r
 e^{-\overline{(s_0-1/2)}y}.
\]
Then
\[
E(k_{r,Y})=e^{-Y}\int_0^\infty t^{2r}e^{-t}\,dt
=e^{-Y}(2r)!.
\]
Using the pairing \(\int u\overline{k}\), the exact orthogonal-projection identity is
\[
E(\tau_M)=
\frac{e^Y|F^{(r)}(s_0)|^2}{(2r)!}
+
E\!\left(
\tau_M-\frac{e^Yd}{(2r)!}k_{r,Y}
\right).
\]
In particular,
\[
E(\tau_M)\ge
\frac{e^a|F^{(r)}(s_0)|^2}{(2r)!}(M+1).
\]
The coefficient is strictly positive and independent of \(M\).

Thus the written argument rules out subpower growth for the canonical multiplicative family with one fixed nonzero entire head transform, even when the head vanishes at every artificial conductor zero. Vanishing merely changes the finite derivative order carrying the obstruction.

## Scope and research consequence

This argument concerns the canonical inverse-prefix construction with
\(T_M=(C_nB_M-1)F\).
It does not rule out independently chosen inverse potentials, heads depending on \(M\), varying conductors, or mixed-conductor constructions.

A fixed compact smoothing, if followed by the same canonical construction and if its resulting head is nonzero, still falls under the finite-jet argument. In particular, the interval-convolution multiplier \(P_n(s)/(s-1)\) does not resolve the issue: a zero value can become a fixed nonzero derivative signature.

Conductors \(2\) and \(3\) have no common artificial zero away from the removable point; that exact fact is already formalized in ArithmeticConductorCommonZeros. It explains why a mixed construction avoids this specific common-zero obstruction. It does not provide the required mixed-tail support, regularity, or subpower/variance estimate. Those remain genuine open obligations. No signed prime-power, boundary, or mixed covariance term may be omitted to assert them.

## Provenance and remaining Lean work

Source: continuation of the user-provided Nyman–Weil arithmetic-tail program, the user's standard countability observation, and arguments developed in this session. No novelty claim is made.

Existing formal providers used in the written proof:
NymanTailTransform, NymanActualTailEnergy, BilateralLaplaceTranslation, ArithmeticConductorCommonZeros, ZetaConductorRegularization.

Remaining formal work for the universal finite-jet conclusion:

1. Package the finite inverse transform factor \(B_M\) and exact multiplicative tail identity.
2. Prove finite-order derivative signatures at an artificial conductor zero.
3. Supply differentiated integral identities and the shifted-moment kernel norm.
4. Verify the exact projection remainder, then specialize to the actual canonical tails.
