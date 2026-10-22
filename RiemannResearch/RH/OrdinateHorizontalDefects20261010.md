# Ordinate harmonic analysis: exact horizontal defects and Lean continuation

Research continuation of the supplied `Ordinate_Harmonic_Theory_20261010(1).md`, 10 October 2026.

The main formal result is an unconditional convergence theorem and exact equivalence
\[
E_4=\sum_{\rho\ \mathrm{nontrivial}}m_\rho
\frac{(\Re\rho-1/2)^2}{(1+(\Im\rho)^2)^2},\qquad
E_4=0\iff\mathrm{RH}.
\]
The sum is over all actual zeros of Mathlib's `riemannZeta`, with analytic multiplicities. It includes both ordinate signs and imposes no height restriction. This verifies the reduction, not the unresolved assertion that its left side is zero.

## Formal results and exact scope

| Module | Verified result | Assumptions and boundary |
|---|---|---|
| `Analysis/ActualZeroHorizontalEnergy.lean` | Actual all-zero energy converges, is nonnegative, and is zero iff Mathlib RH; RH fails iff it is strictly positive | No domain-specific hypothesis; uses existing proved actual-zero summability and critical-strip bridge. The assertion `E_4=0` remains Open. |
| `Analysis/ResolventHorizontalDefect.lean` | Exact reflected resolvent identity, positivity/equality detection, constants 1/5 and 9 | Generic real variables. Sign condition is explicit; quantitative bounds require squared ordinate at least 1 and displacement at most 1/2. |
| `Analysis/DeterminantHorizontalDefect.lean` | Exact polynomial certificate, positive factor comparison, equality detection, and a complete maximum-ratio square remainder | Squared ordinate positive; nonzero real probe for equality detection. No lower-height assumption. |
| `Analysis/ActualZeroHorizontalDefect.lean` | Exact actual-cutoff resolvent gap after reflection; quantitative cutoff bounds; nonnegative determinant gap and cofinal detection of every positive-height zero | Actual analytic multiplicities. Height premise remains visible only for the resolvent bounds. Cofinal positive-height detection is not silently identified with a full RH criterion. |
| `Analysis/ConjugatePairHankel.lean` | Exact determinant `-4*normSq(v)*im(z)^2`, negative quadratic witnesses, Gaussian specialization, and an entrywise tail budget | Isolated nonreal conjugate pair, nonzero weight; no assertion that the infinite full-zero Hankel form has this determinant. |

There are 37 public supporting theorem declarations across these five modules. This count is not a count of independent zeta-distribution discoveries.

## Server verification record

- Generic resolvent, determinant, and conjugate-pair bundle: server job `job_ybt9TpDrpOVPAhva2Z2_ZS261XPC88MZ`, exit code 0, `verified=true`.
- Final actual-cutoff and all-zero energy bundle: server job `job_xB9pfBSLHvCFL_byfhyyt1jqM5C9lybW`, exit code 0, `verified=true`.
- Printed foundation reports for the energy/RH equivalence, energy summability, cofinal determinant criterion, exact cutoff resolvent identity, and quantitative cutoff bounds contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The final bundle replayed a pre-existing copyright-header style warning in `RiemannHypothesisStrip.lean`. New module candidates introduce no warnings, placeholders, local axioms, or unsafe declarations.
- Final project acceptance and publication are gated by the introducing server checkpoint. A snippet success alone is not a full repository rebuild or a publication record.

## What the exact formulas improve

For `delta = Re(rho)-1/2` and `y = gamma^2`, the kernel-verified identity is
\[
\frac{2x}{x^2+y}-\frac{x-\delta}{(x-\delta)^2+y}
-\frac{x+\delta}{(x+\delta)^2+y}
=\frac{2x\delta^2(3y+\delta^2-x^2)}
{(x^2+y)((x-\delta)^2+y)((x+\delta)^2+y)}.
\]
It identifies the scalar gap in the supplied report as an exact positive weighted displacement energy in its sign range. It preserves all horizontal partners, signs, squares, and denominators.

The determinant alternative has no height-dependent sign restriction. With
\[
A=x^2+y,\quad q=\delta^2,\quad D=((x-\delta)^2+y)((x+\delta)^2+y),
\]
Lean proves
\[
A^2(y+q)^2-y^2D=x^2q[2y(3y+x^2)+q(2y+x^2)].
\]
The right side is positive exactly when the probe and horizontal displacement are nonzero. Lean also retains the exact maximum-ratio remainder
\[
(4y+q)D-4yA^2=q(x^2-3y-q)^2.
\]

## Analytical continuation and remaining RH obligations

The appendix gives complete paper proofs of the Gaussian-to-resolvent Laplace bridge, normalized centered Hadamard determinant comparison, positive logarithmic defect, and endpoint-preserving tail estimates. These infinite product/integral identities have not been assembled into Lean declarations in this continuation.

For any fixed nonzero real x, the paper deduction is
\[
\frac{\xi(1/2+x)}{\xi(1/2)}\le
P(x):=\prod_{\gamma_\rho>0}(1+x^2/\gamma_\rho^2)^{m_\rho},
\]
with equality iff RH. The opposite inequality is the Open arithmetic target. All upper horizontal partners are included; the product of symmetrized pair factors over all upper zeros equals the square of the normalized xi product, as detailed in the appendix.

Open obligations are: (1) proving the actual energy `E_4` vanishes; (2) assembling the infinite completed-zeta product/resolvent identification in Lean; (3) proving the reverse arithmetic comparison; and (4) controlling the complete tail when transferring isolated-pair negative witnesses to full Gaussian Hankel forms. None is discharged by unconditional ordinate-only spectral positivity or finitely many narrow-width tests.

The most concrete next formalization is the centered Hadamard product bridge with the exact positive per-zero logarithmic defect. Its arithmetic reverse comparison would force every horizontal displacement to vanish. Publication priority of these derived formulations is unconfirmed.

Primary literature: Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, Section 2.2 equation (2.6) and Theorems 1.2/1.8, <https://arxiv.org/html/2206.03682v4>; Ford–Zaharescu, Lemma 2, <https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>. These support the classical analytical inputs, not a claim that the arithmetic target has been proved. Wolfram was used only for small rational/polynomial checks; kernel verification supplies the formal algebra.

# Appendix: complete audited paper continuation

# Exact horizontal-displacement defects for zeta ordinates

Research continuation of `Ordinate_Harmonic_Theory_20261010(1).md`, 10 October 2026.

This paper continuation gives exact identities and complete analytical proofs. The finite rational and polynomial statements are suitable for Lean; no Lean verification is claimed by this file. It does not establish the arithmetic reverse inequalities that would prove RH, and it makes no claim of publication priority.

## 1. Conventions and classical inputs

Write each nontrivial zero as
\[
\rho=\tfrac12+\delta_\rho+i\gamma_\rho,
\qquad w_\rho=\rho-\tfrac12,
\]
and let \(m_\rho\) be its analytic multiplicity. In every positive-height sum below, distinct zeros with \(\gamma_\rho>0\) are indexed and multiplied by \(m_\rho\). Equivalently, one may index the zero multiset directly. A hypothetical horizontal pair at a common ordinate is counted twice. It is never collapsed to one simple zero.

Functional equation and complex conjugation preserve multiplicity under
\[
w\mapsto-w,\qquad w\mapsto\overline w,
\qquad \delta+i\gamma\mapsto-\delta+i\gamma.
\]
There are no nontrivial zeros on the real axis. For instance, the alternating Dirichlet series shows \(\zeta(s)<0\) for real \(0<s<1\). The critical strip gives \(|\delta|<1/2\). The Riemann–von Mangoldt bound \(N(T)=O(T\log(T+2))\) implies
\[
\sum_{\gamma_\rho>0}\frac{m_\rho}{\gamma_\rho^2}<\infty.
\tag{1.1}
\]
The bounded initial-height portion is finite, and there is a strictly positive least ordinate.

We use the standard completed function
\[
\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
\tag{1.2}
\]
It is entire of order one, satisfies \(\xi(s)=\xi(1-s)\), and its zeros are exactly the nontrivial zeros with their multiplicities. In particular \(\xi(1/2)>0\).

The Hadamard logarithmic derivative and its standard zero pairing are stated explicitly in Grigutis–Turčinskas, equations (3)–(4), <https://arxiv.org/html/2509.18963v1>. Ford–Zaharescu, <https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>, defines the multiplicity convention on page 2, gives the counting formula (1.6), and states the Selberg density estimate in Lemma 2 on page 7. The deductions below use these classical inputs; no new zero-density theorem is asserted.

## 2. An exact rational defect, with all horizontal partners

Fix \(x>0\). For one upper zero put
\[
y=\gamma^2>0,\quad q=\delta^2\ge0,\quad
A=x^2+y,
\]
\[
D=((x-\delta)^2+y)((x+\delta)^2+y)
  =(x^2+y+q)^2-4x^2q>0.
\tag{2.1}
\]
The elementary identity is
\[
\boxed{
\frac{2x}{x^2+y}
-\frac{x-\delta}{(x-\delta)^2+y}
-\frac{x+\delta}{(x+\delta)^2+y}
=\frac{2xq(3y+q-x^2)}{AD}.}
\tag{2.2}
\]
It follows by bringing the three fractions to the common positive denominator \(AD\). All squares are retained. Under \(x^2<3y\), the right side is nonnegative and vanishes exactly when \(\delta=0\). The weaker non-strict condition \(x^2\le3y\) also suffices for the same equality characterization, since a nonzero \(q\) then makes \(3y+q-x^2\) strictly positive.

Identity (2.2) is the contribution **per indexed upper zero after horizontal averaging**. For an off-line upper horizontal pair \(\delta,-\delta\), the pair's total contribution is twice the displayed expression. A critical upper zero is counted once and its defect is zero.

Define
\[
B(x)=\sum_{\gamma_\rho>0}m_\rho
       \frac{2x}{x^2+\gamma_\rho^2}.
\tag{2.3}
\]
Centered Hadamard factorization, or the paired logarithmic derivative, gives for real \(x>0\)
\[
\frac{\xi'}{\xi}(\tfrac12+x)
=\sum_{\gamma_\rho>0}m_\rho
  \frac{2(x-\delta_\rho)}{(x-\delta_\rho)^2+\gamma_\rho^2}.
\tag{2.4}
\]
All real summands are absolutely summable: for fixed \(x\), their absolute values are \(O_x(\gamma^{-2})\). The real point \(1/2+x\) is not a zero, including when it lies in the critical strip. Averaging (2.4) under the multiplicity-preserving upper horizontal reflection, then subtracting from (2.3), proves
\[
\boxed{
\mathcal D(x):=B(x)-\frac{\xi'}{\xi}(\tfrac12+x)
=\sum_{\gamma_\rho>0}m_\rho
\frac{2x\delta_\rho^2
 (3\gamma_\rho^2+\delta_\rho^2-x^2)}
 {(x^2+\gamma_\rho^2)
 ((x-\delta_\rho)^2+\gamma_\rho^2)
 ((x+\delta_\rho)^2+\gamma_\rho^2)}.}
\tag{2.5}
\]
The defect series has tail \(O_x(\delta_\rho^2\gamma_\rho^{-4})\), not merely \(O_x(\gamma_\rho^{-2})\). Therefore it is absolutely convergent and agrees with the difference of the full, untruncated sums.

If \(x^2\le3\gamma_\rho^2\) for every upper zero, then
\[
\mathcal D(x)\ge0,
\qquad \mathcal D(x)=0\iff\mathrm{RH}.
\tag{2.6}
\]
The converse is exact: one off-line upper zero has positive multiplicity and contributes a strictly positive summand; every other summand is nonnegative. No simplicity hypothesis is used.

## 3. The scalar target at \(s=2\) is an exact weighted displacement energy

Set \(x=3/2\). The classical lowest-zero ordinate exceeds 1; the much stronger familiar value is approximately 14.13. Only \(\gamma^2\ge1\) is used in this section. Formula (1.2), \(\psi(1)=-\gamma_E\), and the absolutely convergent Euler logarithmic derivative give
\[
\frac{\xi'}{\xi}(2)=
\frac32-\frac{\log\pi+\gamma_E}{2}
-\sum_{n\ge2}\frac{\Lambda(n)}{n^2}.
\tag{3.1}
\]
Thus the scalar target already identified in the attachment has the exact gap
\[
\begin{aligned}
\mathcal D(3/2)
={}&3\sum_{\gamma_\rho>0}\frac{m_\rho}{\gamma_\rho^2+9/4}
-\left[\frac32-\frac{\log\pi+\gamma_E}{2}
-\sum_{n\ge2}\frac{\Lambda(n)}{n^2}\right]\\
={}&\sum_{\gamma_\rho>0}m_\rho
\frac{3\delta_\rho^2(3\gamma_\rho^2+\delta_\rho^2-9/4)}
 {(\gamma_\rho^2+9/4)
 ((3/2-\delta_\rho)^2+\gamma_\rho^2)
 ((3/2+\delta_\rho)^2+\gamma_\rho^2)}.
\end{aligned}
\tag{3.2}
\]
It is unconditionally nonnegative. Proving the reverse inequality \(\mathcal D(3/2)\le0\) would prove RH. The new identity identifies exactly what that reverse inequality must eliminate.

There is a simple quantitative comparison. For \(y\ge1\) and \(0\le q\le1/4\), define the summand without multiplicity
\[
d(q,y)=\frac{3q(3y+q-9/4)}{(y+9/4)D}.
\]
Then
\[
\boxed{\frac15\frac{q}{(1+y)^2}
\le d(q,y)\le9\frac{q}{(1+y)^2}.}
\tag{3.3}
\]
For the upper bound, \(|\delta|\le1/2\) gives \((3/2\pm\delta)^2\ge1\), hence \(D\ge(y+1)^2\). Also \(3y+q-9/4\le3(y+9/4)\).

For the lower bound, use
\[
D\le(y+5/2)^2\le\frac{49}{16}(y+1)^2,
\quad y+9/4\le\frac{13}{8}(y+1),
\]
\[
3y+q-9/4\ge\frac38(y+1).
\]
The resulting lower constant is \(144/637>1/5\). All denominator bounds are positive, so multiplication and division preserve the inequalities.

Consequently, with
\[
\mathcal E=\sum_{\gamma_\rho>0}m_\rho
\frac{\delta_\rho^2}{(1+\gamma_\rho^2)^2},
\]
one has the unconditional two-sided estimate
\[
\boxed{\tfrac15\mathcal E\le\mathcal D(3/2)\le9\mathcal E.}
\tag{3.4}
\]
This is a weighted horizontal squared-displacement energy. It vanishes if and only if RH. The statement is quantitative but does not supply an independent upper bound tending to zero for the total energy.

For example, if \(\mathcal D(3/2)\le\varepsilon\), every individual upper zero obeys
\[
|\delta_\rho|\le(1+\gamma_\rho^2)
\sqrt{5\varepsilon/m_\rho}.
\tag{3.5}
\]
The deterioration with height is explicit.

## 4. An exact Laplace bridge from the Gaussian theory

Use exactly the attachment's signed full-zero heat traces
\[
H(a)=\sum_\rho m_\rho e^{-a\gamma_\rho^2},
\qquad R(a)=\sum_\rho m_\rho e^{a w_\rho^2},
\quad a>0.
\tag{4.1}
\]
Here \(H(a)=Z_a(0)\), while \(R(a)=S_a(0)\). For \(x>1/2\), termwise Laplace integration gives
\[
B(x)=x\int_0^\infty e^{-x^2a}H(a)\,da,
\]
\[
\frac{\xi'}{\xi}(\tfrac12+x)
=x\int_0^\infty e^{-x^2a}R(a)\,da.
\tag{4.2}
\]
Indeed, the second integral before pairing equals
\(x\sum_\rho m_\rho/(x^2-w_\rho^2)\). Pairing \(w\) and \(-w\) turns this into the centered Hadamard logarithmic derivative. Absolute Fubini is justified directly by
\[
\sum_\rho m_\rho\int_0^\infty
e^{-(x^2+\gamma_\rho^2-\delta_\rho^2)a}\,da
=\sum_\rho\frac{m_\rho}
 {x^2+\gamma_\rho^2-\delta_\rho^2}<\infty.
\]
All denominators are positive because \(x^2>1/4\) and \(|\delta|<1/2\); the tail is controlled by (1.1).

Subtracting yields the exact identity
\[
\boxed{\mathcal D(x)=x\int_0^\infty
e^{-x^2a}[H(a)-R(a)]\,da.}
\tag{4.3}
\]
The pointwise heat-trace mismatch is oscillatory. In particular,
\[
H(a)-R(a)=\sum_\rho m_\rho e^{-a\gamma_\rho^2}
\big[1-e^{a\delta_\rho^2}
\cos(2a\delta_\rho\gamma_\rho)\big],
\tag{4.4}
\]
where conjugation justifies the real expression. One must not assert that (4.4) is pointwise nonnegative. Its Laplace average is nonnegative in the range of (2.6), by the exact rational identity, with no absolute value substituted for the signed mismatch.

## 5. A determinant comparison needing no low-height hypothesis

There is a stronger structural comparison whose sign does not require \(x^2\le3\gamma^2\).

Define the positive ordinate determinant
\[
P(x)=\prod_{\gamma_\rho>0}
\left(1+\frac{x^2}{\gamma_\rho^2}\right)^{m_\rho},
\qquad x\in\mathbb R.
\tag{5.1}
\]
The product converges normally for complex \(x\), by (1.1), and defines an even entire function. Its value is strictly positive for real \(x\).

Centered genus-one Hadamard factorization gives
\[
\boxed{\frac{\xi(1/2+x)}{\xi(1/2)}
=C(x):=\prod_{\gamma_\rho>0}
\left(1-\frac{x^2}{w_\rho^2}\right)^{m_\rho}.}
\tag{5.2}
\]
To check normalization, apply the genus-one factorization to the even entire order-one function \(x\mapsto\xi(1/2+x)\). Pair each upper \(w\) with the lower \(-w\):
\[
E_1(x/w)E_1(-x/w)=1-x^2/w^2.
\]
The remaining exponential has degree at most one; evenness eliminates its linear coefficient. Evaluation at \(x=0\) supplies the constant \(\xi(1/2)\). The resulting product is normally convergent since \(\sum m_\rho/|w_\rho|^2<\infty\). This argument uses all actual zeros, including their horizontal coordinates.

For one upper horizontal pair, the actual normalized factor in (5.2) is
\[
\frac{D}{(y+q)^2},
\]
whereas the pair's ordinate-only factor in (5.1) is \(A^2/y^2\). The exact positive certificate is
\[
\boxed{A^2(y+q)^2-y^2D
=x^2q\,[2y(3y+x^2)+q(2y+x^2)].}
\tag{5.3}
\]
For real \(x\ne0\) and \(y>0\), the right side is nonnegative and vanishes exactly when \(\delta=0\). Unlike the derivative defect, this identity imposes no comparison between \(x\) and the ordinate.

Multiplying over horizontal orbits, with every orbit's multiplicity retained, proves the unconditional inequality
\[
\boxed{\frac{\xi(1/2+x)}{\xi(1/2)}\le P(x)
\quad(x\in\mathbb R).}
\tag{5.4}
\]
Both sides are positive. For **any one fixed real \(x\ne0\)**,
\[
\boxed{\mathrm{RH}\iff
P(x)=\frac{\xi(1/2+x)}{\xi(1/2)}
\iff P(x)\le\frac{\xi(1/2+x)}{\xi(1/2)}.}
\tag{5.5}
\]
The equality and the reverse comparison are the unresolved RH-strength targets. Formula (5.4) alone is unconditional and does not establish them.

## 6. Exact logarithmic energy and the factor of one half

For real \(x\ne0\), let
\[
\mathcal L(x)=\log P(x)
-\log\frac{\xi(1/2+x)}{\xi(1/2)}.
\]
Then
\[
\boxed{
\mathcal L(x)=\frac12\sum_{\gamma_\rho>0}m_\rho
\log\left(1+
\frac{x^2\delta_\rho^2
 [2\gamma_\rho^2(3\gamma_\rho^2+x^2)
 +\delta_\rho^2(2\gamma_\rho^2+x^2)]}
 {\gamma_\rho^4
 ((x-\delta_\rho)^2+\gamma_\rho^2)
 ((x+\delta_\rho)^2+\gamma_\rho^2)}
\right).}
\tag{6.1}
\]
The factor \(1/2\) is necessary. Summing over **all** upper zeros counts the two members of each off-line horizontal pair. Each member has the same \(D,y,q\). Their two half-log contributions give the log of the pair ratio. A critical upper zero likewise has actual squared factor \(D/(y+q)^2=(1+x^2/y)^2\), whose half-log is the log of the single actual factor.

More concretely, for a finite upper cutoff \(0<\gamma\le T\), closed under horizontal reflection, write the finite products in (5.1) and (5.2) as \(P_T,C_T\). Then
\[
\prod_{0<\gamma_\rho\le T}
\left[\frac{D_\rho}{(y_\rho+q_\rho)^2}\right]^{m_\rho}
=C_T(x)^2,
\]
\[
\prod_{0<\gamma_\rho\le T}
\left[\frac{A_\rho^2}{y_\rho^2}\right]^{m_\rho}
=P_T(x)^2.
\tag{6.2}
\]
These are squared products; they must not be identified with the unsquared completed-function ratio. Formula (6.1) follows by taking half the logarithm of their ratio and passing to the normally convergent infinite products.

Every logarithmic summand is nonnegative. Its fixed-\(x\) high-ordinate asymptotic, uniformly for \(|\delta|\le1/2\), is
\[
\frac12\log(1+\cdots)
=\frac{3x^2\delta^2}{\gamma^4}
\left[1+O_x(\gamma^{-2})\right].
\tag{6.3}
\]
Thus (6.1) converges absolutely and \(\mathcal L(x)=0\) exactly when RH holds. In the low-height range where the derivative comparison is positive,
\[
\mathcal L'(x)=\mathcal D(x).
\tag{6.4}
\]
The identity itself holds for all real \(x\), regardless of the sign of \(\mathcal D(x)\); it follows by normal differentiation of the products. A nonnegative logarithmic gap need not have a nonnegative derivative everywhere.
Here \(\mathcal L\) is extended evenly to negative \(x\) and \(\mathcal D\) oddly; both have value zero at \(x=0\), as their defining formulas show. These extensions are analytic near every real \(x\).

There is also an exact uniform bound retaining another square:
\[
\boxed{(4y+q)D-4y(x^2+y)^2
=q(x^2-3y-q)^2.}
\tag{6.5}
\]
Consequently the determinant ratio in (6.1) is at most
\((1+q/y)^2(1+q/(4y))\). Its per-upper-zero half-log is bounded by
\[
\log(1+q/y)+\tfrac12\log(1+q/(4y))
\le\tfrac98\frac{q}{y}.
\tag{6.6}
\]
For \(q>0\), the exact half-log maximum is the sum of the two logarithms in (6.6), attained exactly at \(x^2=3y+q\); the final linear bound \(9q/(8y)\) is a convenient larger bound. Bound (6.6) is summable by (1.1), independently of \(x\). Taking \(x\to+\infty\) in each summand of (6.1) and using dominated convergence therefore gives
\[
\boxed{\lim_{x\to+\infty}\mathcal L(x)
=\sum_{\gamma_\rho>0}m_\rho
\log\left(1+\frac{\delta_\rho^2}{\gamma_\rho^2}\right).}
\tag{6.7}
\]
This finite limit is nonnegative and is zero exactly when RH holds. Thus asymptotic agreement of logarithmic derivatives can still leave a positive multiplicative determinant defect. It does not by itself establish the normalized determinant equality.

## 7. Exact tails and the Selberg improvement

Put
\[
B_\delta(T)=\sum_{0<\gamma_\rho\le T}m_\rho\delta_\rho^2.
\]
The Selberg density estimate quoted in Ford–Zaharescu, Lemma 2, and horizontal reflection give the classical consequence
\[
B_\delta(T)\ll\frac{T}{\log T}\quad(T\ge T_0>1).
\tag{7.1}
\]
Indeed, layer-cake integration of \(\delta^2\) bounds the moment by a constant multiple of
\(T\log T\int_0^{1/2}s e^{-s\log T/4}\,ds\).
All counts include multiplicity.

Let \(\mathcal E_{>T}\) be the part of \(\mathcal E\) with \(\gamma>T\). The exact integration-by-parts identity is
\[
\boxed{
\mathcal E_{>T}=
-\frac{B_\delta(T)}{(1+T^2)^2}
+4\int_T^\infty
\frac{tB_\delta(t)}{(1+t^2)^3}\,dt.}
\tag{7.2}
\]
This retains the negative endpoint term; no truncation replaces the full tail by zero. If \(B_\delta(t)\le Ct/\log t\) for every \(t\ge T\), then
\[
0\le\mathcal E_{>T}\le
\frac{4C}{3T^3\log T}.
\tag{7.3}
\]
Here one uses \(t/(1+t^2)^3\le t^{-5}\) and \(\log t\ge\log T\). Applying (3.3) gives
\[
0\le\mathcal D(3/2)-\mathcal D_T(3/2)
\le\frac{12C}{T^3\log T},
\tag{7.4}
\]
where \(\mathcal D_T\) is the exact finite positive defect sum.

For the determinant energy, suppose \(T\ge\max(T_0,|x|)\), where \(T_0>1\), and retain the same bound \(B_\delta(t)\le Ct/\log t\) for every \(t\ge T\). For every upper zero in the tail, \(y\ge1\), \(x^2\le y\), \(q\le1/4\), and \(D\ge y^2\). Therefore the positive argument increment in (6.1) is at most
\[
\frac{35}{4}\frac{x^2q}{y^2}.
\]
Using \(\log(1+r)\le r\) and keeping the factor \(1/2\),
\[
0\le\mathcal L(x)-\mathcal L_T(x)
\le\frac{35}{8}x^2
\sum_{\gamma_\rho>T}\frac{m_\rho\delta_\rho^2}{\gamma_\rho^4}
\le\frac{35Cx^2}{6T^3\log T}.
\tag{7.5}
\]
For the last bound, the exact unsmoothed tail identity is
\[
\sum_{\gamma_\rho>T}\frac{m_\rho\delta_\rho^2}{\gamma_\rho^4}
=-\frac{B_\delta(T)}{T^4}
+4\int_T^\infty\frac{B_\delta(t)}{t^5}\,dt.
\tag{7.6}
\]
Without the density input, the strip bound and ordinary counting still give an \(O_x(\log T/T^3)\) tail. Formula (7.1) improves this to \(O_x(1/(T^3\log T))\). Both estimates control an actual nonnegative tail; neither proves that the tail is identically zero.

## 8. Concrete formalization boundaries and next target

The finite core consists of (2.1)–(2.2), defect positivity/equality characterization, the explicit bounds (3.3), the polynomial identity (5.3), finite-product positivity/comparison, and equality detection with positive multiplicities. These are exact algebraic claims suitable for kernel verification. Finite cutoff assembly can use the repository's actual-zero cutoff and multiplicity functions.

The analytical providers needed to connect finite products to (5.2), or finite resolvent sums to (3.1), are centered Hadamard factorization, normal convergence with differentiation, the completed-function logarithmic derivative, and the Euler logarithmic derivative. They must be formalized or supplied by independently verified existing theorems; the generic finite algebra does not by itself verify these full-zeta bridges.

The paper continuation supplies two scalar targets:

1. Prove the attachment's reverse resolvent inequality at \(s=2\), equivalently force the positive energy (3.2) to vanish.
2. For one real \(x\ne0\), prove the reverse normalized determinant comparison in (5.5). This formulation removes the low-height sign condition completely and retains all zeros in a positive exact logarithmic defect.

These targets are genuinely RH-strength. The continuation isolates the exact horizontal displacement that must be eliminated; it does not hide that elimination inside a positivity assumption. Ordinary unconditional ordinate-kernel positivity remains insufficient to establish either reverse comparison.

## 9. Small symbolic checks and provenance

Wolfram was used only for a small rational identity check and a polynomial expansion supporting possible explicit constants. `Together[2*x/(x^2+y)-(x-d)/((x-d)^2+y)-(x+d)/((x+d)^2+y)]` returned exactly the factored right side of (2.2). No numerical zero computations enter any proof.

Primary sources inspected:

- Grigutis–Turčinskas, *Note on the positivity of the real part of the log-derivative of the Riemann ξ-function near the critical line*, <https://arxiv.org/html/2509.18963v1>: completed-function definition, zero symmetries, paired Hadamard product and logarithmic derivative. The excerpt about the lowest ordinate is used only as the classical input \(\gamma^2\ge1\), not as a new verification result.
- Ford–Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, <https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>: multiplicities, zero counting, and the quoted Selberg density bound.

The determinant comparison is a deduction from classical centered Hadamard factorization and the explicit positive polynomial certificate. Publication priority has not been established.
