# The sharp uniform prefactor for the reflected Montgomery pair

Let \(H_h f(x)=(f(x+h)+f(x-h))/2-f(x)\), \(w(d)=4/(4+d^2)\), and
\[
Q_d(x)=\frac4{4-(x+id)^2},\qquad
F_{u,d}(x)=e^{ux}Q_d(x).
\]
For \(|a|,|b|\le 1/2\) and all real \(u,d\),
\[
\boxed{\ |H_a H_b F_{u,d}(0)|
 \le \frac8{15}\,a^2b^2(1+|u|)^4 e^{|u|(|a|+|b|)}w(d).\ }
\]
The prefactor \(8/15\) is optimal for this exact combination of factors. The equality case has \(u=d=0\) and \(a=b=1/2\).

## Control of all five derivatives

Write \(Q_d(x)=(2-x-id)^{-1}+(2+x+id)^{-1}\). Its \(k\)-th derivative is a signed sum of the two reciprocal powers of order \(k+1\), multiplied by \(k!\). Set \(D=d^2\), \(r_-=2-|x|\), \(r_+=2+|x|\) on \(|x|\le1\). For \(k=1,2,3\) the triangle inequality and \((4+D)/(r^2+D)\le\max(4/r^2,1)\) give
\[
\frac{|Q_d^{(k)}(x)|}{w(d)}
\le k!\left(r_-^{-k-1}+\tfrac14 r_+^{-(k-1)}\right).
\]
After multiplying by \(r_-^5\), each summand on the right is at most \(k!\,2^{4-k}\), since \(1\le r_-\le2\le r_+\). Their sums are at most \(16,16,24\), respectively. As
\[
Q_0^{(4)}(x)=24\big[(2-x)^{-5}+(2+x)^{-5}\big],
\]
these three bounds imply \(|Q_d^{(k)}(x)|\le w(d)Q_0^{(4)}(x)\).

For \(k=4\), the squared ordinate enters each normalized pole modulus through \(g_r(D)=(4+D)/[4(r^2+D)^{5/2}]\). Its derivative is
\[
g_r'(D)=\frac{2r^2-20-3D}{8(r^2+D)^{7/2}}<0
\]
because \(r\le3\). Evaluating both summands at \(D=0\) proves the same comparison for \(k=4\). For \(k=0\), the real part of \(4-(x+id)^2\) gives \(|Q_d(x)|/w(d)\le4/3\), while the even convex function \(Q_0^{(4)}\) has minimum \(Q_0^{(4)}(0)=3/2\). All statements include both endpoints \(x=\pm1\).

Leibniz's formula now gives one pointwise majorant for every term of the fourth derivative on \(|x|\le |a|+|b|\),
\[
|F_{u,d}^{(4)}(x)|\le
 (1+|u|)^4 e^{|u|(|a|+|b|)} w(d)\,Q_0^{(4)}(x).
\]

## Central-difference comparison and the extremizer

For nonzero \(h\), let \(X_h\) have density \((|h|-|t|)/h^2\) on \([-|h|,|h|]\). Integrating the second derivative twice gives the identity \(H_h f(x)=h^2\,\mathbb E f''(x+X_h)/2\). Independent \(X_a,X_b\) therefore give
\[
H_aH_b f(0)=\tfrac14 a^2 b^2\,\mathbb E f^{(4)}(X_a+X_b).
\]
When either displacement vanishes both central differences vanish. The pointwise comparison gives an upper bound by \(H_aH_b Q_0(0)\) times \((1+|u|)^4 e^{|u|(|a|+|b|)}w(d)\).

Let \(Z,Z'\) be independent width-one triangular variables. For fixed \(b\), \(a\mapsto\mathbb E Q_0^{(4)}(aZ+bZ')\) is convex because \(Q_0^{(4)}\) is convex on \([-1,1]\), and even because \(Z\) is symmetric. It is nondecreasing for \(0\le a\le1/2\). The same argument applies to \(b\), so the maximum is attained at both halfwidths \(1/2\). At those displacements the exact mixed difference is
\[
H_{1/2}H_{1/2}Q_0(0)=\tfrac12Q_0(1)-2Q_0(1/2)+\tfrac32Q_0(0)
 =\tfrac23-\tfrac{32}{15}+\tfrac32=\tfrac1{30}.
\]
Dividing by \((1/2)^4\) gives \(8/15\). Substitution of this same pair with \(u=d=0\) attains the claimed upper bound.

## A polynomial certificate for the comparison model

The upper bound \(H_aH_bQ_0(0)\le(8/15)a^2b^2\) also has an algebraic certificate. Put \(A=a^2,\ B=b^2,\ U=1-4A,\ V=1-4B\), and
\[
N=(A-B)^2-12(A+B)+96,\quad
\Delta=(4-a^2)(4-b^2)(4-(a+b)^2)(4-(a-b)^2)>0.
\]
Direct simplification gives \(H_aH_bQ_0(0)=a^2b^2N/\Delta\). The identity
\[
32(8\Delta-15N)=UV(U-V)^2+15(U^3+V^3)+17UV(U+V)
 +675(U^2+V^2)+762UV+8640(U+V)
\]
shows \(N/\Delta\le8/15\) throughout the admissible square.

The argument yields the optimal displacement-dependent bound as well. For each fixed nonzero \(a,b\) in the admissible square, the smallest constant multiplying \(a^2b^2(1+|u|)^4e^{|u|(|a|+|b|)}w(d)\) for all \(u,d\) is \(N/\Delta\). Indeed the derivative comparison already bounds the entire left side by \(H_aH_bQ_0(0)\) times the frequency and ordinate factors, and \(u=d=0\) realizes equality for this particular pair. The continuous extension of \(N/\Delta\) tends to \(96/256=3/8\) when both displacements tend to zero. On a restricted rectangle \(|a|\le A,\ |b|\le B\) with positive \(A,B\le1/2\), monotonicity under the triangular averaging above gives the best common constant \(N(A,B)/\Delta(A,B)\).

For a symmetric restriction \(|a|,|b|\le r\le1/2\), the exact worst-pair coefficient has the simpler form
\[
  \frac{3}{2(4-r^2)(1-r^2)}
  =\frac38+\frac{15}{32}r^2+O(r^4).
\]
For \(r>0\), the extremizer is again \(u=d=0\) with \(|a|=|b|=r\). At \(r=0\) both differences vanish. The displayed expression extends continuously to the transverse origin.

There is a simpler sharp approximation suitable for sums over zeta zeros. The optimal affine majorant whose intercept is the limiting value is
\[
\frac N\Delta\le \frac38+\frac{19}{60}(a^2+b^2).
\]
Indeed \(P(A,B)=N/\Delta\) has the absolutely convergent series
\[
P(A,B)=\sum_{i,j\ge0}\binom{2i+2j+4}{2i+2}\frac{A^iB^j}{4^{i+j+2}} .
\]
For \(i+j>0\), \(A^iB^j\le 4^{1-i-j}(iA+jB)/(i+j)\) on the admissible square. Summing and using the symmetry of the coefficients gives the affine interpolation from \(3/8\) at the origin to \(8/15\) at \((1/4,1/4)\). The corner equality also forces its slope to be at least \(19/60\). For a finite family let \(D\) bound every Cauchy row sum, and put \(E_j=\sum_i |a_i|^j\exp(2|u||a_i|)\). The nonnegative symmetric Cauchy matrix has \(\ell^2\) norm at most \(D\). Applied first to the vector \(a_i^2e^{|u||a_i|}\), then bilinearly to that vector and \(a_i^4e^{|u||a_i|}\), the affine bound gives the unnormalized Gram majorant
\[
 D(1+|u|)^4\left(\tfrac38 E_4+\tfrac{19}{30}\sqrt{E_4 E_8}\right).
\]
If the normalized moments have Selberg orders \(L^{-3}\) and \(L^{-7}\), this correction has order \(L^{-5}\) before the common frequency and row-mass factors. These statements concern the arithmetic prefactor within the majorant.

This is a bound for an individual reflected pair. The extremal parameters are admissible for the kernel inequality. A zero-density or ordinate-sum estimate for the actual zeta zeros has further restrictions, so this extremizer alone supplies no equality case for the full horizontal defect. The earlier contour argument gives \(1536e\) in this normalization. The optimal constant improves that bound by the factor \(2880e\); it affects the prefactor and leaves the quartic powers and frequency ranges as stated.
