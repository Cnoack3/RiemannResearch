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

This is a bound for an individual reflected pair. The extremal parameters are admissible for the kernel inequality. A zero-density or ordinate-sum estimate for the actual zeta zeros has further restrictions, so this extremizer alone supplies no equality case for the full horizontal defect. The earlier contour argument gives \(1536e\) in this normalization. The optimal constant improves that bound by the factor \(2880e\); it affects the prefactor and leaves the quartic powers and frequency ranges as stated.
