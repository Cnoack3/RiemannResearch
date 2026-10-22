# Appendix: the exact annular lattice correction has an entire Mellin continuation

**Status: paper proof, not Lean verified in this continuation.** The statements below concern only the deterministic lattice correction. They do not establish the missing quantitative bound for the actual prime signal, or prove RH.

## 1. Definitions and the exact correction

For real \(u\), write \(v_+=\max(v,0)\), and define

\[
W(u)=(1-u)_+^2-\frac74(1-2u)_+^2
       +\frac78(1-4u)_+^2-\frac18(1-8u)_+^2.
\]

The cancellations in this expression make \(W\) supported on \([1/8,1]\). Its mass is \(c=7/64\). For every real \(x>0\), put

\[
\delta(x)=\sum_{n\ge1}W(n/x)-cx.
\]

The sum is finite. In particular, \(\delta(x)=-cx\) for \(0<x\le1\), including \(x=1\), since \(W(1)=0\).

Let \(\{t\}\) denote the fractional part, and set

\[
B_3(t)=t^3-\frac32t^2+\frac12t,
\qquad
B_4(t)=t^4-2t^3+t^2-\frac1{30}.
\]

For \(t>0\), direct use of the finite sums of the first two powers gives

\[
\sum_{n\ge1}(1-n/t)_+^2
=\frac t3-\frac12+\frac1{6t}
 -\frac{B_3(\{t\})}{3t^2}.
\tag{1}
\]

This formula holds at integer \(t\) as well: the terminal summand is zero and \(B_3(0)=0\). Applying (1) at \(t=x,x/2,x/4,x/8\), the constant and reciprocal terms cancel, while the linear terms sum to \(cx\). Thus

\[
\boxed{\delta(x)=\frac{P(x)}{x^2}},
\qquad
P(x)=-\frac13\left[
B_3(\{x\})-7B_3(\{x/2\})
+14B_3(\{x/4\})-8B_3(\{x/8\})
\right].
\tag{2}
\]

All endpoints are retained in (2). The periodic extensions of \(B_3\) are continuous, since \(B_3(0)=B_3(1)=0\). Consequently \(P\) is continuous and \(8\)-periodic. Each constituent has mean zero over its period, so \(\int_0^8P(x)\,dx=0\). The function is not zero: on \([0,1]\), formula (2) simplifies to \(P(x)=-7x^3/64\).

## 2. A bounded periodic primitive

Define

\[
H(x)=-\frac1{12}\left[
B_4(\{x\})-14B_4(\{x/2\})
+56B_4(\{x/4\})-64B_4(\{x/8\})
\right].
\tag{3}
\]

The identity \(B_4'=4B_3\) gives \(H'=P\). This includes the joining points: \(B_4(0)=B_4(1)\), and its derivative is zero at both endpoints. Hence \(H\) is continuously differentiable and \(8\)-periodic. It also has mean zero, although boundedness alone suffices for the following estimate.

For \(0\le t\le1\),

\[
B_4(t)=t^2(1-t)^2-\frac1{30},
\qquad
0\le t^2(1-t)^2\le\frac1{16}.
\]

Therefore \(-1/30\le B_4(t)\le7/240\), and in particular \(|B_4(t)|\le1/30\). Formula (3) yields the explicit bound

\[
\boxed{|H(x)|\le\frac{1+14+56+64}{12\cdot30}=\frac38.}
\tag{4}
\]

No arithmetic cancellation involving primes is used here.

## 3. Ordinary improper Mellin convergence

Use \(x^{-s}=\exp(-s\log x)\) for \(x>0\). Define the transform by the **ordinary improper limit**

\[
D(s)=\lim_{R\to\infty}\int_1^R\delta(x)x^{-s-1}\,dx.
\tag{5}
\]

Let \(\sigma=\Re s>-3\). Using (2) and integrating by parts on \([X,R]\) gives the exact endpoint identity

\[
\int_X^R\delta(x)x^{-s-1}\,dx
=H(R)R^{-s-3}-H(X)X^{-s-3}
+(s+3)\int_X^R H(x)x^{-s-4}\,dx.
\tag{6}
\]

The upper endpoint tends to zero; the remaining integral is absolutely convergent. Thus, for every real \(X>0\),

\[
\int_X^\infty\delta(x)x^{-s-1}\,dx
=-H(X)X^{-s-3}
+(s+3)\int_X^\infty H(x)x^{-s-4}\,dx,
\tag{7}
\]

and

\[
\boxed{
\left|\int_X^\infty\delta(x)x^{-s-1}\,dx\right|
\le\frac38\left(1+\frac{|s+3|}{\sigma+3}\right)X^{-\sigma-3}.
}
\tag{8}
\]

This bound is uniform on every compact subset of \(\Re s>-3\). The finite-interval transforms are entire, so their locally uniform limit \(D\) is holomorphic on that half-plane.

Absolute convergence holds exactly for \(\Re s>-2\). Indeed, the absolute integrand is \(|P(x)|x^{-\sigma-3}\), and the continuous, nonzero periodic function \(|P|\) has a strictly positive mean. Comparison over successive periods proves divergence when \(\sigma\le-2\).

The ordinary improper convergence boundary \(-3\) is also sharp. Choose a fixed short interval \([u,v]\subset(0,1)\), so \(\int_u^vP(x)\,dx\ne0\). For any fixed \(s\),

\[
\int_{8k+u}^{8k+v}P(x)x^{-s-3}\,dx
=(8k)^{-s-3}\left(\int_u^vP(t)\,dt+o(1)\right).
\]

Its modulus does not tend to zero when \(\sigma\le-3\). Hence the Cauchy criterion for an ordinary improper integral fails there. Entire continuation below this boundary must therefore be distinguished from ordinary convergence.

**Lean integration distinction.** For \(-3<\Re s\le-2\), (5) is generally a conditionally convergent improper integral. It is not an absolutely integrable Bochner integral over \([1,\infty)\). A Lean formalization should express (5) as a limit of finite interval integrals, or use (7) as the definition and then prove the limit identity. It should not silently replace (5) by a measure-theoretic integral that requires integrability; such replacement would lose the conditional-convergence assertion.

## 4. Exact entire continuation

Define

\[
\widehat W(s)=\int_{1/8}^1W(u)u^{s-1}\,du.
\]

Compact support away from zero makes \(\widehat W\) entire. For \(\Re s>0\), integrating the four truncated quadratics separately gives

\[
\widehat W(s)
=\frac{2\left(1-\frac74\,2^{-s}+\frac78\,4^{-s}-\frac18\,8^{-s}\right)}{s(s+1)(s+2)}
=\boxed{\frac{2(1-2^{-s})(1-2^{-s-1})(1-2^{-s-2})}{s(s+1)(s+2)}}.
\tag{9}
\]

The values at \(s=0,-1,-2\) in the quotient are removable; the entire integral supplies them.

For \(\Re s>1\), absolute convergence permits termwise integration. With \(u=n/x\), and using that the raw lattice signal vanishes for \(0<x\le1\),

\[
\int_1^\infty\left(\sum_{n\ge1}W(n/x)\right)x^{-s-1}\,dx
=\sum_{n\ge1}n^{-s}\widehat W(s)
=\zeta(s)\widehat W(s).
\]

The centering contributes exactly \(c/(s-1)\). Therefore

\[
\boxed{D(s)=\zeta(s)\widehat W(s)-\frac{7/64}{s-1}.}
\tag{10}
\]

Initially this is proved for \(\Re s>1\). The right side has an entire extension: \(\zeta\) has only its simple pole at \(1\), with residue \(1\), and \(\widehat W(1)=c\). That pole is canceled by the displayed rational term. The identity theorem consequently proves (10) throughout the ordinary convergence domain \(\Re s>-3\), and the right side specifies its unique entire continuation beyond it.

For completeness, the full \((0,\infty)\) improper transform exists for \(-3<\Re s<1\). Its initial segment contributes

\[
\int_0^1(-cx)x^{-s-1}\,dx=-\frac{c}{1-s}.
\]

This cancels the term \(-c/(s-1)\) in (10), giving the exact full-transform identity

\[
\boxed{\int_0^\infty\delta(x)x^{-s-1}\,dx
=\zeta(s)\widehat W(s),\qquad -3<\Re s<1.}
\tag{11}
\]

The tail in (11) is interpreted as an ordinary improper limit; it is conditional when \(\Re s\le-2\).

## 5. Three exact moments and the RH implication of this correction analysis

Taking removable limits in (9) gives

\[
\widehat W(0)=\frac38\log2,
\qquad \widehat W(-1)=\log2,
\qquad \widehat W(-2)=3\log2.
\]

Using \(\zeta(0)=-1/2\), \(\zeta(-1)=-1/12\), and \(\zeta(-2)=0\) in (10) gives

\[
\boxed{\int_1^\infty\frac{\delta(x)}x\,dx
=\frac7{64}-\frac3{16}\log2,}
\]

\[
\boxed{\int_1^\infty\delta(x)\,dx
=\frac7{128}-\frac1{12}\log2,}
\]

\[
\boxed{\lim_{R\to\infty}\int_1^R x\delta(x)\,dx
=\frac7{192}.}
\tag{12}
\]

The first two integrals converge absolutely. The third converges conditionally and does not converge absolutely.

For the actual signals

\[
A(x)=\sum_{n\ge1}\Lambda(n)W(n/x)-cx,
\qquad
U(x)=\sum_{n\ge1}(\Lambda(n)-1)W(n/x),
\]

the pointwise identity \(A=U+\delta\) is exact. Equation (10) shows that their initial-domain Mellin transforms differ by an entire function. Therefore, wherever meromorphic continuations of those actual transforms have independently been constructed, they have identical nontrivial-zero pole principal parts. The deterministic lattice correction cannot supply or cancel such a pole.

This removes one possible analytic ambiguity between the two centered signals. It does **not** construct the missing continuation for the prime signal, improve the square-integrability threshold for \(\delta\), or bound the complete signed arithmetic residual.

## Sources and symbolic checks

The proof above derives the formulas for this exact spline. Standard background identities can be checked in the primary references:

- NIST DLMF, Bernoulli polynomial derivative, difference, and integral identities: <https://dlmf.nist.gov/24.4>.
- NIST DLMF, definitions of periodic Bernoulli functions: <https://dlmf.nist.gov/24.2>.
- NIST DLMF, zeta continuation and pole: <https://dlmf.nist.gov/25.2>.
- NIST DLMF, zeta values at integers: <https://dlmf.nist.gov/25.6>.

Wolfram was used only to check the small removable-limit calculations in (9) and the resulting constants in (12). Those checks agree with the displayed algebra. They are not substitutes for the all-\(x\) and all-\(s\) arguments above, and none of this appendix is claimed as Lean verified in this continuation.
