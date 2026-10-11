# Quantitative reciprocal compatibility of actual zero-sampled growing polynomials

These are paper deductions from Ford--Meng--Zaharescu (FMZ), *Simultaneous distribution of the fractional parts of Riemann zeta zeros*, Lemmas 1--2, https://arxiv.org/pdf/1511.06814. Both lemmas are unconditional. This note does not prove those literature inputs in Lean and does not identify the polynomials with actual shifted zeta functions. No RH is assumed in the deductions.

Write `L=log T`, and let `E_T` average over all actual ordinates `0<gamma<=T`, with multiplicity. Let

\[
 Z_Y(s;\gamma)=\sum_{n\le Y}n^{-s+i\gamma},\qquad
 M_Y(s;\gamma)=\sum_{n\le Y}\mu(n)n^{-s+i\gamma}.
\]

## 1. Exact product coefficients

Define, for positive integers k,

\[
 b_J(k)=\sum_{de=k,\ d,e\le J}\mu(e).
\]

Then the exact finite convolution identity is

\[
 Z_J(s;\gamma)M_J(s;\gamma)-1
 =\sum_{J<k\le J^2}b_J(k)k^{-s+i\gamma}.
\tag{Q1}
\]

Indeed, the product expansion uses `d^{-s+i gamma} e^{-s+i gamma}=(de)^{-s+i gamma}`. For `k<=J`, both truncation conditions hold for every factorization, so `b_J(k)=sum_{e|k} mu(e)`, equal to one at k=1 and zero otherwise. Always `|b_J(k)|<=tau(k)`. No incomplete divisor sum is replaced by a complete divisor sum at k>J.

## 2. Elementary divisor-square tail, without an epsilon loss

For x>=1,

\[
 \sum_{n\le x}\tau(n)^2\le x(1+\log x)^3.
\tag{Q2}
\]

To see this, count ordered quadruples `ab=cd<=x`. Write `a=gr,c=gs` with `g=gcd(a,c)` and `(r,s)=1`. The relation forces `b=sh,d=rh`, so `n=grsh`. On dropping coprimality,

\[
 \sum_{n\le x}\tau(n)^2
 \le\sum_{rs\le x}\sum_{gh\le x/(rs)}1
 \le x(1+\log x)\sum_{r,s\le x}\frac1{rs}
 \le x(1+\log x)^3.
\]

Dyadic decomposition consequently gives, for every fixed 1/2<sigma<1,

\[
 \sum_{k>J}\tau(k)^2 k^{-2\sigma}
 \le C_\sigma J^{1-2\sigma}(1+\log J)^3.
\tag{Q3}
\]

The constant is an explicit convergent multiple of `sum_{h>=0} 2^{h(1-2 sigma)}(h+2)^3`. Thus the complete diagonal of the residual polynomial in (Q1) is bounded by (Q3).

## 3. Exact prime-power contribution and its tail

Put `a_k=b_J(k)k^{-s}` on `J<k<=J^2` and zero elsewhere. In the FMZ quadratic law retain the signed quantity

\[
 Q_J(s)=\sum_{J<m,\ mp^h\le J^2}\frac{\log p}{p^{h/2}}
 \Re\!\left(b_J(mp^h)\overline{b_J(m)}(mp^h)^{-s}m^{-\bar s}\right).
\tag{Q4}
\]

Then the exact empirical identity is

\[
 E_T|Z_JM_J-1|^2
 =\sum_{J<k\le J^2}|b_J(k)|^2k^{-2\Re s}
 -\frac{T}{\pi N(T)}Q_J(s)+\frac{E(T,J^2,a)}{N(T)}.
\tag{Q5}
\]

Absolute values are taken only after this signed identity has been preserved. If `Re s>=sigma>1/2`, `tau(mp^h)<=tau(m)(h+1)` and the support condition forces m>J. Consequently

\[
 |Q_J(s)|\le
 \left(\sum_{m>J}\tau(m)^2m^{-2\sigma}\right)
 \left(\sum_{p,h\ge1}(h+1)(\log p)p^{-h(\sigma+1/2)}\right)
 \le C_\sigma J^{1-2\sigma}(1+\log J)^3.
\tag{Q6}
\]

The prime-power series converges because sigma+1/2>1. The explicit lower support restriction is essential: `b_J(1)=1`, but the residual coefficient at 1 is zero after subtracting the constant. This removes the spurious constant `O(1/log T)` obstruction: the prime term is a tail term with its own vanishing factor.

## 4. Product-specific weighted dispersion has no logarithmic loss

Let `w_k=|b_J(k)| k^{-sigma}`, `u_k=log(J^2/k)`, on the residual support. By retaining the factorization domination,

\[
 A_1:=\sum_k w_k\le
 \left(\sum_{n\le J}n^{-\sigma}\right)^2
 \le\frac{J^{2-2\sigma}}{(1-\sigma)^2}.
\tag{Q7}
\]

Put `S_h=sum_{n<=J} n^{-sigma} log^h(J/n)`, for h=0,1,2. Decreasing-integrand comparison yields

\[
 S_0\le\frac{J^{1-\sigma}}{1-\sigma},\quad
 S_1\le\frac{J^{1-\sigma}}{(1-\sigma)^2},\quad
 S_2\le\frac{2J^{1-\sigma}}{(1-\sigma)^3}.
\]

As `u_{de}=log(J/d)+log(J/e)`,

\[
 \sum_k w_ku_k^2\le2S_0S_2+2S_1^2
 \le\frac{6J^{2-2\sigma}}{(1-\sigma)^4}.
\]

There is a sharper bound retaining the complete tensor-product variance. Define the full fiber weights `v_k=sum_{de=k,d,e<=J}d^{-sigma}e^{-sigma}`. Every actual residual coefficient modulus is bounded by v_k, including the zero residual coefficients at k<=J. Nonnegative pointwise domination preserves dispersion. Grouping equal products also preserves dispersion because the logarithmic frequencies agree in each fiber. The tensor-product identity is exactly

\[
 W_2(s)\le\sum_{k,l}v_kv_l\log^2(k/l)
 =4S_0^3S_2-4S_0^2S_1^2
 =2S_0^2\left(2S_0S_2-2S_1^2\right).
\]

The exact negative-square term is retained before obtaining

\[
 W_2(s)\le4S_0^3S_2\le\frac{8J^{4-4\sigma}}{(1-\sigma)^6}.
\tag{Q8}
\]

This improves the constant 12 from separately bounding the residual first and second centered moments. The product-specific estimate uses exact convolution rather than `tau(k)<=C_epsilon k^epsilon`, so no epsilon loss occurs in the FMZ error term.

## 5. Quantitative scalar and compact product mean-square theorem

Using the full FMZ error from the prior note at length `X=J^2`, together with `N(T) asymp T log T`, (Q3)--(Q8) give

\[
 E_T|Z_J(s)M_J(s)-1|^2\le C_\sigma\left[
 J^{1-2\sigma}(1+\log J)^3
 +\frac{J^{4-4\sigma}}{L^2}
 +\frac{J^{4-4\sigma}}{TL}
 \left(J^2\log(2J^2)+J\log^2(2J^2T)+J^2\log(2T)\right)
 \right].
\tag{Q9}
\]

The `T/L^{10}` FMZ error adds `J^{4-4 sigma}/L^{11}`, which is absorbed by the displayed `L^{-2}` term once L>=1. The tail prime contribution in (Q6), multiplied by `T/(pi N(T))`, is likewise absorbed by the first displayed term. All bounds are uniform in `Im s`.

Validity requires `J^2<=exp(L/(50 log L))`; any fixed polylogarithmic J satisfies this eventually. For `J=floor(L^b)` one has, suppressing only exponentially small terms,

\[
 E_T|Z_JM_J-1|^2
 \ll_\sigma L^{-b(2\sigma-1)}(1+\log L)^3
 +L^{b(4-4\sigma)-2}.
\tag{Q10}
\]

Thus direct product convergence in empirical mean square holds for all sigma>1/2 provided `b(4-4 sigma)<2`. In particular, the originally specified cutoff `J=floor(L^2)` has the stronger estimate

\[
 E_T|Z_JM_J-1|^2\ll_\sigma L^{6-8\sigma},
 \qquad 3/4<\sigma<1.
\tag{Q11}
\]

The diagonal is faster since `4 sigma-2>8 sigma-6` for sigma<1; its logarithmic factor is absorbed by that strict exponent margin. This estimate is valid without RH.

For a compact K in `Re s>sigma`, choose a bounded measurable neighborhood U of K and radius r>0 so all radius-r disks centered on K lie in U and `Re s>=sigma` on U. Analytic mean value gives, for every entire f,

\[
 \|f\|_K^2\le\frac1{\pi r^2}\int_U|f(s)|^2dA(s).
\tag{Q12}
\]

Apply (Q12), finite-sum interchange, and the uniform scalar bound to obtain exactly the same orders for `E_T ||Z_JM_J-1||_K^2`, with a constant depending on K, U, r and sigma. The empirical sup norm is therefore controlled without any appeal to an unformalized random analytic limit.

## 6. An explicit mean rate for the original cutoff on every compact in Re s>1/2

Let `Y=floor(L^2)` and let J<=Y be an intermediate cutoff. The linear FMZ law, with coefficients supported on `J<n<=Y`, gives

\[
 E_T\|Z_Y-Z_J\|_K^2+E_T\|M_Y-M_J\|_K^2
 \le C_K\left[J^{1-2\sigma}+L^{2-4\sigma}+e^{-L}L^{C_\sigma}\right],
\tag{Q13}
\]

where 1/2<sigma<1 is below the real parts in the fixed neighborhood U. Its prime-power sum is at most `C_sigma J^{1-2 sigma}`, and the normalized prime term has an additional factor `1/L`. The same argument for the complete polynomials gives bounded empirical second moments of the compact sup norms of `Z_Y`, `M_Y`, `Z_J`, and `M_J`, uniformly in T and J<=Y.

Keep the exact decomposition

\[
 Z_YM_Y-1=(Z_Y-Z_J)M_Y+Z_J(M_Y-M_J)+(Z_JM_J-1).
\tag{Q14}
\]

Cauchy--Schwarz, the bounded moments, (Q9), and (Q13) imply

\[
 E_T\|Z_YM_Y-1\|_K
 \le C_K\left[
 J^{1/2-\sigma}(1+\log J)^{3/2}
 +\frac{J^{2-2\sigma}}{L}
 +L^{1-2\sigma}+e^{-L/2}L^{C_\sigma}
 \right].
\tag{Q15}
\]

This is a finite-sum deterministic proof and bypasses fixed-character-to-growing-family rate issues entirely.

Define

\[
 c=\frac2{3-2\sigma},\quad
 d=\frac3{3-2\sigma},\quad
 \kappa=\frac{2\sigma-1}{3-2\sigma},\quad
 q=\frac{6(1-\sigma)}{3-2\sigma}.
\]

Choose `J=floor(L^c (log L)^d)`. Since c<2, one has J<=Y eventually. Balancing the first two terms in (Q15) proves the explicit compact-uniform mean rate

\[
 \boxed{E_T\|Z_YM_Y-1\|_K
 \ll_K (\log T)^{-\kappa}(\log\log T)^q.}
\tag{Q16}
\]

Here sigma may be any fixed number in `(1/2,min(1,inf_{s in U} Re s))`. The constants depend on its distance from both endpoints. Since `kappa<2 sigma-1`, the original long-polynomial tail term `L^{1-2 sigma}` is strictly faster. If a pure power is preferred, for every `0<kappa'<kappa` the bound is `O_K((log T)^{-kappa'})`.

At the scalar level take sigma=Re s when `1/2<Re s<1`; for a compact take a slightly smaller sigma to allow the analytic neighborhood. In particular, the full half-plane result is effective and no longer relies only on abstract fixed-truncation convergence.

Markov yields, for every eta>0,

\[
 \frac{\#\{0<\gamma\le T:\|Z_YM_Y-1\|_K\ge\eta\}}{N(T)}
 \le\frac{C_K}{\eta}L^{-\kappa}(\log L)^q.
\tag{Q17}
\]

Taking eta=1 bounds the proportion of ordinates for which either polynomial has a zero in K by the same order.

If `sigma_K=inf_{s in K} Re s>1`, there is the additional, simpler pointwise bound valid for every real gamma,

\[
 \|Z_YM_Y-1\|_K\le\frac{2\zeta(\sigma_K)}{\sigma_K-1}Y^{1-\sigma_K}.
\]

Here the infinite ordinary and Mobius series converge absolutely, their exact convolution gives product one, their moduli are at most `zeta(sigma_K)`, and each truncation tail is at most `Y^{1-sigma_K}/(sigma_K-1)`. For the original cutoff this yields `O_K(L^{-2(sigma_K-1)})` uniformly in gamma, stronger than empirical averaging when K is sufficiently far into the absolute-convergence region.

## 7. Lean-friendly provider boundary

The deterministic scalar proof can first be formalized under these precisely stated analytic inputs, without asserting them as new axioms:

1. `N(T)>=c*T*log T` eventually, c>0.
2. The uniform two FMZ character estimates for actual ordinates, over the full growing range, or the already-derived finite quadratic law with the signed prime-power main term.
3. The analytic neighborhood inequality (Q12) and finite-sum/integral interchange.
4. The divisor-square tail bound (Q3), obtainable from (Q2) by dyadic decomposition.

Exact convolution (Q1), the factorization-based ell1 and dispersion bounds (Q7)--(Q8), preservation of the signed quadratic (Q5), finite empirical Cauchy--Schwarz (Q14)--(Q15), and scalar exponent balancing are independent proof obligations. A theorem merely assuming (Q9) or (Q13) establishes a conditional transfer result; it is not a fully Lean-proved unconditional FMZ theorem. The primary literature proof certifies the mathematics as unconditional, but a kernel-checked implementation must transparently identify the remaining literature interfaces.
