# Burnol's polynomial model: rigorous refinements

Prepared 2026-10-18 from a careful reading of Jean-François Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, arXiv:math/0103058v2 (March 2001), especially Theorems 1.4 and 2.1 and Section 2.

These are independently derived refinements of the statements in the supplied paper. No claim of priority in the approximation-theory literature is made. The proofs below are ordinary mathematics; they are not, by themselves, Lean verification. The accompanying Lean modules verify the real finite coefficient identities; the complex polynomial and analytic bridges in this note remain ordinary proofs.

## 1. Conventions and the exact finite Gram formula

Let Q be a complex polynomial of degree q whose distinct roots alpha lie on the unit circle, with multiplicities m_alpha. Multiplying Q by a nonzero scalar changes none of the approximation spaces. Define

\[
E(N,P)=\min_{\deg A\le N}\int_{|z|=1}|P(z)-Q(z)A(z)|^2\,\frac{d\theta}{2\pi}.
\]

Put L=N+q, and assume deg P <= L. This last condition is automatic for all sufficiently large N when P is fixed. Parseval identifies the integral with the sum of squares of the coefficients of the residual R.

For 0 <= k < m_alpha, use the ordinary, unnormalized derivative jet

\[
b_{\alpha,k}=\alpha^kP^{(k)}(\alpha).
\]

Writing R(z)=sum_{n=0}^L r_n z^n, divisibility of P-R by Q is equivalent to

\[
\sum_{n=0}^L n^{\underline{k}}\alpha^n r_n=b_{\alpha,k},
\qquad n^{\underline{k}}=n(n-1)\cdots(n-k+1).
\]

Let T be the q by (L+1) matrix with entries T[(alpha,k),n]=n_under_k alpha^n. Its rows are independent: polynomial Hermite interpolation at these distinct roots realizes arbitrary jets with degree at most q-1. Thus M=T T* is positive definite, and

\[
\boxed{E(N,P)=b^*M^{-1}b.}
\]

Indeed r*=T* M^{-1}b satisfies Tr*=b, and every other feasible r is r*+v with Tv=0. The two summands are orthogonal, proving the exact remainder identity

\[
\|r\|_2^2=b^*M^{-1}b+\|r-r^*\|_2^2.
\]

This also explains the essential distinction from Burnol's zeta argument: the polynomial annihilators exhaust the entire orthogonal complement. The zeta witnesses provide a subspace of the orthogonal complement and therefore only a lower bound unless the remaining orthogonal component is controlled.

## 2. Double root: an exact answer for every target polynomial

Take Q(z)=(1-conjugate(alpha) z)^2, |alpha|=1, L=N+2, and deg P <= L. Set

\[
a=P(\alpha),\qquad b=\alpha P'(\alpha),\qquad \mu=L/2,
\qquad V=\frac{L(L+1)(L+2)}{12}.
\]

Then

\[
\boxed{
E(N,P)=\frac{|a|^2}{L+1}
+\frac{12|b-La/2|^2}{L(L+1)(L+2)}.
}
\]

### Proof with the full nonnegative remainder

For a residual R with coefficients r_n put t_n=alpha^n r_n. This rotation preserves its coefficient norm. The two jet constraints become sum t_n=a and sum n t_n=b. The vectors 1 and n-mu are orthogonal because sum(n-mu)=0, and their squared norms are L+1 and V, respectively. Consequently, for every feasible t,

\[
\begin{aligned}
\sum_{n=0}^L|t_n|^2
={}&\frac{|a|^2}{L+1}+\frac{|b-\mu a|^2}{V}\\
&+\sum_{n=0}^L\left|t_n-\frac{a}{L+1}
-\frac{b-\mu a}{V}(n-\mu)\right|^2.
\end{aligned}
\]

The affine choice t_n*=a/(L+1)+(b-mu a)(n-mu)/V satisfies both constraints, so it realizes equality. Its residual R* satisfies P-R* divisible by Q; the quotient has degree at most L-2=N. This proves the formula and attainment.

Expanded equivalently,

\[
E(N,P)=\frac{2(2L+1)}{(L+1)(L+2)}|a|^2
-\frac{12}{(L+1)(L+2)}\Re(a\overline b)
+\frac{12}{L(L+1)(L+2)}|b|^2.
\]

There is no factorial normalization hidden here: b=alpha P'(alpha), using the ordinary derivative. The rotation in the coefficient constraint is alpha^n, not its conjugate. The optimal original coefficient is r_n*=conjugate(alpha)^n t_n*.

### Two examples

For P=1,

\[
E(N,1)=\frac{2(2L+1)}{(L+1)(L+2)}
=\frac{4N+10}{(N+3)(N+4)}.
\]

For alpha=1 and P=1-z, a=0 and b=-1, giving

\[
\boxed{E(N,1-z)=\frac{12}{(N+2)(N+3)(N+4)},
\qquad \lim_{N\to\infty}N^3E(N,1-z)=12.}
\]

Burnol's stated theorem supplies only N E(N,1-z) -> 0 in this example; the exact cubic rate is a stronger statement.

## 3. General hierarchy determined by the first surviving jet

Keep Q and P fixed. If Q divides P, E(N,P)=0 whenever deg(P/Q)<=N. Otherwise let

\[
r=\min\{\operatorname{ord}_{\alpha}P:
\operatorname{ord}_{\alpha}P<m_\alpha\}.
\]

Then

\[
\boxed{
E(N,P)=\frac{1}{N^{2r+1}}
\sum_{\alpha:\,\operatorname{ord}_\alpha P=r<m_\alpha}
C(m_\alpha,r)|P^{(r)}(\alpha)|^2
+O_{P,Q}(N^{-2r-2}),
}
\]

where

\[
C(m,r)=(2r+1)
\binom{m+r}{m-r-1}^{\!2}\binom{2r}{r}^{\!2}.
\]

In particular C(m,0)=m^2, recovering Burnol's constant and additionally giving an O(N^-2) remainder for each fixed P,Q. C(2,1)=12 recovers the exact double-root example.

### Proof

Scale the matrix rows by L^(-k-1/2), and let

\[
H_L[(\alpha,k),(\beta,l)]
=L^{-k-l-1}\sum_{n=0}^L
n^{\underline{k}}n^{\underline l}(\alpha\overline\beta)^n.
\]

For alpha=beta, the polynomial in n has degree k+l with leading coefficient one, so its power sum yields

\[
H_L[(\alpha,k),(\alpha,l)]
=\frac1{k+l+1}+O_{k,l}(L^{-1}).
\]

For alpha != beta, finite summation by parts gives, for every fixed polynomial f of degree d and omega != 1 on the unit circle,

\[
\sum_{n=0}^L f(n)\omega^n=O_{f,\omega}(L^d).
\]

For example, multiplying the sum by 1-omega leaves two endpoint terms and a sum involving f(n)-f(n-1), and induction proves the estimate. Hence every cross-root entry is O(L^-1). In finite dimension,

\[
H_L=H+O_Q(L^{-1}),\qquad
H=\bigoplus_\alpha H_{m_\alpha},\qquad
H_m[i,j]=\frac1{i+j+1}.
\]

Every H_m is positive definite since c*H_m c=integral_0^1 |sum c_j x^j|^2 dx. Thus H_L^-1=H^-1+O_Q(L^-1).

Define c_L[(alpha,k)]=L^-k alpha^k P^(k)(alpha). The finite Gram formula becomes

\[
E(N,P)=L^{-1}c_L^*H_L^{-1}c_L.
\]

By the definition of r, every coordinate with k<r is zero, and

\[
c_L=L^{-r}v+O_{P,Q}(L^{-r-1}),
\]

where v has coordinate alpha^r P^(r)(alpha) at (alpha,r) when ord_alpha P=r<m_alpha, and zero elsewhere. Roots where the entire required jet already vanishes contribute nothing, even if their actual vanishing order happens to equal r. Therefore

\[
E(N,P)=L^{-2r-1}v^*H^{-1}v+O_{P,Q}(L^{-2r-2}).
\]

The standard finite Cauchy inversion identity gives

\[
(H_m^{-1})_{rr}
=(2r+1)\binom{m+r}{m-r-1}^{2}\binom{2r}{r}^{2}.
\]

This identity follows, for example, from the full inverse formula

\[
(H_m^{-1})_{ij}=(-1)^{i+j}(i+j+1)
\binom{m+i}{m-j-1}\binom{m+j}{m-i-1}
\binom{i+j}{i}^{2},\quad 0\le i,j<m,
\]

which may be checked by multiplying with H_m, or derived by partial fractions for a Cauchy matrix. Since |alpha|=1 and L=N+q with q fixed, the displayed asymptotic follows.

### A useful finite perturbation estimate

Define eta_L=||H^(-1/2)(H_L-H)H^(-1/2)||_op. Whenever eta_L<1,

\[
\frac{c_L^*H^{-1}c_L}{L(1+\eta_L)}
\le E(N,P)\le
\frac{c_L^*H^{-1}c_L}{L(1-\eta_L)}.
\]

This follows by the Loewner inequalities (1-eta_L)H <= H_L <= (1+eta_L)H and inversion. The root-separation dependence is retained in eta_L; it cannot silently be made uniform when roots move or collide.

## 4. One repeated root: exact factorial formula for P=1

For Q(z)=(1-z)^m, m>=1, and L=N+m,

\[
\boxed{
E(N,1)=1-\frac{(L!)^2}{(L-m)!(L+m)!}
=1-\frac{((N+m)!)^2}{N!(N+2m)!}.
}
\]

The same formula holds for Q(z)=(1-conjugate(alpha)z)^m, |alpha|=1, by rotating coefficient sequences.

### Elementary proof by finite differences

Write s=m-1, use falling factorial notation x_under_j, and let Delta f(x)=f(x+1)-f(x). Define

\[
F(x)=x^{\underline m}(x-L-1)^{\underline s},
\qquad q(x)=\frac{\Delta^sF(x)}x.
\]

The numerator vanishes at zero because F(j)=0 for j=0,...,s. Thus q is a polynomial of degree m-1, with q(0) interpreted as the derivative of the numerator at zero.

For every polynomial h of degree at most m-2,

\[
\sum_{n=0}^L n q(n)h(n)=0.
\]

Indeed expand Delta^s F(n), shift k=n+j, and observe that F(k)=0 for k=1,...,m-1 and k=L+1,...,L+m-1. The surviving interior sum contains the s-th backward difference of h, which vanishes. For m=1 this statement imposes no condition.

Put

\[
A=\frac{(L+m)!}{L!},\qquad B=\frac{L!}{(L-m)!}.
\]

At an integer 0<=j<=s, differentiating the unique vanishing factor of x_under_m gives

\[
F'(j)=(-1)^{s-j}j!(s-j)!(j-L-1)^{\underline s}.
\]

Consequently

\[
q(0)=s!\sum_{j=0}^{s}(j-L-1)^{\underline s}
=\frac{(-1)^s s!}{m}(A-B),
\]

where the last equality is the elementary telescoping sum of rising factorials.

For the remaining sum, the same boundary cancellations give

\[
\sum_{n=1}^Lq(n)
=\sum_{k=m}^{L}F(k)
\sum_{j=0}^{s}\frac{(-1)^{s-j}\binom{s}{j}}{k-j}.
\]

The elementary partial-fraction identity

\[
\sum_{j=0}^{s}\frac{(-1)^{s-j}\binom{s}{j}}{k-j}
=\frac{s!}{k^{\underline m}},\qquad k\ge m,
\]

then yields

\[
\sum_{n=1}^Lq(n)
=s!\sum_{k=m}^L(k-L-1)^{\underline s}
=\frac{(-1)^s s!}{m}B.
\]

It follows that S=sum_{n=0}^L q(n)=(-1)^s s! A/m is nonzero. Let u_n=q(n)/S. The sequence u has the reproducing property

\[
\sum_{n=0}^L u_n p(n)=p(0)
\qquad (\deg p<m),
\]

because p(n)-p(0) is n times a polynomial of degree at most m-2. In particular sum u=1 and sum u_n n_under_k=0 for 1<=k<m. Hence R(z)=sum u_n z^n satisfies R(1)=1 and R^(k)(1)=0 for 1<=k<m, so 1-R is divisible by (1-z)^m and the quotient has degree at most N.

Further, the coefficient sequence u is polynomial in n of degree<m. It is therefore orthogonal to the coefficient sequence of every multiple of (1-z)^m of degree at most L, because those sequences have all the first m derivative moments zero. Thus R is the optimal residual. Its squared norm is sum u_n^2=u_0 by applying the reproducing property to the real polynomial p(n)=q(n)/S. Finally

\[
E(N,1)=u_0=\frac{A-B}{A}=1-\frac{(L!)^2}{(L-m)!(L+m)!}.
\]

This proof was checked independently in exact rational arithmetic for m=1,...,6 at L=8: the normalization, all vanishing moments, energy identity, and factorial formula agreed. These computational checks supplement the proof; they are not Lean verification.

### Fixed-m expansion and bounds

Expanding the exact finite product gives

\[
E(N,1)=\frac{m^2}{N}-\frac{m^2(m+1)^2}{2N^2}
+\frac{m^2(m+1)^2(m^2+4m+1)}{6N^3}+O_m(N^{-4}).
\]

For every m,N in the range above,

\[
1-\exp\!\left(-\frac{m^2}{N+2m}\right)
\le E(N,1)\le
\min\left\{1,\frac{m^2}{N+m+1}\right\}.
\]

Indeed write E=1-product_{j=0}^{m-1}(1-a_j), where a_j=(2j+1)/(L+j+1). Use product(1-a_j)<=exp(-sum a_j), sum a_j>=m^2/(L+m), and the union bound 1-product(1-a_j)<=sum a_j<=m^2/(L+1).

### Growing multiplicity is not covered by the fixed-m asymptotic

For an integer sequence m=m_N>=1:

* If m_N/sqrt(N) -> c in [0,infinity), then E(N,1) -> 1-exp(-c^2).
* If m_N/sqrt(N) -> infinity, then E(N,1) -> 1.
* In particular vanishing approximation error for this family occurs exactly when m_N^2/N -> 0.

For the first assertion m=O(sqrt N) gives max a_j=O(N^-1/2), sum a_j=m^2/N+o(1), and sum a_j^2=o(1), so the logarithm of the product tends to -c^2. The second follows directly from the exponential lower bound, since m^2/(N+2m) -> infinity. The equivalence in the third bullet follows from the upper bound and the converse lower-bound argument (or the same bounds along subsequences).

This is a concrete warning against passing from Burnol's asymptotics for a fixed finite family of zero witnesses to an expanding family without quantitative control.

## 5. What the paper gives toward RH, and the remaining gap

Burnol proves the multiplicity-square lower bound

\[
\liminf_{\lambda\downarrow0}\log(1/\lambda)D(\lambda)^2
\ge\sum_\rho\frac{m_\rho^2}{|\rho|^2}.
\]

Under RH the sum is over all nontrivial zeros, each distinct zero once and weighted by its multiplicity squared. If RH fails, the distance does not tend to zero and the left side is infinite, so the lower bound does not force RH. The critical-line witnesses themselves can be used without assuming RH; the assumption in the exposition is used to make the resulting lower bound nontrivial and exhaustive on zeros.

The polynomial refinements above show that:

1. The square of multiplicity is exactly a finite Hilbert-matrix endpoint constant.
2. Cancellation of initial target jets improves the power of the approximation rate from N^-1 to N^-(2r+1).
3. Full finite Gram identities expose the nonnegative orthogonal remainder which must vanish to turn a witness lower bound into a matching upper bound.
4. Uniformity in an expanding family is a separate analytic problem, already visible in the elementary repeated-root model.

They do not prove the upper bound D(lambda)->0, nor completeness of Burnol's zero witnesses. The corresponding RH task is to control the residual component beyond any chosen family of zero witnesses, or to construct legal approximants whose full norm of the error tends to zero. Lower bounds alone cannot supply this.

## 6. A quantitative fixed-family refinement on the zeta side

Burnol's own pointwise estimates also imply a stronger fixed-family statement than the final liminf alone. Fix a nonempty finite set R of zeros on the critical line and include every multiplicity jet k<m_rho. Put T=log(1/lambda), let H_R(lambda) be the span of his normalized witnesses X_(rho,k)^lambda, and let Pi_R(lambda) denote orthogonal projection to that span. Then

\[
\boxed{
\|\Pi_R(\lambda)\chi_1\|^2
=\frac{S_R}{T}+O_R(T^{-2}),\qquad
S_R=\sum_{\rho\in R}\frac{m_\rho^2}{|\rho|^2}.
}
\]

Consequently, for some constants C_R,T_R depending on this fixed family,

\[
D(\lambda)^2\ge \frac{S_R}{T}-\frac{C_R}{T^2}
\qquad (T\ge T_R).
\]

### Details

Theorem 4.11 expands V Y_(rho,k)^lambda on lambda<t<=1 as the k-th s-derivative of V(s)t^-s plus a bounded remainder. Each derivative is a finite combination of t^-rho log(1/t)^j with j<=k. Diagonal inner products therefore have leading term T^(k+l+1)/(k+l+1), and the lower-degree terms contribute O_R(T^(k+l)). Cross-root integrals have an oscillatory factor with nonzero fixed frequency and are O_R(T^(k+l)) by integration by parts. The bounded remainders have bounded cross integrals against t^-1/2 log(1/t)^j; the tail t>=1 is also integrable by Theorem 4.11. After normalization the witness Gram matrix is therefore H+O_R(T^-1), with H the direct sum of the Hilbert blocks.

All target-jet limits can also be evaluated. For Re w<1/2, unitarity gives

\[
\langle\chi_1,\psi_{w,k}\rangle
=\frac{k!}{(1-\overline w)^{k+1}}
-\frac{(k+1)!}{(1-\overline w)^{k+2}}.
\]

The paper uses scalar products linear in the first argument. Passing w to rho from the left is justified after applying V because V chi_1(t)=O(t^2) at zero, and the continued V psi_(rho,k) has size O_R(t^-1/2(1+log(1/t))^k). The omission of 0<t<lambda is consequently bounded by O_R(lambda^(5/2)(1+T)^k). Thus

\[
\sqrt T\,\langle\chi_1,X_{\rho,k}^{\lambda}\rangle
=T^{-k}\left[
\frac{k!(\rho-k-1)}{\rho^{k+2}}
+O_R\!\left(\lambda^{5/2}(1+T)^k\right)\right].
\]

The k=0 coordinate has limit (rho-1)/rho^2; all other coordinates are O_R(T^-1). Inverting the finite Gram matrix gives the asserted projection expansion. On the critical line |rho-1|=|rho|, so the leading constant is S_R.

This result is a consequence of Burnol's analytic estimates, with the finite matrix perturbation made quantitative. It is not a uniform estimate over an increasing set of zeros: the constants depend on the zero separations, heights, multiplicities, and derivatives of V. It remains a lower bound for D(lambda)^2 and does not close the RH argument.
