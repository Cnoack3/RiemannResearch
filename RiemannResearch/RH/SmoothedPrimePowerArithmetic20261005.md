# A sharp bound for the smoothed full prime-power arithmetic matrix

Date: 2026-10-05. Status: unconditional paper proof; no Lean verification is claimed.

## 1. Matrix and conclusion

For an integer \(d\ge1\), use the full coordinate space
\(\mathbb C^{\{1,\ldots,d\}}\), including every composite coordinate. Set

\[
B_d(n,m)=
\begin{cases}
\displaystyle\frac{2\Lambda(q)}{q+1},&n=mq\text{ or }m=nq,
\quad q\ge2\text{ an integer},\\
0,&\text{otherwise}.
\end{cases}
\tag{1}
\]

Here \(\Lambda(p^k)=\log p\), and \(\Lambda(q)=0\) at integers that are not prime powers. The two alternatives in (1) are disjoint. The diagonal is zero.

**Theorem.** As \(d\to\infty\),

\[
\boxed{\ \|B_d\|=4\log\log d+O(1).\ }
\tag{2}
\]

This is an operator-norm assertion on the full matrix. It does not discard composite coordinates, products of distinct primes, higher prime powers, or any multiplicative interaction present in (1). Its proof requires neither RH nor the prime number theorem.

Write \(C_\psi=4\log2\). A finite upper bound valid for \(d\ge1\) and \(y\ge1\) is

\[
\boxed{
\|B_d\|\le
4\sum_{2\le q\le y}\frac{\Lambda(q)}{q+1}
+4\sqrt{\log d\sum_{q>y}\frac{\Lambda(q)}{(q+1)^2}}
\le4(\log y+C_\psi)
+4\sqrt{\frac{2C_\psi\log d}{y}}.
}
\tag{3}
\]

For \(d\ge e\), choosing \(y=\log d\) gives the completely explicit estimate

\[
\boxed{\ \|B_d\|\le
4\log\log d+4C_\psi+4\sqrt{2C_\psi}.\ }
\tag{4}
\]

The existing weaker universal bound
\(\sum_{q\le y}\Lambda(q)/q\le\log y+\log4+4\)
can also be used in (3), giving

\[
\|B_d\|\le4(\log y+\log4+4)
+4\sqrt{\frac{2C_\psi\log d}{y}}.
\tag{5}
\]

## 2. Elementary arithmetic inputs, with constants

Prime factorization gives the exact identity

\[
\sum_{q\mid n}\Lambda(q)=\log n.
\tag{6}
\]

Indeed, if \(n=\prod_p p^{a_p}\), its nonzero terms are exactly
\(\Lambda(p),\ldots,\Lambda(p^{a_p})\), whose sum is
\(\sum_pa_p\log p\).

Define \(\psi(x)=\sum_{q\le x}\Lambda(q)\). The elementary binomial argument gives

\[
\psi(x)\le C_\psi x\qquad(x\ge1),\qquad C_\psi=4\log2.
\tag{7}
\]

For completeness, for every integer \(m\ge1\), each prime-power term
\(q=p^k\in(m,2m]\) contributes at least \(\log p\) to
\(\log\binom{2m}{m}\). This follows from

\[
v_p\!\binom{2m}{m}
=\sum_{j\ge1}\left(\left\lfloor\frac{2m}{p^j}\right\rfloor
-2\left\lfloor\frac{m}{p^j}\right\rfloor\right),
\]

whose terms are nonnegative and whose term at \(j=k\) is one. Thus
\(\psi(2m)-\psi(m)\le2m\log2\). Summing at dyadic integers gives
\(\psi(2^k)\le(2^{k+1}-2)\log2\). If
\(2^{k-1}<x\le2^k\), monotonicity now gives (7). The interval
\(1\le x<2\) has \(\psi(x)=0\).

Let

\[
M(x)=\sum_{q\le x}\frac{\Lambda(q)}q.
\]

The divisor identity implies

\[
\log(N!)=\sum_{q\le N}\Lambda(q)\left\lfloor\frac Nq\right\rfloor.
\]

Consequently, for an integer \(N\ge1\),

\[
\frac{\log(N!)}N\le M(N)
\le\frac{\log(N!)}N+\frac{\psi(N)}N.
\]

The integral estimate
\(N\log N-N+1\le\log(N!)\le N\log N\), together with (7), yields

\[
\log N-1\le M(N)\le\log N+C_\psi.
\]

Taking \(N=\lfloor x\rfloor\), using
\(\log(x/N)\le\log2\) when \(x\ge2\), and treating
\(1\le x<2\) directly proves

\[
|M(x)-\log x|\le C_\psi\qquad(x\ge1),
\tag{8}
\]

because \(C_\psi\ge1+\log2\). In particular, this supplies the first term in (3).

Stieltjes partial summation and (7) give

\[
\begin{aligned}
\sum_{q>y}\frac{\Lambda(q)}{(q+1)^2}
&=-\frac{\psi(y)}{(y+1)^2}
+2\int_y^\infty\frac{\psi(x)}{(x+1)^3}\,dx\\
&\le2C_\psi\int_y^\infty\frac{x}{(x+1)^3}\,dx
\le\frac{2C_\psi}{y}\qquad(y\ge1).
\end{aligned}
\tag{9}
\]

The sum in (9) is over integers strictly larger than \(y\); the subtraction term incorporates the endpoint correctly, including when \(y\) is a prime power.

## 3. Exact operator split and the tail estimate

For \(q\ge2\), define the truncated multiplication shift

\[
D_qe_m=\begin{cases}e_{qm},&qm\le d,\\0,&qm>d.\end{cases}
\]

Its norm is at most one. Put

\[
L=\sum_{2\le q\le d}\frac{2\Lambda(q)}{q+1}D_q,
\qquad B_d=L+L^*.
\tag{10}
\]

Split \(L=L_{\le y}+L_{>y}\), preserving the exact equality (10). The low part satisfies

\[
\|L_{\le y}+L_{\le y}^*\|
\le4\sum_{2\le q\le y}\frac{\Lambda(q)}{q+1}.
\tag{11}
\]

For the high part, its \(n\)-th coordinate is

\[
(L_{>y}u)(n)=
\sum_{\substack{q\mid n\\q>y}}\frac{2\Lambda(q)}{q+1}u(n/q).
\]

Applying weighted Cauchy–Schwarz with the positive weights
\(\Lambda(q)\) on the prime-power terms, and then retaining the exact complete divisor budget (6), gives

\[
\begin{aligned}
|(L_{>y}u)(n)|^2
&\le\left(\sum_{\substack{q\mid n\\q>y}}\Lambda(q)\right)
\left(\sum_{\substack{q\mid n\\q>y}}
\frac{4\Lambda(q)}{(q+1)^2}|u(n/q)|^2\right)\\
&\le\log d\sum_{\substack{q\mid n\\q>y}}
\frac{4\Lambda(q)}{(q+1)^2}|u(n/q)|^2.
\end{aligned}
\tag{12}
\]

For \(n=1\), the left and right sides are zero. Sum (12) over all \(1\le n\le d\), exchange the finite nonnegative sums, and use \(n=mq\):

\[
\begin{aligned}
\|L_{>y}u\|^2
&\le4\log d\sum_{q>y}\frac{\Lambda(q)}{(q+1)^2}
\sum_{m\le d/q}|u(m)|^2\\
&\le4\log d\left(\sum_{q>y}\frac{\Lambda(q)}{(q+1)^2}\right)\|u\|^2.
\end{aligned}
\tag{13}
\]

Thus

\[
\|L_{>y}+L_{>y}^*\|
\le4\sqrt{\log d\sum_{q>y}\frac{\Lambda(q)}{(q+1)^2}}.
\tag{14}
\]

Equations (11), (14), (8), and (9) prove (3)–(5). This argument controls all cross terms through (12); no assertion of independent prime blocks is made.

## 4. Matching lower bound with bounded error

The lower bound can also retain bounded error, strengthening the simpler constant-exponent-box argument. Put

\[
\ell=\log d,\qquad y=\frac{\ell}{2C_\psi},
\qquad k_p=\left\lfloor\sqrt{\frac yp}\right\rfloor\quad(p\le y).
\tag{15}
\]

Assume \(y\ge2\). Every \(k_p\ge1\). Partial summation and
\(\vartheta(x)=\sum_{p\le x}\log p\le\psi(x)\le C_\psi x\)
give

\[
\sum_{p\le y}\frac{\log p}{\sqrt p}
=\frac{\vartheta(y)}{\sqrt y}
+\frac12\int_1^y\frac{\vartheta(x)}{x^{3/2}}\,dx
\le2C_\psi\sqrt y.
\tag{16}
\]

Consequently

\[
\sum_{p\le y}k_p\log p
\le\sqrt y\sum_{p\le y}\frac{\log p}{\sqrt p}
\le2C_\psi y=\ell.
\tag{17}
\]

Every integer in the exponent box

\[
\mathcal D_y=
\left\{\prod_{p\le y}p^{a_p}:0\le a_p\le k_p\right\}
\]

therefore belongs to \(\{1,\ldots,d\}\). Let \(u\) be the unit vector constant on \(\mathcal D_y\), and zero elsewhere. For each prime \(p\le y\), the proportion of box coordinates \(m\) for which \(mp\) stays in the box is \(k_p/(k_p+1)\). All entries of \(B_d\) are nonnegative. Keeping just these prime edges in the Rayleigh quotient gives

\[
\begin{aligned}
\langle u,B_du\rangle
&\ge4\sum_{p\le y}\frac{\log p}{p+1}\frac{k_p}{k_p+1}\\
&\ge4\sum_{p\le y}\frac{\log p}{p+1}
-\frac4{\sqrt y}\sum_{p\le y}\frac{\log p}{\sqrt p}\\
&\ge4\sum_{p\le y}\frac{\log p}{p+1}-8C_\psi.
\end{aligned}
\tag{18}
\]

The second inequality uses \(k_p+1>\sqrt{y/p}\) and
\(\sqrt p/(p+1)\le1/\sqrt p\).

The higher prime powers and the replacement of \(p\) by \(p+1\) have uniformly bounded total cost:

\[
\begin{aligned}
0\le M(y)-\sum_{p\le y}\frac{\log p}{p+1}
&\le\sum_p\frac{\log p}{p(p-1)}
+\sum_p\frac{\log p}{p(p+1)}\\
&=\sum_p\frac{2\log p}{p^2-1}<3.
\end{aligned}
\tag{19}
\]

For the numerical constant, enlarge the last sum to all integers \(n\ge2\), use
\(1/(n^2-1)\le4/(3n^2)\), and use that
\(\log x/x^2\) is decreasing for \(x\ge2\):

\[
\sum_{n\ge2}\frac{2\log n}{n^2-1}
\le\frac83\left(\frac{\log2}{4}
+\int_2^\infty\frac{\log x}{x^2}\,dx\right)
=2\log2+\frac43<3.
\]

Combining (8), (18), and (19), and using the variational principle, yields

\[
\begin{aligned}
\|B_d\|\ge\lambda_{\max}(B_d)
&\ge4\log y-12C_\psi-12\\
&=4\log\log d
-4\log(2C_\psi)-12C_\psi-12.
\end{aligned}
\tag{20}
\]

This is valid when \(\log d\ge4C_\psi\). Together with (4), it proves (2), with fully explicit bounded upper and lower errors. The vector achieving the lower bound is supported on prime-power products, predominantly composite integers. Thus the leading constant four specifically survives the complete multiplicative coordinate structure.

## 5. Exact relation to Cauchy smoothing

Let the original symmetric arithmetic matrix have entries

\[
A_d(n,m)=\frac{\Lambda(q)}{\sqrt q}
\quad\text{if }n=mq\text{ or }m=nq,
\]

and zero otherwise. Define the real correlation matrix

\[
S_d(n,m)=\frac{2\sqrt{nm}}{n+m}
=\int_0^\infty\left(\sqrt{2n}e^{-nt}\right)
\left(\sqrt{2m}e^{-mt}\right)\,dt.
\tag{21}
\]

Its diagonal entries are one and it is positive semidefinite. Entrywise multiplication gives the exact identity

\[
S_d\circ A_d=B_d.
\tag{22}
\]

The Schur map \(X\mapsto S_d\circ X\) is a contraction in operator norm. One direct proof uses the isometry
\(Ve_n=e_n\otimes f_n\), where \(f_n(t)=\sqrt{2n}e^{-nt}\) has norm one: the Schur map equals \(V^*(X\otimes I)V\).

Consequently, whenever an actual finite zero matrix has an established decomposition

\[
H_{T,d}=I-c_TA_d+R_{T,d},
\]

its smoothed version satisfies the exact decomposition

\[
K_{T,d}:=S_d\circ H_{T,d}=I-c_TB_d+S_d\circ R_{T,d},
\]

and hence

\[
\|K_{T,d}-I\|
\le |c_T|\bigl(4\log\log d+O(1)\bigr)+\|R_{T,d}\|.
\tag{23}
\]

If \(|c_T|=O(1/\log T)\), \(d\le T^\theta\) for a fixed \(\theta>0\), and the actual residual estimate gives \(\|R_{T,d}\|\to0\) in that support range, then

\[
\|K_{T,d}-I\|
=O\!\left(\frac{\log\log T}{\log T}\right)+o(1)\longrightarrow0.
\tag{24}
\]

The checked actual provider in
[LandauHilbertSchmidtResidual.lean](../Analysis/LandauHilbertSchmidtResidual.lean)
supplies the residual premise whenever d^3/((T+3)*log(T+3))->0, including
 d=O(T^(1/3)*log(T)^b), b<1/3. The leading budget forces
log(log d)=O(log(log T)), so (23) also proves the smoothed frame throughout
that entire regime. This combined actual application is a paper proof;
the actual Fourier and sharp arithmetic specializations are not Lean declarations. The arithmetic theorem itself is unconditional. It does not prove the Landau residual provider, a zero-density specialization, the hyperbolic-form lower bound, an unsmoothed lower bound, or a transfer to the physical Pareto Gram matrix.

## 6. Primary references and proof provenance

The elementary divisor identity (6) and the estimate
\(\sum_{q\le x}\Lambda(q)/q=\log x+O(1)\) are standard: see Todd Cochrane, *Math 706: Theory of Numbers*, Kansas State University, Spring 2019, Lemma 11.4.2 and Theorem 11.4.2, Section 11.4:

<https://math.ksu.edu/~cochrane/m706/m706s19/m706s19notes.pdf>.

The standard von Mangoldt Dirichlet series is independently recorded in NIST DLMF, equation 27.4.12:

<https://dlmf.nist.gov/27.4.E12>.

No Dirichlet-series estimate is needed here. Sections 2–4 provide a self-contained elementary derivation with deliberately coarse constants. The new operator conclusion is obtained from the exact split (10), the complete divisor budget in weighted Cauchy–Schwarz (12), and the variable-length exponent-box construction (15)–(20). This document does not assert novelty relative to the full operator-theory literature.
