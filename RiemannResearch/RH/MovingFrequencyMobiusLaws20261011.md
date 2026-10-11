# Moving-frequency laws for actual growing Dirichlet polynomials

Status: paper proofs from audited unconditional literature inputs; not yet Lean-verified. These are consequences of known estimates, not a claim of literature novelty or a proof of RH.

Primary input: Ford–Meng–Zaharescu, *Simultaneous distribution of the fractional parts of Riemann zeta zeros*, Lemmas 1–2, pp. 5–6, https://arxiv.org/pdf/1511.06814. All zeros are counted with multiplicity and their actual real ordinates are used. Neither lemma assumes RH. The asymptotic zero-counting law and fixed-character equidistribution are also unconditional.

## 1. A uniform finite quadratic law with arithmetic main term

Put L=log T and let 2≤Y≤exp(L/(50 log L)), with T sufficiently large. For arbitrary complex coefficients a_n, supported on integers 1≤n≤Y, define

\[
D_Y(t)=\sum_{n\le Y}a_n n^{it},\quad A_1=\sum_{n\le Y}|a_n|,\quad A_2=\sum_{n\le Y}|a_n|^2,
\]
\[
W_2=\sum_{n,m\le Y}|a_na_m|\log^2(n/m),\qquad
Q_Y(a)=\sum_{mp^k\le Y}\frac{\log p}{p^{k/2}}\Re(a_{mp^k}\overline{a_m}),
\]
where the last sum runs over m≥1, primes p, and k≥1. Then

\[
\boxed{\sum_{0<\gamma\le T}|D_Y(\gamma)|^2
=N(T)A_2-\frac T\pi Q_Y(a)+E(T,Y,a)}
\]
and, with an absolute implied constant,

\[
|E|\ll A_1^2\left[Y\log(2Y)+\sqrt Y\log^2(2YT)
+Y\log(2T)+\frac{T}{L^{10}}\right]+\frac TLW_2.
\tag{1}
\]

Proof. Expand the square exactly. The n=m terms are N(T)A_2. Pair n>m with its conjugate. At x=n/m, apply the two FMZ lemmas, keeping their complex nearest-prime-power main term. Exact resonance x=p^k contributes −T(log p)/(2π p^{k/2}); pairing gives the displayed −TQ_Y/π.

For a nonresonant ratio x=n/m, if q is a nearest prime power to x, then q≤2x: a power of two no greater than x, or q=2 for 1<x<2, supplies that elementary upper bound. Since n−qm is a nonzero integer,

\[
|\log(x/q)|\ge\frac{|n-qm|}{\max(n,qm)}\ge\frac1{2Y}.
\]

Thus the remaining signed complex main term has modulus O(Y log(2Y)); it is retained until this explicit nonresonance bound is justified. Also log(n/m)≥(n−m)/n≥1/Y, so the singular small-frequency part of the FMZ remainder is O(Y log(2T)). The other FMZ errors sum to the remaining terms in (1). No horizontal-coordinate term is deleted: FMZ Lemma 2 provides its unconditional estimate.

## 2. An exact weighted-dispersion identity improves the rate

For arbitrary finite real w_i,u_i,

\[
\sum_{i,j}w_iw_j(u_i-u_j)^2
=2\Bigl(\sum_iw_i\Bigr)\Bigl(\sum_iw_iu_i^2\Bigr)
-2\Bigl(\sum_iw_iu_i\Bigr)^2.
\tag{2}
\]

This is an algebraic equality, requiring no positivity hypotheses. It follows by expanding the square and factoring finite double sums. For nonnegative w_i its right-hand side is at most the first term; the subtracted square has been identified explicitly.

Suppose |a_n|≤n^(−σ), where 0≤σ<1 is fixed. Set w_n=|a_n| and u_n=log(Y/n). By decreasing-integrand comparisons,

\[
\sum_{n\le Y}n^{-\sigma}\le\int_0^Yx^{-\sigma}dx
=\frac{Y^{1-\sigma}}{1-\sigma},
\]
\[
\sum_{n\le Y}n^{-\sigma}\log^2(Y/n)
\le\int_0^Yx^{-\sigma}\log^2(Y/x)dx
=\frac{2Y^{1-\sigma}}{(1-\sigma)^3}.
\]

Therefore (2) gives

\[
A_1^2\le\frac{Y^{2-2\sigma}}{(1-\sigma)^2},\qquad
W_2\le\frac{4Y^{2-2\sigma}}{(1-\sigma)^4}.
\]

In particular,

\[
\boxed{|E|\ll_\sigma
\frac{T Y^{2-2\sigma}}{\log T}
+Y^{3-2\sigma}\log^2(2YT).}
\tag{3}
\]

This improves the crude frequency-supremum estimate by removing a spurious factor log²Y from its principal error.

## 3. The growing Möbius observable has a positive secondary correction

Take a_n=μ(n)n^(−σ), with 1/2≤σ<1 fixed. Nonzero products μ(mp^k)μ(m) force k=1 and p∤m, and then μ(mp)μ(m)=−μ(m)². Consequently

\[
Q_Y(a)=-\sum_{mp\le Y,\ p\nmid m}
\frac{\mu(m)^2\log p}{p^{\sigma+1/2}m^{2\sigma}}.
\]

For Y(T)=floor((log T)^b), with b>0 and b(2−2σ)<1, (3) yields the unconditional growing-family law

\[
\boxed{
\sum_{0<\gamma\le T}\left|\sum_{n\le Y(T)}\frac{\mu(n)}{n^{\sigma-i\gamma}}\right|^2
=N(T)\sum_{n\le Y(T)}\frac{\mu(n)^2}{n^{2\sigma}}
+\frac T\pi\sum_{mp\le Y(T),\ p\nmid m}
\frac{\mu(m)^2\log p}{p^{\sigma+1/2}m^{2\sigma}}+o(T).
}
\tag{4}
\]

The full finite diagonal is retained: replacing it by an infinite diagonal at the o(T) scale would require an additional rate and is not justified by mere summability.

For σ>1/2 the secondary sum converges to the finite positive quantity

\[
\frac{\zeta(2\sigma)}{\zeta(4\sigma)}
\sum_p\frac{\log p}{p^{\sigma+1/2}(1+p^{-2\sigma})}.
\]

This follows by absolute convergence and the squarefree Euler product with the prime p omitted. It involves ζ only in its half-plane of absolute convergence.

## 4. Full tail control and an unconditional growing-observable limiting law

Fix 1/2<σ<1, fixed coefficients |a_n|≤n^(−σ), and b>0 with b(2−2σ)<2. Let Y(T)=floor((log T)^b). For every fixed integer K≥0, apply (1)–(3) to the coefficients supported on K<n≤Y(T). The prime-power quadratic is uniformly bounded in Y:

\[
|Q_Y|\le\sum_{m\ge1}m^{-2\sigma}
\sum_{p,k\ge1}\frac{\log p}{p^{k(\sigma+1/2)}}<\infty.
\]

Since N(T) is asymptotic to T log T/(2π), (3) now gives

\[
\boxed{
\lim_{T\to\infty}\frac1{N(T)}\sum_{0<\gamma\le T}
\left|\sum_{K<n\le Y(T)}a_n n^{i\gamma}\right|^2
=\sum_{n>K}|a_n|^2.}
\tag{5}
\]

In particular the iterated limit as K→∞ is zero. This is control of the complete growing-polynomial tail, and is stronger than separately controlling every fixed Fourier mode.

Let Z_p be independent Haar unit-circle variables and Z(n)=product_p Z_p^(v_p(n)). Orthogonality gives L² convergence of Σ_n a_nZ(n). Fixed-prime phase equidistribution gives the limiting law of every fixed truncation. For bounded Lipschitz tests, Cauchy–Schwarz and (5) control the difference between a growing truncation and a fixed one. The identical Haar L² tail bound controls the random side. Let T→∞ first and K→∞ second. Hence the empirical law of

\[
\sum_{n\le Y(T)}a_n n^{i\gamma},\qquad 0<\gamma\le T,
\]

converges weakly to the law of Σ_na_nZ(n). For a_n=μ(n)n^(−σ), this is the L² random Möbius Dirichlet series, equivalently the random product product_p(1−Z_p/p^σ), understood as its L² limit.

## 5. A law in the space of analytic functions, with growing cutoff

There is also a compact-uniform consequence that directly sharpens the fixed-smoothed-observable baseline. Let H be the space of analytic functions on Re s>1/2, with uniform convergence on compact sets. For any fixed coefficients |c_n|≤1, take the growing analytic polynomials

\[
P_T(s;\gamma)=\sum_{n\le\lfloor(\log T)^2\rfloor}c_n n^{-s+i\gamma}.
\]

Their empirical laws, with 0<γ≤T sampled with multiplicity, converge weakly in H to the Haar-random analytic Dirichlet series

\[
P(s;Z)=\sum_{n\ge1}c_n Z(n)n^{-s}.
\tag{6}
\]

Proof of the additional analytic step. For each compact K in Re s>1/2, choose a bounded neighborhood U with compact closure in that half-plane and a fixed σ₀∈(1/2,1) below inf_(s∈U) Re s. The analytic mean-value inequality, or a finite disk cover, gives

\[
\sup_{s\in K}|f(s)|^2\le C_K\int_U|f(s)|^2\,dA(s).
\]

Apply this to the difference of the growing polynomial and its J-term truncation. The scalar bound above is uniform for s∈U, since |c_n n^(-s)|≤n^(-σ₀), and its probability-normalized remainder is O((log T)^(2−4σ₀))+o(1), which tends to zero. Consequently

\[
\limsup_{T\to\infty}\frac1{N(T)}\sum_{0<\gamma\le T}
\sup_{s\in K}|P_T(s;\gamma)-P_J(s;\gamma)|^2
\le C'_K\sum_{n>J}n^{-2\sigma_0}\longrightarrow0.
\]

The same inequality and Haar orthogonality prove that the random J-term polynomials are Cauchy in expected squared sup norm on each compact; these construct the H-valued limit in (6). More precisely, use a countable compact exhaustion to choose one subsequence converging almost surely uniformly on every compact. Its limit is analytic, and uniqueness of the mean-square limits gives convergence of the entire sequence in expected squared sup norm on each compact. This construction specifies the meaning of the random series without silently inferring almost-sure convergence of an arbitrary orthogonal series from square summability. Fixed J has a limiting law by prime-torus equidistribution. Using an exhaustion by compacts and the standard bounded metric for H, the preceding tails and the bounded-Lipschitz triangle inequality prove convergence of the growing laws.

Write Z(s) for the limit with c_n=1 and M(s) for the limit with c_n=μ(n), using the same Haar phases. Finite-prime products converge to these constructed analytic limits in compact-uniform mean square:

\[
Z(s)=\lim_{R\to\infty}\prod_{p\le R}(1-Z_p p^{-s})^{-1},\qquad
M(s)=\lim_{R\to\infty}\prod_{p\le R}(1-Z_p p^{-s}).
\]

Indeed, the first product has Dirichlet coefficient Z(n) when every prime divisor of n is at most R and zero otherwise; the second has coefficient μ(n)Z(n) with the same restriction. On a neighborhood with real part at least σ₀>1/2, the missing coefficients have squared sum bounded by Σ_n n^(−2σ₀), and each missing-coefficient indicator tends to zero. Haar orthogonality, dominated convergence, and the same analytic mean-value inequality prove the claimed convergence. The empty prime-divisor set for n=1 is always included.

For Re s>1, the two Dirichlet series converge absolutely, and complete multiplicativity of Z(n), together with Σ_(d|n) μ(d)=0 for n>1, gives Z(s)M(s)=1. Uniqueness of the constructed mean-square limits identifies them with those absolutely convergent functions there (first on a countable dense set, simultaneously almost surely). The identity theorem then yields

\[
\boxed{Z(s)M(s)=1\quad\text{for all Re }s>1/2,\quad\text{almost surely}.}
\tag{7}
\]

Thus both limiting random analytic functions are almost surely nowhere zero in this half-plane. This is a statement about Haar-random analytic functions.

This supplies an actual growing, unsmoothed family and proves its tightness. It does not prove that the family approximates actual shifted ζ or 1/ζ; the approximation bottleneck in Priority 3 remains precisely that identification.

## 6. Joint reciprocal compatibility of the growing observables

Set Y(T)=floor((log T)²) and, for each actual zero ordinate γ, define

\[
Z_T(s;\gamma)=\sum_{n\le Y(T)}n^{-s+i\gamma},\qquad
M_T(s;\gamma)=\sum_{n\le Y(T)}\mu(n)n^{-s+i\gamma}.
\]

The preceding proof applies jointly to any finite collection of coefficient sequences: every fixed truncation is a continuous function of the same finite prime torus, and the compact-uniform mean-square tail estimates control all coordinates. In particular, the empirical joint laws of (Z_T,M_T) converge weakly in H×H to the law of (Z,M).

There is a stronger quantitative-type conclusion than convergence in distribution to reciprocal limits: for every compact K contained in Re s>1/2,

\[
\boxed{\lim_{T\to\infty}\frac1{N(T)}\sum_{0<\gamma\le T}
\sup_{s\in K}|Z_T(s;\gamma)M_T(s;\gamma)-1|=0.}
\tag{8}
\]

This is convergence of the product to 1 in empirical mean, uniformly on each fixed compact. No rate in T is asserted in (8).

Proof. Write ||f||_K=sup_(s∈K)|f(s)| and E_T for averaging over the ordinates 0<γ≤T with multiplicity. The same mean-value inequality and scalar estimates show

\[
\limsup_{T\to\infty}E_T\|Z_T\|_K^2<\infty,\qquad
\limsup_{T\to\infty}E_T\|M_T\|_K^2<\infty.
\]

For the fixed integer truncations Z_J and M_J, put

\[
\delta_J^2=C_K'\sum_{n>J}n^{-2\sigma_0},
\]

enlarging C_K' if necessary. The empirical limsup of each squared truncation tail, and the corresponding expected squared Haar tail, are bounded by δ_J². The Haar second moments of ||Z_J||_K and ||M_J||_K are bounded independently of J, by the same area estimate. Fixed-prime equidistribution transfers these fixed-J second moments and the fixed-J continuous quantity ||Z_JM_J−1||_K to their Haar expectations.

The exact decomposition

\[
Z_TM_T-1=(Z_T-Z_J)M_T+Z_J(M_T-M_J)+(Z_JM_J-1)
\]

and Cauchy–Schwarz therefore give

\[
\limsup_{T\to\infty}E_T\|Z_TM_T-1\|_K
\le C_K\delta_J+\mathbb E\|Z_JM_J-1\|_K.
\]

On the Haar side, (7) and another exact decomposition give

\[
Z_JM_J-1=(Z_J-Z)M_J+Z(M_J-M),
\]

so Cauchy–Schwarz bounds the final expectation by C_K δ_J. Let J→∞. This proves (8).

Markov's inequality gives the explicit consequence that, for every ε>0,

\[
\frac{\#\{0<\gamma\le T:\sup_{s\in K}|Z_T(s;\gamma)M_T(s;\gamma)-1|>\varepsilon\}}{N(T)}\longrightarrow0.
\tag{9}
\]

The count includes multiplicity. In particular, the proportion of ordinates for which either Z_T or M_T has a zero anywhere in K tends to zero: such a zero forces the product error to be at least 1. The conclusions concern these specific growing polynomials. They do not identify Z_T(s;γ) with ζ(s−iγ), nor M_T(s;γ) with 1/ζ(s−iγ).

## 7. Precise boundary of what has been proved

These theorems control actual growing arithmetic observables sampled at all actual zero ordinates, their full internal truncation tails, and the reciprocal compatibility of the paired growing polynomials. They do not identify the growing Möbius polynomial with 1/ζ(s−iγ) in 1/2<Re s<1. Proving that analytic approximation without RH remains a separate problem. They do not force the Balazard–Saias–Yor positive defect to vanish or establish Bagchi self-recurrence. No claim of an RH proof or a groundbreaking new literature theorem is warranted.

Lean candidates: (2); weighted finite-error summation; the exact finite quadratic/prime-resonance reduction; Möbius prime-multiplication sign; and the bounded-Lipschitz three-term approximation inequality. Imported analytic estimates should remain explicit hypotheses until their proofs are formalized.
