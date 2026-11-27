# Consecutive prime ratios, Haar independence and exact gap recovery

Enumerate the primes as $p_0=2,p_1=3,\ldots$. Set $X_k(t)=e^{it\log p_k}$ and $Y_k(x)=x_k/x_{k+1}$ for $x\in\mathbb T^{\mathbb N}$. A gap is a signed difference of two consecutive real ordinates. Repeated ordinates are retained as separate occurrences with a gap of zero.

## The infinite diagonal and the Jacobian

Starting with the prime Haar probability $H$ and its diagonal image $\Delta_*H$, map $(x,x)$ to $(Y_k(x))_{k\ge0}$. Lean proves the exact identity
$$
Y_*(\Delta_*H)=\bigotimes_{k\ge0}m_{\mathbb T}.
$$
Every coordinate is uniform and the entire indexed family is independent. The two ratios $x_p/x_q$ and $x_q/x_r$ therefore have product Haar law even though they share $x_q$. Two successive triple observations $(Y_k,Y_{k+1})$ and $(Y_{k+1},Y_{k+2})$ share the same random coordinate.

Two phase chains have the same ratios exactly when one is a common circle multiple of the other. Retaining $x_0$ makes the map bijective, with the inverse $x_{k+1}=x_k/Y_k$. For a prefix of $m$ ratios write $\delta_i=\theta_i-\theta_{i+1}$. The inverse in lifted angular coordinates is
$$
\theta_k=\theta_0-\sum_{j<k}\delta_j,\qquad
\det J_m=\det J_m^{-1}=(-1)^m,\qquad |\det J_m^{-1}|=1 .
$$
The finite matrices compose to the identity over the integers. The countable pushforward follows from uniqueness of normalized Haar probability for a continuous surjective group homomorphism. Each finite Jacobian has unit modulus. A phase multiplier acts separately on the Fourier coefficients.

The normalized empirical laws obtained by evaluating the ratios at actual positive zeta-zero occurrences converge weakly to the countable product. In particular every nonempty open cylinder is visited by actual zero phases. This is the prime flow with real height as its parameter and the product topology on phase sequences. FMZ on Compact Orbit refers to Ford, Meng and Zaharescu.

There are also two different assertions along the prime index. For product Haar almost every sequence has a dense coordinate-shift orbit. Blocks of each fixed positive length have independent product law, so an open block with probability $p>0$ is missed in the first $k$ disjoint trials with probability at most $(1-p)^k$. A countable topological basis suffices. At each fixed real height $t$, the prime number theorem gives $p_{j+1}/p_j\to1$, and consequently $Y_j(X(t))\to1$. The shift orbit of that particular sequence converges to the constant-one configuration and cannot be dense.

[RatioChainHaar](Analysis/RatioChainHaar.lean) · [ConsecutiveRatioOrbitLaw](Analysis/ConsecutiveRatioOrbitLaw.lean) · [ConsecutiveRatioShift](Analysis/ConsecutiveRatioShift.lean) · [Compact Orbit](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/current-proofs.html#three-prime-gap-tests) · [Ford, Meng and Zaharescu](https://arxiv.org/abs/1511.06814)

## Exact observations and the law of successive gaps

For a triple $p<q<r$ of consecutive primes put $a=\log(q/p)$, $b=\log(r/q)$ and
$$
E(t)=(e^{-iat},e^{-ibt}).
$$
The frequencies in $a\mathbb Z+b\mathbb Z$ are dense by prime factorization. If $E(t)=E(s)$, the characters $\omega\mapsto e^{i\omega t}$ and $\omega\mapsto e^{i\omega s}$ agree on that dense group and hence on all of $\mathbb R$. Taking $\omega=\pi/(t-s)$ proves $t=s$.

Between observations at heights $u,v$, coordinatewise division gives $E(v-u)$. Thus the measurements recover each labeled consecutive gap including ties. The proof applies to every consecutive triple and permits an independently specified triple index for each gap. For the corresponding map $\mathbf E:\mathbb R^{\mathbb N}\to(\mathbb T^2)^{\mathbb N}$, Lean proves it is a Borel embedding and
$$
\mathbf E_*\mu=\mathbf E_*\nu\quad\Longleftrightarrow\quad\mu=\nu
$$
for arbitrary Borel measures on labeled real sequences.

For one triple, the image $E(\mathbb R)$ is dense, Borel, and has product Haar measure zero. To see the last assertion, fix the first angle $z$. Its possible preimages are $-(\arg z+2\pi k)/a$, $k\in\mathbb Z$. The second coordinates above $z$ are countable and have circle Haar measure zero. Fubini proves the claim. The pushforward of any real gap law is consequently singular to product Haar. Empirical one-height angle laws can converge weakly to Haar while each actual observation retains an exact displacement. Replacing labeled observations by their static limiting law discards that information.

[ConsecutiveRatioGapDecoder](Analysis/ConsecutiveRatioGapDecoder.lean) · [ConsecutiveRatioGapLaw](Analysis/ConsecutiveRatioGapLaw.lean)

## Covariance, gauge and a uniform error estimate

Write $\chi_m(y)=\prod_j y_j^{m_j}$ for a finitely supported integer word. Its pullback has exponent $m_j-m_{j-1}$ at $p_j$, with $m_{-1}=0$. Literal word presentations with the same net exponents represent the same Fourier coefficient. With $\operatorname{Cov}(F,G)=\mathbb E[F\overline G]-\mathbb E[F]\overline{\mathbb E[G]}$, the exact Haar identity is
$$
\operatorname{Cov}(\chi_m,\chi_n)
=\mathbf1_{m=n}-\mathbf1_{m=0}\mathbf1_{n=0}.
$$
For grouped square-summable coefficients, real $c$ and arbitrary unit phases $g_m$, Parseval gives
$$
\left\|\sum_{m\ne0} c\,g_m a_m\chi_m\right\|_2^2
=c^2\sum_{m\ne0}|a_m|^2 .
$$

For each index $i$, choose its own consecutive triple and test frequencies $(\xi_i,\eta_i)$. Let $E_{T,i}$ be the error of its rounded three-prime sample relative to the actual two-adjacent-gap Fourier transform at microscopic scale $\log T/(2\pi)$. Let $w_i$ be the net word from the corresponding rounded orders. For distinct resulting net words, $T\ge0$, and phases $|g_i|=1$, the bound is
$$
\left\|\sum_{i:\,w_i\ne0} g_i a_i E_{T,i}\chi_{w_i}\right\|_2^2
=\sum_{i:\,w_i\ne0}|a_i E_{T,i}|^2
\le \left(\frac{(\log 2)T}{N(0,T]}\right)^2\sum_i |a_i|^2 .
$$
Lean uses totalized real division when $N(0,T]=0$. The prefactor tends to zero at increasing height. The bound allows the triple and the rounded Fourier word to vary with the test and the height, provided the net words used at each height are distinct. The coefficients must be combined within a Fourier mode before Parseval is applied.

[ConsecutiveRatioCovariance](Analysis/ConsecutiveRatioCovariance.lean) · [ConsecutiveRatioGapEnergy](Analysis/ConsecutiveRatioGapEnergy.lean)

## Relation to the sine kernel and the physical pairs

For the prime probe the existing bulk calculation gives the limiting two-point determinant $1-\operatorname{sinc}^2(\pi h)$. A gauge $K(x,y)\mapsto g(x)K(x,y)g(y)^{-1}$ preserves each finite determinant. Wolfram independently gives $uz-vw$ for the gauged matrix with rows $(u,v)$ and $(w,z)$. The angular Jacobian above controls a different change of variables.

For the legal Pareto inverse-Gram model, write $Z(t)=\zeta(1/2+it)/(1/2+it)$ and let $A$ be the finite kernel core. The two-point determinant carries the factor $|Z(t)Z(u)|^2$ multiplying $A(t,t)A(u,u)-|A(t,u)|^2$. Identifying a local limiting law needs estimates on this core and its normalization. The repository's Hilbert–Pólya implication additionally requires a symmetric operator with spectral parameters covering every nontrivial zero. Matching each analytic order with an eigenspace of dimension one also gives simplicity. An idempotent Pareto projection has only $0$ and $1$ as possible eigenvalues.

Obtaining physical PCC still requires the normalized actual positive-gap counts to approach the integrated determinant at every fixed positive rational endpoint. For RH with all nontrivial zeros simple, the existing absolute collision criterion requires $\sum_y m_T(y)^2-N_T<2$ at arbitrarily large heights. One-height Haar convergence and the coefficient reconstruction bound here supply neither physical estimate.

[Prime and Mellin sine-kernel transfer](THEOREM_CATALOG_PRIME_BULK_KERNEL_TRANSFER.md) · [Compact FMZ tests and physical collision certificates](THEOREM_CATALOG_COMPACT_FMZ_FOURIER.md)
