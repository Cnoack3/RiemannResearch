# Unconditional arithmetic lower bounds and exact zero-window exponents for the Mellin DPP

## Status and normalization

These are rigorous paper proofs from the existing Mellin projection DPP construction. They are not claimed to be Lean-verified here. They do not assume RH, simplicity of any zero, random-matrix conjectures, or an inverse-Gram growth estimate. They concern the Mellin-frequency DPP already constructed in `RiemannResearch/RH/MellinProjectionDPP.lean`; the sampled frequencies are not asserted to be zeta zeros or samplewise Mellin transforms of another point process.

Use cutoff notation

\[
V_N=\operatorname{span}\{g_2,\ldots,g_N\},\qquad N\ge2,
\]

so the repository's rank parameter is \(n=N-1\). Put

\[
s(t)=\tfrac12+it,\quad E(t)=\frac{\zeta(s(t))}{s(t)},\quad
v_d(t)=d^{-1}-d^{-s(t)},\quad d\ge2,
\]

and let \(G_N\) be the full Pareto Gram matrix of these atoms. Relative to \(\mu(dt)=dt/(2\pi)\), the existing kernel is

\[
K_N(t,u)=E(t)\overline{E(u)}\,v_N(t)^T G_N^{-1}\overline{v_N(u)}.
\]

Its \(k\)-point correlation density is

\[
\rho_{N,k}(t_1,\ldots,t_k)=\det[K_N(t_i,t_j)]_{i,j=1}^k.
\]

This follows directly from the existing rank-\(N-1\) determinant density: integrate out \(N-1-k\) coordinates using orthonormality and determinant expansion. Thus

\[
\mathbb E\binom{X_N(I)}k=\frac1{k!}\int_{I^k}\rho_{N,k}(\mathbf t)\,d\mu^k(\mathbf t).
\]

Here \(X_N(I)\) counts sampled Mellin frequencies in \(I\).

## 1. Global dimension-independent determinant lower bound

For \(k\ge1\), define the fixed \(k\times k\) positive definite matrix

\[
D_k=(\langle g_{2^j},g_{2^\ell}\rangle_P)_{j,\ell=1}^k.
\]

For every cutoff \(N\ge2^k\) and all real \(t_1,\ldots,t_k\), set \(q_i=2^{-s(t_i)}\). Then

\[
\boxed{
\rho_{N,k}(\mathbf t)\ge
\frac1{\det D_k}
\prod_{i=1}^k\left|\frac{\zeta(s(t_i))}{s(t_i)}\right|^2
\left|\tfrac12-q_i\right|^2
\prod_{i<j}|q_j-q_i|^2.}
\tag{1}
\]

The right side is independent of the large cutoff \(N\), and (1) is global in the frequencies.

**Proof.** The dyadic space \(W_k=\operatorname{span}\{g_2,g_4,\ldots,g_{2^k}\}\) is contained in \(V_N\). Choose a Pareto-orthonormal basis of \(W_k\) and extend it to one of \(V_N\). Under the actual Mellin isometry, this gives

\[
K_N=K_{W_k}+\sum_r f_r\otimes\overline{f_r}.
\]

Consequently every finite kernel matrix for \(K_N\) dominates the corresponding matrix for \(K_{W_k}\) in positive-semidefinite order. Determinants of positive-semidefinite Hermitian matrices are monotone in that order: this follows by conjugation when the smaller matrix is positive definite and then by continuity after adding \(\delta I\). Therefore \(\rho_{N,k}\ge\rho_{W_k,k}\).

Put \(a=1/2\). The dyadic symbols satisfy

\[
v_{2^j}(t_i)=a^j-q_i^j=(a-q_i)P_{j-1}(q_i),
\quad
P_{j-1}(z)=\sum_{r=0}^{j-1}a^{j-1-r}z^r.
\]

Each \(P_{j-1}\) is monic of degree \(j-1\). Hence the evaluation matrix \(A_{ij}=v_{2^j}(t_i)\) has

\[
\det A=\prod_i(a-q_i)\prod_{i<j}(q_j-q_i).
\]

The dyadic kernel matrix is

\[
\operatorname{diag}(E(t_i))\,A D_k^{-1}A^*\,
\operatorname{diag}(\overline{E(t_i)}).
\]

Taking its determinant proves (1). \(\square\)

For \(k=1\), the exact Pareto norm is \(\|g_2\|_P^2=\log2/4\): its defining sum is one quarter of the alternating harmonic series. Since \(|q|=2^{-1/2}\), (1) gives the particularly simple uniform result

\[
\boxed{
K_N(t,t)\ge\frac{4}{\log2}|\tfrac12-2^{-s(t)}|^2
\frac{|\zeta(s(t))|^2}{|s(t)|^2}
\ge\frac{3-2\sqrt2}{\log2}\frac{|\zeta(s(t))|^2}{|s(t)|^2}.}
\tag{2}
\]

The corresponding core diagonal is strictly positive at every real frequency. Thus its only intensity zeros are exactly the critical-line zeta zeros, already for \(N=2\).

## 2. A global probability lower bound with no cutoff loss

For every Borel set \(I\subseteq\mathbb R\), every \(k\ge1\), and every \(N\ge2^k\),

\[
\boxed{
\mathbb P\{X_N(I)\ge k\}\ge
\frac1{k!\det D_k}
\int_{I^k}
\prod_i |E(t_i)|^2|\tfrac12-q_i|^2
\prod_{i<j}|q_j-q_i|^2\,d\mu^k(\mathbf t).}
\tag{3}
\]

This is stronger than converting (1) to a probability by dividing by \(\binom{N-1}k\).

**Proof.** In an orthonormal basis of \(V_N\) whose first \(k\) elements span \(W_k\), form the compression matrix

\[
B_N(I)_{ab}=\int_I f_a(t)\overline{f_b(t)}\,d\mu(t).
\]

It is a Hermitian positive contraction. Expanding the existing DPP determinant density and integrating shows

\[
\mathbb E z^{X_N(I)}=\det(I+(z-1)B_N(I)).
\]

Thus \(X_N(I)\) has the distribution of a sum of independent Bernoulli variables whose parameters are the eigenvalues of \(B_N(I)\). The dyadic compression \(B_{W_k}(I)\) is its top-left principal block. By eigenvalue interlacing, its \(j\)-th decreasing eigenvalue is at most the \(j\)-th decreasing eigenvalue of \(B_N(I)\), \(1\le j\le k\). Coupling these Bernoulli variables through common uniform variables proves stochastic domination of the dyadic count by \(X_N(I)\). No spatial coupling theorem is needed.

The dyadic process has exactly \(k\) points. Consequently

\[
\mathbb P\{X_{W_k}(I)=k\}=\frac1{k!}\int_{I^k}\rho_{W_k,k}\,d\mu^k.
\]

Insert the determinant identity proved above. \(\square\)

The same argument proves stochastic monotonicity of each fixed-window count as \(N\) increases, even without constructing a joint coupling of the processes on all windows.

## 3. Exact local exponents at every actual critical-line zero

Let \(\rho=1/2+i\gamma\) be an actual zero of \(\zeta\) of multiplicity \(m\ge1\). Its multiplicity is finite, since \(\zeta\) is analytic and not identically zero near \(\rho\). Define

\[
a_\rho=\frac{i^m\zeta^{(m)}(\rho)}{m!\rho},
\qquad
E(\gamma+x)=a_\rho x^m+O(x^{m+1}).
\]

For \(0\le a,b\le k-1\), define the normalized core-jet Gram matrix

\[
J_{N,k}(\gamma)_{ab}
=\frac{v_N^{(a)}(\gamma)^T}{a!}G_N^{-1}
\frac{\overline{v_N^{(b)}(\gamma)}}{b!},
\qquad H_{N,k}(\gamma)=\det J_{N,k}(\gamma).
\]

For \(N\ge2^k\),

\[
\boxed{
H_{N,k}(\gamma)\ge
\frac{|\tfrac12-q(\gamma)|^{2k}(\log2)^{k(k-1)}
2^{-k(k-1)/2}}{\det D_k}>0.}
\tag{4}
\]

Indeed the same subspace comparison applies to all derivative evaluation functionals. For the dyadic normalized derivative matrix,

\[
\det\left[\frac{d^a}{dt^a}v_{2^j}(\gamma)\frac1{a!}\right]_{
\substack{0\le a\le k-1\\1\le j\le k}}
=(\tfrac12-q(\gamma))^k(q'(\gamma))^{k(k-1)/2}
\]

up to the harmless transpose convention. To see this, multiplication by the common factor \(1/2-q\) acts on normalized jets through a triangular matrix with that factor on its diagonal; composition of monic polynomials with \(q(t)\) acts triangularly with diagonal \((q')^a\). Finally \(q'=-i(\log2)q\) and \(|q|=2^{-1/2}\). This proves (4).

In particular, (4) has the frequency-uniform weaker lower bound obtained by replacing \(|1/2-q|\) with \(2^{-1/2}-1/2\). The jet Gram matrices increase in positive-semidefinite order when the cutoff increases, so \(H_{N,k}\) is nondecreasing wherever it is defined.

For fixed \(N,k,\rho\), uniformly for \(x_i\in[-1,1]\),

\[
\begin{split}
\rho_{N,k}(\gamma+\varepsilon x_1,\ldots,\gamma+\varepsilon x_k)
={}&|a_\rho|^{2k}H_{N,k}(\gamma)
\varepsilon^{2mk+k(k-1)}
\prod_i x_i^{2m}\prod_{i<j}(x_j-x_i)^2\\
&+O(\varepsilon^{2mk+k(k-1)+1}).
\end{split}
\tag{5}
\]

**Proof of (5).** Write the core as the Gram kernel of the finite-dimensional analytic feature vector \(G_N^{-1/2}v_N(t)\), with the conjugation convention adjusted if desired. Its exterior product at \(\gamma+\varepsilon x_i\) equals

\[
\varepsilon^{k(k-1)/2}\prod_{i<j}(x_j-x_i)
\,h_0\wedge\cdots\wedge h_{k-1}
+O(\varepsilon^{k(k-1)/2+1}),
\]

where \(h_a=G_N^{-1/2}v_N^{(a)}(\gamma)/a!\). Terms with repeated derivative indices vanish; the lowest surviving indices are exactly \(0,\ldots,k-1\), and their scalar determinant is the Vandermonde. Taking squared norms yields the core determinant asymptotic with coefficient \(H_{N,k}\). Multiplying the \(k\) envelope factors gives (5). Analyticity on a compact neighborhood provides the uniform error, including collisions and zero coordinates. \(\square\)

Set \(I_\varepsilon=[\gamma-\varepsilon,\gamma+\varepsilon]\). Then

\[
\boxed{
\mathbb P\{X_N(I_\varepsilon)\ge k\}
\sim C_{N,k}(\rho)\varepsilon^{k^2+2mk},
\quad \varepsilon\downarrow0,}
\tag{6}
\]

where the strictly positive constant is

\[
\boxed{
C_{N,k}(\rho)=
\frac{|a_\rho|^{2k}H_{N,k}(\gamma)}{(2\pi)^k}
\det\left[\frac{1+(-1)^{a+b}}{2m+a+b+1}\right]_{a,b=0}^{k-1}.}
\tag{7}
\]

The moment determinant in (7) is strictly positive: it is the Gram determinant of \(1,x,\ldots,x^{k-1}\) in \(L^2([-1,1],x^{2m}dx)\).

**Proof of (6)–(7).** Integrating (5) and including the Jacobian \(\varepsilon^k\) proves

\[
\mathbb E\binom{X_N(I_\varepsilon)}k
\sim\frac{|a_\rho|^{2k}H_{N,k}}{k!(2\pi)^k}
\varepsilon^{k^2+2mk}
\int_{[-1,1]^k}\prod_i x_i^{2m}\prod_{i<j}(x_j-x_i)^2\,d\mathbf x.
\]

Expanding the two Vandermonde determinants gives the integral as \(k!\) times the moment determinant in (7). The same exterior-product argument, without requiring nonzero leading coefficient, gives

\[
\mathbb E\binom{X_N(I_\varepsilon)}{k+1}
=O(\varepsilon^{(k+1)^2+2m(k+1)}).
\]

When the rank is less than \(k+1\), this term is zero. Since the total number of points is at most \(N-1\), the difference between \(\mathbb E\binom{X_N(I_\varepsilon)}k\) and \(\mathbb P\{X_N(I_\varepsilon)\ge k\}\) is bounded by a fixed multiple of the last factorial moment. Its exponent is strictly larger, proving (6). The same leading asymptotic holds for \(\mathbb P\{X_N(I_\varepsilon)=k\}\). \(\square\)

For a simple critical zero, the first cases are

\[
\mathbb P\{X_N(I_\varepsilon)\ge1\}
\sim\frac{|\zeta'(\rho)|^2H_{N,1}(\gamma)}{3\pi|\rho|^2}\varepsilon^3,
\]

\[
\mathbb P\{X_N(I_\varepsilon)\ge2\}
\sim\frac{|\zeta'(\rho)|^4H_{N,2}(\gamma)}{15\pi^2|\rho|^4}\varepsilon^8
\quad(N\ge4).
\]

For three points the exponent is \(15\), for four points it is \(24\), and in general it is \(k(k+2)\). A zero of multiplicity \(m\) has exponent \(k(k+2m)\).

A genuinely cutoff-uniform conclusion follows from (3), not by interchanging limits in (6). For each fixed \(\rho,k\), there are explicit positive leading dyadic constants \(C_{W_k,k}(\rho)\) from (7), and some \(\varepsilon_0>0\) independent of \(N\), such that

\[
\mathbb P\{X_N(I_\varepsilon)\ge k\}
\ge\tfrac12 C_{W_k,k}(\rho)\varepsilon^{k^2+2mk}
\quad(0<\varepsilon<\varepsilon_0,\ N\ge2^k).
\tag{8}
\]

The factor \(1/2\) can be replaced by any number strictly below one.

## 4. Universal conditional window shape

Condition on exactly \(k\) points lying in \(I_\varepsilon\), scale them by \(x=(t-\gamma)/\varepsilon\), and label the \(k\) points uniformly at random. Their joint distribution converges in total variation on \([-1,1]^k\) to the probability density

\[
\frac{\prod_i x_i^{2m}\prod_{i<j}(x_j-x_i)^2}
{\displaystyle\int_{[-1,1]^k}\prod_i y_i^{2m}\prod_{i<j}(y_j-y_i)^2\,d\mathbf y}.
\tag{9}
\]

For completeness, the finite-rank Janossy density on the window is the finite inclusion-exclusion sum

\[
j_{k,I}(\mathbf t)=\sum_{r=0}^{N-1-k}\frac{(-1)^r}{r!}
\int_{I^r}\rho_{N,k+r}(\mathbf t,\mathbf u)\,d\mu^r(\mathbf u).
\]

The integrated absolute contribution of \(r\ge1\), after scaling, is bounded by higher factorial moments and is \(o(\varepsilon^{k^2+2mk})\). Equation (5), its uniform remainder, and (6) therefore prove (9). Only the multiplicity \(m\) remains in this normalized limiting shape; the Gram matrix and zeta derivative cancel in the conditional normalization.

## 5. Removing the binary aliasing in strict positivity

The lower bound (1) vanishes when two frequencies differ by an integer multiple of \(2\pi/\log2\). This is a feature of the chosen dyadic comparison subspace, not necessarily a zero of the full determinant.

There is a finite-cutoff global strictness theorem: if \(N\ge2\cdot3^{k-1}\) and the real frequencies \(t_1,\ldots,t_k\) are pairwise distinct, then

\[
\boxed{\rho_{N,k}(t_1,\ldots,t_k)>0
\quad\Longleftrightarrow\quad
\zeta(\tfrac12+it_i)\ne0\text{ for every }i.}
\tag{10}
\]

**Proof.** Put \(x(t)=2^{-s(t)}\), \(y(t)=3^{-s(t)}\). The map \(t\mapsto(x(t),y(t))\) is injective. Equality for \(t,u\) would give \((t-u)\log2\in2\pi\mathbb Z\) and \((t-u)\log3\in2\pi\mathbb Z\); for \(t\ne u\), this would make \(\log2/\log3\) rational, contradicting unique factorization.

With \(v_1=0\), the legal symbol identities

\[
v_{2^{a+1}3^b}(t)-\tfrac12v_{2^a3^b}(t)
=(\tfrac12-x(t))x(t)^ay(t)^b
\]

hold for all nonnegative \(a,b\). For \(a+b\le k-1\), the largest atom index is at most \(2\cdot3^{k-1}\). Thus the full symbol span contains \((1/2-x)\) times every polynomial in \(x,y\) of total degree at most \(k-1\).

At any \(k\) distinct points of \(\mathbb C^2\), such polynomials interpolate arbitrary values: to produce a polynomial nonzero at one specified point and zero at the others, multiply \(k-1\) linear forms, each separating that point from one other point. Because \(|x(t)|=2^{-1/2}\ne1/2\), the factor \(1/2-x(t)\) never vanishes. Therefore the full symbol evaluation vectors have row rank \(k\). Their Gram matrix under the positive definite metric \(G_N^{-1}\) is strictly positive definite. Multiplication by the envelopes gives strict positivity if every zeta value is nonzero. If one zeta value is zero, the corresponding kernel row vanishes. \(\square\)

## What this establishes, and the remaining RH issue

The global bounds (1) and (3), their fixed-size Gram constants, the exact exponents (6), and the cutoff-uniform lower bound (8) are unconditional. They turn the Mellin factorization into quantitative statements about actual DPP probabilities and separate the zeta vanishing from purely arithmetic repulsion. If an imported theorem supplies verified simple critical-line zeros, it supplies concrete instances of the cubic/eighth-power hierarchy; no unproved simplicity statement is necessary for the general multiplicity theorem.

These results do not imply that off-line zeros are absent. They supply lower bounds and local structure, not the missing upper bound on the global projection defect or vanishing inverse-Gram correction. In particular, a critical-line zero of intensity is perfectly compatible with this absolutely continuous DPP. Fixed-cutoff asymptotic remainders need not be uniform as \(N\to\infty\), and no such interchange is used. The global comparison probability (3) does remain valid uniformly in \(N\).

## References and verification boundary

- Hough–Krishnapur–Peres–Virág, [Determinantal Processes and Independence](https://arxiv.org/abs/math/0503110), supports the standard determinantal counting and independent Bernoulli descriptions.
- Alpöge–Furman, [arXiv:2608.13637](https://arxiv.org/abs/2608.13637), and the pinned Zeta23 import supply actual arbitrarily high simple critical zeros. The local DPP arguments above are derived here from the project's kernel.
- `MellinDPPIntensity.lean` kernel-verifies (2) and the exact one-point zero set. The higher-point comparison, window probabilities, asymptotics, conditional law, and two-prime interpolation in this note are on-paper proofs.
