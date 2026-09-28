# Exact Dyson connection, sine universality, and an operator obstruction

Date: 2026-09-28. Status: complete on-paper derivation; not Lean verified.

## 1. Normalization and dyadic subspace

Put $a=\log2$, $r=2^{-1/2}$, $s(t)=1/2+it$, and
\[
F_d(t)=\frac{\zeta(s(t))}{s(t)}(d^{-1}-d^{-s(t)}).
\]
The Mellin transform is normalized so that its target measure is $dt/(2\pi)$.
Let $D_k$ be the Gram matrix of $g_2,g_4,\ldots,g_{2^k}$, equivalently of
$F_2,F_4,\ldots,F_{2^k}$. We consider the rank-$k$ projection DPP belonging
to precisely this dyadic subspace. This is a subspace of the full residue
space for $N\ge2^k$, but its DPP is not being identified with the full DPP.

Writing $q(t)=r e^{-iat}$ gives
\[
F_{2^j}(t)=F_2(t)P_{j-1}(q(t)),\qquad
P_{j-1}(q)=\sum_{\ell=0}^{j-1}2^{-(j-1-\ell)}q^\ell.
\]
Each $P_{j-1}$ is monic. Thus the symmetric density of the $k$ labeled
points, relative to $\prod_i dt_i/(2\pi)$, is exactly
\[
\frac{1}{k!\det D_k}\prod_i|F_2(t_i)|^2
\prod_{i<j}|q(t_j)-q(t_i)|^2.
\tag{1}
\]
The only determinant step is the monic-polynomial Vandermonde identity.

## 2. Exact folding to a circular Dyson gas

Fold each frequency by $\theta=at\pmod{2\pi}$. Define
\[
w(\theta)=\frac1a\sum_{m\in\mathbb Z}
\left|F_2\left(\frac{\theta+2\pi m}{a}\right)\right|^2.
\tag{2}
\]
Initially this expression is defined almost everywhere by Tonelli. The
analysis below produces a positive real-analytic representative, so all
densities and kernels can use that representative without ambiguity.
Let $T_k(w)$ be the Gram matrix of $1,z,\ldots,z^{k-1}$ for
$w(\theta)d\theta/(2\pi)$, with $z=e^{-i\theta}$. Then
\[
\det D_k=r^{k(k-1)}\det T_k(w).
\tag{3}
\]
This follows either by the triangular change of polynomial basis, whose
diagonal is $1,r,\ldots,r^{k-1}$, or by integrating (1).

The folded joint density, relative to $\prod_i d\theta_i/(2\pi)$, is
\[
\boxed{\quad
\frac{1}{k!\det T_k(w)}\prod_iw(\theta_i)
\prod_{i<j}|e^{i\theta_j}-e^{i\theta_i}|^2.\quad}
\tag{4}
\]
This is an exact circular orthogonal-polynomial ensemble, equivalently a
circular log gas with Dyson index $\beta=2$ and one-body potential
$V=-\log w$. It is not merely a resemblance in the two-point function.
By the unitary Weyl integration formula, it is also exactly the
eigenangle law of a random unitary matrix whose density relative to Haar
measure is proportional to $\prod_i w(\theta_i)$. After the Cayley change
$x_i=\cot(\theta_i/2)$, its random Hermitian-matrix eigenvalue density is
proportional to
\[
\prod_i\frac{w(2\operatorname{arccot}x_i)}{(1+x_i^2)^k}
\prod_{i<j}(x_i-x_j)^2.
\]
This is an explicit finite-dimensional random-matrix realization. Its
random eigenvalues are not being identified with zeta zeros.

Conversely, conditional on folded locations, the integer lifts are
independent, with
\[
\Pr(M_i=m\mid\theta_i)
=\frac{|F_2((\theta_i+2\pi m)/a)|^2}{a\,w(\theta_i)}.
\tag{5}
\]
This recovers the original line ensemble from the circular ensemble.

## 3. The alias weight is explicitly bounded away from zero

Define on the logarithmic physical coordinate
\[
\phi(y)=\frac12e^{-y/2}
\mathbf1_{\{\lfloor e^y\rfloor\text{ odd}\}}\mathbf1_{\{y\ge0\}}.
\]
Since $g_2(\lfloor x\rfloor)=\frac12\mathbf1_{\{\lfloor x\rfloor\text{ odd}\}}$,
its Fourier transform is $F_2(t)=\int_0^\infty\phi(y)e^{-ity}\,dy$.
This integral identity holds initially in an absolutely convergent Mellin
half-plane and then throughout $\Re s>0$ by analytic continuation of the
bounded physical function, including $\Re s=1/2$.

For $0\le y<a$ define
$Z_\theta(y)=\sum_{n\ge0}\phi(y+na)e^{-in\theta}$.
The sum converges uniformly in $y,\theta$ by its geometric majorant.
Fourier-series Parseval on the interval $[0,a)$ yields
\[
w(\theta)=\int_0^a|Z_\theta(y)|^2\,dy
=\frac14\int_1^2\left|
\sum_{n\ge0}r^n\varepsilon_n(x)e^{-in\theta}\right|^2\frac{dx}{x^2},
\qquad \varepsilon_n(x)=\lfloor2^n x\rfloor\bmod2.
\tag{6}
\]
In particular this equality furnishes a continuous representative of (2).

For $1\le x<33/32$, one has $\varepsilon_0(x)=1$ and
$\varepsilon_1(x)=\cdots=\varepsilon_5(x)=0$. Bounding the remaining
geometric tail gives, uniformly in $\theta$,
\[
\left|\sum_{n\ge0}r^n\varepsilon_n(x)e^{-in\theta}\right|
\ge1-\frac{r^6}{1-r}
=\frac{6-\sqrt2}{8}>\frac12.
\]
Since $\int_1^{33/32}x^{-2}dx=1/33$, this proves
\[
\boxed{\qquad\frac1{528}\le w(\theta)
\le\frac{3+2\sqrt2}{4}\qquad(\theta\in\mathbb R).\qquad}
\tag{7}
\]
The upper bound follows directly from $\varepsilon_n\le1$ and
$\int_1^2x^{-2}dx=1/2$.

The Fourier coefficients also have an exponential bound. For $m\ge0$,
up to the immaterial Fourier-sign convention,
\[
\widehat w(m)=\int_0^\infty\phi(y+ma)\phi(y)\,dy,
\qquad
|\widehat w(m)|\le\frac14r^m.
\tag{8}
\]
Hence $w$ extends holomorphically to $|\Im\theta|<a/2$ and is strictly
positive and real analytic on the circle. This proof uses neither RH nor
knowledge of any particular zeta zero. In particular no folded angle is
a forbidden site, even though each unfurled critical zero is a zero of
the frequency density.

There is also a dimension-independent inverse-Gram consequence. Define
the normalized arithmetic dyadic differences
\[
a_n=2^{n/2}\left(g_{2^{n+1}}-\tfrac12g_{2^n}\right),\quad n\ge0,
\qquad g_1:=0.
\]
The Mellin transform of $a_n$ is $F_2(t)e^{-inat}$, so the Gram matrix of
$a_0,\ldots,a_{k-1}$ is exactly $T_k(w)$. From (7), for every finite
coefficient vector,
\[
\boxed{\quad
\frac1{528}\sum_n|c_n|^2
\le\left\|\sum_nc_na_n\right\|_H^2
\le\frac{3+2\sqrt2}{4}\sum_n|c_n|^2.
\quad}
\tag{8a}
\]
In particular $\|T_k(w)^{-1}\|_{\ell^2\to\ell^2}\le528$ uniformly in
$k$. This is a Riesz-sequence theorem for this explicit normalized
dyadic difference basis; it is not a bound on the full residue Gram
inverse, or on the inverse in the unnormalized $g_{2^j}$ coordinates.

The geometric separation of dyadic frequencies is essential. For every
integer $d\ge1$ define
\[
h_d=\sqrt d\left(g_{2d}-\tfrac12g_d\right).
\]
Its Mellin transform is $F_2(t)e^{-it\log d}$, so
$\|h_d\|_H^2=\|g_2\|_H^2=\log2/4$. Nevertheless,
\[
\|h_{d+1}-h_d\|_H^2
=\int_{\mathbb R}|F_2(t)|^2
\left|e^{-it\log(1+1/d)}-1\right|^2\frac{dt}{2\pi}\longrightarrow0.
\tag{8b}
\]
Dominated convergence applies with majorant $4|F_2|^2$. Since the two
nonzero coefficients $1,-1$ have squared $\ell^2$ norm two, no positive
Riesz lower bound holds uniformly over this all-integer dilation family.
Even the union of two distinct prime-power dilation families fails: the
irrationality of $\log p/\log q$ and elementary rational approximation
give pairs with $|n\log p-m\log q|\to0$, and the same proof applies.
This explains a precise limitation when adding missing arithmetic scales.

There is also a strictly positive obstruction to proving RH with only
the dyadic span. Every dyadic atom satisfies
\[
g_{2^j}(3)=g_{2^j}(1)+g_{2^j}(2)\qquad(j\ge1).
\]
For $j=1$ this is $1/2=1/2+0$, and for $j\ge2$ it is
$3/2^j=1/2^j+2/2^j$. The bounded coordinate functional
$\ell(f)=f(3)-f(1)-f(2)$ therefore vanishes on the closed dyadic span.
In the Pareto norm its Riesz vector is
$u=(-2,-6,12,0,\ldots)$ and $\|u\|_H^2=20$. Since $\ell(\mathbf1)=-1$,
Cauchy–Schwarz proves
\[
\boxed{\qquad
\inf_{f\in\overline{\operatorname{span}\{g_{2^j}:j\ge1\}}}
\|\mathbf1-f\|_H^2\ge\frac1{20}.
\qquad}
\tag{8c}
\]
For the unit vector at the first physical site, $e_1=\sqrt2\,mathbf1_{\{1\}}$,
one has $|\ell(e_1)|^2=2$. Therefore every dyadic physical projection DPP
has first-site vacancy at least $1/10$. Exact Dyson sine universality
thus coexists here with a quantitative failure of arithmetic saturation.
These are lower bounds, not assertions that either defect equals the
displayed constant.

## 4. A self-contained sine-kernel limit

Here is a direct strong-asymptotic proof, included to avoid importing an
unverified universality hypothesis. Let $p_n(z)$ be the orthonormal
polynomial of degree $n$ for $w(\theta)d\theta/(2\pi)$, with positive
leading coefficient. Since $w>0$ is analytic, $\log w$ is analytic in a
smaller annulus. Factoring its absolutely convergent Fourier series gives
an analytic nonvanishing function $D$ on $|z|<R$ for some $R>1$ such that
$D(0)>0$ and $|D(z)|^2=w$ on $|z|=1$. Specifically, if
$\log w=\sum_{j\in\mathbb Z}\ell_jz^j$, use
$D(z)=\exp(\ell_0/2+\sum_{j\ge1}\ell_jz^j)$.

On the circle put $q_n(z)=z^n/\overline{D(z)}$. Its weighted norm is one,
and for $0\le j<n$,
\[
\langle q_n,z^j\rangle_w
=\int z^{n-j}D(z)\frac{d\theta}{2\pi}=0.
\]
Choose $1<R_1<R$. Expanding $1/D(z)=\sum_{j\ge0}b_jz^j$ and truncating
the Laurent representation of $q_n$ gives a polynomial
$h_n(z)=\sum_{j=0}^n\overline{b_j}z^{n-j}$ with
$\|h_n-q_n\|_\infty=O(R_1^{-n})$ and positive leading coefficient $b_0$.
Project $h_n$ orthogonally off the lower-degree polynomials. Since $q_n$
is already orthogonal to those polynomials, the projection removed has
weighted norm $O(R_1^{-n})$. For every degree-$(n-1)$ polynomial $P$,
\[
\|P\|_\infty\le\sqrt n\|P\|_{L^2(d\theta/(2\pi))}
\le\sqrt{n/\inf w}\|P\|_w.
\]
After normalizing the remaining polynomial (whose norm is
$1+O(R_1^{-n})$), uniqueness gives
\[
p_n(z)=\frac{z^n}{\overline{D(z)}}
+O(\sqrt{n+1}\,R_1^{-n})\qquad(|z|=1),
\tag{9}
\]
uniformly on the circle.

The folded correlation kernel relative to $d\theta/(2\pi)$ is
\[
\mathcal K_k(\theta,\varphi)
=\sqrt{w(\theta)w(\varphi)}
\sum_{n=0}^{k-1}p_n(e^{-i\theta})\overline{p_n(e^{-i\varphi})}.
\]
Put $\chi(\theta)=D(e^{-i\theta})/|D(e^{-i\theta})|$. Summing (9), whose
error is summable over $n$, proves the uniform estimate
\[
\boxed{\quad
\mathcal K_k(\theta,\varphi)
=\chi(\theta)\overline{\chi(\varphi)}
\sum_{n=0}^{k-1}e^{-in(\theta-\varphi)}+O(1).
\quad}
\tag{10}
\]
The constant in $O(1)$ is independent of $k,\theta,\varphi$. In particular,
$\mathcal K_k(\theta,\theta)=k+O(1)$ uniformly.

For any fixed center $\theta_0$, put
$\theta_k(u)=\theta_0+2\pi u/k$. The transformed kernel relative to $du$
is $k^{-1}\mathcal K_k(\theta_k(u),\theta_k(v))$. Uniformly for bounded
$u,v$, it converges to
\[
e^{-i\pi(u-v)}\frac{\sin\pi(u-v)}{\pi(u-v)}.
\tag{11}
\]
The phase is a gauge and cancels from every determinant. Therefore for
every fixed $j$, the rescaled $j$-point correlation functions converge,
uniformly on compact coordinate sets, to
\[
\boxed{\quad
\det\left[\frac{\sin\pi(u_i-u_\ell)}{\pi(u_i-u_\ell)}
\right]_{i,\ell=1}^j.\quad}
\tag{12}
\]
This is unconditional bulk sine-kernel universality for the folded dyadic
Mellin DPP. It is not a statement about the correlations of the actual
Riemann zeros, nor about universality of the full nondyadic residue DPP.

## 5. Dyson dynamics and what it determines

For the positive smooth density (4), its logarithmic derivative in a
noncollision chamber is
\[
\partial_{\theta_i}\log p
=\frac{w'(\theta_i)}{w(\theta_i)}
+\sum_{j\ne i}\cot\frac{\theta_i-\theta_j}{2}.
\]
Consequently the differential operator
\[
\mathcal L=\sum_i\partial_i^2+
\sum_i\left(\frac{w'(\theta_i)}{w(\theta_i)}+
\sum_{j\ne i}\cot\frac{\theta_i-\theta_j}{2}\right)\partial_i
\tag{13}
\]
is symmetric for (4) on smooth test functions supported away from
collisions, by integration by parts. With the convention of Brownian
noise $\sqrt2\,dB_i$, (13) is circular Dyson drift at $\beta=2$, with the
additional smooth external drift $w'/w$. The invariant-density identity
is exact; no unproved global SDE construction is needed for it.

Dyson's original circular ensembles and Brownian-motion model are the
historical connection: F. J. Dyson, *Statistical Theory of the Energy
Levels of Complex Systems. I*, J. Math. Phys. 3 (1962), 140–156,
doi:10.1063/1.1703773; and *A Brownian-Motion Model for the Eigenvalues of
a Random Matrix*, J. Math. Phys. 3 (1962), 1191–1198,
doi:10.1063/1.1703862. The arithmetic formulas and the proofs above are
derived here, not attributed to those papers.

## 6. The canonical multiplication operator is not Hilbert–Polya

On $\mathscr H=L^2(w(\theta)d\theta/(2\pi))$, multiplication by
$z=e^{-i\theta}$ is a canonical unitary $U$. Bounds (7) show directly that
its spectrum is the entire unit circle and is purely absolutely
continuous. Its Cayley transform
\[
A=i(I+U)(I-U)^{-1}
\]
is multiplication by $\cot(\theta/2)$ on its maximal domain. It is
self-adjoint with full real, purely absolutely continuous spectrum and
has no eigenvalues. Thus this concrete operator, or its CMV matrix
representation in a Laurent-polynomial basis, is not a Hilbert–Polya
operator with discrete eigenvalues equal to zero ordinates.

The DPP itself gives a projection, not distinguished energy eigenvalues.
On the closure of the union of its occupied polynomial subspaces, one
may assign any strictly increasing real sequence tending to infinity to
the corresponding orthonormal polynomial basis and obtain the same
family of low-energy fermionic projections. That closure is a proper
Hardy-type subspace of the full $L^2(w)$ space: multiplication by $z$ on
it is an isometry, whereas the full-space multiplication operator above
is unitary.

There is a sharper obstruction on this occupied closure. Multiplication
by the Szegő factor $D$ maps it unitarily onto the usual $H^2$ space and
intertwines multiplication by $z$ with the unilateral shift $S$. Its
Cayley operator
\[
B=i(I+S)(I-S)^{-1},\qquad\operatorname{Dom}B=\operatorname{ran}(I-S),
\]
is densely defined and symmetric. Indeed the range of $I-S$ is dense
because $S^*$ has no eigenvector at $1$, and the usual Cayley inner-product
identity proves symmetry. More explicitly,
\[
\operatorname{ran}(B+i)=H^2,\qquad
\operatorname{ran}(B-i)=\operatorname{ran}S.
\]
As the range of $S$ has codimension one, the deficiency indices
$(\dim\ker(B^*-i),\dim\ker(B^*+i))$ are $(0,1)$. Thus $B$ has no
self-adjoint extension on this same occupied Hilbert space. The operator
is closed: $(B+i)^{-1}=(I-S)/(2i)$ is everywhere defined and bounded, so
the graph of $B+i$, and hence that of $B$, is closed. Enlarging
to the canonical bilateral multiplication model gives the self-adjoint
operator $A$ above, but its spectrum is purely absolutely continuous.

The spectral nonuniqueness of the projection family, together with this
deficiency obstruction for its direct shift, is the exact gap between
establishing a Dyson law and constructing a Hilbert–Polya Hamiltonian.

Finally, multiplication of all orbitals by the common factor $F_2(t)$
makes every critical zeta zero a node of the unfurled DPP intensity.
Such nodal exclusion is not a spectral eigenvalue condition. Folding
even removes these nodes by (7). A future Hilbert–Polya construction must
retain extra arithmetic/phase information and prove an independent
spectral determinant or equivalent exact zero correspondence.
