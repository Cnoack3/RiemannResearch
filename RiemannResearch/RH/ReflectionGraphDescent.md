# Exact sequences and quotient descent for mixed reflection

Let $H=L^2(P)$, where $P(n)=1/[n(n+1)]$ for $n\ge1$. Let $M$ be the closed mixed packet span, $V$ the closed legal span, $L=\mathbb R\mathbf1$, and $S$ the anchored backward shift. Write $q_K:H\to H/K$ for the quotient by a closed subspace. The closed graph of periodic reflection on mixed packets is the linear relation
\[
\Gamma=\{(m,l-Sm):m\in M,\ l\in L\}.
\]
Its legal pullback is $\Gamma_V=\Gamma\cap(M\times V)$. All the following Hilbert quotients use closed denominators.

## A diagram of short exact sequences

Put $W=V+L$, a closed subspace because $L$ is finite-dimensional. The maps below give a morphism of short exact sequences.

| Position | Upper row | Lower row | Vertical arrow |
|---|---|---|---|
| Left | $L$ | $(V+L)/V$ | $l\mapsto[l]_V$ |
| Middle | $\Gamma$ | $H/V$ | $D(m,y)=[y]_V$ |
| Right | $M$ | $H/(V+L)$ | $m\mapsto[-Sm]_{V+L}$ |

The upper arrows send $l\mapsto(0,l)$ and $(m,y)\mapsto m$. The bounded section is $m\mapsto(m,-Sm)$. The lower arrows are the natural inclusion and quotient. Commutativity follows from $[l-Sm]_{V+L}=[-Sm]_{V+L}$. Apply the snake lemma to the underlying real vector spaces. Both rows split by bounded maps. The left vertical arrow is surjective, so the new connecting homomorphism from the right kernel to the left cokernel vanishes. Taking kernels gives
\[
0\longrightarrow L\cap V\longrightarrow\Gamma_V\longrightarrow
M_0\longrightarrow0,\qquad M_0=\{m\in M:Sm\in V+L\}.
\]
For a direct lift, write $Sm=v+l$ with $v\in V$ and $l\in L$. Then $(m,-v)\in\Gamma_V$. All legal lifts at that $m$ differ by a vertical element of $L\cap V$.

If $\mathbf1\notin V$, put $e=P_{V^\perp}\mathbf1$. For $m\in M_0$ the unique legal reflected coordinate is
\[
y=-Sm+\frac{\langle Sm,e\rangle}{\|e\|^2}\mathbf1.
\]
If $\mathbf1\in V$, the repository's density theorem gives $V=H$ and hence $\Gamma_V=\Gamma$.

The vertical generator recovers the earlier centered snake boundary, including its sign. With the established identification $\Phi:\mathbf1^\perp/M\to H/V$, one has $D(0,a\mathbf1)=-\Phi(\partial a)=a[\mathbf1]_V$. Thus the vanishing of the older boundary on $1$ is exactly the remaining legal-lift test for the vertical generator. The new diagram's connecting arrow above has zero target. [Graph and exactness](PacketReflectionQuotients.lean) · [Earlier boundary transport](CenteredMeanQuotients.lean)

## Quotients inside the graph

For $z=(m,y)\in\Gamma$ set $r_z=y-P_Vy$. Let $C_N$ consist of graph points for which $r_z(1),\ldots,r_z(N)$ all vanish. These are closed subspaces with
\[
C_{N+1}\subseteq C_N,\qquad \bigcap_{N\ge0} C_N=\Gamma_V.
\]
Each quotient $\Gamma/C_N$ identifies algebraically with the range of the first $N$ residual coordinates in $\mathbb R^N$. Forgetting the last coordinate induces $\Gamma/C_{N+1}\to\Gamma/C_N$. The map
\[
\Gamma/\Gamma_V\longrightarrow\varprojlim_N\Gamma/C_N
\]
is injective. Its image can be characterized by the cost of lifting the finite classes. Equip the graph with its split Hilbert norm
\[
\|(m,y)\|_{\Gamma}^2=\|m\|_P^2+\|y+Sm\|_P^2.
\]
A compatible family of finite residual profiles comes from a graph point of norm at most $C$ exactly when every finite head admits a graph lift of norm at most the same $C$. Indeed the finite constraints define nested weakly closed affine subsets of the weakly compact graph ball. Equivalently, a compatible family of quotient classes comes from $\Gamma/\Gamma_V$ precisely when its finite quotient norms are uniformly bounded. The least lift norm is their supremum. Each finite quotient has a least-norm representative because its denominator is closed.

For a fixed graph point, the squared obstruction is exactly
\[
\|Dz\|^2=\sum_{n\ge1}\frac{|r_z(n)|^2}{n(n+1)}.
\]
The tests involve the complete legal projection $P_V$. Matching the unprojected coordinates of $y$ through $N$ is a different problem. [Head quotients, compatibility and the exact sum](PacketReflectionHeadDescent.lean)

For computations with legal packets, take increasing closed conductor spaces $V_n$ with dense union in $V$. For example, enumerate the successive finite spans of all residue packets. Put $d_n(z)=\|[y]_{V_n}\|$. The quotient transition sends $[y]_{V_n}$ to $[y]_{V_j}$ for $j\ge n$, and
\[
d_n(z)^2=d_j(z)^2+\|P_{V_j}y-P_{V_n}y\|^2,\qquad d_n(z)\downarrow\|Dz\|.
\]
For any fixed $0<c<1$, membership $z\in\Gamma_V$ is equivalent to arbitrarily late starting indices $n$ admitting $j\ge n$ with $d_j(z)^2\le c\,d_n(z)^2$. On $z=(0,\mathbf1)$ this is equivalent to RH. The quantified contraction for this particular class is open. [Block descent](PacketReflectionQuotients.lean)

Reflection commutes with passage down the conductor quotients in a quantitative sense. For $f_k=2^{-k}J_{6\cdot 2^k}$ and any closed denominator $K$ the signed identity $[Rf_k]_K-2[\mathbf1]_K=-[Sf_k]_K$ gives
\[
\|[Rf_k]_K-2[\mathbf1]_K\|^2+\|P_K S f_k\|^2+
\sum_{n\ge1}(P(n)-P(n+1))|f_k(n)|^2
=2^{-k}\frac{\pi}{\sqrt3}.
\]
In particular the reflected tower approximates twice the vertical obstruction uniformly even when $K$ moves with $k$. The equality keeps both sources of lost energy. [Exact quotient energy](PacketReflectionQuotients.lean)

## What the cokernel detects

The anchored difference $\Delta=I-S$ has dense image on $M$ in the full Pareto space. Here is the arithmetic behind this fact. Write $r_d(n)=n\bmod d$ and $I_d(n)=\mathbf1_{d\mid n}$. Then
\[
\Delta r_d=\mathbf1-dI_d,\qquad
r_d-(\log d)\,r_2/\log2\in M\quad(d\ge2).
\]
Transport the physical functions to the equivalent inverse-square law $Q$. Here $\|dI_d\|_Q=1$ and $dI_d$ converges weakly to zero, by uniform boundedness and eventual pointwise vanishing. For a test vector $h$ orthogonal in $Q$ to the transported differences of mixed vectors, the two displayed identities imply
\[
\langle h,\mathbf1-dI_d\rangle_Q=(\log d)\,\langle h,\Delta(r_2/\log2)\rangle_Q.
\]
The left side is uniformly bounded, so the logarithmic coefficient vanishes. Weak convergence gives $\langle h,\mathbf1\rangle_Q=0$. The same identity now says $h$ annihilates every $I_d$. Divisibility indicators are total in $L^2(Q)$, so $h=0$. Equivalence of the two physical norms transfers density back to $P$. [Mixed difference density](MixedDifferenceDensity.lean) · [Divisibility totality](QDivisibilityDensity.lean)

Since $m\in V$, $D(m,-Sm)=[\Delta m]_V$. Consequently $D$ has dense range in $H/V$ and its Hausdorff cokernel is zero unconditionally. The algebraic quotient $\Gamma/\Gamma_V$ identifies with $\operatorname{im}D$. Density alone gives no identification of its quotient norm with the norm inherited from $H/V$. The target for RH is $D=0$, already detected by $D(0,\mathbf1)$.

The loss of control when taking primitives can be seen on $\mathbf1$ itself. Any anchored primitive of $\mathbf1$ would have value $n$ at positive site $n$, with squared Pareto norm $\sum_{n\ge1}n/(n+1)=\infty$. In particular, $\Delta M$ is dense and proper. If $\Delta m_j\to\mathbf1$, coordinatewise telescoping gives $m_j(n)\to n$ for each fixed $n$. The first $N$ terms of the norm then give $\liminf_j\|m_j\|_P^2\ge\sum_{n=1}^N n/(n+1)$, proving $\|m_j\|_P\to\infty$.
