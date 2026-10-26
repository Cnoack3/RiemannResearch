# One-atom smoothing and the limit of abstract projection arguments

These are paper proofs prepared on 26 October 2026 for the raw-source
continuation. They are not Lean-verified declarations. Neither statement
settles the full masked squarefree stages.

Write `z = zeta(2)`, `Q(n) = 1/(z n^2)`,
`a(n) = n/(8+log n)^2`, and `Bf(n) = f(n)/(n+1)`, for positive integers.
The Q norm of the physical constant function 1 is one.

## 1. A uniform physical bound for every one-atom smoothed projection

For any integer d >= 2, let

\[
g_d(n)=\frac{n\bmod d}{d},\qquad
P_d f=\frac{\langle f,g_d\rangle_Q}{\|g_d\|_Q^2}g_d.
\]

Then, for every f in L2(Q),

\[
\boxed{\sup_{n\ge1}|P_d Bf(n)|
\le \sqrt{z(z-1)}\,\|f\|_Q.}
\]

More precisely, the right side at site n can be multiplied by
`(n mod d)/(d-1)`.

Proof. Since `g_d(n) <= n/d`,

\[
\|Bg_d\|_Q^2
\le \frac1{z d^2}\sum_{n\ge1}\frac1{(n+1)^2}
=\frac{z-1}{z d^2}.
\]

At each of the sites `1 <= n < d`, the contribution to `||g_d||_Q^2`
is exactly `1/(z d^2)`. Thus

\[
G_d:=\|g_d\|_Q^2\ge\frac{d-1}{z d^2}>0.
\]

Self-adjointness of B and Cauchy--Schwarz therefore give, for the coefficient
`beta_d = <Bf,g_d>/G_d`,

\[
|\beta_d|
\le \frac{\|f\|_Q\,\|Bg_d\|_Q}{G_d}
\le \sqrt{z(z-1)}\frac d{d-1}\|f\|_Q.
\]

Multiplication by `g_d(n)=(n mod d)/d <= (d-1)/d` proves the claim.
No assumption of primality or squarefreeness was needed.

Consequently the complete weighted energy satisfies

\[
\boxed{\mathcal E(P_dBf)
\le z(z-1)\mathcal E(1)\|f\|_Q^2
\le \frac{9(z-1)}{64}\|f\|_Q^2.}
\]

Indeed, the decreasing function `x -> 1/[x(8+log x)^2]` gives

\[
z\mathcal E(1)
=\sum_{n\ge1}\frac1{n(8+\log n)^2}
\le\frac1{64}+\int_1^\infty\frac{dx}{x(8+\log x)^2}
=\frac9{64}.
\]

For `r_d = (I-P_d)1`, the same statements hold with
`||f||_Q^2 = e_d <= 1`. In particular, the one-atom actual coupled correction
`P_d B(I-P_d)1` has a physical bound independent of d. This is compatible
with the unbounded weighted/unweighted norm ratio of the atoms themselves:
smoothing the input supplies the compensating factor.

This does **not** prove a bound for `P_N B(I-P_N)1` with many correlated legal
atoms. Its missing extension is precisely control of the inverse Gram
matrix on the smoothed forcing.

## 2. Exact coupled obstruction for arbitrary projections, even with parity

Use the isometry from L2(Q) to the real sequence space ell2,

\[
\widehat f_n=\frac{f(n)}{\sqrt z\,n},\qquad n\ge1.
\]

Let `e_n` be the unit coordinate vectors, `q_n=1/(sqrt(z)n)` the transformed
constant target, and `D e_n = (n+1)^(-1)e_n` the transformed B. Set

\[
w_n=\begin{cases}1/(2\sqrt z\,n),&n\text{ odd},\\0,&n\text{ even},\end{cases}
\]

so w is exactly the transformed legal atom g_2. For an even integer K >= 4,
define

\[
v_K=(e_2+e_K)/\sqrt2,\quad
V_K=\operatorname{span}\{w,v_K\},\quad
r_K=(I-P_{V_K})q,\quad b_K=P_{V_K}Dr_K.
\]

The two spanning vectors have disjoint parity supports, and v_K is a unit
vector. Therefore `r_K` is orthogonal to g_2 and is an actual projection
residual of the constant target. It has norm at most one. The coefficient
of v_K in b_K is exactly

\[
\begin{aligned}
\alpha_K
&=\langle Dq,v_K\rangle
 -\langle q,v_K\rangle\langle Dv_K,v_K\rangle\\
&=\frac{(q_2-q_K)((1/3)-(1/(K+1)))}{2\sqrt2}\\
&=\frac{(K-2)^2}{12\sqrt{2z}\,K(K+1)}
\longrightarrow\frac1{12\sqrt{2z}}>0.
\end{aligned}
\]

The remaining component of b_K is supported on odd sites. Hence, with the
same physical weighted energy expressed in internal coordinates,

\[
\mathcal E(b_K)=\sum_{n\ge1}a(n)|(b_K)_n|^2
\ge\frac{\alpha_K^2}{2}(a(2)+a(K))\longrightarrow\infty.
\]

At the high even site the corresponding physical value is particularly
simple:

\[
\boxed{b_K(K)=\frac{(K-2)^2}{24(K+1)}\sim K/24.}
\]

Meanwhile the raw sources obey the uniform bound
`E(D r_K) <= ||r_K||^2/256 <= 1/256` already in the handoff.
This example retains the target, reciprocal smoothing, exact projection
residual coupling, projection contraction, and parity orthogonality. Thus
these abstract properties together cannot prove the desired weighted bound.

The spaces V_K are not the masked squarefree stages, are not nested, and
contain a nonlegal coordinate vector. Accordingly this is **not** a
counterexample to the arithmetic conjecture for the actual sequence. It
identifies arithmetic structure that a successful proof must use.
