# Arithmetic investigation of logarithmic-depth resolvent heads

Date: 28 October 2026. Source baseline: `d9ceacb7d4783447af945c8df671a8a31a294f98`.

**Status.** All new resolvent-kernel identities, finite-stage centered recurrences,
and deductions in this note are ordinary mathematical arguments, not new
Lean-verified declarations. The existing Lean declarations cited below were
read in the published source. The separate coordinate-error development must
state its own actual verification status. No uniform arithmetic head bound or
unconditional RH proof is supplied here.

## 0. Formal coordinate results and verification boundary

The sibling module `QSquarefreeResolventHeads.lean` adds:

- `resolvent_error_physical_le`: the physical error is at most
  `sqrt(zetaTwo) * n * (1/3)^k * norm(displacement)`.
- `headDepth N m = Nat.clog 3 N + m` and `headDepth_scale_le`.
- `resolvent_error_head_le`: simultaneously for every natural site
  `n <= N`, the error is at most
  `sqrt(zetaTwo) * (1/3)^m * norm(displacement)`.
- `UniformHeadBound m C`: one common C bounds those heads for all N.
  Site zero is the conventional zero extension.
- `displacement_bounded_of_head_bound` and
  `head_bound_of_displacement_bounded`: the two bounds transfer with
  additive constant `sqrt(zetaTwo) * (1/3)^m * norm(displacement)`.
- `uniform_head_bound_iff_displacement_bounded` and
  `uniform_head_bound_iff_residual_zero`: for every fixed natural m,
  existence of a common head bound is equivalent to the existing
  displacement-boundedness criterion and to zero limiting residual.
- `riemannHypothesis_of_uniform_head_bound` and
  `riemannHypothesis_of_positive_head_bound`: conditional conclusions are
  Mathlib's `RiemannHypothesis`. The latter takes C >= 0 and only positive
  physical sites n <= N. No uniform-bound provider is supplied.

The exact signed vector remainder recursion remains the imported
`resolvent_error_succ`; coordinate evaluation and the triangle inequality
are used only for the stated estimates. All norms, projections and tails
refer to the full Q Hilbert space.

The complete candidate passed isolated Lean verification in
`job_TAzmBowJAgVAYXoRI3a7UVVhZEGfeK3f`, with exit code 0 and reported
server duration 6.296 seconds. Axiom inspection for the positive-site RH
corollary and residual-zero equivalence returned only `propext`,
`Classical.choice`, and `Quot.sound`. The earlier coordinate/head
candidate passed `job_1MggLr6dhV0osRU0NWxqwfWTrJx5dhTJ` in 6.708 seconds
and the head-error axiom inspection returned the same list. These are
isolated checks; the final project acceptance and publication are governed
by the single checkpoint associated with this source change.

Timing boundary: workspace-opening request duration was not separately
captured, and must not be conflated with Lean checking. The final isolated
candidate had approximately 0.0014 seconds between server submission and
start. Polling latency is separate from the reported server duration; no
kernel-only duration was measured.

**Open arithmetic hypothesis:** a common C for one fixed m, independent of
N and n. The new Lean result gives a quantitative reformulation, not a
weaker regularity condition. In particular, it does not assert that RH
itself is equivalent to these conditions; the formal conclusion uses the
existing one-way capacity-to-RH bridge.

## 1. Operators and exact evaluation kernels

Let

\[
H_Q=\ell^2(\mathbb N_{\ge1},Q),\qquad
Q(n)=\frac1{\zeta(2)n^2},\qquad
(Bf)(n)=\beta_n f(n),\quad \beta_n=\frac1{n+1}.
\]

Let \(P\) project onto the closed actual squarefree span \(V\), and set
\(r=1-P1\), \(b=PBr\). The physical evaluation Riesz vector is
\(e_n(m)=\mathbf1_{m=n}/Q(n)\); hence
\(\langle f,e_n\rangle_Q=f(n)\) and
\(\|e_n\|_Q=\sqrt{\zeta(2)}n\).

The published feedback is \(R=(4/3)P(B-\tfrac14 I)\). It is self-adjoint
**on \(V\)**; it need not be self-adjoint on all of \(H_Q\). To avoid that
ambiguity define the genuinely self-adjoint ambient operator

\[
T=\frac43P(B-\tfrac14I)P,
\qquad
F_k=\frac43\sum_{j=0}^{k-1}T^jP,
\qquad K_{k,n}=F_ke_n.
\]

The empty sum is zero. Since \(TP=PT=T\), \(F_k\) is self-adjoint with
range in \(V\), and \(T\) agrees with \(R\) on \(V\). Therefore

\[
d_k=F_kBr,\qquad
\|F_k\|\le \frac43\sum_{j<k}3^{-j}
=2(1-3^{-k}),
\tag{1}
\]

\[
\boxed{\|K_{k,n}\|_Q\le
2(1-3^{-k})\sqrt{\zeta(2)}n.}
\tag{2}
\]

Self-adjointness and \(r\perp V\) give exact signed identities

\[
\boxed{d_k(n)
=\langle r,BK_{k,n}\rangle_Q
=\langle r,(I-P)BK_{k,n}\rangle_Q
=\langle r,(B-\beta_n I)K_{k,n}\rangle_Q.}
\tag{3}
\]

These are finite operator sums; no interchange of a Neumann infinite series
with a coordinate evaluation is needed.

## 2. The complete upper physical tail is already controlled

Put \(u_{k,n}=(B-\beta_n I)K_{k,n}\). Its physical coordinate at \(n\)
vanishes. The complete signed split is

\[
d_k(n)=L_k(n)+U_k(n),
\]

\[
L_k(n)=\sum_{m=1}^{n-1}Q(m)r(m)(\beta_m-\beta_n)K_{k,n}(m),
\quad
U_k(n)=\sum_{m\ge n}Q(m)r(m)(\beta_m-\beta_n)K_{k,n}(m).
\tag{4}
\]

The second sum retains every physical site \(m\ge n\), and converges
absolutely by weighted Cauchy--Schwarz. Here \(\operatorname{tail}_{n-1}\)
means the complete physical tail at sites \(m\ge n\). For those sites,
\(|\beta_m-\beta_n|\le\beta_n\), so (2) implies

\[
\|\operatorname{tail}_{n-1}u_{k,n}\|_Q
\le 2(1-3^{-k})\sqrt{\zeta(2)}\frac n{n+1}.
\]

Consequently

\[
\boxed{|U_k(n)|\le
2(1-3^{-k})\sqrt{\zeta(2)}\frac n{n+1}
\|\operatorname{tail}_{n-1}r\|_Q
\le2\sqrt{\zeta(2)}\|\operatorname{tail}_{n-1}r\|_Q.}
\tag{5}
\]

Thus \(U_k(n)\to0\) as \(n\to\infty\), uniformly over **every depth
\(k\)**. In particular, for \(k(N)=\lceil\log_3N\rceil+m\) with fixed
\(m\ge0\), a uniform bound on \(|d_{k(N)}(n)|\), \(1\le n\le N\),
exists if and only if a uniform bound on \(|L_{k(N)}(n)|\) exists.
The constants in the two bounds differ by at most
\(2\sqrt{\zeta(2)}\|r\|_Q\). The signed lower-site response is still open.

The exact residualized energy is also retained:

\[
\begin{aligned}
\Lambda_{k,n}
&=\|(I-P)BK_{k,n}\|_Q^2\\
&=\|BK_{k,n}\|_Q^2-\|PBK_{k,n}\|_Q^2\\
&=\|\operatorname{head}_{n-1}u_{k,n}\|_Q^2
 +\|\operatorname{tail}_{n-1}u_{k,n}\|_Q^2
 -\|Pu_{k,n}\|_Q^2,
\end{aligned}
\tag{6}
\]

\[
|d_k(n)|^2\le\|r\|_Q^2\Lambda_{k,n}.
\tag{7}
\]

A common bound for the product in (7) over the logarithmic heads would
suffice. Dropping the final negative square in (6) creates a stronger
sufficient requirement and may destroy essential cancellation.

Equations (3)--(7) are the resolvent counterparts of the **existing** checked
single-correction results in `QSquarefreeCorrectionKernel.lean` and
`QSquarefreeKernelLocalization.lean`. They locate the remaining problem;
they do not solve it.

## 3. Exact finite signed Gram recurrences

Use a separate stage index \(M\). The actual stage has masked atoms
\(a_i=\mathbf1_{\mathrm{Squarefree}(i+2)}g_{i+2}\), \(i<M\), where
\(g_d(n)=(n\bmod d)/d\). Define

\[
G_{ij}=\langle a_i,a_j\rangle_Q,
\quad H_{ij}=\langle a_i,Ba_j\rangle_Q,
\quad m_i=\langle a_i,1\rangle_Q,
\quad h_i=\langle a_i,B1\rangle_Q.
\]

Every entry is an inner product over the **complete infinite physical
space**. Zero columns make the masked system potentially singular; no
inverse of this masked \(G\) is assumed. If \(Gc=m\), then
\(r_M=1-\sum_i c_i a_i\) and the exact signed forcing is
\(\rho=h-Hc\).

Let \(P_M\) be stage projection,
\(R_M=(4/3)P_M(B-\tfrac14I)\), and

\[
w_{M,0}=0,\qquad
w_{M,j+1}=\frac43P_MBr_M+R_Mw_{M,j}.
\]

Coefficient vectors can be chosen recursively with

\[
\boxed{G\alpha_{j+1}
=\frac43\rho+(\frac43H-\frac13G)\alpha_j,
\qquad \alpha_0=0.}
\tag{8}
\]

For evaluation \(\phi_n=(a_i(n))_i\), the analogous resolvent-kernel
coefficients solve

\[
\boxed{Gx_{j+1}
=\frac43\phi_n+(\frac43H-\frac13G)x_j,
\qquad x_0=0.}
\tag{9}
\]

These systems are solvable because their right-hand sides come from actual
Hilbert-space vectors. Their synthesized vectors are unique even when the
coefficients are not. Symmetry gives the exact signed scalar

\[
\boxed{w_{M,k}(n)=\phi_n^\mathsf T\alpha_k=x_k^\mathsf T\rho.}
\tag{10}
\]

This extends the existing `QSquarefreeSignedNormal` normal-system and
choice-independence framework. Replacing (10) by absolute bounds for
individual coefficients discards the sought arithmetic cancellation.

The published forcing estimates already include the decomposition
\(\rho_d=A_M/d+\eta_{M,d}\) on active conductors, uniform
\(\eta_{M,d}=o(d^{-3/2})\), and the complete Bessel estimate
\(\zeta(2)\sum d^2|\eta_{M,d}|^2\le4\|r_M\|_Q^2\).
They do not bound the inverse response
\((\sum x_d^2/d^2)^{1/2}\), nor the signed combination (10).
Sources: `QSquarefreeForcingDecomposition.lean`,
`QSmoothedResidueAsymptotic.lean`, and `QSmoothedResidueBessel.lean`.

## 4. What is finite, and comparison with existing criteria

The closed-space \(d_k\) uses \(P\) and the limiting \(r\). Finite depth
alone does **not** make it a finite arithmetic algorithm. Equations
(8)--(10) use finite conductor systems, while still retaining their
complete infinite Q-weighted inner products.

Let \(D_M\) denote the actual matched finite Q/P displacement from
`QSquarefreeFiniteDisplacement.lean`. Its checked `finite_resolvent` is
\(D_M=P_MBr_M+P_MBD_M\). The same elementary centering and induction
as for the closed space gives, as an ordinary deduction,

\[
\|D_M-w_{M,k}\|_Q\le3^{-k}\|D_M\|_Q.
\tag{11}
\]

The published `finiteDisplacement_energy_bound` gives
\(8\|D_M\|_Q^2\le\|r_M\|_Q^2\le1\). Hence for
\(k(M)=\lceil\log_3M\rceil+m\), \(M\ge1\), and \(n\le M\),

\[
\boxed{|D_M(n)-w_{M,k(M)}(n)|
\le\sqrt{\zeta(2)/8}\,3^{-m}.}
\tag{12}
\]

Therefore existence of a uniform finite-stage logarithmic-depth head bound
is **equivalent**, up to a fixed additive constant, to the already existing
uniform finite-displacement head bound. The latter has the checked consumer
`riemannHypothesis_of_finiteDisplacement_head_bound`. This is a quantitative
reformulation, not a weaker sufficient arithmetic premise.

For completeness, `finiteDisplacement_tendsto` already proves
\(D_M\to d\) strongly. Equation (11) then shows
\(w_{M,k(M)}\to d\) for any \(k(M)\to\infty\), without a quantitative
stage-convergence rate. A common expanding-head bound consequently passes
to each fixed physical coordinate and implies RH. A quantitative rate is
needed only for a claimed **uniform error over the growing physical head**
between these finite-stage vectors and the closed-space \(d\) or \(d_k\).

The closed-space proposed bound is likewise equivalent to physical
boundedness of \(d\), using its uniform logarithmic-head error. Moreover,
`QSquarefreeSmoothedProjection.correction_bounded_iff_residual_zero` and
`QSquarefreeDisplacementRigidity.residual_eq_zero_iff_displacement_physically_bounded`
already identify boundedness of \(b\) and \(d\) with vanishing of the
same actual residual. The existing `riemannHypothesis_of_moving_head_bound`
and `riemannHypothesis_of_signed_normal_head_bound` are finite-stage
correction alternatives. None of their arithmetic head premises is proved
by the centered Hilbert contraction.

## 5. Why a squarefree-specific estimate is still needed

There is no generic theorem turning reciprocal smoothing followed by
orthogonal projection into a physical uniform bound. In the same \(H_Q\),
take the one-dimensional subspace generated by \(v(n)=n^{1/4}\). Then
\(v\in H_Q\), because \(\sum n^{-3/2}<\infty\), but \(v\) is physically
unbounded. The projection of the bounded vector \(B1\) is

\[
P_vB1=\frac{\langle B1,v\rangle_Q}{\|v\|_Q^2}v,
\]

which is unbounded; the scalar is positive. The same centered Hilbert
contraction holds for this projection. This counterexample concerns an
arbitrary subspace, **not** the actual squarefree span. It demonstrates why
the missing step must exploit squarefree arithmetic rather than just the
multiplier range and Hilbert projection contractivity.

The concrete remaining targets are the signed lower-site bound (4), the
full residualized kernel-product bound (7), or a direct bound on (10) using
the actual signed forcing and actual complete Gram equations. The upper
tail estimate (5), individual forcing decay, and Hilbert inverse norm do
not establish any of those targets.
