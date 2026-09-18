# Multi-range divisor corrections: exact construction, signed optimization, and the remaining bound

September 18, 2026

## Scope and outcome

This continues Priority 1 of `RH_Conditional_IID_Research_Agenda_2026-09-18.md`, checked against its longer LaTeX rendering. Google Drive searches did not locate the named item; the matching saved Markdown and LaTeX files were read instead. The original agenda is preserved.

The results below have mathematical proofs in this document. They have **not** been checked in Lean in this task. No current repository or historical verification claim is made.

The strongest conclusions established here are:

1. Unrestricted finite divisor corrections are exactly the entire legal affine space with prescribed initial values. Thus allowing all divisor ranges removes an ansatz restriction, but does not simplify away the RH-strength difficulty.
2. An explicit legal starting family has conditional-mean energy less than `4Y`, unconditionally.
3. Each finite multi-range optimization has a unique minimizer and an exact signed Schur-complement formula. Successive ranges give an exact telescoping energy budget.
4. Rational finite computations admit convergent, rigorous upper and lower certificates for each fixed collection of ranges.
5. The missing statement is a uniform bound on the remaining tail energy as both the initial interval and the allowed divisor set grow. No subpolynomial bound is proved here.

## 1. Spaces and normalization

All sequence indices are positive integers; let `Y >= 2` be an integer. Put

\[
w_n=\frac1{n(n+1)},\quad q_t=\frac2{(t+1)(t+2)},\quad
H=\ell^2(w),\quad J=\ell^2(q),
\]
\[
g_d(n)=\{n/d\},\qquad V=\operatorname{span}_{\mathbb R,\mathrm{finite}}\{g_d:d\ge2\},
\qquad (CF)(t)=\frac1t\sum_{n=1}^tF(n),\quad E(F)=\|CF\|_J^2.
\]

Every legal function is bounded and periodic, so all energies and polarized pairings used below converge absolutely. Indeed `sum q_t = sum w_n = 1`, and bounded functions belong to both weighted spaces. For general `F in H`, Jensen and Tonelli give

\[
\|CF\|_J^2\le\sum_{n\ge1}|F(n)|^2\sum_{t\ge n}\frac{q_t}{t}
=\sum_{n\ge1}\frac{|F(n)|^2}{n(n+1)}.
\tag{1.1}
\]

The inner sum telescopes because `q_t/t = 1/[t(t+1)] - 1/[(t+1)(t+2)]`.

Write

\[
\mathcal A_Y=\{F\in V:F(1)=\cdots=F(Y)=1\},\qquad
c_Y=\sum_{t=1}^Yq_t=\frac{Y}{Y+2}.
\]

For every such function, there is the exact separation

\[
E(F)=c_Y+\sum_{t>Y}q_t(CF(t))^2.
\tag{1.2}
\]

The constant target is used only on the prescribed initial interval. The optimization below minimizes `E(F)`, exactly as in the agenda; it does not silently change the objective to `||CF-1||²`.

## 2. Completeness of divisor corrections

Let

\[
Q=\prod_{p\le Y}p,\qquad \alpha=\prod_{p\le Y}(1-1/p),\qquad
R(n)=\sum_{d\mid Q}\mu(d)\lfloor n/d\rfloor.
\]

**Theorem 2.1.** A sequence belongs to `A_Y` if and only if it has a representation

\[
F(n)=R(n)+\sum_{d>Y}t_d\lfloor n/d\rfloor,
\qquad \sum_{d>Y}t_d/d=-\alpha,
\tag{2.1}
\]

with finite real support.

**Proof.** The forward construction in the agenda follows from `floor(n/d)=n/d-g_d(n)` and the displayed balance. Also `R(n)=1` for `1<=n<=Y`: the only positive integer at most `Y` coprime to `Q` is 1, while all correction floors vanish there.

Conversely write `F=sum c_d g_d`, set `a_1=sum c_d/d` and `a_d=-c_d` for `d>=2`. Then

\[
F(n)=\sum_{d\ge1}a_d\lfloor n/d\rfloor,\qquad \sum_da_d/d=0.
\]

Extend `F(0)=0`. The first differences satisfy

\[
F(n)-F(n-1)=\sum_{d\mid n}a_d.
\]

The initial values force the left side to be 1 at `n=1` and 0 at `2<=n<=Y`. Finite Möbius inversion gives `a_d=mu(d)` for every `d<=Y`. For such `d`, this equals the sieve coefficient `mu(d) 1_{d|Q}`, since a nonsquarefree `d` has Möbius value zero. Subtracting the sieve coefficients therefore leaves a finite correction supported above `Y`. Subtracting their reciprocal sums gives its balance. ∎

This also proves uniqueness of finite floor coefficients. The functions `g_d`, for distinct `d>=2`, are linearly independent: if their combination is zero, the same first-difference argument gives first `a_1=0` and then every `a_d=0`.

**Interpretation.** Multi-range corrections, when every finite divisor set is allowed, are not a smaller family than the agenda's legal interpolation problem. A failure for a particular selection of ranges is only a failure of that selection.

## 3. An explicit unconditional starting family

Define

\[
\beta_Y=\sum_{d\le Y}\frac{\mu(d)}d,\qquad A=Y+1,
\]
\[
F_Y^{(0)}(n)=\sum_{d\le Y}\mu(d)\lfloor n/d\rfloor
-A\beta_Y\lfloor n/A\rfloor
=-\sum_{2\le d\le Y}\mu(d)g_d(n)+A\beta_Yg_A(n).
\tag{3.1}
\]

**Theorem 3.1.** This family belongs to `A_Y` and satisfies

\[
\boxed{c_Y\le E(F_Y^{(0)})<4Y.}
\tag{3.2}
\]

**Proof.** The linear slopes cancel in (3.1). For `n<=Y`, the last floor vanishes, and the divisor identity `sum_{d<=n} mu(d) floor(n/d)=1` gives the required values. That same identity at `n=Y` gives

\[
Y\beta_Y=1+\sum_{d\le Y}\mu(d)\{Y/d\},\qquad |\beta_Y|\le1.
\]

Here the `d=1` fractional part is zero and the other `Y-1` absolute summands are at most 1. Consequently `|F_Y^(0)(n)|<=2Y` for every `n`. Using its exact initial values and the contraction (1.1),

\[
E(F_Y^{(0)})\le\|F_Y^{(0)}\|_H^2
\le\frac{Y}{Y+1}+\frac{4Y^2}{Y+1}<4Y.
\]

The lower bound follows from (1.2). ∎

In the original sieve notation, an explicit correction vector for this family is

\[
t_d=-\mu(d)\mathbf1_{d\mid Q,\ d>Y}
-A\beta_Y\mathbf1_{d=A},\qquad d>Y.
\tag{3.3}
\]

When the two supports overlap their coefficients are added. Its reciprocal sum is `-(alpha-beta_Y)-beta_Y=-alpha`. Thus this really is an instance of the proposed divisor correction, not a change of legal space. Formula (3.1) cancels its potentially large sieve support exactly before computing energy.

The bound `O(Y)` is polynomial, and does not imply RH. Absolute values above are used only to certify this coarse starting bound; all improvement formulas below retain their signs and cross terms.

## 4. Eliminate balance before forming a Gram matrix

Keep the anchor `A=Y+1`. For every `d>Y`, `d!=A`, put

\[
u_d(n)=\lfloor n/d\rfloor-\frac A d\lfloor n/A\rfloor
=\frac A d g_A(n)-g_d(n).
\tag{4.1}
\]

Each direction is legal and vanishes on `[1,Y]`. Any finitely supported balanced perturbation above `Y` has the unique form `sum_{d!=A} x_d u_d`: its anchor coefficient is forced to be `-A sum x_d/d`.

By Theorem 2.1,

\[
\mathcal A_Y=\left\{F_Y^{(0)}+\sum_{d\in D}x_du_d:
D\subset\{Y+2,Y+3,\ldots\}\text{ finite}\right\}.
\tag{4.2}
\]

**Important summability restriction.** Do not form an infinite `J` Gram matrix of the raw smoothed floors. A floor grows linearly, so its smoothed sequence is not in `J`. The cancellation in (4.1) must occur first. Subtracting divergent raw Gram entries is not a valid derivation of the balanced Gram matrix.

Let `v_d=Cu_d`, `M_0=CF_Y^(0)`, and, for a finite set `D`, define

\[
G_{de}=\langle v_d,v_e\rangle_J,\qquad h_d=\langle M_0,v_d\rangle_J.
\]

Then

\[
E\left(F_Y^{(0)}+\sum x_du_d\right)
=E(F_Y^{(0)})+2h^Tx+x^TGx.
\tag{4.3}
\]

The `u_d` are linearly independent by their distinct non-anchor `g_d` coefficients. The map `C` is injective, since `F(t)=tCF(t)-(t-1)CF(t-1)`. Thus `G` is positive definite and

\[
\boxed{x_*=-G^{-1}h,\qquad E_D=E(F_Y^{(0)})-h^TG^{-1}h.}
\tag{4.4}
\]

This proves existence and uniqueness in every fixed finite family. It asserts neither existence of an unrestricted minimizer nor a uniform estimate in `Y`.

## 5. Exact smoothed arithmetic and CRT data

For `t=kd+r`, `0<=r<d`, direct summation gives

\[
a_d(t):=(Cg_d)(t)=\frac{k(d-1)/2+r(r+1)/(2d)}t.
\tag{5.1}
\]

Consequently

\[
v_d(t)=\frac A d a_A(t)-a_d(t),
\quad M_0(t)=-\sum_{2\le d\le Y}\mu(d)a_d(t)+A\beta_Ya_A(t).
\tag{5.2}
\]

Equations (5.1)–(5.2), summed with the actual weights `q_t`, give the exact Gram entries and signed correlations. They use one deterministic vector for all latent values.

There is also a finite residue representation of the *infinite* energy. Let `P` be any common period of a legal `F`, let

\[
m=\frac1P\sum_{n=1}^PF(n),\qquad B(r)=\sum_{n=1}^r(F(n)-m),\quad 1\le r\le P.
\]

Then `B(P)=0`, and

\[
CF(kP+r)=m+\frac{B(r)}{kP+r}.
\]

Define the positive, absolutely convergent weights

\[
L_P(r)=\sum_{k\ge0}\frac2{(kP+r)(kP+r+1)(kP+r+2)},
\]
\[
M_P(r)=\sum_{k\ge0}\frac2{(kP+r)^2(kP+r+1)(kP+r+2)}.
\]

Regrouping absolutely convergent series gives exactly

\[
\boxed{E(F)=m^2+2m\sum_{r=1}^PL_P(r)B(r)
+\sum_{r=1}^PM_P(r)B(r)^2.}
\tag{5.3}
\]

For two functions with a common period, polarization gives

\[
\langle CF,CH\rangle_J=m_Fm_H
+\sum_rL_P(r)(m_FB_H(r)+m_HB_F(r))
+\sum_rM_P(r)B_F(r)B_H(r).
\tag{5.4}
\]

For a single generator, its mean is `(d-1)/(2d)` and its centered cumulative defect at `r=t mod d` is `r(r-d+2)/(2d)`. Thus all defects above can be obtained by finite linear combinations.

CRT organizes these residues through their compatible prime-power coordinates. It does not replace `L_P` and `M_P` by uniform averages, and does not remove the mixed term in (5.3) or the products in (5.4). The formulas already retain every signed coefficient interaction.

## 6. What adding a divisor range actually gains

Split the chosen divisors into an old set `O` and a disjoint new range `N`. Write the full Gram matrix and correlations as

\[
G=\begin{pmatrix}G_O&B\\B^T&G_N\end{pmatrix},\qquad
h=\binom{h_O}{h_N}.
\]

Let

\[
S=G_N-B^TG_O^{-1}B,\qquad k=h_N-B^TG_O^{-1}h_O.
\tag{6.1}
\]

**Theorem 6.1.** The matrix `S` is positive definite, and

\[
\boxed{E_{O\cup N}=E_O-k^TS^{-1}k.}
\tag{6.2}
\]

**Proof.** Orthogonally project the new `v_d` off the span of the old ones, writing `z_d=(I-P_O)v_d`. Their Gram matrix is `S`. They are independent because all old and new directions together are independent. The old optimized sequence is `M_O=M_0-P_OM_0`; its correlations with the `z_d` are exactly `k`. Minimizing `||M_O+sum y_d z_d||²` gives `y=-S^{-1}k` and (6.2). ∎

In particular, retaining the old coefficients unchanged while optimizing the new range generally does **not** realize (6.2). The old coefficients must be reoptimized as well. Discarding `B` changes both the residual correlation and the reconstruction cost.

In spectral coordinates of `S`, the exact gain is

\[
k^TS^{-1}k=\sum_i\frac{|\langle k,e_i\rangle|^2}{\lambda_i(S)}.
\tag{6.3}
\]

Thus no unproved uniform lower eigenvalue bound is needed to state the optimization. The missing arithmetic concerns the actual correlations together with these eigenvalues, not positivity alone.

For successive disjoint finite ranges, with reoptimization after each addition, define `Delta_j=k_j^T S_j^{-1}k_j`. Then

\[
\boxed{E_{D_1\cup\cdots\cup D_J}=E(F_Y^{(0)})-\sum_{j=1}^J\Delta_j,\quad
0\le\sum_{j=1}^J\Delta_j\le E(F_Y^{(0)})-c_Y.}
\tag{6.4}
\]

This telescoping identity is unconditional. It supplies no positive lower bound for any particular `Delta_j`.

## 7. Certified finite computations, including the infinite tail

Suppose `F=sum c_d g_d`, and put `L(F)=sum |c_d|`. Since `|CF(t)|<=L(F)`,

\[
0\le E(F)-\sum_{t\le N}q_tCF(t)^2\le\frac{2L(F)^2}{N+2}.
\tag{7.1}
\]

This bound is only a tail certificate, not a substitute for the signed objective. A sharper available certificate from (5.3) is

\[
\sum_{t>N}q_tCF(t)^2\le\frac2{N+2}
\left(|m|+\frac{B_{\max}}{N+1}\right)^2,
\quad B_{\max}=\max_{1\le r\le P}|B(r)|.
\tag{7.2}
\]

For a fixed divisor set `D`, form `G_N,h_N,E_{0,N}` using `t<=N`. For

\[
N\ge\max(\{A\}\cup D),
\]

`G_N` is positive definite. Indeed a vanishing linear combination of `Cu_d` up to `N` gives a vanishing combination of `u_d` there. Its first differences at integers up to the largest divisor recover, by the triangular divisor equations, every floor coefficient. All must be zero.

Define

\[
x_N=-G_N^{-1}h_N,\quad F_N=F_Y^{(0)}+\sum_{d\in D}(x_N)_du_d,
\quad \ell_N=E_{0,N}-h_N^TG_N^{-1}h_N.
\]

The exact minimum of the full infinite energy satisfies

\[
\boxed{\ell_N\le E_D\le E(F_N)
\le\ell_N+\frac{2L(F_N)^2}{N+2}.}
\tag{7.3}
\]

All finite entries and `x_N` are rational, so this is an exact rational certificate. It is not necessary to identify special-function constants numerically.

For fixed `Y,D`, these certificates converge to the full minimum: absolute convergence gives `G_N -> G` and `h_N -> h`, positive definiteness gives `x_N -> x_*`, and the finitely many legal coefficients of `F_N` remain bounded. The gap in (7.3) therefore tends to zero. Also `ell_N` increases because each truncated objective increases pointwise.

This convergence is only for a fixed family. There is no uniform bound here on `L(F_N)`, on how large `N` must be, or on the resulting minima as `Y,D` vary. Optimizing separately at each `t` would not produce a legal coefficient vector.

## 8. A precise delayed-correction obstruction

If all correction divisors in the original representation (2.1) satisfy `d>=D`, then `F(n)=R(n)` for `n<D`. Consequently

\[
\boxed{E(F)\ge\sum_{t<D}q_t\left(\frac1t\sum_{n\le t}R(n)\right)^2.}
\tag{8.1}
\]

No choice of coefficients at those delayed divisors can alter this lower bound. It is an exact obstruction which can be evaluated before optimizing the coefficients.

A general version is equally useful. If all perturbations vanish for `n<D`, their smoothed versions vanish for `t<D`, so an energy reduction is at most the current energy carried by `t>=D`. Late corrections cannot remove energy already fixed before their first activation.

**Anchor caveat.** The balanced direction `u_d` in (4.1), even for extremely large `d`, starts at `A=Y+1` because it adjusts the anchor. Thus (8.1) cannot be applied merely because the *non-anchor* divisors are large. It applies to the actual support of the complete correction, including its balance compensation.

## 9. The exact remaining quantitative problem

Choose any exhaustive disjoint collection of finite ranges, for example

\[
D_1=\{Y+2,\ldots,2(Y+1)\},\qquad
D_j=\{2^{j-1}(Y+1)+1,\ldots,2^j(Y+1)\}\ (j\ge2).
\]

Let `rho_0=E(F_Y^(0))-c_Y` and `rho_J=E_{D_1 union ... union D_J}-c_Y`. Then

\[
\rho_J=\rho_0-\sum_{j=1}^J\Delta_j\ge0,\qquad \rho_0<4Y.
\tag{9.1}
\]

By completeness (4.2), the decreasing limit equals

\[
\lim_{J\to\infty}\rho_J=\inf_{F\in\mathcal A_Y}E(F)-c_Y.
\tag{9.2}
\]

This is an equality of infima, not an assertion that a finite or infinite coefficient vector attains the limit.

**Unresolved construction problem, now in exact multi-range form.** Find `Y_i -> infinity` and finite `J_i` such that

\[
c_{Y_i}+\rho_0(Y_i)-\sum_{j=1}^{J_i}\Delta_j(Y_i)
\le C_\varepsilon Y_i^\varepsilon
\quad\text{eventually for every }\varepsilon>0.
\tag{9.3}
\]

The minimizing coefficients then construct the desired legal witnesses. Conversely any finite witness is contained in one of these exhaustive families, whose optimum is no worse. Thus (9.3) neither loses witnesses nor hides an additional approximation hypothesis.

One sufficient, stronger mechanism would be a fixed fractional reduction of the *actual* remaining tail energy. If for successive finite added ranges

\[
\Delta_j\ge\delta\rho_{j-1},\qquad 0<\delta<1,
\]

then `rho_J <= 4Y(1-delta)^J`. Taking `J >= log(4Y)/[-log(1-delta)]` gives `E<=c_Y+1<2`. **No such lower bound on the gains has been proved.** It would solve the central target, and cannot be inferred from CRT, positive definiteness, or conditional independence.

More generally, where `rho_{j-1}>0`, define `eta_j=Delta_j/rho_{j-1}`. Until the tail vanishes,

\[
\rho_J=\rho_0\prod_{j=1}^J(1-\eta_j).
\tag{9.4}
\]

This gives an exact arithmetic gain budget to investigate; every `eta_j` is computed against the reoptimized residual with the full signed Schur complement. Bounding each range independently or replacing correlations by magnitudes would address a different problem.

## 10. Why the remaining bound has RH strength

For completeness, the agenda's one-way implication can be checked without claiming a converse. For `Re s=sigma>1/2`, define

\[
b_s(n)=n\bigl(n^{-s}-2(n+1)^{-s}+(n+2)^{-s}\bigr),\qquad
\Lambda_s(M)=\sum_{n\ge1}b_s(n)M(n).
\]

The double-integral formula for the second difference gives

\[
|b_s(n)|\le |s(s+1)|n^{-\sigma-1},\quad
\sum_{n>Y}\frac{|b_s(n)|^2}{q_n}
\le\frac{3|s(s+1)|^2}{2\sigma-1}Y^{1-2\sigma}.
\tag{10.1}
\]

Thus `Lambda_s` is continuous on `J`. If `A_n=sum_{k<=n}g_d(k)`, a finite summation by parts gives

\[
\sum_{n=1}^N A_n\Delta^2(n^{-s})
=\sum_{n=1}^Ng_d(n)\bigl(n^{-s}-(n+1)^{-s}\bigr)
-A_N\bigl((N+1)^{-s}-(N+2)^{-s}\bigr).
\]

The boundary term tends to zero for `sigma>0`, since `A_N=O(N)`. Both remaining series are locally uniformly convergent there, using boundedness of `g_d`. For `sigma>1`, floor summation gives their value `(d^{-1}-d^{-s}) zeta(s)`. Analytic continuation, with the removable value at `s=1`, therefore gives

\[
\Lambda_s(Cg_d)=(d^{-1}-d^{-s})\zeta(s),\qquad \Lambda_s(1)=1.
\tag{10.2}
\]

The second identity follows by the same summation by parts with the constant sequence 1 and telescoping. These manipulations establish summability and keep the boundary term before passing to the limit.

Suppose `zeta(s)=0` with `sigma>1/2`, `s!=1`. Every legal `F` satisfies `Lambda_s(CF)=0`. If `F=1` through `Y`, then

\[
\sum_{n>Y}b_s(n)CF(n)=-\sum_{n\le Y}b_s(n).
\]

The sum on the right tends to `-1`, and therefore has magnitude at least `1/2` for all sufficiently large `Y`. Cauchy–Schwarz and (10.1) give the slightly more informative tail bound

\[
\boxed{E(F)-c_Y\ge
\frac{2\sigma-1}{12|s(s+1)|^2}Y^{2\sigma-1}.}
\tag{10.3}
\]

A subpolynomial family contradicts (10.3). Together with the standard symmetry of nontrivial zeta zeros, this yields RH. It does not prove that such a family exists.

The broader approximation context is the established [strong Nyman–Beurling criterion of Báez-Duarte](https://arxiv.org/abs/math/0202141). That published criterion is not being cited as a proof of (9.3); the conditional-mean implication above is derived directly.

## 11. Status and next precise target

**Proved here:** completeness, an explicit `E<4Y` family, finite existence and uniqueness, exact weighted residue formulas, exact cross-range gains, convergent rational certificates, and the delayed-activation obstruction. The conditional zero obstruction is also supplied with its boundary term and tail estimate.

**Not proved:** any unconditional `Y^{o(1)}` bound for the optimized family, any uniform fraction of tail energy removed by a new range, or RH. No numerical experiment is being presented as asymptotic evidence, and no Lean verification was performed.

The next mathematical target is a lower bound on `k^T S^{-1} k` for the actual reoptimized residual, sufficient to meet (9.3). The explicit starting family and exhaustive ranges now give fully specified objects for that target. A rigorous computation can use (7.3) to locate promising ranges, but the proof must control the accumulated gains uniformly as `Y` grows.
