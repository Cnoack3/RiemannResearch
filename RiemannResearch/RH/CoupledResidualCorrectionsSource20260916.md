# Coupled corrections for the actual Pareto residual

Christian Noack research program · 16 September 2026

## Status and main outcome

This continuation pursues the requested bound on the Pareto energy of legal corrections normalized by their correlation with the actual projection residual. It gives an explicit two-direction correction built from transported changes in the actual old optimum, a bound for its energy in terms of earlier error reductions, and an exact decomposition of the full dyadic block into transported and fresh arithmetic directions.

The logarithmic upper bound remains unproved. The results below identify the signed source inequalities needed by the proposed construction. They also show that an eventual improvement of the logarithmic order is impossible for the actual spaces, by applying the classical Nyman–Beurling distance lower bound. No Lean or numerical experiments were used in this continuation. The dilation, decomposition, and moment calculations received independent analytic audits; no priority claim is made.

## 1. Setting and the cost being estimated

All logarithms are natural.

Work in the real Hilbert space

\[
H=\ell^2(\mathbb N_{\ge1},w),\qquad w_n=\frac1{n(n+1)},\qquad b(n)=1.
\]

Let

\[
r_q(n)=n\bmod q,\qquad g_{p,m}=r_{pm}-r_m,
\qquad p\in\{2,3\},\quad m\ge1.
\]

Every positive integer dilation is allowed. Define

\[
V_M=\operatorname{span}\{g_{p,m}:m\le M,\ p=2,3\},
\quad P_M=P_{V_M},\quad F_M=P_Mb,
\]

\[
e_M=b-F_M,\qquad D_M=\|e_M\|^2,\qquad
\Delta_M=D_M-D_{2M}.
\]

Set \(V_0=\{0\}\), \(F_0=0\), and \(D_0=1\). Nested projection geometry gives

\[
\langle e_M,b\rangle=D_M,\qquad
\|F_B-F_A\|^2=D_A-D_B\quad(0\le A\le B).
\]

Every finite residual is nonzero: for a common period \(L\) of the generators in \(V_M\), all of them vanish at the positive coordinate \(L\), and \(e_M(L)=1\).

For the full increment \(W_M=V_{2M}\cap V_M^\perp\), put

\[
\mathcal C_M=
\inf\{\|w\|^2:w\in W_M,\ \langle e_M,w\rangle=D_M\}.
\]

The infimum is \(+\infty\) if the constraint is impossible. The exact formula is

\[
\boxed{\mathcal C_M=\frac{D_M^2}{\Delta_M}.}
\]

Indeed, the projection of \(e_M\) onto \(W_M\) is \(F_{2M}-F_M\), with squared norm \(\Delta_M\). Cauchy–Schwarz gives the lower bound, attained by multiplying that projection by \(D_M/\Delta_M\) when the gain is positive.

The requested sufficient estimate is

\[
\mathcal C_M\le C D_M\log(2M),
\quad\text{equivalently}\quad
\Delta_M\ge\frac{D_M}{C\log(2M)}.
\]

This equivalence concerns the full increment. A bound using a specified smaller collection of trial vectors is only a sufficient condition.

## 2. Exact dilation identities

For a Hilbert-space sequence, use zero extension at the auxiliary coordinate zero and define

\[
(\mathscr D_af)(n)=a f(\lfloor n/a\rfloor),\qquad a\in\mathbb N_{\ge1}.
\]

For each \(k\ge1\),

\[
\sum_{n=ak}^{a(k+1)-1}w_n
=\frac1{ak}-\frac1{a(k+1)}=\frac{w_k}{a}.
\]

Consequently,

\[
\boxed{
\langle\mathscr D_af,\mathscr D_ag\rangle
=a\langle f,g\rangle,\qquad
\mathscr D_a^*b=b.
}
\]

The second identity follows by the same block summation. All sums are absolutely convergent by Cauchy–Schwarz. Also

\[
\mathscr D_a g_{p,m}=g_{p,am},\qquad
\mathscr D_aV_N\subset V_{aN}.
\]

These statements use the actual Pareto measure and no probabilistic independence.

## 3. A coupled correction whose energy is controlled by previous gains

For \(p=2,3\), define

\[
L_p=\lfloor M/p\rfloor,\qquad N_p=\lfloor2M/p\rfloor,
\]

\[
\eta_p=F_{N_p}-F_{L_p},\qquad
\delta_p=D_{L_p}-D_{N_p}=\|\eta_p\|^2,
\qquad v_p=\mathscr D_p\eta_p.
\]

Thus \(v_p\in V_{2M}\), and

\[
\boxed{\|v_p\|^2=p\delta_p.}
\]

Moreover, \(\mathscr D_pF_{L_p}\in V_M\), so the fully screened column satisfies

\[
q_p=(I-P_M)v_p=(I-P_M)\mathscr D_pF_{N_p}.
\]

Subtracting the old projection increment before dilation avoids paying for the part already represented in the old space.

Let \(\mathsf V(a_2,a_3)=a_2v_2+a_3v_3\), and define the exact matrices and source

\[
R=\mathsf V^*\mathsf V,
\qquad S=\mathsf V^*(I-P_M)\mathsf V,
\qquad h=\mathsf V^*e_M.
\]

Then

\[
R=\begin{pmatrix}2\delta_2&c_M\\c_M&3\delta_3\end{pmatrix},
\qquad c_M=\langle\mathscr D_2\eta_2,\mathscr D_3\eta_3\rangle,
\]

\[
0\preceq S\preceq R,\qquad
\tau_M:=\operatorname{tr}R=2\delta_2+3\delta_3.
\]

The off-diagonal entry remains signed. Both \(h\in\operatorname{ran}R\) and \(h\in\operatorname{ran}S\): a null synthesis vector has zero correlation with the residual.

### Theorem 1: certified gain from transported actual innovations

If \(\tau_M>0\), then

\[
\boxed{
\Delta_M\ge h^TS^\dagger h
\ge G_M:=h^TR^\dagger h
\ge\frac{h_2^2+h_3^2}{2\delta_2+3\delta_3}.
}
\]

The first quantity is the exact gain in the two screened trial directions. The second is achieved by optimizing with their raw Gram matrix and then allowing the old coefficients to refit. The final estimate uses the positive-semidefinite matrix inequality \(\lambda_{\max}(R)\le\operatorname{tr}R\); it does not replace individual correlations by absolute values.

For clarity, the middle inequality also follows directly from the variational formula

\[
h^TS^\dagger h=\sup_a(2h^Ta-a^TSa)
\ge\sup_a(2h^Ta-a^TRa)=h^TR^\dagger h.
\]

If \(R\) is nonsingular, its exact signed expression is

\[
\boxed{
G_M=
\frac{3\delta_3h_2^2-2c_Mh_2h_3+2\delta_2h_3^2}
{6\delta_2\delta_3-c_M^2}.
}
\]

Use the pseudoinverse formula when the determinant is zero.

### Theorem 2: explicit correlation-normalized witness

Whenever \(G_M>0\), set

\[
\boxed{
w_M=\frac{D_M}{G_M}(I-P_M)\mathsf V R^\dagger h.
}
\]

It belongs to \(V_{2M}\cap V_M^\perp\), and

\[
\boxed{
\langle e_M,w_M\rangle=D_M,\qquad
\|w_M\|^2
=\frac{D_M^2}{G_M^2}h^TR^\dagger SR^\dagger h
\le\frac{D_M^2}{G_M}.
}
\]

The equality retains the complete old-space screening and mixed energy. For the inequality, use \(S\preceq R\) and \(R^\dagger RR^\dagger=R^\dagger\).

This proves the energy half of a concrete construction. In particular, either of the following unproved source conditions would establish the desired logarithmic cost for this witness:

\[
G_M\ge\frac{D_M}{C\log(2M)},
\]

or the stronger, simpler condition

\[
\boxed{
h_2^2+h_3^2\ge
\frac{D_M(2\delta_2+3\delta_3)}{C\log(2M)}.
}
\]

If \(\tau_M=0\), both trial vectors vanish. If \(h=0\), the two-direction construction gives no improvement. Neither statement implies that the full dyadic increment is unproductive.

## 4. The signed correlation that remains, and an interscale constraint

Let \(N=\lfloor2M/3\rfloor\). Since \(\mathscr D_pb=p\mathbf1_{\{n\ge p\}}\), the two sources have the exact expressions

\[
\boxed{
h_2=2D_M-e_M(1)-\langle e_M,\mathscr D_2e_M\rangle,
}
\]

\[
\boxed{
h_3=3D_M-\frac32e_M(1)-\frac12e_M(2)
-\langle e_M,\mathscr D_3e_N\rangle.
}
\]

For example, \(h_2=\langle e_M,\mathscr D_2F_M\rangle\), and substituting \(F_M=b-e_M\) proves the first formula. The second follows the same way. These show exactly which signed cancellations the proposed source bound must control.

There is an additional restriction on any attempted nondegeneracy proof. Put

\[
d_j=D_{2^j},\qquad h_j=h_2(2^j),\qquad d_\infty=\lim_jd_j.
\]

Then

\[
\boxed{
|h_j|^2\le
2(d_{j-1}-d_j)(d_j-d_{j+1}).
}
\]

Indeed, the binary raw trial has norm squared \(2(d_{j-1}-d_j)\). Its correlation with \(e_{2^j}\) equals its correlation with \(F_{2^{j+1}}-F_{2^j}\), because the later residual annihilates every vector in \(V_{2^{j+1}}\). Cauchy–Schwarz proves the inequality. In particular,

\[
\sum_{j\ge J}|h_j|
\le\sqrt{2(d_{J-1}-d_\infty)(d_J-d_\infty)},
\]

\[
\sum_{j\ge J}\frac{|h_j|^2}{2(d_{j-1}-d_j)}
\le d_J-d_\infty,
\]

where a zero denominator contributes zero. Thus the signed expression in the first box of this section is automatically absolutely summable. A lower bound for it cannot be asserted without respecting these restrictions.

## 5. Exactly which directions all old transports omit

The trial above uses just two vectors. Even transporting the entire old spaces leaves a substantial, explicitly identifiable part of the full increment.

Define

\[
U_M=V_M+\mathscr D_2V_M+
\mathscr D_3V_{\lfloor2M/3\rfloor},
\qquad
\mathcal A_M=\{m:M<m\le2M,\ \gcd(m,6)=1\}.
\]

### Theorem 3: exact transported/fresh decomposition

\[
\boxed{
V_{2M}=U_M\oplus_{\mathrm{alg}}
\operatorname{span}\{g_{2,m},g_{3,m}:m\in\mathcal A_M\}.
}
\]

The sum is algebraically direct, not generally orthogonal in the Pareto norm. Its dimension consequence is

\[
\boxed{\dim(V_{2M}/U_M)=2|\mathcal A_M|=\frac{2M}{3}+O(1).}
\]

**Proof.** Use the established canonical basis

\[
\{g_{3,m}:m\le N\}\cup
\{g_{2,m}:m\le N,\ 3\nmid m\}.
\]

Its elimination identity is

\[
g_{2,3k}=g_{3,2k}+g_{2,k}-g_{3,k}.
\]

A new ternary canonical index divisible by two comes from \(\mathscr D_2V_M\); one divisible by three comes from \(\mathscr D_3V_{\lfloor2M/3\rfloor}\). A new binary canonical index is not divisible by three; if it is even, it comes from \(\mathscr D_2V_M\). The remaining canonical indices are exactly those in \(\mathcal A_M\), with two columns for each.

Conversely, canonical reduction of a transported binary column divisible by three introduces only an even index \(2k\) and indices \(k\le M\). Thus transported columns have zero coefficients on the displayed fresh canonical list. Canonical independence proves directness.

For an exact count, set

\[
a(X)=X-\lfloor X/2\rfloor-\lfloor X/3\rfloor+\lfloor X/6\rfloor.
\]

Then \(|\mathcal A_M|=a(2M)-a(M)\). For dyadic \(M\ge2\), the transported increment has dimension \(M+1\) when \(M\equiv2\pmod6\), and \(M-1\) when \(M\equiv4\pmod6\).

This is a precise limitation on constructions using only transports of old directions. It is not a counterexample for the actual residual: the residual might have little mass in the omitted directions, or those directions might supply the required gain.

## 6. The exact signed Schur remainder on the fresh block

Let

\[
P_U=P_{U_M},\quad F_U=P_Ub,\quad e_U=b-F_U,
\quad \Delta_U=D_M-\|e_U\|^2.
\]

List the fresh generators of Theorem 3 as \(\gamma_i\), and define

\[
t_i=(I-P_U)\gamma_i,\qquad
K_{ij}=\langle t_i,t_j\rangle,\qquad
z_i=\langle e_U,t_i\rangle.
\]

Algebraic independence modulo \(U_M\) proves \(K\succ0\). The exact formula is

\[
\boxed{\Delta_M=\Delta_U+\mathcal R_M,\qquad
\mathcal R_M=z^TK^{-1}z.}
\]

No cross terms have been omitted. If \(A\) is an old Gram matrix for \(U_M\), \(B\) its cross matrix with the fresh generators, and \(C\) the fresh raw Gram, then

\[
K=C-B^TA^\dagger B,
\qquad z=\ell_{\mathrm{fresh}}-B^TA^\dagger\ell_U,
\]

with mean vectors \(\ell_i=\langle b,\text{column}_i\rangle\). In particular, the fresh unscreened means are \(\log2\) and \(\log3\); their screened values need not have either sign.

The fresh fitted vector

\[
v_{\mathrm{fresh}}=\sum_i(K^{-1}z)_i t_i
\]

has norm squared and correlation with \(e_M\) both equal to \(\mathcal R_M\). It is orthogonal to \(U_M\).

This combines with the two-direction construction without adding incompatible separately optimized gains. Set

\[
u=(I-P_M)\mathsf V R^\dagger h\in U_M,
\qquad H_M=G_M+\mathcal R_M.
\]

Then \(\langle e_M,u\rangle=G_M\), \(\|u\|^2\le G_M\), and \(u\perp v_{\mathrm{fresh}}\). Therefore, if \(H_M>0\),

\[
\boxed{
\widetilde w_M=\frac{D_M}{H_M}(u+v_{\mathrm{fresh}}),
\quad \langle e_M,\widetilde w_M\rangle=D_M,
\quad \|\widetilde w_M\|^2\le\frac{D_M^2}{H_M}.
}
\]

In particular,

\[
\boxed{\Delta_M\ge G_M+\mathcal R_M.}
\]

The sufficient remaining estimate for this completed construction is

\[
G_M+\mathcal R_M\ge\frac{D_M}{C\log(2M)}.
\]

It remains open. Using the exact \(\Delta_U\) instead of its two-direction lower bound \(G_M\) recovers the original full target without loss.

A crude unconditional fallback, when the fresh list is nonempty, is

\[
\mathcal R_M\ge
\frac{\|z\|_2^2}
{(\|r_2\|^2+\|r_3\|^2)\sum_{m\in\mathcal A_M}m}.
\]

This follows from \(\operatorname{tr}K\le\sum_i\|\gamma_i\|^2\) and exact dilation scaling. The denominator is \(O(M^2)\); it supplies no logarithmic source estimate. The constant obeys \(\|r_2\|^2+\|r_3\|^2\le\log2+2\log3\).

## 7. The logarithmic cost is unavoidable for the actual spaces

The map

\[
(Jf)(t)=f(\lfloor1/t\rfloor)\mathbf1_{(0,1]}(t)
\]

is an isometry into \(L^2(0,\infty)\). For all \(t>0\),

\[
Jg_{p,m}(t)=pm\left\{\frac1{pmt}\right\}
-m\left\{\frac1{mt}\right\}.
\]

Hence \(JV_M\) is contained in the classical Nyman–Beurling space with parameters \(1/(3M)\le\theta\le1\). The distance lower bound of Báez-Duarte–Balazard–Landreau–Saias, strengthened in [Burnol, Theorem 1.3](https://arxiv.org/pdf/math/0103058), gives

\[
\boxed{D_M\ge c_0/\log(3M)\quad\text{for all sufficiently large }M}
\]

for some \(c_0>0\), unconditionally.

Apply this input to \(d_j=D_{2^j}\) and \(\theta_j=(d_j-d_{j+1})/d_j\). Exact telescoping yields

\[
\sum_{j=J_0}^{J-1}-\log(1-\theta_j)
=\log(d_{J_0}/d_J)\le\log J+O(1).
\]

Thus \(\liminf_j(j+1)\theta_j\le1\): an eventual lower bound strictly larger than \(1/(j+1)\) contradicts this inequality. Since \(\mathcal C_{2^j}=d_j/\theta_j\),

\[
\boxed{
\limsup_{M\to\infty,\ M\ \mathrm{dyadic}}
\frac{\mathcal C_M}{D_M\log(2M)}
\ge\frac1{\log2}.
}
\]

Consequently an eventual \(o(D_M\log M)\) cost bound is impossible. A uniform bound with constant \(C\) requires \(C\ge1/\log2\), equivalently a gain constant \(c\le\log2\). This is an obstruction to improving the proposed order, not a proof of its upper bound.

## 8. Head/tail relaxation: the missing constraint is arithmetic

Let \(R_M\) denote physical restriction to coordinates \(1,\ldots,M\), and \(Z_M=\ker R_M\). The restrictions of \(g_{2,1},\ldots,g_{2,M}\) form a triangular matrix with diagonal \(1,\ldots,M\). Therefore

\[
R_MV_M=R_MH,\qquad V_M+Z_M=H,
\qquad (I-P_M)Z_M=V_M^\perp.
\]

Allowing arbitrary raw tail corrections thus permits the entire screened residual at energy \(D_M\). Tail support alone does not obstruct the desired correction.

The raw energy required before screening is more informative. On the finite head space set

\[
A_M=R_MP_MR_M.
\]

This operator is positive definite by the surjectivity just proved. For \(x=R_Me_M\), the minimum-norm old vector satisfying \(R_Mv=-x\) is \(-P_MA_M^{-1}x\). Since \(e_M\perp V_M\),

\[
\boxed{
\min_{\substack{R_Mz=0\\(I-P_M)z=e_M}}\|z\|^2
=D_M+\langle R_Me_M,A_M^{-1}R_Me_M\rangle.
}
\]

The minimizer is \(z=e_M-P_MA_M^{-1}R_Me_M\). Equivalently, this minimum is the least error \(\|b-u\|^2\) among \(u\in V_M\) that equal one on the first \(M\) coordinates.

In an orthonormal eigenbasis of \(A_M\), the extra cost is

\[
\sum_j\frac{|\langle R_Me_M,v_j\rangle|^2}{\lambda_j}.
\]

This keeps the actual residual's spectral weights. The minimizing tail need not be a legal combination of new generators, so this relaxation does not solve the arithmetic problem.

## 9. A separate finite arithmetic advance: only linearly many moments can vanish

The earlier far-dilation argument bounded the first nonzero periodic Laplace order by the common period minus one. That period can be very large. The finite conductor structure improves the order bound to \(4M-1\).

Write the actual old fit in residues as

\[
F_M=\sum_{n\in S}b_n r_n,\qquad \sum_{n\in S}b_n=0,
\]

retaining the formal coefficient of \(r_1=0\) supplied by expansion of the legal generators. The possible conductor set is

\[
S\subset\{m,2m,3m:1\le m\le M\}.
\]

Let \(s=|S|\) after discarding zero coefficients. For the periodic Laplace average, use the periodic extension \(e_M(0)=1\). This is separate from the zero extension used to define the Hilbert dilation operator in Section 2.

For a common period \(L\), define

\[
K_e(t)=\frac{\sum_{j=0}^{L-1}e_M(j)e^{-jt}}
{\sum_{j=0}^{L-1}e^{-jt}}.
\]

The finite generating-function calculation gives

\[
\boxed{K_e(t)=1+\sum_{n\in S}b_n\frac{n}{e^{nt}-1}.}
\]

The pole at zero cancels because \(\sum b_n=0\). Put

\[
\alpha=1-\frac12\sum b_nn,\qquad Q_{2j}=\sum b_nn^{2j}.
\]

The convergent Taylor expansion near zero is

\[
K_e(t)=\alpha+
\sum_{j\ge1}\frac{B_{2j}}{(2j)!}Q_{2j}t^{2j-1},
\]

where \(B_{2j}\ne0\) are the even Bernoulli numbers.

### Theorem 4: finite-order charge forcing

If \(\alpha=0\), at least one of \(Q_2,\ldots,Q_{2(s-1)}\) is nonzero. Otherwise the Vandermonde equations at the distinct points \(n^2\), including \(Q_0=\sum b_n=0\), force every \(b_n=0\), contradicting \(\alpha=0\). Hence the first nonzero Taylor order is at most \(2s-3\). If \(\alpha\ne0\), the order is zero.

Inclusion–exclusion gives the uniform support bound

\[
s\le3M-\lfloor M/2\rfloor-2\lfloor M/3\rfloor+\lfloor M/6\rfloor
\le2M+1.
\]

Therefore

\[
\boxed{\operatorname{ord}_{t=0}K_e\le4M-1.}
\]

There is also an exact finite identity. Let \(P(x)=\sum_{j=0}^{s-1}c_jx^j\) interpolate \(P(n^2)=n\) for \(n\in S\). Then

\[
\boxed{1=\alpha+\frac12\sum_{j=1}^{s-1}c_jQ_{2j}.}
\]

This follows by expanding \(\sum b_nP(n^2)=\sum b_nn\), with the constant coefficient disappearing because \(Q_0=0\). It forces at least one finite signed charge to survive; it does not control the conditioning of the interpolation coefficients.

For reference, the exact far-period correlation formula is

\[
\langle e_M,g_{2,m}\rangle
=\int_0^\infty K_e(u/m)J_2(u)\,du,
\qquad J_2(u)=\frac1{e^u+1},\qquad L\mid m.
\]

It follows by writing \(w_n=\int_0^\infty e^{-nt}(1-e^{-t})\,dt\), partitioning \(n=mk+j\), and using periodicity when \(L\mid m\). If the first nonzero Taylor term is \(c_kt^k\), dominated convergence gives a nonzero leading correlation proportional to \(m^{-k}\). For domination, \(K_e\) is bounded on \([0,\infty)\), and its zero of order \(k\) gives \(|K_e(t)|\le C_et^k\) globally when \(k>0\); all moments of \(J_2\) are finite.

Since \(\|g_{2,m}\|^2=m\log2\), the one-column gain is at least a positive residual-dependent constant times \(m^{-2k-1}\) for all sufficiently large period multiples. The exponent can now be taken at most \(8M-1\). The amplitude, threshold, and period are still uncontrolled as \(M\) grows. This improves the finite no-stagnation analysis but does not give a dyadic or logarithmic estimate.

## 10. What remains and how this advances the requested bound

The explicit transported-innovation witness proves a useful Pareto energy bound with the complete signed two-seed covariance. Its denominator is a source quantity built from the actual old optimum; the energy scale is earlier projection gains.

The full block has an exact additional contribution from the fresh indices coprime to six. Theorem 3 identifies all those missing directions, and Section 6 retains their full signed Schur complement. It would be unjustified to discard them on the ground that two seed dilations are available.

The concrete next estimate is a lower bound for the combined source

\[
G_M+z_M^TK_M^{-1}z_M
\]

at scale \(D_M/\log(2M)\), or, without the two-direction restriction, for

\[
\Delta_U+z_M^TK_M^{-1}z_M.
\]

The latter is exactly the original target, now split into explicitly identified arithmetic parts. No estimate above establishes this lower bound or rules out concentration of the actual residual in weakly detected directions. In particular, finite compatibility, small trial energies, and nonzero far-period charges do not establish the required amount of nearby-budget correlation.

If the bound is proved, dyadic iteration forces \(D_M\to0\). This implies RH through the usual Mellin annihilator argument: a zero \(\rho\) with \(\Re\rho>1/2\) defines a bounded functional annihilating all the legal generators but taking value \(1/\rho\) on the constant target. No converse asserting that RH implies this particular two-seed rate is used.

### Source notes

The current definitions and previously established canonical basis, local resonance gains, and periodic Laplace formula were checked against:

- `RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md`.
- `RH_Arithmetic_Improvement_and_Far_Dilation_2026-09-15.md`.
- `RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16.md`.

External input for the order obstruction: [Jean-François Burnol, A lower bound in an approximation problem involving the zeros of the Riemann zeta function, Theorem 1.3](https://arxiv.org/pdf/math/0103058). Standard approximation background: [Luis Báez-Duarte, A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis](https://arxiv.org/abs/math/0202141).
