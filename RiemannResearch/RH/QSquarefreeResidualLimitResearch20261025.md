# Squarefree projection residuals: exact limits and obstructions

Date: 2026-10-25.

## Outcome and scope

For the actual squarefree legal spaces in L²(Q), this investigation does not prove convergence to zero and does not construct an L²(Q) counterexample. It verifies the exact zero-limit criterion, an explicit finite-stage progression decomposition, and the implication from zero convergence to Mathlib's RiemannHypothesis.

The ordinary mathematical argument below identifies zero convergence with RH, including the squarefree restriction. The RH-to-squarefree-density direction and the explicit Mellin witness calculation are not newly formalized in the accompanying module. They must not be reported as new Lean-verified theorems.

Let
\[
Q(k)=\frac1{\zeta(2)k^2},\qquad g_d(k)=\frac{k\bmod d}{d},\qquad k\ge1.
\]
Let \(d_1<d_2<\cdots\) enumerate squarefree integers at least two, and set
\[
V_n=\operatorname{span}_{\mathbb R}\{g_{d_1},\ldots,g_{d_n}\},\qquad
r_n=1-P_{V_n}1,\qquad V=\overline{\bigcup_n V_n}.
\]
“Contains” is interpreted here as this finite legal span. If additional directions are allowed, their identities matter; a space containing 1 already has zero residual.

The repository uses a redundant masked dictionary: stage N contains squarefree conductors in 2,...,N+1, with nonsquarefree entries replaced by zero. The first n genuine squarefree atoms occur at stage \(d_n-1\). These stages are cofinal; repetitions do not change any limit conclusion.

## 1. Unconditional strong convergence

For \(m\ge n\), \(r_m\perp(P_{V_m}1-P_{V_n}1)\), hence
\[
\|r_n\|_Q^2=\|r_m\|_Q^2+\|r_n-r_m\|_Q^2.
\]
The nonnegative errors decrease, so the residuals are Cauchy. Their limit lies in \(V^\perp\), while \(1-r\in V\). Therefore
\[
r_n\longrightarrow r=P_{V^\perp}1,
\qquad
\|r_n\|_Q^2=\|r\|_Q^2+\|r_n-r\|_Q^2.
\]
In particular,
\[
r_n\to0\text{ in }L^2(Q)\iff r=0\iff1\in V.
\]
The automatic estimate \(\|r_n\|_Q\le1\) does not make the limiting error zero.

Existing formal infrastructure:
- ZetaTwoOptimizerStage.residual_tendsto.
- ZetaTwoOptimizerStage.error_tendsto_zero_iff_mem_closure.
- ExhaustiveWalk.nested_projection_energy and walkError_eq_limitingError_add.

The new vector-valued zero-limit criterion is QSquarefreeResidualLimit.residual_tendsto_zero_iff_mem.

## 2. An exact finite-stage obstruction

Let \(L>0\) be any common multiple of the conductors in a stage. Every legal vector vanishes at each positive multiple of L. Thus
\[
r_n(jL)=1\quad(j\ge1).
\]
Write \(I_L(k)=\mathbf1_{\{L\mid k\}}\). In the actual Q law,
\[
\langle r_n,I_L\rangle_Q=\|I_L\|_Q^2=Q(L\mid k)=L^{-2}.
\]
Consequently
\[
\boxed{\|r_n\|_Q^2=L^{-2}+\|r_n-I_L\|_Q^2.}
\]
The complete progression, including its infinite tail, is present in this identity.

New declarations:
- stage_coordinate_zero_of_dvd.
- residual_coordinate_one_of_dvd.
- qDivisor_mem_stage_orthogonal.
- residual_inner_qDivisor.
- error_eq_progression_mass_add.
- error_ge_progression_mass.
- residual_not_uniformly_small.

Taking L to be the least common multiple gives
\[
\|r_n\|_Q^2\ge L_n^{-2}>0,\qquad \sup_{k\ge1}|r_n(k)|\ge1.
\]
Thus uniform convergence to zero is false for these exact residuals. The estimate \(L_n^{-2}\to0\) supplies no counterexample to norm convergence. A moving nonzero coordinate cannot establish that the limiting residual is nonzero.

## 3. Why the squarefree zero-limit question is RH-equivalent

External input: Luis Báez-Duarte, “A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis, 2,” arXiv:math/0205003, Theorem 1.1 and Section 2.2:
https://arxiv.org/pdf/math/0205003

After the substitution y=1/x, the source supplies, under RH, approximating finite sums with coefficients \(-\mu(d)d^{-\varepsilon}\). Because \(\mu(d)=0\) at nonsquarefree d, every sum is supported on squarefree conductors. The following transfer identifies the exact discrete problem, rather than assuming that continuous and discrete projections agree.

In \(L^2((0,\infty),dy/y^2)\), let
\[
F(y)=\sum_d c_d\{y/d\},\qquad A=\sum_d c_d/d,\qquad
TF(y)=F(y)-A\{y\}.
\]
Then TF vanishes on (0,1), and for \(k\le y<k+1\),
\[
TF(y)=\sum_d c_d g_d(k).
\]
With \(\chi=\mathbf1_{[1,\infty)}\),
\[
\|\chi-TF\|^2=\sum_{k\ge1}\frac{|1-\sum_dc_dg_d(k)|^2}{k(k+1)}.
\]
Also
\[
|A|^2=\int_0^1|F(y)|^2\,dy/y^2\le\|F-\chi\|^2,
\]
and \(\|\{y\}\|_{L^2(dy/y^2)}\le\sqrt2\), so
\[
\|TF-\chi\|\le(1+\sqrt2)\|F-\chi\|.
\]
This proves RH implies squarefree approximation in the Pareto norm.

Conversely, each TF is a natural Beurling combination, with the conductor-one coefficient adjusted by -A. Thus discrete Pareto approximation implies RH by the same criterion. Finally
\[
\frac1{\zeta(2)}\|f\|_P^2
\le\|f\|_Q^2
\le\frac2{\zeta(2)}\|f\|_P^2.
\]
The closed membership question is identical for the two equivalent norms, although the orthogonal projections generally differ. Hence, in ordinary mathematics,
\[
\boxed{r_n\to0\text{ in }L^2(Q)\iff1\in V\iff\mathrm{RH}.}
\]

The accompanying Lean module verifies the implication from residual convergence to Mathlib's RiemannHypothesis, by assembling the existing squarefree capacity and Mellin obstruction results. It does not assume RH or assume closure as a global fact. The convergence premise in that theorem remains open.

## 4. A concrete conditional counterexample certificate

This section is an ordinary proof, not newly Lean verified.

For \(s=\sigma+it\), \(\sigma>1/2\), define
\[
D_s(f)=\sum_{k\ge1}f(k)\Delta_s(k),\qquad
\Delta_s(k)=k^{-s}-(k+1)^{-s}.
\]
Weighted Cauchy–Schwarz proves continuity with squared norm, on the complexified Hilbert space,
\[
C_s^2=\zeta(2)\sum_{k\ge1}k^2|\Delta_s(k)|^2.
\]
Since \(\Delta_s(k)=s\int_k^{k+1}x^{-s-1}\,dx\),
\[
k^2|\Delta_s(k)|^2
\le |s|^2\int_k^{k+1}x^{-2\sigma}\,dx,
\qquad
C_s^2\le\frac{\zeta(2)|s|^2}{2\sigma-1}.
\]
Telescoping gives \(D_s(1)=1\). Discrete summation by parts first in \(\Re s>1\), then holomorphic continuation to \(\Re s>0\), gives
\[
D_s(g_d)=(d^{-1}-d^{-s})\zeta(s).
\]
The apparent singularity at s=1 on the right is removable.

Therefore, if an off-line zero with \(\sigma>1/2\) exists, it annihilates every legal atom and supplies
\[
D_s(r_n)=1,\qquad
\boxed{\|r_n\|_Q^2\ge\frac{2\sigma-1}{\zeta(2)|s|^2}>0\quad\text{for every }n.}
\]
A real separator is \(u_s(k)=\zeta(2)k^2\Re\Delta_s(k)\). It has mean 1 and is orthogonal to all legal atoms. This does not construct an off-line zero.

## 5. Checks on proposed shortcut arguments

- Compactness identifies the already-existing limit; it does not identify it as zero.
- The divergent branch of the residual-tail dichotomy concerns a scaled tail quantity, not \(\|r\|_Q\). Furthermore, full-conductor residual theorems cannot be applied to the squarefree residual without a squarefree proof.
- Squarefree atoms interpolate the constant on every fixed finite head. For prime p>H, Möbius inversion gives on \(1\le k\le H\):
  \[
  1=p\left(\sum_{d\le H}\frac{\mu(d)}d\right)g_p(k)
    -\sum_{d\le H}\mu(d)g_d(k).
  \]
  The missing ingredient is control of complete Q energy as H grows.
- Properness of the squarefree subspace does not separate the constant target. A separating vector must have nonzero pairing with 1, not merely be nonzero.

The remaining arithmetic task is to prove squarefree closure, or construct an actual continuous annihilator with nonzero mean. Neither has been accomplished here.


## 6. The precise epsilon request and the remaining CRT estimate

Source: user's follow-up request on 25 October 2026 to use finite or infinite
CRT to prove that every sufficiently late canonical optimizer has squared
complete-Q error at most epsilon.

The newly checked quantifier statement is
\[
[\forall\varepsilon>0\ \exists M_0\ \forall M\ge M_0,\
  \|1-F_M\|_Q^2\le\varepsilon]
\quad\Longleftrightarrow\quad 1\in H_{\mathrm{sf}}.
\]
It is an established equivalence, not an established assertion of either side.
Declaration: `epsilon_approximation_iff_mem`.

Unconditionally, for every epsilon > 0, all sufficiently late M satisfy
\[
\|1-F_M\|_Q^2\le \|1-P_{H_{\mathrm{sf}}}1\|_Q^2+\varepsilon.
\]
Declaration: `eventual_error_le_limitingResidual_add`.
The exact equality behind this estimate retains the full residual:
\[
\|1-F_M\|_Q^2=
\|1-P_{H_{\mathrm{sf}}}1\|_Q^2+
\|P_{H_{\mathrm{sf}}}1-F_M\|_Q^2.
\]

The constructive finite-certificate bridge is now explicit:
\[
G\in V_N,\ M\ge N
\quad\Longrightarrow\quad
\|1-F_M\|_Q^2\le\|1-G\|_Q^2.
\]
Declaration: `later_error_le_competitor`. It follows from the existing exact
least-squares identity
\[
\|1-G\|_Q^2=\|1-F_M\|_Q^2+\|F_M-G\|_Q^2.
\]
Consequently, a single complete-Q CRT certificate G for each epsilon would give
the requested threshold M_0=N. No cofinal or monotone choice of these
certificate indices is required.

### Concrete arithmetic provider still Open

The following calculation is ordinary mathematics, not a new Lean theorem in
this update. Let G_H be a finite squarefree legal combination with
G_H(n)=1 for 1 <= n <= H. Then exactly
\[
\|1-G_H\|_Q^2=
\frac1{\zeta(2)}\sum_{n>H}\frac{|1-G_H(n)|^2}{n^2}.
\]
If B_H = sup_n |G_H(n)|, then for H >= 1,
\[
\|1-G_H\|_Q^2
\le \frac{(1+B_H)^2}{\zeta(2)}
        \sum_{n>H}\frac1{n^2}
\le \frac{(1+B_H)^2}{\zeta(2)H}.
\]
Thus B_H=o(sqrt(H)) would be one sufficient provider. It is a sufficient,
potentially lossy estimate; the exact signed tail energy remains the primary
target. The current CRT identities do not supply this amplitude bound or
vanishing complete tail energy.

The explicit exact-head formula from Section 5 is legal, but its coefficients
alone do not establish the required complete-Q control. Simultaneous CRT
rewrites these finite sums into prime atoms and carries without changing their
energy. The ambient cylinders h_L=1-I_L are not admissible replacements:
h_6 is already separated from H_sf by the checked conductor-25 functional.
Projected cylinders converge to P_Hsf(1), with the same unresolved residual
energy retained.

**Open:** construct actual finite legal CRT combinations with complete-Q error
arbitrarily small, or otherwise prove the constant target lies in H_sf.
This update does not prove the requested unconditional convergence and does
not provide a counterexample to it.
