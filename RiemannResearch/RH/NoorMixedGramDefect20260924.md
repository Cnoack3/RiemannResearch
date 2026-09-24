# Full mixed arithmetic Gram matrix and exact shifted-lift defect

**Date:** September 24, 2026.
**Foundation:** `8dfe2e0a39c94325d81c840d15c1c1bc00ecb67f`.
**Conclusion:** This continuation does not prove unconditional RH. It computes the complete mixed matrix, identifies its asymmetric limits, and gives an exact nonnegative remainder for the canonical regularized minimum. The divided-energy provider remains open.

## 1. Preserve the actual arithmetic family

Use the handoff's complete Hilbert inner products, legal generators
\(u_d=Tg_d\), \(U_N=\operatorname{span}\{u_2,\ldots,u_{N+1}\}\),
actual residual \(a_N=T(\mathbf1-P_{V_N}\mathbf1)\), and
\(E_N=\|a_N\|^2\). Let \(S\) be the unilateral shift and \(D=I-S\).
The matrices and source remain
\[
G_N(d,e)=\langle u_d,u_e\rangle,\quad
K_N(d,e)=\langle Du_d,Du_e\rangle,\quad
B_N(d,e)=\langle Du_d,u_e\rangle,\quad
h_N(d)=\langle Du_d,a_N\rangle.
\]
For \(t>0\), retain the existing canonical minimizer
\[
x_N(t)=(K_N+t^2G_N)^{-1}h_N,\qquad
v_N(t)=\sum_d x_N(t)_d u_d,
\]
and \(J_N(t)=E_N-h_N^{\mathsf T}x_N(t)\).
The lift coefficients are not the original projection coefficients.

## 2. Complete harmonic arithmetic formula

Write \(H_0=0\) and \(H_n=\sum_{k=1}^n1/k\). Telescoping the exact forward-difference formula gives
\[
\boxed{u_d(n)=\frac{H_n-H_{\lfloor n/d\rfloor}-\log d}{d}.}
\]
This coefficient formula is consistent with equation (3.3) of
[Calderaro–Manzur–Noor–Santos](https://arxiv.org/html/2203.05030v3),
with their generator scaled by \(1/d\). That source supports the coefficient formula; the mixed-entry calculation below is an elementary deduction from the handoff, with no novelty claim.

Pairing \(dDu_d=-(\log d)e_0+L_1-L_d\) with \(u_e\), then using the complete moment identity, gives
\[
\boxed{
de\,B(d,e)=\log d\log e+
\sum_{m=1}^{\infty}
\frac{H_m-H_{\lfloor m/e\rfloor}-H_{dm}
+H_{\lfloor dm/e\rfloor}}{m}.
}
\]
The series is absolutely convergent. Indeed, for every coefficient vector \(w\in\ell^2\) and positive integer \(d\), the series \(\sum_m w(dm)/m\) is absolutely convergent by Cauchy–Schwarz. The displayed series is \(e\) times the difference of two such series for \(w=u_e\). No tail is discarded.

In Lean, sums start at zero and the zeroth summand is zero by totalized real division. The formula applies to all \(d,e\ge2\), including every entry at every finite stage. It determines the full matrix, including its skew part.

## 3. The skew part contributes at leading order

For every fixed coefficient vector \(w\), the exact decomposition and the logarithmic-vector limit give
\[
\frac{d\langle Du_d,w\rangle}{\log d}\longrightarrow-w(0).
\]
Consequently, for fixed \(e\ge2\),
\[
\boxed{
\frac{dB(d,e)}{\log d}\longrightarrow\frac{\log e}{e},\qquad
\frac{dB(e,d)}{\log d}\longrightarrow0.
}
\]
For the second limit, use the exact identity
\(\langle Du,v\rangle+\langle Dv,u\rangle=\langle Du,Dv\rangle\)
and \((Du_e)(0)=u_e(0)\). Thus replacing \(B\) by \(K/2\) would already lose a leading contribution in these fixed-column limits. These remain fixed-column statements; they do not establish estimates uniform over growing coefficient arrays.

## 4. Exact square completion at the arithmetic minimizer

For any norm-preserving linear map \(S\), any \(a\perp v\), and real \(t,r\), direct expansion proves
\[
r\bigl(\|Dv-a\|^2+t^2\|v\|^2\bigr)
=r(1-r)\|a\|^2+\|Sv-r(v-a)\|^2
+\bigl(rt^2-(1-r)^2\bigr)\|v\|^2.
\]
In particular, if \(rt^2=(1-r)^2\), the actual canonical minimizer satisfies
\[
\boxed{rJ_N(t)=r(1-r)E_N+
\|Sv_N(t)-r(v_N(t)-a_N)\|^2.}
\]
The equivalent inverse-gain identity is
\[
r\left(rE_N-h_N^{\mathsf T}(K_N+t^2G_N)^{-1}h_N\right)
=\|Sv_N(t)-r(v_N(t)-a_N)\|^2.
\]
For \(0<s<1\), put \(r=s^2\) and \(t=(1-s^2)/s\). Then
\[
\boxed{
\frac{J_N(t)}{t}=sE_N+
\frac{\|Sv_N(t)-s^2(v_N(t)-a_N)\|^2}{s(1-s^2)}.
}
\]
This is an exact identity, without asymptotic error notation. Both terms on the right are nonnegative. Solving for \(s\) yields the stronger universal lower bound
\[
\frac{J_N(t)}t\ge
E_N\frac{\sqrt{t^2+4}-t}{2}.
\]
The Lean interface uses the algebraic parameter relation and the \(s\)-parameterization rather than a separate square-root theorem.

## 5. What is still required

The original cofinal divided-rate target remains
\[
\frac{E_{N_j}-h_{N_j}^{\mathsf T}
(K_{N_j}+t_j^2G_{N_j})^{-1}h_{N_j}}{t_j}\longrightarrow0,
\qquad N_j\to\infty,\quad t_j>0,\quad t_j\to0.
\]
The new arithmetic formula and limits do not prove this target. Along the corresponding \(s_j\to1\), the exact identity requires vanishing of the residual-energy term and of the normalized square remainder. Controlling only the remainder would still leave the limiting residual energy.

A substantive next attack must give uniform information on the full growing matrix and actual source. The published reductions must retain `hrate` and `hsource` as open hypotheses. A standard-axiom report does not discharge either hypothesis.

## 6. Lean interfaces and verification

The general and arithmetic defect candidate group passed Lean with exit code 0 (18.182 seconds). The full mixed arithmetic and asymmetric-limit group passed with exit code 0 (18.248 seconds), with no warnings. Axiom inspection reported only `propext`, `Classical.choice`, and `Quot.sound` for the inspected public identities and limits. No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced. Publication uses affected-module checkpoint validation; a fresh whole-repository build is not claimed. The new modules are `Analysis/ShiftedLiftDefect.lean`, `RH/NoorShiftedDefect.lean`, and `RH/NoorMixedGramArithmetic.lean`; the general logarithmic-moment summability helper belongs to `Analysis/NoorLogarithmGram.lean`.


---

# Literature audit and a geometric countermodel

**Date:** September 24, 2026.
**Scope:** The shifted-lift continuation attached to this session, whose published checkpoint is `8dfe2e0a39c94325d81c840d15c1c1bc00ecb67f`. This note audits relevant primary literature and explains why shifted density alone cannot supply the missing divided-energy estimate. It does not claim an unconditional proof of RH.

## 1. The question that needs an arithmetic answer

The handoff uses the actual arithmetic spaces
\[
U_N=\operatorname{span}\{Tg_d:2\le d\le N+1\},\qquad
a_N=T(\mathbf1-P_{V_N}\mathbf1),\qquad E_N=\|a_N\|^2,
\]
and the unilateral shift \(S\), with \(D=I-S\). The finite minimum is
\[
J_N(t)=\inf_{v\in U_N}\bigl(\|Dv-a_N\|^2+t^2\|v\|^2\bigr)
=E_N-h_N^{\mathsf T}(K_N+t^2G_N)^{-1}h_N.
\]
The existing unconditional conclusion is \(J_N(t_N)\to0\) for every prescribed vanishing schedule. The requested additional conclusion is a cofinal sequence with \(J_{N_j}(t_j)/t_j\to0\). The papers below do not establish that additional conclusion.

## 2. What the inspected literature actually supplies

**Noor, “A Hardy space analysis of the Báez-Duarte criterion for the RH” (2019).** For
\[
h_k(z)=\frac{1}{1-z}\log\frac{1+z+\cdots+z^{k-1}}k,
\qquad \mathcal N=\operatorname{span}\{h_k:k\ge2\},
\]
Theorem 9 proves density of \((I-S)\mathcal N\) in \(H^2\). Theorem 10 obtains density of \(\mathcal N\) in the compact-open topology. Theorem 12 excludes nonzero vectors of \(\mathcal N^\perp\) from the local Dirichlet space at 1. These are unconditional conclusions, but they do not assert \(H^2\)-density of \(\mathcal N\). That last density is RH-equivalent. The shifted-density input in the handoff is therefore correctly weaker than the remaining target. [Primary text](https://arxiv.org/html/1809.09577v4).

**Calderaro, Manzur, Noor and Santos, “Orthogonality questions in the Hardy space related to ζ-zeros” (2024 revision).** Theorem 13 strengthens the regularity exclusion to \(\mathcal N^\perp\cap\mathcal D_1^p=\{0\}\) for all \(p>1\). Theorem 14 turns density of a suitably multiplied family \(\varphi\mathcal N\) into a zero-free half-plane, under an integrability hypothesis on \(1/\varphi\). Theorem 15 supplies a complete biorthogonal polynomial family. None asserts completeness of the original family without an additional premise; completeness does not generally transfer between biorthogonal families. [Primary text](https://arxiv.org/html/2203.05030v3).

**Manzur, Noor and Santos, “A weighted composition semigroup related to three open problems” (2023).** For \(W_nf(z)=(1+\cdots+z^{n-1})f(z^n)\), Theorem 12 proves that \(\overline{\mathcal N}\) reduces some \(W_n\), \(n\ge2\), exactly when RH holds. Consequently, adding adjoint invariance to the available forward invariance would add a substantive RH-equivalent assertion. [Primary text](https://arxiv.org/pdf/2111.05398).

**Álvarez and Manzur, “On the dynamics of a semigroup and its relation with the Riemann Hypothesis” (2025).** Theorem 9 characterizes RH by existence of a hypercyclic vector for \(W_k^*\) whose eventual orbit lies in \(\overline{\mathcal N}\). Its orbit-membership condition remains essential: hypercyclicity of the operator does not supply it. This is an equivalent reformulation, not an unconditional approximation rate. [Primary text](https://arxiv.org/html/2507.03625v1).

**Manzur, Noor and Quintero, “A Hardy space approximation supporting zero-free half-planes for the ζ-function” (June 2026 preprint).** Theorem 3.1 proves convergence of the displayed Möbius series in \(H^2(\mathbb C_\alpha)\) for \(\alpha>1\). Section 4 expressly separates this theorem from numerical investigations in \(1/2\le\alpha\le1\). Those computations do not prove convergence in the critical strip. The paper also distinguishes the divergence of raw Möbius approximants at the critical boundary from the existence of better approximants. [Primary text](https://arxiv.org/pdf/2606.16097).

**Bettin, Conrey and Farmer, “An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion.”** Theorem 1 obtains an optimal error asymptotic assuming RH and an additional bound on sums involving \(1/|\zeta'(\rho)|^2\). It therefore cannot supply an unconditional rate for this project. [Primary text](https://arxiv.org/pdf/1211.5191).

## 3. Explicit countermodel to a purely geometric deduction

**Status:** The following is an informal mathematical argument, not a Lean-checked theorem. It is not the actual arithmetic model and is not a counterexample to RH. It disproves the proposed implication from the generic geometric hypotheses alone.

Work in the real Hilbert space \(H=\ell^2(\mathbb N_0)\). Define
\[
p_n=\frac1{n+1},\qquad W=p^\perp,\qquad
v_n=e_n-\frac{e_0}{n+1}\quad(n\ge1),\qquad
U_N=\operatorname{span}\{v_1,\ldots,v_N\}.
\]
Since \(p\in H\setminus\{0\}\), \(W\) is closed and proper. Each \(v_n\in W\). Conversely, orthogonality to every \(v_n\) forces \(x_n=x_0/(n+1)\), so \((\bigcup_N U_N)^\perp=\mathbb Rp\). Thus \(\overline{\bigcup_N U_N}=W\).

Nevertheless, \(DW\) is dense in \(H\). If \(y\perp DW\), then \(D^*y\in W^\perp=\mathbb Rp\). Write \(D^*y=cp\). Since \((D^*y)_n=y_n-y_{n+1}\), iteration gives
\[
y_n=y_0-cH_n,\qquad H_n=\sum_{j=1}^n\frac1j.
\]
An \(\ell^2\) sequence tends to zero, whereas \(H_n\to\infty\). Therefore \(c=0\), and the resulting constant sequence must have \(y_0=0\). This proves \((DW)^\perp=\{0\}\).

Now project target \(b=-e_0\) onto \(U_N\). Put
\[
p^{(N)}=\sum_{n=0}^N\frac{e_n}{n+1},\qquad
q_N=\|p^{(N)}\|^2=\sum_{j=1}^{N+1}\frac1{j^2}.
\]
Inside \(\operatorname{span}\{e_0,\ldots,e_N\}\), the orthogonal complement of \(U_N\) is \(\mathbb Rp^{(N)}\). Hence the residual and its squared norm are exactly
\[
a_N=b-P_{U_N}b=-\frac{p^{(N)}}{q_N},\qquad
E_N=\frac1{q_N}\longrightarrow\frac1{\zeta(2)}>0.
\]
Also \(a_N\to a=-p/\zeta(2)\) in norm.

Define \(J_N(t)\) as above. For any \(t_N\to0\), density of \(D\bigcup_N U_N\) supplies a fixed finite lift approximating \(a\) arbitrarily closely. Keeping that lift fixed while \(N\to\infty\), its energy tends to its squared approximation error. Nonnegativity then proves \(J_N(t_N)\to0\).

For positive \(t\), however, set \(r=Dv-a_N\). Orthogonality \(a_N\perp v\) and the isometry of \(S\) give
\[
E_N=\|r\|^2+2\langle r,Sv\rangle
\le\|r\|^2+2\|r\|\|v\|.
\]
Using \(2t\|r\|\|v\|\le\|r\|^2+t^2\|v\|^2\), taking infima yields
\[
\frac{J_N(t)}t\ge\frac{E_N}{1+t}.
\]
Therefore every positive vanishing schedule has divided-energy lower limit at least \(1/\zeta(2)\). Shifted density, exact finite minimization, residual convergence, and unscaled convergence all hold together here, while the desired divided rate fails. The actual arithmetic source and Gram structure must contribute information absent from this model.
