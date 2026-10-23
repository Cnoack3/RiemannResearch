# Optimal exact heads and annihilator rigidity in complete Q

**Date:** 23 October 2026.
**Continuation of:** `RH_Uniform_Dual_Bound_Research_Agenda_Continued (1).md`.
**Scope:** the actual complete Q Hilbert space and the closed full legal residue span.
**RH status:** not proved. The arithmetic providers identified below remain open.

## 1. Setting and conclusions

Let
\[
Q(n)=\frac1{\zeta(2)n^2},\qquad
V=\overline{\operatorname{span}_{\mathbb R}\{g_d:d\ge2\}},\qquad
g_d(n)=\frac{n\bmod d}{d}.
\]
Write \(P_V\) for the actual orthogonal projection, \(r=1-P_V1\),
and \(T_M\) for restriction to the first M normalized coordinates.
The Lean `QHilbert` coordinate with index n represents the physical value
at n+1 multiplied by \(\sqrt{Q(n+1)}\).

The continuation formalizes the optimal exact-head problem, its finite-legal
repair, and stronger restrictions on possible annihilators. These results use
the entire infinite Q tail. No sampled metric or truncated norm is substituted.

## 2. The exact optimal interpolation problem

Define
\[
\mathcal E_M=\min\{\|f\|_Q^2:f\in V,\ T_Mf=T_M1\}.
\]
There is a unique minimizer \(f_M\). If \(e_i\) denotes a normalized coordinate
atom and \(t_M=T_M1\), the actual compressed projection matrix is
\[
K_M(i,j)=\langle P_Ve_j,e_i\rangle_Q.
\]
It is strictly positive definite, without any RH or invertibility hypothesis.
The checked construction gives the literal inverse formula
\[
\boxed{\mathcal E_M=t_M^{\mathsf T}K_M^{-1}t_M.}
\]
For every feasible \(f\in V\),
\[
\boxed{\|f\|_Q^2=\mathcal E_M+\|f-f_M\|_Q^2.}
\]
For \(N\ge M\), therefore,
\[
\boxed{\mathcal E_N-\mathcal E_M=\|f_N-f_M\|_Q^2.}
\]
The successive innovations \(f_{M+1}-f_M\) are pairwise orthogonal.

For each fixed M, finite legal vectors can approximate every closed feasible
vector while preserving its head exactly. A continuous right inverse into the
finite legal span repairs any approximate head. Its operator estimate uses the
Pi sup norm on the finite coordinate codomain; no bound uniform in M is assumed.
Consequently, \(\mathcal E_M\) is also the greatest lower bound of the squared
norms of finite legal exact-head vectors. This resolves the density qualification
in the previous agenda.

Principal declarations in `RH.QOptimalExactHead` include `headGram_posDef`,
`energy_inverseMatrix`, `norm_sq_completion`, `energy_increment`,
`innovation_orthogonal`, and `energy_isGLB_finiteLegal`.
The repair construction is in `RH.QFullHeadRepair`.

For M>0 the exact squared dual constant is also attained. The finite supported
witness uses the inverse-Gram coefficients:
\[
a_M=\sum_{i<M}(K_M^{-1}t_M)_i e_i,\qquad
P_Va_M=f_M,\qquad
\langle1,a_M\rangle_Q=\mathcal E_M.
\]
Its projected squared norm is \(\mathcal E_M>0\). Hence
\[
\boxed{\mathcal E_M=
\max_{a\ne0,\ \mathrm{supp}(a)\subseteq[1,M]}
\frac{|\langle1,a\rangle_Q|^2}{\|P_Va\|_Q^2}.}
\]
The declarations `energy_isLeast_squared_dual_constant` and
`dualWitness_quotient` give the least constant and its explicit equality witness.
The zero-head case is excluded from the least-constant statement because all
of its tests are zero.

## 3. A strong convergence dichotomy

The formal results give
\[
1\in V\iff\sup_M\mathcal E_M<\infty
\iff\forall M,\ \mathcal E_M\le1.
\]
More precisely,
\[
\begin{aligned}
1\in V&\implies f_M\to1\text{ strongly},\quad\mathcal E_M\uparrow1,\\
1\notin V&\implies\mathcal E_M\to+\infty.
\end{aligned}
\]
In the first branch there is the explicit estimate
\[
\|f_M-1\|_Q\le\|1-\operatorname{finiteHead}_M1\|_Q.
\]
Unconditionally, \(\mathcal E_M\le\|E_M\|_Q^2\), where E_M is the existing
Möbius interpolant; in particular, \(\mathcal E_M/M\to0\).
Sublinear divergence is still possible under the available estimates.

The RH implication `riemannHypothesis_of_energy_bounded` is conditional:
it assumes, and does not prove, bounded optimal energies.

## 4. The sharp head-versus-tail energy inequality

Set \(m_M=\sum_{n\le M}Q(n)\) and
\(\tau_M(u)=\sum_{n>M}Q(n)|u(n)|^2\).
For \(u\in V^\perp\) and any exact-head \(f\in V\), the complete signed identity is
\[
\boxed{\langle1,\operatorname{finiteHead}_Mu\rangle_Q
=-\langle f-\operatorname{finiteHead}_M1,
u-\operatorname{finiteHead}_Mu\rangle_Q.}
\]
The remainder has squared norm \(\|f\|_Q^2-m_M\). Therefore
\[
\boxed{
|\langle1,\operatorname{finiteHead}_Mu\rangle_Q|^2
\le(\|f\|_Q^2-m_M)\tau_M(u).
}
\]
Specializing to the actual optimizer and residual gives
\[
\boxed{(\mathcal E_M-m_M)\tau_M(r)
\ge |\langle1,\operatorname{finiteHead}_Mr\rangle_Q|^2.}
\]
No head contribution or signed cross term has been dropped in the identity.
These statements are in `RH.QExactHeadTailEnergy`, with the optimizer
specialization `QOptimalExactHead.actualResidual_energy_tail_bound`.

## 5. Tail escape for every nonzero annihilator

The former theorem required \(\langle1,u\rangle_Q\ne0\).
That hypothesis is removed by floor dilation:
\[
S_df(n)=f(\lfloor n/d\rfloor),\qquad f(0)=0.
\]
These operators preserve legal vectors. Since E_M is exact on the first M
physical coordinates, so is the vanishing of \(S_d(1-E_M)\). Thus
\[
\boxed{\langle S_d1,u\rangle_Q
=\langle S_d(1-E_M),\operatorname{tail}_Mu\rangle_Q.}
\]
Successive targets satisfy \(S_d1-S_{d+1}1=\mathbf1_{\{d\}}\), so a nonzero
u has a nonzero pairing with some S_d1. Dilation norm control and the already
verified all-logarithmic energy savings yield
\[
\boxed{
u\in V^\perp,\ u\ne0
\implies
\frac{M\tau_M(u)}{(6+\log M)^k}\longrightarrow+\infty
\quad\text{for every fixed }k\in\mathbb N.
}
\]
The module also proves that a cofinal bounded logarithmically scaled tail forces
the entire annihilator to vanish. This is stronger for zero-mean annihilators.
For the actual residual the earlier nonzero-mean condition was already automatic
when r is nonzero, because \(\langle1,r\rangle_Q=\|r\|_Q^2\).

Principal module: `RH.QAnnihilatorDilationEscape`.

## 6. Harmonic sign rigidity

For a nonzero full-span annihilator u, both nonnegative harmonic series must diverge:
\[
\boxed{\sum_{n\ge1}\frac{u_+(n)}n=+\infty,
\qquad\sum_{n\ge1}\frac{u_-(n)}n=+\infty.}
\]
Here \(u_+=\max(u,0)\) and \(u_-=\max(-u,0)\). In particular, finiteness of
either series for the actual residual would imply RH. This is a conditional
criterion; no such finiteness provider is established.

Consequently every nonzero annihilator has strictly positive and strictly
negative physical coordinates arbitrarily far out. Eventual nonnegativity or
eventual nonpositivity of the actual residual would therefore also imply RH.
Neither eventual-sign hypothesis is proved for that residual.

An ordinary corollary, not separately formalized here, is a one-sided
logarithmic barrier: for any fixed C>=0 and epsilon>0, either eventual bound
\[
r(n)\ge-\frac{C}{(\log n)^{1+\varepsilon}}
\quad\text{or}\quad
r(n)\le\frac{C}{(\log n)^{1+\varepsilon}}
\]
would suffice for RH, without controlling the opposite sign. The corresponding
harmonic sign series is dominated by the convergent series
\(\sum_{n\ge2}1/[n(\log n)^{1+\varepsilon}]\). Such a barrier for r remains open.

The proof retains signs throughout. Put \(a_n=Q(n)u(n)\). Residue orthogonality
gives \(\sum(n\bmod d)a_n=0\). If the first harmonic mass of one sign is finite,
these exact identities bound every finite partial first moment of the other
sign. Hence \(\sum n|a_n|<\infty\). Dominated convergence then gives
\(\sum na_n=0\), and subtraction yields
\(\sum\lfloor n/d\rfloor a_n=0\).

Let \(F(k)=\sum_{n\ge k}a_n\), with F(0)=0. Absolute first moment makes F summable,
and justified exchange of sums gives \(\sum_{j\ge1}F(dj)=0\). A finite factorial
Möbius sieve isolates F(d); dominated convergence implies F=0. Taking successive
tail differences then gives u=0.

Lean's `Summable` for real sequences is absolute, unconditional summability.
None of the conclusions uses mere conditional convergence of signed partial sums.

Modules: `Analysis.SummableMultiplesRigidity`, `RH.QSignedTailRigidity`,
and `RH.QOneSidedHarmonicRigidity`.

## 7. Finite checks and sources

Wolfram Language checked exactly, for M=1,...,12, the consecutive-conductor head
determinant \(1/(M+1)\), the floor-matrix determinant 1, and the full Möbius
inverse formula. These finite checks do not establish an infinite-dimensional
uniform bound and are not used as Lean proof evidence.
It also checked the factorial Möbius sieve exactly on the signed finite sequence
\(F(n)=(-1)^n/n^2\) supported on 1,...,12, recovering each F(k) for k=1,...,12.

The mathematical source for the agenda's optimization and sign arguments is the
user-provided continuation. Related primary references consulted were:

- Luis Báez-Duarte, [Arithmetical Aspects of Beurling's Real Variable Reformulation
  of the Riemann Hypothesis](https://arxiv.org/abs/math/0011254): arithmetic closure
  criteria and the distinction between pointwise/L1 and L2 approximation.
- Luis Báez-Duarte, [A strengthening of the Nyman-Beurling criterion](https://arxiv.org/abs/math/0202141):
  the natural-number dilation framework.
- Calderaro, Manzur, Noor, Santos, [Orthogonality questions in the Hardy space
  related to zeta-zeros](https://arxiv.org/html/2203.05030v3): related orthogonality,
  biorthogonality, and dilation questions. Its Hardy-space statements are not
  silently substituted for complete-Q statements.

No mathematical novelty claim is made.

## 8. What still needs to be proved for RH

Any one of the following would complete the corresponding verified route:

1. An unconditional bound \(\sup_M\mathcal E_M<\infty\).
2. Finiteness of either harmonic sign series of the actual residual r.
3. A cofinal bound \(M_j\tau_{M_j}(r)\le B(6+\log M_j)^k\) for one fixed k and B.

Strict positivity of each finite K_M does not supply (1). Orthogonality of energy
increments does not imply their squared norms are summable. L2 membership alone
does not supply (2) or (3). Multiplying an annihilator by a decay factor usually
destroys its residue orthogonality, so harmonic regularization requires its own
invariance argument. The full-span statements here do not automatically become
squarefree-span statements.

## 9. Verification scope

The successful prepublication Lean job was
`job_6JSQQECThEusPOCdbcq6HWin9cDQ4NJD` (`verified: true`, exit code 0).
It imported the saved modules and checked the exact dual-attainment extension.
The server reported 8.347 seconds of checking; its queue delay was below 0.01
seconds. An earlier iteration waited about 324 seconds in the shared queue;
that wait was not proof-checking time. Workspace hydration was not instrumented.

The saved signed-tail and one-sided modules had been source-built in the
preceding job (8.3 and 5.3 seconds respectively). The other new modules had
also been source-built earlier. The final dual extension was then copied into
`RH.QOptimalExactHead` with the same declarations and namespace context.

Axiom audits of the inverse matrix, finite legal infimum, energy dichotomy,
attained least dual constant, harmonic divergence, sign oscillation, conditional
RH consumers, and universal logarithmic tail escape reported only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx` occurs in those dependencies.
No proof placeholders or new axioms were added to the saved sources.

The publication checkpoint validates the final affected source modules and the
root import aggregate before committing and pushing. Its terminal publication
result and commit are reported in the accompanying conversation; the successful
prepublication check is not presented as a substitute for that final validation.
