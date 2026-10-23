# Continuation: stronger complete-Q bounds and sharper RH criteria

**Date:** 22 October 2026.
**Scope:** the actual complete \(Q\)-norm and the full legal residue span.
**RH status:** not proved. The new sufficient conditions on the actual residual remain open.

This continuation strengthens the original agenda in three distinct ways: it transfers a stronger arithmetic estimate already present in the repository to \(Q\), proves a sharper residual-tail criterion, and resolves several finite-head optimization questions in ordinary mathematics. It also records a stronger sign-rigidity theorem. No mathematical novelty claim is intended.

## What is stronger

Write \(E_M\) for the original Möbius exact-head vector, \(C_M=\|E_M\|_Q\), \(D_M=\|1-E_M\|_Q\), and
\[
\phi(M)=\bigl((6+\log M)\log(6+\log M)\bigr)^{1/11}.
\]
The new Lean development proves unconditional, complete-norm bounds: there are positive \(a\) and nonnegative constants \(C,C'\) such that eventually
\[
\boxed{C_M^2\le\frac6{\zeta(2)}+CM e^{-a\phi(M)}},
\qquad
\boxed{D_M^2\le\frac{16}{\zeta(2)}+C'M e^{-a\phi(M)}}.
\tag{S1}
\]
The exponent coefficients and constants may differ between the two displayed bounds; decrease the coefficient and enlarge the constant to obtain a common pair if desired. These bounds reuse the existing unconditional Pareto Mertens/energy provider; they do not assume RH.

For every fixed integer \(k\ge0\), this gives constants depending on \(k\) with
\[
\boxed{C_M^2\le\frac6{\zeta(2)}+\frac{C_kM}{(6+\log M)^k}},
\qquad
\boxed{D_M^2\le\frac{16}{\zeta(2)}+\frac{C'_kM}{(6+\log M)^k}}
\tag{S2}
\]
eventually. This strengthens \(C_M^2=o(M)\) to every fixed logarithmic saving. It still permits divergent energy.

For every \(u\in V^\perp\), the exact identity and its consequence are
\[
\boxed{\langle1,u\rangle_Q
=\langle1-E_M,\mathbf1_{n>M}u\rangle_Q},
\qquad
\boxed{|\langle1,u\rangle_Q|^2\le D_M^2\tau_M(u)}.
\tag{S3}
\]
This holds for every head \(M\), without an eventual factor \(1/4\). Here
\(\tau_M(u)=\sum_{n>M}Q(n)|u(n)|^2\).

Consequently the new Lean tail theorem gives
\[
\boxed{\langle1,u\rangle_Q\ne0
\quad\Longrightarrow\quad
\frac{M\tau_M(u)}{(6+\log M)^k}\longrightarrow+\infty
\quad\text{for every fixed }k\ge0.}
\tag{S4}
\]
For the actual residual \(r=(I-P_V)1\), its mean equals \(\|r\|_Q^2\). Thus a cofinal subsequence \(M_j\to\infty\) with
\[
\boxed{M_j\tau_{M_j}(r)\le B(6+\log M_j)^k}
\tag{S5}
\]
for some fixed \(k,B\) suffices for RH. A bound eventually in \(j\) is equivalent for this purpose, after enlarging \(B\) for finitely many terms. This permits polylogarithmic growth where the original agenda required boundedness. **No bound of the form \(S5\) has been proved for the actual residual.**

## Exact formalization scope

| Result | Status in this continuation |
| --- | --- |
| Exact defect-tail identity for every full-span annihilator | Lean checked |
| Arbitrary-weight tail escape from \(D_M^2/w_M\to0\) | Lean checked |
| Unconditional complete-\(Q\) stretched energy estimates \(S1\) | Lean checked |
| Every fixed logarithmic saving \(S2\) | Lean checked |
| Logarithmic tail escape \(S4\) and conditional RH consumer \(S5\) | Lean checked |
| Every finite head has a finite legal interpolant | Lean checked |
| Projection kernel is trivial on finite coordinate heads | Lean checked |
| Compensated residue equals a signed floor on its anchored head | Lean checked |
| Determinant \(1/(M+1)\), explicit inverse formula, minimum attainment, exact repair, strong minimizer dichotomy | Ordinary proofs below; determinant also checked in Wolfram for \(M=1,\ldots,10\) |
| Both signs of a nonzero annihilator have infinite harmonic mass | Ordinary proof below; not formalized here |
| Sharper classical Korobov–Vinogradov \(3/5\) energy profile | Ordinary proof using an external analytic theorem; not formalized here |
| Uniform signed dual bound, bounded optimal energies, or the actual residual hypotheses | **Open** |

The all-logarithmic consequences are formally obtained from the repository's \(1/11\) profile. They do not rely on the external \(3/5\) theorem discussed below.

## Lean modules and assumptions

The continuation adds:

- `RiemannResearch/RH/QMobiusStretchedEnergy.lean`: the complete-\(Q\) transfer, its finite Mertens-envelope estimate, and all logarithmic energy bounds.
- `RiemannResearch/RH/QAnnihilatorTailEscape.lean`: exact identities, weighted escape, logarithmic escape, and conditional RH consumers for the actual residual.
- `RiemannResearch/RH/QFullHeadControllability.lean`: arbitrary physical heads and finite-test projection injectivity.

It extends `RiemannResearch/Analysis/StretchedExponentialBounds.lean` by proving domination by every fixed inverse natural power, with an explicit factorial-based constant.

Principal declarations:

- `QMobiusStretchedEnergy.exactHead_eventual_stretched_energy`
- `QMobiusStretchedEnergy.exactHead_error_eventual_stretched_energy`
- `QMobiusStretchedEnergy.exactHead_energy_of_uniform_mertens_log`
- `QMobiusStretchedEnergy.exactHead_eventual_log_power_energy`
- `QMobiusStretchedEnergy.exactHead_error_eventual_log_power_energy`
- `QAnnihilatorTailEscape.annihilator_defect_tail_identity`
- `QAnnihilatorTailEscape.actualResidual_fourth_le`
- `QAnnihilatorTailEscape.annihilator_weighted_tail_tendsto_atTop`
- `QAnnihilatorTailEscape.annihilator_log_scaled_tail_tendsto_atTop`
- `QAnnihilatorTailEscape.riemannHypothesis_of_cofinal_log_tail_bound`
- `QFullHeadControllability.interpolate_head`
- `QFullHeadControllability.finiteHead_projection_eq_zero_iff`
- `QFullHeadControllability.compensatedResidue_floor`

All names in this list are under `RiemannResearch.RH`, except the two inverse-power lemmas under `RiemannResearch.Analysis`. The unconditional energy declarations have no unresolved arithmetic hypotheses. The finite-envelope theorem explicitly assumes its Mertens envelope, and the RH consumer explicitly assumes \(S5\). The verification record below distinguishes these theorem types from a proof of their hypotheses.

## Wolfram experiments with the complete Gram matrix

For each conductor pair \(d,e\), with \(L=\operatorname{lcm}(d,e)\), the experiment used
\[
G(d,e)=\frac1{\zeta(2)L^2}\sum_{r=1}^{L}
g_d(r)g_e(r)\,\psi_1(r/L).
\]
Thus the periodic infinite tail is included analytically. For a dictionary \(2,\ldots,D\) and head matrix \(A(n,d)=g_d(n)\), the constrained coefficients were computed from
\[
c=G^{-1}A^T(AG^{-1}A^T)^{-1}\mathbf1.
\]

| Head \(M\) | Largest conductor \(D\) | Computed minimum complete energy |
| ---: | ---: | ---: |
| 1 | 2 | 0.750000000000 |
| 1 | 3 | 0.747427239399 |
| 2 | 3 | 0.916510303869 |
| 2 | 5 | 0.902516623944 |
| 3 | 4 | 0.967211121816 |
| 3 | 6 | 0.922411941854 |
| 4 | 5 | 1.002101671598 |
| 4 | 8 | 0.966302787446 |

These are 35-digit working-precision Wolfram computations, displayed rounded, without interval certification. The computed head discrepancies were zero to the reported precision. They are diagnostic evidence, not a proof of a uniform bound. The \(M=4\) example illustrates why an optimum exceeding one for a small dictionary is not a lower bound for the full-span optimum.

## Updated research priorities

1. **Actual residual growth:** prove \(S5\) for one fixed logarithmic exponent, or a still weaker subexponential condition derived below. The analytic energy side is now substantially stronger; the missing side is information about \(r\).
2. **One-sided harmonic summability:** determine whether either \(\sum r_+(n)/n\) or \(\sum r_-(n)/n\) is finite. The ordinary rigidity theorem below would force (r=0). Neither finiteness assertion is known here.
3. **Optimal exact-head energy:** use the inverse formula and exact orthogonal increments below to seek \(\sup_M\mathcal E_M<\infty\). Finite-dimensional invertibility alone does not bound inverse norms as (M\to\infty\).
4. **Formalization priorities:** formalize the sign-rigidity proof and the closed-span minimizer/inverse identities. These would complete more of the structural picture but would not by themselves establish the missing arithmetic bounds.
5. **Sharper analytic provider:** the classical \(3/5\) profile below improves the size of the allowed residual tail. Its Lean formalization is additional work, not a prerequisite for the already checked all-logarithmic criterion.

## Verification and publication record

The combined isolated development passed Lean verification in job `job_vbzwte60hQzd4HQikwe_HyWUVPs4VpMO` (exit code 0; server checking duration 8.651 seconds). The energy theorem and strengthened RH consumer report only `propext`, `Classical.choice`, and `Quot.sound`; earlier checks confirmed the same for the arithmetic provider and finite-head injectivity. No `sorry`, project-local axioms, or unsafe declarations are introduced.

The isolated job began approximately 0.005 seconds after submission; polling and workspace opening are separate from the reported checking duration. Workspace-opening latency was not separately instrumented. This note is included in the final project checkpoint, which must validate the changed modules and required dependents before publication; the user-facing copy records the terminal checkpoint result and commit after completion.

The original agenda is retained next as a historical snapshot. Its sections listing open formalization milestones are superseded where the status table above says they have now been checked; its unresolved uniform signed bound remains unresolved.

---

# Uniform Dual Bounds in the Complete Q Space
## Verified results and a research agenda toward RH

**Research snapshot:** commit `75c8b7a193bd9d23696c2d0f7837e8937ad350c1`.
**Mathematical status:** the uniform bound for arbitrary signed tests remains **Open**.
**Scope of this document:** summarize the verified development and specify further research targets. The research agenda below contains ordinary mathematical derivations and proposed formalizations, clearly distinguished from completed Lean proofs.

## 1. The exact problem

Work in the real Hilbert space
\[
H=L^2(Q),\qquad Q(n)=\frac{1}{\zeta(2)n^2},\quad n\ge1.
\]
For each integer \(d\ge2\), let
\[
g_d(n)=\frac{n\bmod d}{d}.
\]
Let
\[
V=\overline{\operatorname{span}_{\mathbb R}\{g_d:d\ge2\}},
\qquad P_V:H\longrightarrow V
\]
be the actual closed full legal residue span and its orthogonal projection. All norms and inner products in this note use the complete \(Q\) measure, including the infinite tail. The constant target satisfies \(\|1\|_Q=1\).

Write \(a_M\) for the restriction of a test \(a\) to physical coordinates \(1,\ldots,M\), extended by zero. The desired estimate is
\[
\boxed{
\exists C<\infty\ \forall M\ \forall a,\qquad
|\langle1,a_M\rangle_Q|
\le C\|P_Va_M\|_Q.
}
\tag{U}
\]

The same constant must work for every support size and every signed test. No sign restriction is permitted in (U).

The existing Lean criterion proves
\[
1\in V
\quad\Longleftrightarrow\quad
\text{(U)}.
\]
It also proves that membership gives the sharp sufficient constant \(C=1\). The repository's established closure-to-RH implication then supplies RH from (U). This is a **conditional research reduction** until an unconditional arithmetic provider for (U) is proved.

In Lean, `QHilbert` is a normalized \(\ell^2\) realization. Its coordinate `a n` corresponds to physical coordinate \(n+1\), multiplied by \(\sqrt{Q(n+1)}\). Thus `finiteHead M a` keeps normalized indices \(0,\ldots,M-1\), equivalently physical indices \(1,\ldots,M\). These positive normalization factors preserve signs.

## 2. What Lean has verified

| Result | Status | Scope |
| --- | --- | --- |
| Finite-support projected-test criterion for \(1\in V\) | Verified | All signed finite tests; the common bound is a hypothesis in the RH implication |
| Exact pairing with the Möbius head interpolant | Verified unconditionally | All signed finite tests |
| Support-dependent signed bound with constant \(C_M\) | Verified unconditionally | One constant for each \(M\) |
| \(C_M^2/M\to0\) and \(C_M^2<8M/\zeta(2)\) for \(M>0\) | Verified unconditionally | Does not establish \(\sup_M C_M<\infty\) |
| Uniform bound with \(4\sqrt{2/\zeta(2)}\) | Verified unconditionally | Nonnegative tests, including infinite support |
| Uniform bound for arbitrary signed tests | **Open** | The missing statement (U) |
| Unconditional RH conclusion from this development | **Not obtained** | The signed arithmetic provider is still missing |

### 2.1 Exact signed pairing

Let \(E_M\) be the existing concrete Möbius exact-head interpolant. Lean proves
\[
E_M\in\operatorname{span}\{g_d:d\ge2\},
\qquad E_M(n)=1\quad(1\le n\le M).
\]
Consequently, for every signed test \(a_M\),
\[
\boxed{
\langle1,a_M\rangle_Q
=\langle E_M,a_M\rangle_Q
=\langle E_M,P_Va_M\rangle_Q.
}
\tag{1}
\]
This is an exact identity. It retains the signs of the test.

Define
\[
C_M=\|E_M\|_Q.
\]
Applying Cauchy–Schwarz to (1) gives
\[
\boxed{
|\langle1,a_M\rangle_Q|
\le C_M\|P_Va_M\|_Q.
}
\tag{2}
\]

The implementation reuses the existing unconditional Möbius energy estimates to establish
\[
\boxed{\frac{C_M^2}{M}\longrightarrow0},
\qquad
\boxed{C_M^2<\frac{8M}{\zeta(2)}\quad(M>0)}.
\tag{3}
\]
The first statement is sublinear growth of the squared constants. It does not imply bounded constants: for example, \(C_M=M^{1/4}\) would satisfy that asymptotic while growing without bound. This example illustrates the logical distinction; it is not a claimed asymptotic for the actual \(C_M\).

Declarations in `RH/QFiniteSupportDualEstimates.lean`:

- `exactHead_finite_test_pairing`
- `dualHeadConstant`
- `finiteHead_dual_bound`
- `dualHeadConstant_sq_sublinear`
- `dualHeadConstant_sq_lt`

### 2.2 Finite legal majorants with a uniform complete norm

For \(K\ge0\), define
\[
\boxed{B_K=4\sum_{k=0}^{K-1}g_{4^{k+1}}.}
\tag{4}
\]
Each \(B_K\) is a finite legal vector. Its physical sequence is exactly the sum in (4).

The previously established complete atom estimate
\[
\|g_d\|_Q^2\le\frac{2}{\zeta(2)d},\qquad d\ge2,
\]
gives
\[
\|g_{4^{k+1}}\|_Q
\le\sqrt{\frac2{\zeta(2)}}\,2^{-(k+1)}.
\]
Summing the geometric series yields
\[
\boxed{\|B_K\|_Q\le4\sqrt{\frac2{\zeta(2)}}.}
\tag{5}
\]

If \(0<n<4^K\), there is a \(k<K\) with
\[
4^k\le n<4^{k+1}.
\]
At this conductor,
\[
g_{4^{k+1}}(n)=\frac{n}{4^{k+1}}\ge\frac14.
\]
Every other summand in (4) is nonnegative, so
\[
\boxed{B_K(n)\ge1\qquad(0<n<4^K).}
\tag{6}
\]

These conductors are powers of \(4\). The construction therefore belongs to the **full legal span**. It is not a squarefree-conductor construction.

### 2.3 Uniform dual control for nonnegative tests

Take \(K=M+1\). Since \(M<4^{M+1}\), (6) covers the support of \(a_M\). If \(a_M\ge0\), then
\[
\begin{aligned}
0\le\langle1,a_M\rangle_Q
&\le\langle B_K,a_M\rangle_Q\\
&=\langle B_K,P_Va_M\rangle_Q\\
&\le\|B_K\|_Q\|P_Va_M\|_Q.
\end{aligned}
\]
Thus Lean proves
\[
\boxed{
|\langle1,a_M\rangle_Q|
\le4\sqrt{\frac2{\zeta(2)}}\,\|P_Va_M\|_Q,
\qquad a_M\ge0.
}
\tag{7}
\]

The constant is independent of \(M\) and \(a\). Strong convergence of finite heads and continuity of \(P_V\) extend this to every nonnegative \(a\in H\):
\[
\boxed{
|\langle1,a\rangle_Q|
\le4\sqrt{\frac2{\zeta(2)}}\,\|P_Va\|_Q,
\qquad a\ge0.
}
\tag{8}
\]

The principal declarations in `RH/QNonnegativeDualBound.lean` are:

- `fourMajorant_sequence`
- `fourMajorant_mem_legalSpan`
- `fourMajorant_norm_le`
- `fourMajorant_majorizes`
- `nonnegative_finite_test_uniform_dual_bound`
- `nonnegative_uniform_dual_bound`

No target-membership hypothesis is assumed in these results.

## 3. Why the full signed problem remains

For \(a=a_+-a_-\), the exact projected energy is
\[
\boxed{
\|P_Va\|_Q^2
=\|P_Va_+\|_Q^2+\|P_Va_-\|_Q^2
-2\langle P_Va_+,P_Va_-\rangle_Q.
}
\tag{9}
\]
Separate estimates for the positive and negative parts do not control this cancellation. Replacing \(a\) by \(|a|\) gives a bound involving \(\|P_V|a|\|_Q\), not the denominator in (U).

Likewise, a uniformly bounded legal majorant need not be an exact-head interpolant. A limiting vector \(B\in V\) satisfying \(B\ge1\) does not identify \(B\) with \(1\). With \(B\in V\), proving \(B-1\in V\) is equivalent to proving \(1\in V\).

An elementary finite-dimensional example shows why positivity alone is insufficient. In \(\mathbb R^2\), take
\[
t=(1,1),\qquad V_0=\operatorname{span}(1,2),\qquad b=(1,2).
\]
Then \(b\in V_0\), \(b\ge t\), and the orthogonal projector onto \(V_0\) has nonnegative matrix entries. Yet for \(a=(2,-1)\),
\[
P_{V_0}a=0,\qquad \langle t,a\rangle=1.
\]
Hence no signed dual bound exists in this example. This is an explanatory calculation, not a newly checked Lean declaration.

## 4. Research priority I: combine the sublinear constants with actual residual tails

**Status of this section:** ordinary mathematical derivation; the corresponding declarations were not added or checked in this documentation turn. Search the repository for existing versions before formalizing.

Define the actual orthogonal residual
\[
r=(I-P_V)1,\qquad r_M=\operatorname{finiteHead}_M r,
\qquad \tau_M=\|r-r_M\|_Q^2.
\]
Then
\[
P_Vr=0,\qquad
\langle1,r\rangle_Q=\|r\|_Q^2.
\]
Apply the verified signed estimate (2) to \(r_M\):
\[
\begin{aligned}
|\langle1,r_M\rangle_Q|
&\le C_M\|P_Vr_M\|_Q\\
&=C_M\|P_V(r_M-r)\|_Q\\
&\le C_M\sqrt{\tau_M}.
\end{aligned}
\tag{10}
\]
Finite-head convergence gives
\[
\langle1,r_M\rangle_Q\longrightarrow\|r\|_Q^2.
\]

It follows that a cofinal sequence \(M_j\to\infty\) satisfying
\[
\boxed{C_{M_j}^2\tau_{M_j}\longrightarrow0}
\tag{11}
\]
would force \(r=0\), hence \(1\in V\), and then RH.

The verified asymptotic \(C_M^2/M\to0\) makes the following sufficient:
\[
\boxed{\sup_j M_j\tau_{M_j}<\infty
\quad\text{for some }M_j\to\infty.}
\tag{12}
\]
A bound for every \(M\) would also suffice, but (12) only asks for a cofinal subsequence.

In physical coordinates,
\[
M\tau_M
=\frac{M}{\zeta(2)}
\sum_{n>M}\frac{|r(n)|^2}{n^2}.
\tag{13}
\]

There is also a useful contrapositive. If \(r\ne0\), then eventually
\[
|\langle1,r_M\rangle_Q|\ge\frac12\|r\|_Q^2.
\]
Squaring (10) gives
\[
C_M^2\tau_M\ge\frac14\|r\|_Q^4.
\tag{14}
\]
Combining (14) with \(C_M^2/M\to0\) forces
\[
\boxed{r\ne0\quad\Longrightarrow\quad M\tau_M\longrightarrow+\infty.}
\tag{15}
\]

**Immediate formalization milestone:** establish (10), the subsequence implication (11)–(12), and the escape statement (15) using the actual residual and existing sublinear constants.

**Open arithmetic provider:** prove (12), or directly prove (11), from independent information about the actual residual. Mere square integrability gives \(\tau_M\to0\), without the needed rate.

Uniform boundedness of the physical residual would imply (12), because
\[
|r(n)|\le A
\quad\Longrightarrow\quad
\tau_M\le\frac{A^2}{\zeta(2)M}.
\]
That physical boundedness is itself an unresolved property; an orthogonal projection is not automatically bounded on \(L^\infty\).

## 5. Research priority II: optimize exact-head energy

Instead of requiring the particular Möbius family \(E_M\) to have uniformly bounded norms, consider
\[
\mathcal E_M
=\min\left\{\|f\|_Q^2:
f\in V,\ f(n)=1\ \text{for }1\le n\le M\right\}.
\tag{16}
\]
The feasible set is nonempty because it contains \(E_M\).

The proposed formalization milestones are:

1. Establish attainment in the closed Hilbert subspace \(V\).
2. Prove monotonicity in \(M\) and \(\mathcal E_M\le C_M^2\).
3. Locate or formalize the implication
   \[
   \sup_M\mathcal E_M<\infty\ \Longrightarrow\ 1\in V.
   \]
4. Identify an arithmetic construction or comparison giving a bound independent of \(M\).

**Important distinction:** (16) is a minimum over the closed space \(V\). Equating it with the infimum over finite legal interpolants requires an exact finite-head repair argument; density alone does not automatically preserve exact constraints.

The desired estimate concerns the target direction. A uniform bound for every interpolation problem or every inverse-Gram eigenvalue would be stronger than necessary.

Where applicable, reuse the repository's exact head-step energy identities. An increment of the form
\[
\mathcal E_M-\mathcal E_{M-1}
=\frac{\delta_M^2}{\operatorname{cap}_M}
\tag{17}
\]
suggests proving summability of the complete increments. The hypotheses and the metric underlying any existing capacity theorem must be matched before using (17). Neither nonnegativity of the increments nor sublinear growth proves their summability.

## 6. Research priority III: identify the optimal signed dual quantity

For normalized coordinate atoms \(e_1,\ldots,e_M\), define
\[
t_M=(\sqrt{Q(1)},\ldots,\sqrt{Q(M)})^\top,
\qquad
K_M(i,j)=\langle P_Ve_i,e_j\rangle_Q.
\]
Then \(K_M\) is positive semidefinite, and a finite test with normalized coefficient vector \(x\) satisfies
\[
\langle1,a_M\rangle_Q=t_M^\top x,
\qquad
\|P_Va_M\|_Q^2=x^\top K_Mx.
\]

The desired uniform estimate is exactly the target-direction matrix inequality
\[
\boxed{t_Mt_M^\top\preceq C^2K_M\quad\text{for every }M.}
\tag{18}
\]

A proposed next formalization is
\[
\boxed{
\mathcal E_M
=\sup_{x:\,x^\top K_Mx>0}
\frac{|t_M^\top x|^2}{x^\top K_Mx}
=t_M^\top K_M^+t_M,
}
\tag{19}
\]
where \(K_M^+\) denotes the Moore–Penrose pseudoinverse. Use \(M\ge1\) for the displayed quotient formulation. Handle zero-denominator vectors separately.

The exact-head feasible vector supplies the necessary range condition. Use a pseudoinverse until positive definiteness has actually been established.

**Status:** (18)–(19) are ordinary finite-dimensional formulations and proposed Lean milestones, not new Lean declarations from the completed checkpoint. Proving their equivalence does not itself supply the arithmetic bound.

## 7. Research priority IV: correct the excess of the legal majorants

For \(K=M+1\), seek a finite legal correction \(H_M\) satisfying
\[
H_M(n)=B_{M+1}(n)-1,\qquad 1\le n\le M.
\]
Then
\[
F_M=B_{M+1}-H_M
\]
is an exact-head legal vector. Its complete energy is
\[
\boxed{
\|F_M\|_Q^2
=\|B_{M+1}\|_Q^2+\|H_M\|_Q^2
-2\langle B_{M+1},H_M\rangle_Q.
}
\tag{20}
\]

The research target is a uniform upper bound for the full expression (20), retaining the signed cross term.

Choosing \(H_M=B_{M+1}-E_M\) only recovers the existing Möbius interpolant and its support-dependent estimate. A useful correction must provide new arithmetic control. Assuming the limiting excess is legal would assume the missing target-membership conclusion.

Improving the constant in the nonnegative bound is secondary: it does not remove the sign restriction in (7)–(8).

## 8. Research priority V: certified finite-dictionary experiments

Use finite dictionaries to search for and diagnose exact-head constructions. Keep two parameters distinct: the head size \(M\) and the conductor dictionary \(D\).

For a finite dictionary, form the complete matrix
\[
G_D(d,e)=\langle g_d,g_e\rangle_Q
\]
and solve the exact-head constrained energy minimization. If \(L\) is a common period, the exact Gram entry is
\[
G_D(d,e)
=\frac1{\zeta(2)}
\sum_{r=1}^{L}g_d(r)g_e(r)
\sum_{j=0}^{\infty}\frac1{(r+jL)^2}.
\tag{21}
\]
The periodic tail weights are part of the matrix.

For a finite legal vector \(f=\sum_dc_dg_d\), let \(A=\sum_d|c_d|\). Since \(|f(n)|\le A\), for \(T\ge1\),
\[
\sum_{n>T}Q(n)|f(n)|^2
\le\frac{A^2}{\zeta(2)T}.
\tag{22}
\]
For the residual \(1-f\), replace \(A^2\) by \((1+A)^2\). These elementary bounds can support certified truncation enclosures, although coefficient growth may make them too coarse.

Useful experimental outputs are:

- feasible coefficients and a complete norm enclosure;
- exact head verification;
- sensitivity to dictionary enlargement;
- the signed cross term in a proposed correction;
- the energy increment when the head is extended.

A finite legal interpolant gives an upper bound for \(\mathcal E_M\). A large optimum for an inadequate finite dictionary does not give a lower bound for the full-span optimum: enlarging the dictionary can reduce the energy. Likewise, finite numerical evidence cannot establish a uniform statement over all \(M\).

No numerical experiment or new tail certificate was performed for this document.

## 9. Suggested order of work

| Priority | Concrete next deliverable | What would advance the RH argument |
| --- | --- | --- |
| 1 | Lean residual-tail implication and escape statement, after checking for existing declarations | An independent arithmetic proof of bounded \(M\tau_M\) along a cofinal subsequence |
| 2 | Optimal exact-head energy and its monotonicity | A uniform upper bound on those minima |
| 3 | Exact dual quotient and target-direction pseudoinverse identity | Uniform control of \(t_M^\top K_M^+t_M\) |
| 4 | Legal excess-correction identity and construction | A bound on the complete signed energy in (20) |
| 5 | Certified dictionary experiments with full tails | A scalable arithmetic construction or a precise obstruction to a proposed family |

The first priority uses the newly verified sublinear signed constants directly. Its arithmetic hypothesis concerns the actual residual, so it must not be replaced by a bound for a different optimizer or a sampled surrogate.

For a squarefree-only program, keep a separate ledger: the majorants in (4) are not squarefree legal vectors. A full-span result cannot be silently reinterpreted as a squarefree-span result.

## 10. Verification record and source links

Published commit:

- [75c8b7a193bd9d23696c2d0f7837e8937ad350c1](https://github.com/Cnoack3/RiemannResearch/commit/75c8b7a193bd9d23696c2d0f7837e8937ad350c1)

Pinned source modules:

- [QFiniteSupportDualCriterion.lean](https://github.com/Cnoack3/RiemannResearch/blob/75c8b7a193bd9d23696c2d0f7837e8937ad350c1/RiemannResearch/RH/QFiniteSupportDualCriterion.lean)
- [QFiniteSupportDualEstimates.lean](https://github.com/Cnoack3/RiemannResearch/blob/75c8b7a193bd9d23696c2d0f7837e8937ad350c1/RiemannResearch/RH/QFiniteSupportDualEstimates.lean)
- [QNonnegativeDualBound.lean](https://github.com/Cnoack3/RiemannResearch/blob/75c8b7a193bd9d23696c2d0f7837e8937ad350c1/RiemannResearch/RH/QNonnegativeDualBound.lean)
- [UniformDualBoundResearch20261022.md](https://github.com/Cnoack3/RiemannResearch/blob/75c8b7a193bd9d23696c2d0f7837e8937ad350c1/RiemannResearch/RH/UniformDualBoundResearch20261022.md)
- [Earlier finite-test research note](https://github.com/Cnoack3/RiemannResearch/blob/75c8b7a193bd9d23696c2d0f7837e8937ad350c1/RiemannResearch/RH/UnitSignalFiniteTestResearch20261022.md)

Verification evidence:

- Combined candidate: `job_EBU77w9LrkbKruhd-pJ4_vJFynthC18o`, successful; server-reported checking duration 7.252 seconds.
- Saved-source import and axiom audit: `job_lcka8m2T4Zf526dmj0iDIVHRMpeV6j_I`, successful; server-reported duration 18.865 seconds.
- Final checkpoint: `job_KAYRgsUBLASSYwD4nD8mP015fy1plcvE`, successful and pushed.
- Final validation scope: incremental build of the aggregate `RiemannResearch` module plus the three changed Lean modules listed above; unchanged artifacts were reused.
- Final server-reported build duration: 96.222 seconds. Queue delay was below 0.01 seconds. Deliberate polling delays are excluded; the workspace was reused without a new opening request.
- Eleven key declarations in the saved-source axiom audit depended only on `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof or project-local axiom was introduced.

The present file is a documentation and research-agenda artifact. In particular, the residual-tail derivation and the proposed optimization/matrix formalizations in Sections 4–8 are not certified by the earlier checkpoint merely because they appear in this note.

**Remaining central obligation:** establish an unconditional arithmetic estimate that controls signed tests uniformly, or prove another independently justified condition such as the actual residual-tail bound in (12) that yields \(1\in V\).


---

## Continuation: finite-head controllability and exact optimal energies

**Status.** The arguments in this section are ordinary mathematical proofs. They must be distinguished from any declarations subsequently checked in Lean. They concern the full legal span, not a squarefree-only span.

Write \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\), and let \(e_n\) be the orthonormal coordinate atom in \(L^2(Q)\): its physical value at \(n\) is \(1/\sqrt{Q(n)}\), and it vanishes elsewhere. Thus the normalized head map is
\[
T_M f=(\sqrt{Q(1)}f(1),\ldots,\sqrt{Q(M)}f(M)),
\]
whereas a *physical head* lists the values \(f(1),\ldots,f(M)\). This distinction matters in the matrix formulas below.

### 1. An unconditional exact right inverse for every finite head

Fix \(M\ge1\), set \(q=M+1\), and use the harmless convention \(g_1=0\). Define finite legal vectors
\[
u_{M,d}=\frac qd g_q-g_d,\qquad 1\le d\le M.
\]
For \(1\le n\le M\), the inequality \(n<q\) gives
\[
u_{M,d}(n)=\frac nd-\frac{n\bmod d}{d}
=\left\lfloor\frac nd\right\rfloor.
\tag{23}
\]
Consequently the physical head matrix
\[
U_M(n,d)=\left\lfloor n/d\right\rfloor,
\qquad 1\le n,d\le M,
\]
is lower triangular with every diagonal entry equal to one. In particular, **every physical head can be interpolated using only the conductors \(2,\ldots,M+1\)**.

There is an explicit arithmetic formula. Given physical values \(x_1,\ldots,x_M\), put \(x_0=0\) and
\[
b_d=\sum_{e\mid d}\mu(d/e)(x_e-x_{e-1}),\qquad
R_M^{\rm phys}x=\sum_{d=1}^M b_d u_{M,d}.
\tag{24}
\]
Indeed,
\[
\begin{aligned}
(R_M^{\rm phys}x)(n)-(R_M^{\rm phys}x)(n-1)
&=\sum_{d\mid n}b_d\\
&=x_n-x_{n-1},
\end{aligned}
\]
by finite Möbius inversion. Both sequences start at zero, so \((R_M^{\rm phys}x)(n)=x_n\) for \(1\le n\le M\).

In normalized coordinates define
\[
R_M z=R_M^{\rm phys}\bigl(z_n/\sqrt{Q(n)}\bigr)_{n=1}^M.
\]
This is a bounded linear map from \(\mathbb R^M\) into the finite legal span, and
\[
\boxed{T_MR_M=I_{\mathbb R^M}.}
\tag{25}
\]
Boundedness here is for each fixed \(M\); no uniform estimate for \(\|R_M\|\) has been proved or assumed.

### 2. Exact determinant of the consecutive-conductor head matrix

Let
\[
A_M(n,d)=g_{d+1}(n),\qquad 1\le n,d\le M.
\]
The preceding construction gives the unexpectedly simple identity
\[
\boxed{\det A_M=\frac1{M+1}.}
\tag{26}
\]
To verify the sign as well as the magnitude, start with the ordered columns \(g_2,\ldots,g_M,g_q\). Replace them by \(u_{M,2},\ldots,u_{M,M},u_{M,1}\); this transformation has determinant \((-1)^{M-1}q\). Moving its last column to the first position contributes another factor \((-1)^{M-1}\). The resulting matrix is \(U_M\), whose determinant is one. Hence \(1=q\det A_M\).

If the rows are normalized by \(\sqrt{Q(n)}\), the determinant instead equals
\[
\det\bigl[\sqrt{Q(n)}g_{d+1}(n)\bigr]_{n,d=1}^M
=\frac1{Z^{M/2}M!(M+1)}.
\tag{27}
\]
These identities establish invertibility. They do not by themselves give a uniform inverse-norm bound.

### 3. Strict positive definiteness of the compressed actual projection

Retain the actual closed legal span \(V\) and its orthogonal projector \(P_V\). Define
\[
S_Mx=\sum_{i=1}^M x_iP_Ve_i,
\qquad K_M=T_MS_M,
\]
so that
\[
K_M(i,j)=\langle P_Ve_j,e_i\rangle_Q,
\qquad
x^\top K_Mx=\left\|P_V\sum_{i=1}^Mx_ie_i\right\|_Q^2.
\]
Then
\[
\boxed{0<K_M\le I_M.}
\tag{28}
\]
The upper bound follows from contractivity of \(P_V\). For strict positivity, let \(a=\sum_i x_ie_i\) and use the legal interpolant \(R_Mx\). Since \(T_MR_Mx=x\),
\[
\|x\|_2^2=\langle R_Mx,a\rangle_Q
=\langle R_Mx,P_Va\rangle_Q.
\]
If \(P_Va=0\), then \(x=0\). More quantitatively, Cauchy–Schwarz gives
\[
\boxed{K_M\succeq\|R_M\|^{-2}I_M.}
\tag{29}
\]
The norm \(\|R_M\|\) is nonzero because \(T_MR_M=I\) and \(M\ge1\).

Thus **the pseudoinverse in the original agenda can be replaced by an ordinary inverse unconditionally**. No nonzero finitely supported vector is orthogonal to all legal residues. This finite-support statement does not rule out infinite-support vectors in \(V^\perp\).

### 4. Attainment, the exact inverse formula, and the optimal signed bound

Put
\[
t_M=T_M1=(\sqrt{Q(1)},\ldots,\sqrt{Q(M)})^\top,
\qquad f_M=S_MK_M^{-1}t_M.
\tag{30}
\]
Then \(f_M\in V\) and \(T_Mf_M=t_M\). If \(f\in V\) has the same head, then \(T_M(f-f_M)=0\) and
\[
\langle f_M,f-f_M\rangle_Q
=(K_M^{-1}t_M)^\top T_M(f-f_M)=0.
\]
Consequently
\[
\boxed{\|f\|_Q^2=\|f_M\|_Q^2+\|f-f_M\|_Q^2.}
\tag{31}
\]
This proves attainment and uniqueness of the minimum in the agenda, with
\[
\boxed{
\mathcal E_M=\|f_M\|_Q^2
=t_M^\top K_M^{-1}t_M
=\max_{x\ne0}\frac{|t_M^\top x|^2}{x^\top K_Mx}.
}
\tag{32}
\]
For the last equality apply Cauchy–Schwarz in the inner product induced by \(K_M\); equality holds for \(x=K_M^{-1}t_M\), which is nonzero. Hence \(\sqrt{\mathcal E_M}\) is the exact optimal signed dual constant at head size \(M\), and
\[
\sum_{n=1}^M Q(n)\le\mathcal E_M\le C_M^2.
\tag{33}
\]
The first inequality uses the prescribed physical head; the second uses the existing Möbius interpolant as a feasible competitor.

### 5. Exact finite-head repair removes the density qualification

The infimum over finite legal interpolants equals the minimum over the closed space:
\[
\boxed{
\mathcal E_M
=\inf\{\|f\|_Q^2:f\in\operatorname{span}\{g_d:d\ge2\},\ T_Mf=t_M\}.
}
\tag{34}
\]
For a proof, take finite legal \(v_k\to f_M\) in \(H\) and set
\[
\widetilde v_k=v_k+R_M(t_M-T_Mv_k).
\tag{35}
\]
Every \(\widetilde v_k\) is finite legal and has the exact head. Since \(R_M\) is bounded for this fixed \(M\),
\[
\|\widetilde v_k-f_M\|_Q
\le(1+\|R_M\|\|T_M\|)\|v_k-f_M\|_Q\longrightarrow0.
\]
This proves (34). The correction can be made arbitrarily small for a fixed head. Uniform bounds as the head grows remain a separate problem.

### 6. An exact energy increment and a sharp dichotomy

If \(N\ge M\), then \(f_N\) is feasible for the \(M\)-head problem. Equation (31) gives
\[
\boxed{\|f_N-f_M\|_Q^2=\mathcal E_N-\mathcal E_M.}
\tag{36}
\]
Thus \(\mathcal E_M\) is increasing. The increments \(f_{M+1}-f_M\) are pairwise orthogonal: an earlier increment lies in \(\operatorname{span}\{P_Ve_1,\ldots,P_Ve_{M+1}\}\), while a later increment has zero head through that index and belongs to \(V\).

There is an unconditional alternative:
\[
\boxed{
\begin{array}{ll}
1\in V &: f_M\longrightarrow1\text{ strongly and }\mathcal E_M\uparrow1;\\
1\notin V &: \mathcal E_M\longrightarrow+\infty.
\end{array}}
\tag{37}
\]
If the energies are bounded, (36) makes \(f_M\) a Cauchy sequence. Its limit belongs to the closed space \(V\); continuity of each coordinate evaluation and eventual exact agreement at that coordinate identify the limit as \(1\). Conversely, if \(1\in V\), then \(\mathcal E_M\le\|1\|_Q^2=1\); combining this with the preceding argument gives strong convergence and energy limit one.

This proves the bounded-energy implication without invoking weak compactness, and strengthens it to a strong convergence theorem. Together with the already verified \(C_M^2/M\to0\), the divergent branch necessarily obeys
\[
\mathcal E_M\longrightarrow\infty,
\qquad \frac{\mathcal E_M}{M}\longrightarrow0.
\tag{38}
\]
Sublinear divergence is consistent with the available estimates; excluding it remains the arithmetic task.

### 7. A sharper connection between residual tails and optimal energy

Let \(r=(I-P_V)1\), \(r_M=1_{n\le M}r\), and write
\[
m_M=\sum_{n=1}^MQ(n),\quad
\tau_M=\|r-r_M\|_Q^2,\quad
c_M=\langle1,r_M\rangle_Q.
\]
For any exact-head vector \(f\in V\), orthogonality and disjoint supports give
\[
c_M=-\langle f-1_{n\le M},r-r_M\rangle_Q,
\qquad
\|f-1_{n\le M}\|_Q^2=\|f\|_Q^2-m_M.
\]
Therefore
\[
\boxed{(\mathcal E_M-m_M)\tau_M\ge c_M^2.}
\tag{39}
\]
This strengthens the estimate obtained by using the entire norm of a particular exact-head interpolant. Since \(c_M\to\|r\|_Q^2\), it also gives
\[
\boxed{\liminf_{M\to\infty}\mathcal E_M\tau_M\ge\|r\|_Q^4.}
\tag{40}
\]
If \(r\ne0\), then \(\tau_M>0\) for every \(M\), by the finite-support injectivity established above. Combining (39) with \(\mathcal E_M/M\to0\) forces \(M\tau_M\to\infty\), recovering the agenda's escape criterion with the optimal interpolation energy and the sharp asymptotic lower constant.

**Remaining arithmetic question.** These results settle the finite-head algebra, attainment, exact repair, optimal inverse formula, and strong compactness mechanism in ordinary mathematics. They do not prove a uniform bound on \(\mathcal E_M\), nor an independent decay rate for the actual residual tail. Either such estimate, under the repository's established closure-to-RH bridge, would complete this route to RH.


---

# Stronger residual-tail results for the complete Q space

This section supplies ordinary proofs and the sharper external analytic refinement. The exact defect-tail identity, the complete-Q all-logarithmic bounds, and logarithmic tail escape are also formalized by the modules listed in the continuation summary, using the existing repository 1/11-profile provider. The classical 3/5-profile estimate and the weighted-integrability/sign arguments remain ordinary mathematical proofs, not newly kernel-checked declarations.

Write `Z = zeta(2)`, `Q(n)=1/(Z n^2)`, and let `V` be the closed full residue span. Let `E_M` be the agenda's exact-head vector, `C_M=||E_M||_Q`, and `D_M=||1-E_M||_Q`. For `u in V^perp`, put `m(u)=<1,u>_Q` and `tau_M(u)=sum_{n>M}Q(n)|u(n)|^2`.

## A. An exact inequality for every annihilator

Since `E_M in V` and `E_M(n)=1` for `n<=M`,

\[
m(u)=\langle1-E_M,u\rangle_Q
=\langle1-E_M,\mathbf1_{n>M}u\rangle_Q.
\]

Therefore, for every M,

\[
\boxed{|m(u)|^2\le D_M^2\tau_M(u).}
\tag{A1}
\]

This is stronger than an eventual inequality with a factor 1/4, and it applies to every annihilator, not just the target residual. The existing `C_M^2/M -> 0` gives `D_M^2/M -> 0` by `D_M<=1+C_M`. Consequently `m(u) != 0` forces `M tau_M(u) -> infinity`. For the actual residual `r=(I-P_V)1`, one has `m(r)=||r||^2`; hence the left side of (A1) is `||r||^4`.

## B. A genuinely stronger unconditional energy estimate

The exact interpolant is

\[
E_M(n)=-\sum_{d\le M}\mu(d)g_d(n)
 +(M+1)m_Mg_{M+1}(n),\qquad
m_M=\sum_{d\le M}\frac{\mu(d)}d.
\]

Let `A(x)=sum_{d<=x} mu(d)` denote the Mertens function, to avoid confusing it with the head size M. Cancellation of the linear terms gives

\[
E_M(n)=\sum_{d\le M}\mu(d)\lfloor n/d\rfloor
 -(M+1)m_M\lfloor n/(M+1)\rfloor.
\tag{B1}
\]

For `n>M`, put `t=floor(n/(M+1))`. The divisor identity `sum_{d<=n} mu(d) floor(n/d)=1`, followed by finite summation in the opposite order, yields

\[
\boxed{
E_M(n)=1-\sum_{k=1}^{t}\bigl[A(\lfloor n/k\rfloor)-A(M)\bigr]
 -(M+1)m_Mt.
}
\tag{B2}
\]

Every Mertens argument in the sum is at least M+1. This is important: no bound is required at small arguments.

### Explicit finite-window transfer

Suppose `M>=1`, `T>=M` are integers, `delta,eta>=0`, and
`|A(k)|<=delta*k` for every integer k>=M, while `|m_M|<=eta`.
Set `L=delta(2+log(T/M))+eta`. Formula (B2) gives
`|1-E_M(n)|<=nL` for `M<n<=T`; directly from the residue formula,
`|1-E_M(n)|<=1+M+(M+1)eta` for all n. The exact head makes the first M residual coordinates vanish, and `sum_{n>T}1/n^2<=1/T`, so

\[
\boxed{D_M^2\le\frac1Z\left[(T-M)L^2+
\frac{[1+M+(M+1)\eta]^2}{T}\right].}
\tag{B2a}
\]

This separates the elementary arithmetic/energy transfer from the external analytic estimate and is a convenient target for a conditional Lean theorem.

The classical unconditional Mertens bound implies, for every fixed B>1,

\[
|A(x)|\ll_B\frac{x}{(\log x)^B},\qquad
|m_M|\ll_B\frac1{(\log M)^{B-1}}.
\tag{B3}
\]

The second follows from the first and

\[
m_M=\frac{A(M)}M-\int_M^\infty\frac{A(x)}{x^2}\,dx,
\]

using the unconditional identity `sum mu(n)/n=0`. Formula (B2), `H_t<=1+log t`, and `t<=n/(M+1)` imply

\[
|E_M(n)|\ll_B
1+\frac{n(1+\log(n/M))}{(\log M)^{B-1}}
\quad(n>M).
\tag{B4}
\]

There is also the uniform elementary bound `|E_M(n)| <= M+(M+1)|m_M| <= 3M` for all n and sufficiently large M.

Fix A>0 and split the complete norm at `N=floor(M(log M)^A)`. The head contributes at most 1. Take `B=A+2` in (B4). The middle range contributes

\[
\ll_A M^{-1}
+\frac{M(\log\log M)^2}{(\log M)^{A+2}},
\]

and the infinite tail contributes at most

\[
\frac{9M^2}{Z}\sum_{n>N}\frac1{n^2}
\ll_A\frac{M}{(\log M)^A}.
\]

Thus

\[
\boxed{\forall A>0,\qquad
C_M^2\ll_A\frac{M}{(\log M)^A},\qquad
D_M^2\ll_A\frac{M}{(\log M)^A}.}
\tag{B5}
\]

The constants depend on A. This remains an unbounded energy allowance and does not establish a uniform signed dual bound.

### Stronger subexponential version

Let

\[
\Phi(x)=\frac{(\log x)^{3/5}}{(\log\log x)^{1/5}}
\]

for sufficiently large x. The classical Korobov–Vinogradov Mertens bound is `A(x) << x exp(-c Phi(x))` for some c>0. Partial summation gives `m_M << exp(-c_1 Phi(M))` for any fixed `0<c_1<c`; the polynomial factors introduced by the tail integral are absorbed by decreasing c. The function Phi is eventually increasing. Hence (B2) gives

\[
|E_M(n)|\ll 1+n(1+\log(n/M))e^{-c_1\Phi(M)}.
\]

Choose any `0<b<c_1` and split at `N=floor(M exp(b Phi(M)))`. The middle energy is

\[
\ll M^{-1}+M e^{-(2c_1-b)\Phi(M)}(1+\Phi(M))^2,
\]

and the far tail is `O(M exp(-b Phi(M)))`. Since `2c_1-b>b`, the polynomial factor is harmless. Consequently, for some b>0,

\[
\boxed{C_M^2+D_M^2\ll M e^{-b\Phi(M)}.}
\tag{B6}
\]

This is an ordinary deduction from the external Mertens theorem, not a formalized analytic input.

Primary source for the external bound: Ethan Simpson Lee and Nicol Leong, *New explicit bounds for Mertens function and the reciprocal of the Riemann zeta function*, arXiv:2208.06141v5 (9 September 2026), Theorem 1.1, equations (10)–(12), and Theorem 2.2. The displayed logarithmic prefactor is absorbed by decreasing the positive exponential constant. URL: https://arxiv.org/html/2208.06141v5 . The source supplies the Mertens estimate, not the new E_M energy calculation above.

## C. Stronger tail obstructions and RH conditions

Combining (A1) and (B5), any annihilator with nonzero mean satisfies

\[
\boxed{\forall A\ge0,\qquad
\frac{M\tau_M(u)}{(\log M)^A}\longrightarrow+\infty.}
\tag{C1}
\]

Indeed, use (B5) with A+1 to get a lower bound by a positive multiple of log M. Therefore the actual residual condition

\[
\boxed{\exists A\ge0,\quad
\liminf_{M\to\infty}\frac{M\tau_M(r)}{(\log M)^A}<\infty}
\tag{C2}
\]

forces `r=0`, and hence yields RH through the repository's closure criterion. This is weaker than the agenda's bounded-M-tau hypothesis: any fixed logarithmic growth is permitted. In particular `|r(n)|=O((log n)^B)` for any fixed B>=0 would suffice, since summation or integration gives `tau_M=O((log M)^(2B)/M)`.

The sharper estimate (B6) implies

\[
m(u)\ne0\quad\Longrightarrow\quad
M e^{-(b/2)\Phi(M)}\tau_M(u)\longrightarrow+\infty.
\tag{C3}
\]

Thus a finite liminf of the left side for the actual residual suffices for RH. A cofinal estimate `M tau_M(r)=exp(o(Phi(M)))` is a convenient sufficient condition. No such estimate for the actual residual has been established here.

## D. Weighted integrability obstructions

The following general lemma is a useful way to organize critical moments. Let `a_n=Q(n)|u(n)|^2`, let `w_M>=0`, and define `W(n)=sum_{1<=M<n} w_M`. Tonelli gives the exact identity

\[
\sum_{n\ge1}a_nW(n)=\sum_{M\ge1}w_M\tau_M(u).
\tag{D1}
\]

If `D_M>0`, (A1) gives

\[
|m(u)|^2\sum_{M\le J}\frac{w_M}{D_M^2}
\le \sum_{n\ge1}a_nW(n).
\tag{D2}
\]

Therefore a finite weighted norm on the right and divergence of `sum w_M/D_M^2` imply `m(u)=0`. If some `D_M=0`, then `1=E_M in V` already implies `m(u)=0`, so the zero denominator case is harmless but must be separated.

Taking eventually `W(n)=n/(log n)^B`, whose first difference is comparable to `(log n)^(-B)`, and using (B5) with exponent B+1 proves:

\[
\boxed{u\in V^\perp,\quad
\sum_{n\ge3}\frac{|u(n)|^2}{n(\log n)^B}<\infty
\quad\Longrightarrow\quad\langle1,u\rangle_Q=0}
\tag{D3}
\]

for every fixed B>=0. The weaker baseline `D_M^2=O(M)` already proves the case B=1, as well as the iterated-log weights `1/[n log n loglog n ...]` for any fixed finite number of logarithms, by the divergent integral test. Statement (D3) for arbitrary B uses the improved arithmetic estimate.

Likewise, (B6) permits the weight `W(n)=n exp(-a Phi(n))` for any fixed `0<a<=b`. It is eventually increasing, and its first difference is comparable to `exp(-a Phi(n))`, since `n Phi'(n)->0`. Hence

\[
\boxed{u\in V^\perp,\quad
\sum_{n\ge n_0}\frac{|u(n)|^2e^{-a\Phi(n)}}n<\infty
\quad\Longrightarrow\quad\langle1,u\rangle_Q=0.}
\tag{D4}
\]

Applied to the actual residual, each condition forces r=0 and hence RH. Bounded and polylogarithmically growing physical residuals satisfy the weighted condition in (D4). These are sufficient conditions whose truth for the actual residual is still open.

## E. An unconditional sign-oscillation theorem

Every nonzero real `u in V^perp` has positive coordinates at arbitrarily large indices and negative coordinates at arbitrarily large indices. This asserts recurring signs, not unbounded coordinate magnitudes.

Proof: suppose `u(n)>=0` for n>N. For d>N, multiply `<u,g_d>=0` by d:

\[
0=\sum_{n\ge1}Q(n)u(n)(n\bmod d).
\]

All negative terms are among n<=N and their total is bounded independently of d; their residues equal n. Every term with `N<n<d` is `nQ(n)u(n)>=0`. Hence the partial sums of `sum_{n>N}nQ(n)u(n)` are bounded, so `sum nQ(n)|u(n)|<infinity`. Dominated convergence, using `0<=n mod d<=n` and `n mod d -> n` as d->infinity, gives `sum nQ(n)u(n)=0`.

Subtract the residue identity from this moment identity and divide by d:

\[
\sum_{n\ge1}\lfloor n/d\rfloor Q(n)u(n)=0.
\]

For d>N all summands are nonnegative, and the factor floor(n/d) is positive for n>=d. Thus `u(n)=0` for n>=d; u is finitely supported. A finitely supported annihilator is zero: if its support is contained in 1,...,D, compare the moment identity with the residue identity at d=D to get `Q(D)D u(D)=0`, then descend. The case of eventual nonpositivity follows by replacing u with -u.

Consequently, an actual residual that is eventually of one sign must vanish, giving another sufficient RH condition without assuming a tail decay rate. A hypothetical nonzero residual must have infinitely many sign changes. This statement uses full-conductor orthogonality and must not be silently reinterpreted for a squarefree-only span.



### An additional unconditional rigidity theorem: both signs have infinite harmonic mass

**Status:** ordinary mathematical proof, not a newly Lean-verified declaration.
Let \(u\in V^\perp\), with \(V\) the full legal residue closure in \(L^2(Q)\).
Then
\[
\boxed{u\ne0\quad\Longrightarrow\quad
\sum_{n\ge1}\frac{u_+(n)}n=\sum_{n\ge1}\frac{u_-(n)}n=+\infty.}
\tag{H1}
\]
Here \(u_+=\max(u,0)\), \(u_-=\max(-u,0)\). In particular, every nonzero annihilator has arbitrarily late positive and negative coordinates. More strongly, neither sign can have finite harmonic mass.

First suppose
\[
\sum_{n\ge1}nQ(n)|u(n)|<\infty.
\tag{H2}
\]
Write \(w_n=Q(n)u(n)\). Since \(d g_d(n)=n\bmod d\to n\) pointwise and \(|n\bmod d|\le n\), dominated convergence and orthogonality give
\[
\sum_{n\ge1}nw_n=0.
\]
Define the signed tails \(F(k)=\sum_{n\ge k}w_n\). Absolute summation gives
\[
\sum_{k\ge1}|F(k)|\le\sum_{n\ge1}n|w_n|<\infty.
\]
For every integer \(d\ge1\),
\[
A_d:=\sum_{j\ge1}F(dj)
=\sum_{n\ge1}\left\lfloor\frac nd\right\rfloor w_n=0.
\]
For \(d\ge2\), this follows by subtracting residue orthogonality from \(d^{-1}\sum_n nw_n=0\); for \(d=1\), it is the first-moment identity itself. All rearrangements are absolutely convergent by (H2).

Let \(P\) be a primorial. For fixed \(k\ge1\), finite Möbius cancellation yields
\[
0=\sum_{d\mid P}\mu(d)A_{kd}
=\sum_{j\ge1}F(kj)\sum_{d\mid\gcd(j,P)}\mu(d)
=\sum_{\substack{j\ge1\\\gcd(j,P)=1}}F(kj).
\]
As \(P\) includes successively all primes, the indicator in the last sum tends to \(1_{j=1}\). Dominated convergence is valid because \(F\in\ell^1\). Hence \(F(k)=0\) for every \(k\), and \(w_k=F(k)-F(k+1)=0\). This proves \(u=0\) under (H2).

Now suppose only one sign has finite first moment, for example
\(B=\sum_n nQ(n)u_-(n)<\infty\). For each \(d\ge2\), residue orthogonality gives
\[
\sum_nQ(n)(n\bmod d)u_+(n)
=\sum_nQ(n)(n\bmod d)u_-(n)\le B.
\]
The left side dominates \(\sum_{n<d}nQ(n)u_+(n)\). Letting \(d\to\infty\) shows that the positive first moment is finite too. Thus (H2) holds and \(u=0\). The other sign is symmetric. Since \(nQ(n)=1/(\zeta(2)n)\), this proves (H1).

For the actual residual \(r=(I-P_V)1\), it follows that either of the sufficient conditions
\[
\sum_{n\ge1}\frac{r_+(n)}n<\infty
\qquad\text{or}\qquad
\sum_{n\ge1}\frac{r_-(n)}n<\infty
\]
forces \(r=0\), and hence RH through the established closure bridge. In particular, eventual nonnegativity or eventual nonpositivity suffices. These are conditional RH criteria: neither one-sided harmonic summability nor eventual sign has been proved for the actual residual.
