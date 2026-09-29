# Dyadic signed correction: a summable defect and an unavoidable negative drift

Date: 2026-09-29 UTC. Starting repository commit: `824b2610cad6d45da52326344ab249edd44dbd9b`.

## Outcome and verification boundary

RH is not proved. The new formal development proves an unconditional absolute-summability theorem for a signed defect of the **actual optimal inverse-Gram corrections**. Combining its finite inequality with established results of Burnol and Johnston–Leong–Tudzi gives an unconditional paper theorem: the reciprocal corrections sampled at powers of two have summable positive parts and a negative cumulative sum tending to minus infinity, with an explicit logarithmic lower rate.

The finite identities, two-gap bound, absolute summability, cumulative inequality, and finite positive-part bound are formalized in `RH/FiniteDyadicDefect.lean`. The final numerical drift theorem uses cited analytic theorems not formalized in this module; it is not advertised as a fully kernel-checked theorem. No such theorem is inserted as an axiom.

The starting commit already contains the full smooth Weil converse. This work independently checked it and adds the exact two-test reflection block to `RH/WeilConverse.lean`. It does not count the existing converse as a new result.

## 1. Definitions and indexing

Use largest-conductor indexing in this note:

\[
H=\ell^2\!\left(\frac1{j(j+1)}\right)_{j\ge1},\quad
g_d(j)=\frac{j\bmod d}{d},\quad
V_N=\operatorname{span}\{g_2,\ldots,g_N\}.
\]

Let \(F_N=P_{V_N}\mathbf1\), \(r_N=\mathbf1-F_N\), \(E_N=\|r_N\|^2\), and \(D=\lim_NE_N\). Thus \(E_N=1-Q_N\), and \(E_1=1\). Extend every physical sequence by zero at zero.

Write

\[
c_N=G_N^{-1}b_N,\quad \kappa_{N,d}=c_{N,d}+\mu(d),\quad
C_N=\sum_{d=2}^N\frac{\kappa_{N,d}}d,\quad
m(N)=\sum_{d=1}^N\frac{\mu(d)}d.
\]

The finite arithmetic identity already in the project is

\[
\boxed{C_N=m(N)-r_N(1).}\tag{1}
\]

Indeed, \(g_d(1)=1/d\), so \(F_N(1)=\sum c_{N,d}/d\), while \(\mu(1)=1\).

Lean stage `n` corresponds to this note's \(N=n+1\). Hence `doubleStage n = 2*n+1`, and `dyadicStage 0 k` corresponds to conductor cutoff \(2^k\). The statistic here includes **all** conductors through \(N\); it is the existing `reciprocalCorrection`, not the slightly truncated `divisorReciprocalStatistic`.

## 2. Exact finite dyadic identity

Define the scaled integer dilation

\[
(Uf)(j)=2f(\lfloor j/2\rfloor).
\]

The proved dilation relations give \(\|Uf\|^2=2\|f\|^2\) and \(UV_N\subseteq V_{2N}\). Put

\[
A=1+\frac{\sqrt2}{2},\qquad t=1-\frac{\sqrt2}{2},\qquad
J_N=A\|r_N-tUr_N\|^2,
\]

\[
B_N=\langle r_N,UF_N\rangle
=\langle F_{2N}-F_N,UF_N\rangle.
\]

The second expression for \(B_N\) follows from orthogonality of \(r_{2N}\) to \(UF_N\in V_{2N}\).

Let \(\delta_1\) be the sequence supported at physical site one, with value one there. Since \(\delta_1=\mathbf1-U\mathbf1/2\), \(\langle r_N,\mathbf1\rangle=E_N\), and \(\langle r_N,\delta_1\rangle=r_N(1)/2\),

\[
r_N(1)=2E_N-\langle r_N,Ur_N\rangle-B_N.
\]

The identities \(At=1/2\) and \(A(1+2t^2)=2\) show that

\[
J_N=2E_N-\langle r_N,Ur_N\rangle.
\]

Consequently,

\[
\boxed{r_N(1)=J_N-B_N,\qquad C_N+J_N-m(N)=B_N.}\tag{2}
\]

Cauchy–Schwarz and \(\|Ur_N\|=\sqrt2\|r_N\|\) give

\[
\boxed{(2-\sqrt2)E_N\le J_N\le(2+\sqrt2)E_N.}\tag{3}
\]

All objects in (2) come from the unconstrained, full-norm optimal projection. No freely chosen inverse column or test coefficient replaces them.

## 3. Two consecutive energy decreases control the signed defect

Let \(N_k=2^k\) and \(\Delta_k=E_{N_k}-E_{N_{k+1}}\ge0\). For \(k\ge1\), the term \(UF_{N_{k-1}}\) lies in \(V_{N_k}\). Subtracting it inside the residual pairing, and then projecting to the next scale, yields

\[
B_{N_k}=\langle F_{N_{k+1}}-F_{N_k},
U(F_{N_k}-F_{N_{k-1}})\rangle.
\]

Nested-projection Pythagoras gives

\[
\boxed{|B_{N_k}|^2\le2\Delta_{k-1}\Delta_k.}\tag{4}
\]

Using \(2\sqrt{ab}\le a+b\) and telescoping,

\[
\boxed{
\sum_{k=1}^K|B_{2^k}|
\le\frac{\sqrt2}{2}
\bigl(E_1+E_2-E_{2^K}-E_{2^{K+1}}\bigr).
}\tag{5}
\]

In particular \(\sum_{k\ge1}|B_{2^k}|<\infty\). More generally, starting at any conductor cutoff \(N_0\), the total absolute defect after successive doublings is at most \(\sqrt2(E_{N_0}-D)\). This sharper bound is also proved in Lean.

Combining (2) and (5) proves the new unconditional result

\[
\boxed{\sum_{k\ge1}|C_{2^k}+J_{2^k}-m(2^k)|<\infty.}\tag{6}
\]

It also proves, for every finite \(K\),

\[
\sum_{k=1}^K C_{2^k}
\le\sum_{k=1}^K m(2^k)
-(2-\sqrt2)\sum_{k=1}^K E_{2^k}
+\frac{\sqrt2}{2}(E_1+E_2-E_{2^K}-E_{2^{K+1}}),\tag{7}
\]

and

\[
\sum_{k=1}^K(C_{2^k})_+
\le\sum_{k=1}^K|m(2^k)|
+\frac{\sqrt2}{2}(E_1+E_2-E_{2^K}-E_{2^{K+1}}).\tag{8}
\]

Here \(x_+=\max(0,x)\). Equations (4)–(8), including the complete finite remainder, require no RH or additional arithmetic estimate.

## 4. Established analytic input: an explicit positive-part budget

Johnston–Leong–Tudzi, Theorem A.2 (A.8), prove

\[
|m(x)|\le\frac{4.591}{(\log x)^2}\qquad(x>1).
\]

See [arXiv:2408.04143v3](https://arxiv.org/pdf/2408.04143), printed page 27. Summing at powers of two and using \(\zeta(2)=\pi^2/6\),

\[
\sum_{k\ge1}|m(2^k)|\le\frac{4.591\pi^2}{6(\log2)^2}.
\]

A direct one-atom calculation gives \(E_2=1-\log2\): \(\langle1,g_2\rangle=\log2/2\) and \(\|g_2\|^2=\log2/4\). Set

\[
R=\frac{4.591\pi^2}{6(\log2)^2}
+\frac{\sqrt2}{2}(2-\log2)
<16.642358874.
\]

Then (8) proves on paper

\[
\boxed{\sum_{k\ge1}(C_{2^k})_+\le R.}\tag{9}
\]

Equations (2)–(5) also give the finite two-sided comparison

\[
(2-\sqrt2)\sum_{k=1}^KE_{2^k}-R
\le-\sum_{k=1}^KC_{2^k}
\le(2+\sqrt2)\sum_{k=1}^KE_{2^k}+R.\tag{10}
\]

The JLT analytic estimate and the assembled numerical bounds (9)–(10) are cited paper consequences, not additional Lean axioms or fully formalized numeric certificates. The known zeta-two value evaluates a convergent error budget; it supplies no RH-strength cancellation.

## 5. Burnol forces negative logarithmic cumulative drift

Burnol proves the multiplicity-sensitive lower bound for the Nyman–Beurling distance; see [arXiv:math/0103058](https://arxiv.org/pdf/math/0103058), Theorem 1.3. Balazard–de Roton explicitly record the universal consequence

\[
\liminf_{N\to\infty}\log N\,d_N^2
\ge C_0:=2+\gamma-\log(4\pi)>0
\]

in [arXiv:0812.1689](https://arxiv.org/pdf/0812.1689), equation (3), printed page 3.

The normalization transfer is one-sided and exact. In reciprocal physical coordinates, define \(\rho_d(x)=\{1/(dx)\}\). On \(1/(j+1)<x<1/j\),

\[
\rho_d(x)-\rho_1(x)/d=(j\bmod d)/d.
\]

This function vanishes for \(x>1\). Since these intervals have lengths \(1/[j(j+1)]\), our Pareto space embeds isometrically into \(L^2(0,\infty)\), and our finite atom space is contained in the usual length-\(N\) Nyman–Beurling span. Thus \(E_N\ge d_N^2\), giving

\[
\liminf_{N\to\infty}(\log N)E_N\ge C_0.\tag{11}
\]

For every \(\varepsilon>0\), (11) implies eventually
\(E_{2^k}\ge(C_0-\varepsilon)/(k\log2)\). Summing and using \(\sum_{k\le K}1/k=\log K+O(1)\), (10) yields

\[
\boxed{
\liminf_{K\to\infty}
\frac{-\sum_{k=1}^K C_{2^k}}{\log K}
\ge\frac{(2-\sqrt2)(2+\gamma-\log4\pi)}{\log2}
=0.0390368841111\ldots.
}\tag{12}

Therefore the dyadic correction series has finite positive part and divergent negative part. In particular, it cannot be absolutely summable or eventually nonnegative. This is an unconditional theorem on paper derived from the formal finite inequality and the cited established analytic inputs.

It is entirely compatible with RH: a sequence can tend to zero while its negative sum diverges. It does not show that any fixed correction coordinate has a nonzero limit. The RH-sufficient cofinal lower bounds with arbitrarily small negative tolerance remain open.

One further obstruction follows. For any \(\alpha<2-\sqrt2\), scales satisfying \(r_{2^k}(1)\le\alpha E_{2^k}\) have
\(\sum 1/k<\infty\) over that set, because (2)–(5) bound their total energy and (11) bounds energy below by a constant times \(1/k\). Such scales may be cofinal but cannot occupy a set with divergent harmonic weight.

## 6. Exact Weil reflection block

The starting build already constructs a smooth test isolating each actual zero, retaining its full analytic multiplicity. The added theorem `exists_smooth_weil_reflection_block` now records that any off-line zero \(\rho\) gives admissible tests \(f,g\) whose actual arithmetic Weil matrix is

\[
\begin{pmatrix}W(f,f)&W(f,g)\\W(g,f)&W(g,g)\end{pmatrix}
=m_\rho\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

The matrix has eigenvalues \(\pm m_\rho\), and \(W(f-g,f-g)=-2m_\rho\). The four-entry identity is kernel-checked. The eigenvalue interpretation is immediate finite algebra. Universal arithmetic positivity remains exactly the missing side of the already-proved Weil criterion. Background: [Burnol, The Explicit Formula in simple terms](https://arxiv.org/pdf/math/9810169), the discussion of Weil's criterion.

## 7. Declaration map and research boundary

New main module: `RiemannResearch/RH/FiniteDyadicDefect.lean`.

- `finite_firstCoordinate_eq_dyadicSquare_sub_defect`
- `finiteDyadicDefect_two_gap` and `finiteDyadicDefect_two_gap_sq`
- `finiteDyadicDefect_sum_abs_le`
- `finiteDyadicDefect_abs_summable`
- `finiteDyadicDefect_tsum_abs_gap_bound`
- `reciprocalCorrection_centered_dyadic_abs_summable`
- `reciprocalCorrection_dyadic_sum_le`
- `reciprocalCorrection_dyadic_positive_sum_le`

The signed defect is now controlled in total absolute value along a whole dyadic orbit, rather than merely shown to tend to zero. What remains uncontrolled is the nonnegative main energy \(J_N\). Neither the new summability theorem nor the Weil reflection block proves \(E_N\to0\), fixed-coordinate correction limits zero, or universal Weil positivity.

This work makes no mathematical novelty claim. It is an independently developed synthesis of the project's actual arithmetic objects, Hilbert-space projection geometry, and the cited analytic literature.
