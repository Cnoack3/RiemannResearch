# The actual Gram source tends coordinatewise to zero

This is an unconditional analytic result for the **source** \(b_N+G_N\mu_N\). It does not prove that its product with the growing inverse Gram matrix tends coordinatewise to zero. The proof below is mathematical and is not yet formalized in Lean. The module `ResidueGramCorrectionPairing.lean` verifies the exact Hilbert-space identities described at the end of this note. It also identifies the unconditional limit of each actual inverse-Gram correction as \(-\langle r,u_m\rangle_P\), with \(r=\mathbf1-P_V\mathbf1\). Proving these limits all equal zero remains open.

Fix integers \(N\ge1\) and \(m\ge2\). For positive integers \(n,d\), put
\[
w_n=\frac1{n(n+1)},\qquad g_d(n)=\frac{n\bmod d}{d},\qquad
S_N=\sum_{d=1}^N\frac{\mu(d)}d,
\]
\[
A_N(n)=1+\sum_{d=2}^N\mu(d)g_d(n),\qquad
h_N(m)=\langle g_m,A_N\rangle_P.
\]
For \(m\le N\), this is exactly the \(m\)-th entry of \(b_N+G_N\mu_N\). The inner product uses the complete infinite Pareto sum.

The two classical unconditional PNT consequences used are
\[
S_N\longrightarrow0,
\qquad
L_N:=\sum_{d=1}^N\frac{\mu(d)\log d}{d}\longrightarrow-1.
\tag{1}
\]
The first is explicitly discussed in Terence Tao, *A remark on partial sums involving the Möbius function*, equation (1.1), https://arxiv.org/pdf/0908.4323. NIST DLMF equations 27.11.14–15 list both classical limits and their equivalence to PNT: https://dlmf.nist.gov/27.11. The argument below never substitutes an RH-strength Möbius estimate.

## Exact arithmetic identities

Since \(g_1=0\), we can include \(d=1\) in the residual sum. The division algorithm gives, for every positive \(n\),
\[
\boxed{A_N(n)=1+nS_N-\sum_{d=1}^N\mu(d)\left\lfloor\frac nd\right\rfloor.}
\tag{2}
\]
For \(n\le N\), the divisor identity \(\sum_{d\mid k}\mu(d)=1_{k=1}\) yields
\[
\sum_{d=1}^N\mu(d)\left\lfloor\frac nd\right\rfloor
=\sum_{k=1}^n\sum_{d\mid k}\mu(d)=1,
\qquad
\boxed{A_N(n)=nS_N.}
\tag{3}
\]
In particular \(A_N(n)\to0\) for every fixed \(n\).

Define the signed truncated divisor sum
\[
D_N(k)=\sum_{\substack{d\mid k\\d\le N}}\mu(d).
\]
Taking a first difference of (2) gives the exact identity
\[
\boxed{A_N(n+1)-A_N(n)=S_N-D_N(n+1).}
\tag{4}
\]
All Möbius signs remain in this formula.

Choose a finite constant \(C\ge1\) such that \(|S_N|\le C\) for all \(N\); it exists by (1). When \(n\le N\), (3) gives \(|A_N(n)|\le Cn\). When \(n>N\), the original finite sum and \(|g_d(n)|\le1\) give \(|A_N(n)|\le N\le n\). Consequently
\[
|A_N(n)|\le Cn\quad\hbox{for every }N,n\ge1.
\tag{5}
\]
For each fixed \(N\), the sharper bound \(|A_N(n)|\le N\) holds for all \(n\), directly from its finite-sum definition. Thus every original Pareto pairing below is absolutely convergent.

## Separate the periodic mean exactly

The mean of \(g_m\) over one period is
\[
a_m=\frac{m-1}{2m}.
\]
Set
\[
k_m(n)=g_m(n)-a_m,
\qquad K_m(n)=\sum_{j=1}^n k_m(j),\quad K_m(0)=0.
\]
The sequence \(K_m\) is periodic with period \(m\), hence bounded. More explicitly, if \(r=n\bmod m\), with \(0\le r<m\), then
\[
\boxed{K_m(n)=\frac{r(r-m+2)}{2m}.}
\tag{6}
\]
Let \(B_m=\max_{0\le r<m}|r(r-m+2)/(2m)|\).

The exact generator mean is \(\langle1,g_d\rangle_P=\log d/d\). To check its normalization directly, write \(q=\lfloor R/d\rfloor\) and \(H_j=\sum_{k=1}^j1/k\), with \(H_0=0\). Finite interchange and telescoping give
\[
\sum_{n=1}^{R}g_d(n)w_n
=\frac{H_{R+1}-1-H_q}{d}+\frac{q}{R+1}.
\]
Taking \(R\to\infty\), the harmonic-number difference tends to \(\log d\), and the last term tends to \(1/d\), yielding the claimed mean. Therefore
\[
\boxed{
h_N(m)=a_m(1+L_N)+\sum_{n=1}^{\infty}k_m(n)A_N(n)w_n.
}
\tag{7}
\]
The first term tends to zero by (1). We now prove the same for the second term, retaining its entire signed tail.

## Exact summation by parts, including the boundary term

For every finite \(R\ge1\), finite summation by parts gives
\[
\begin{aligned}
\sum_{n=1}^{R}k_m(n)A_N(n)w_n
={}&K_m(R)A_N(R)w_R\\
&+\sum_{n=1}^{R-1}K_m(n)
\bigl(A_N(n)w_n-A_N(n+1)w_{n+1}\bigr).
\end{aligned}
\tag{8}
\]
For fixed \(N\), the displayed boundary term tends to zero, since \(K_m\) is bounded and \(|A_N(R)|\le N\). Moreover, (4) and
\[
w_n-w_{n+1}=\frac{2}{n(n+1)(n+2)}
\]
give the exact signed identity
\[
\boxed{
\sum_{n=1}^{\infty}k_m(n)A_N(n)w_n
=\sum_{n=1}^{\infty}K_m(n)
\left[
\frac{2A_N(n)}{n(n+1)(n+2)}
-\frac{S_N-D_N(n+1)}{(n+1)(n+2)}
\right].
}
\tag{9}
\]
The passage to the infinite series and the later passage \(N\to\infty\) are justified separately as follows.

Let \(\tau(k)\) be the number of positive divisors of \(k\). Then \(|D_N(k)|\le\tau(k)\). By (5), the absolute value of the \(n\)-th summand on the right of (9) is at most
\[
\boxed{B_m\frac{3C+\tau(n+1)}{(n+1)(n+2)}.}
\tag{10}
\]
This bound is independent of \(N\), and is summable: its constant part telescopes, while
\[
\sum_{k=1}^{\infty}\frac{\tau(k)}{k^2}
=\sum_{a=1}^{\infty}\sum_{b=1}^{\infty}\frac1{a^2b^2}
=\left(\sum_{a=1}^{\infty}\frac1{a^2}\right)^2<\infty.
\tag{11}
\]
The rearrangement in (11) involves nonnegative terms.

For each fixed \(n\), once \(N\ge n+1\), equations (3) and (4) give \(A_N(n)=nS_N\) and \(D_N(n+1)=0\), because \(n+1\ge2\). Thus every summand in (9) tends to zero. Dominated convergence for the series, using (10)–(11), proves
\[
\sum_{n=1}^{\infty}k_m(n)A_N(n)w_n\longrightarrow0.
\tag{12}
\]
Combining (7), (1), and (12), we conclude
\[
\boxed{\forall m\ge2,\qquad (b_N+G_N\mu_N)_m\longrightarrow0.}
\tag{13}
\]
The matrix entry in (13) is read only for \(N\ge m\), which suffices for its limit.

## The exact moving-head remainder

If an explicit split at the matrix cutoff is preferred, define
\[
K_{m,N}(n)=\sum_{j=N+1}^{n}k_m(j)=K_m(n)-K_m(N).
\]
Repeating (8) starting at \(N+1\) gives the exact identity
\[
\boxed{
\begin{aligned}
h_N(m)={}&a_m(1+L_N)
+S_N\sum_{n=1}^{N}\frac{k_m(n)}{n+1}\\
&+\sum_{n=N+1}^{\infty}K_{m,N}(n)
\left[
\frac{2A_N(n)}{n(n+1)(n+2)}
-\frac{S_N-D_N(n+1)}{(n+1)(n+2)}
\right].
\end{aligned}}
\tag{14}
\]
No signed divisor sum or infinite-tail term has been discarded. The proof by (9) is shorter because it uses one fixed summable dominating sequence.

## Why this does not prove inverse-Gram correction decay

The requested correction is
\[
\delta_{N,m}=\sum_{d=2}^N(G_N^{-1})_{m,d}\,h_N(d).
\tag{15}
\]
Equation (13) treats a fixed test generator \(g_m\). Equation (15) tests against a different, cutoff-dependent dual vector whose coefficients are the entire \(m\)-th row of \(G_N^{-1}\). Neither dominated convergence above nor PNT supplies a uniform estimate for those growing rows or for their interaction with the signed source.

For a finite linear combination of the generators, the same periodic argument is valid, but its primitive bound depends on the combination. For the inverse-Gram dual this dependence is precisely the unresolved quantity. Thus (13) gives a genuine unconditional step, while the conclusion \(\delta_{N,m}\to0\) still requires new control.

## Classical weighted-log input without a hidden RH assumption

For completeness, the second limit in (1) may be obtained from the classical zero-free-region form of PNT. Its Mertens bound implies ordinary convergence of \(\sum\mu(n)\log n/n\) by partial summation. Abelian continuity then identifies that sum with
\[
\lim_{s\downarrow1}\sum_{n=1}^{\infty}\frac{\mu(n)\log n}{n^s}
=\lim_{s\downarrow1}\frac{\zeta'(s)}{\zeta(s)^2}=-1.
\]
The final limit follows directly from the exact local representation
\[
\zeta(s)=\frac1{s-1}+H(s),\qquad
\frac{\zeta'(s)}{\zeta(s)^2}
=\frac{-1+(s-1)^2H'(s)}{(1+(s-1)H(s))^2},
\]
where \(H\) is holomorphic near one. No hypothesis about zeros inside the critical strip is used.


## Lean-verified exact pairing and energy identity

Let \(u_m\) be the actual finite-support coefficient dual, satisfying
\(\langle g_d,u_m\rangle_P=\mathbf1_{d=m}\) and
\(\langle\mathbf1,u_m\rangle_P=-\mu(m)\).
Let \(P_N\) be projection onto the span of \(g_2,\ldots,g_N\), and set
\(e_{N,m}=u_m-P_Nu_m\). For \(N\ge m\), Lean verifies

\[
\langle A_N,u_m\rangle_P=0,
\qquad
\delta_{N,m}=\langle A_N,P_Nu_m\rangle_P
=-\langle A_N,e_{N,m}\rangle_P.
\]

The published inverse-Gram diagonal identity gives

\[
\|e_{N,m}\|_P^2=\|u_m\|_P^2-(G_N^{-1})_{m,m}.
\]

The new module combines these into the exact signed energy identity

\[
2\delta_{N,m}
=\|A_N\|_P^2+\|u_m\|_P^2-(G_N^{-1})_{m,m}
-\|A_N+e_{N,m}\|_P^2.
\]

No interaction term is dropped. These identities expose the term that needs
a genuinely new vanishing argument. Fixed-source convergence tests against a
fixed periodic vector; it does not furnish control against the varying dual
\(P_Nu_m\).

Lean declaration names in namespace
`RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection`:

- `coefficientDual_inner`
- `mobiusSynthesis_mem`
- `naturalResidual_inner_dual`
- `correction_eq_projected_dual_pairing`
- `correction_eq_neg_dualResidual_pairing`
- `correction_twice_eq_energy_difference`

The project stage n corresponds to the manuscript cutoff N=n+1. The proofs
use the actual Pareto Hilbert space and actual orthogonal projections, with
no RH hypothesis or new axiom.

## Stretched transfer update (2026-09-28)

The new `CanonicalMobiusStretchedCorrection.lean` proves uniform stretched
pairing bounds for the boundary-corrected exact-head residual and actual
inverse-Gram correction bounds retaining the projected dual's physical tail.
The boundary-corrected canonical vector is different from the natural residual
called A_N in this historical note.

A fixed inverse-Gram dual already has bounded Hilbert norm:
its diagonal entry is at most ||u_m||^2. Its physical tail at the moving cutoff
has no checked rate adequate for the transfer. Existing Schur and screening
identities do not supply that missing estimate.

`ParetoStretchedAnnihilatorTail.lean` strengthens the limiting-residual
obstruction to stretched weighted tail divergence. The remaining direct
sufficient condition is cofinal smallness of
N exp(-a Phi(N)) T_N(r), at an exponent supplied by the arithmetic theorem.
It remains Open. See `StretchedInverseGramTransfer20260928.md` for exact
normalizations, the finite two-cutoff estimates, and the conditional scope.
