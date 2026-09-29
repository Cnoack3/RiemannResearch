# Exact CRT Gram control and the actual Weil translation kernel

Date: 2026-09-29.

This combines the user's CRT program with the integrated actual-zeta Weil
formula and zero-isolation theorems. It establishes exact finite identities
and a uniform sparse quadratic-form comparison. It does not establish RH or
claim mathematical novelty. Classical GCD matrices, Ramanujan packet means,
and the off-line-zero obstruction to Weil positivity are existing ingredients.

## Formal scope

| Module | Checked content |
| --- | --- |
| RH/CRTSparseEnergy.lean | Full sparse energy and positive remainder; uniform relative bounds; finite signed-profile summability; physical support reindexing. |
| RH/CRTGCDGram.lean | Exact simultaneous-divisibility/GCD kernel; full signed quadratic expansion; relative comparison for every coefficient vector. |
| RH/PrimePowerRamanujanSchur.lean | Exact elimination of the entire non-prime-power packet space; screened Gram and means; normal equations and both full square remainders. |
| Analysis/SuperexponentialTranslation.lean | Translation preserves every derivative's superexponential decay in the actual smooth test class. |
| RH/WeilPrimeTranslationKernel.lean | Exact actual arithmetic Weil pairing of all translates of a reflected-pair isolating test, conditional on an actual off-line zero. |

The combined development passed an ephemeral Lean check. Endpoint axiom audits
reported only propext, Classical.choice, and Quot.sound. Publication also
requires checkpoint validation of changed modules and reverse dependents.
Paper consequences below are distinguished from Lean declarations.

## 1. Full sparse CRT energy: formalized

Let \(w_n=1/[n(n+1)]\), \(n\ge1\), with coordinate zero anchored at zero.
For a finite set \(S\) of positive conductors, \(M\ge1\), and arbitrary signed
real coefficients \(c_d\), define
\[
A(k)=\sum_{\substack{d\in S\\d\mid k}}dc_d,\qquad
V_M(n)=\sum_{d\in S}Md\,c_d\,\mathbf1_{Md\mid n}\quad(n\ge1).
\]
Then \(V_M(Mk)=MA(k)\), and \(V_M\) vanishes off the positive multiples of \(M\).
All series below converge because \(A\) is bounded:
\[
E_M=\|V_M\|_H^2
=\sum_{k\ge1}\frac{A(k)^2}{k^2}\frac{Mk}{Mk+1},
\quad E_\infty=\sum_{k\ge1}\frac{A(k)^2}{k^2},
\quad R_M=\sum_{k\ge1}\frac{A(k)^2}{k^2(Mk+1)}.
\]
The primary result is the complete exact equality
\[
\boxed{E_M+R_M=E_\infty.}
\]
The subsequent estimates identify the entire remainder being bounded:
\[
0\le R_M\le\frac{E_\infty}{M+1},\qquad
\boxed{\frac M{M+1}E_\infty\le E_M\le E_\infty.}
\]

These are **sparseEnergy_add_remainder**, **positiveRemainder_bounds**, and
**sparseEnergy_relative_bounds** in namespace
RiemannResearch.RH.Pareto.CRTSparseEnergy.
**full_physical_energy_eq_sparseEnergy** reindexes the whole physical energy
under explicit anchored-coordinate, support, and multiple-value hypotheses.
**incidenceProfile_summable** supplies convergence for all finite signed profiles.

Expanding the finite square keeps every signed mixed term:
\[
\begin{aligned}
E_\infty
&=\sum_{d,e\in S}c_dc_e\,de
 \sum_{\substack{k\ge1\\d\mid k,\ e\mid k}}k^{-2}\\
&=\zeta(2)\sum_{d,e\in S}c_dc_e\frac{de}{\operatorname{lcm}(d,e)^2}\\
&=\zeta(2)\sum_{d,e\in S}c_dc_e\frac{\gcd(d,e)^2}{de}.
\end{aligned}
\]
The formal constant **zetaTwoSeries** is the reciprocal-square series, with a
zero term at index zero; no special-value evaluation is needed. The checked
declarations are **gcdReferenceKernel_lcm**, **gcdReferenceKernel_gcd**, and
**referenceEnergy_incidenceProfile**.

If \(G_M\) is the Gram matrix of the columns \(Md\,\mathbf1_{Md\mid n}\) and
\(K_{de}=\gcd(d,e)^2/(de)\), the inequalities for all coefficient vectors give
\[
\boxed{\frac M{M+1}\zeta(2)K\preceq G_M\preceq\zeta(2)K.}
\]
**incidence_sparseEnergy_gcd_relative_bounds** formalizes that quadratic
statement; matrix-order notation is its mathematical interpretation. The
constant is independent of dimension, conductor, and coefficient signs.
It is proved directly on the full signed form.

## 2. Squarefree CRT inversion: paper consequences

For squarefree \(Q\), index all divisors by prime subsets. Factoring each GCD
entry prime by prime gives the classical tensor identity
\[
K_Q=\bigotimes_{p\mid Q}
\begin{pmatrix}1&1/p\\1/p&1\end{pmatrix},
\quad
\operatorname{Spec}(K_Q)=
\left\{\prod_{p\mid Q}(1+\varepsilon_p/p):\varepsilon_p=\pm1\right\}.
\]
These matrix-spectrum statements are paper deductions, not new Lean declarations.
Set
\[
a_Q=\zeta(2)\prod_{p\mid Q}(1-p^{-2})
=\sum_{\substack{k\ge1\\(k,Q)=1}}k^{-2}\ge1,\qquad
G_\infty=\zeta(2)K_Q.
\]
Local two-by-two inversion gives
\[
(G_\infty^{-1})_{de}
=\frac{\mu(d)\mu(e)}{a_Q}\frac{\gcd(d,e)^2}{de}.
\]
Positive definite inversion reverses the established quadratic order:
\[
G_\infty^{-1}\preceq G_M^{-1}
\preceq(1+1/M)G_\infty^{-1},\qquad
\boxed{(G_M^{-1})_{dd}\le1+1/M.}
\]
This concerns the normalized sparse Gram. It does not control the legal
residue Gram inverse or even a uniform sparse inverse operator norm:
\(\lambda_{\min}(K_Q)=\prod_{p\mid Q}(1-1/p)\) can tend to zero.

The relative constant is sharp. Choose \(c_d=\mu(d)/d\) over all divisors
of a primorial \(Q\). Inclusion-exclusion gives \(A(k)=\mathbf1_{(k,Q)=1}\).
As \(Q\) exhausts the primes, dominated convergence gives
\(E_\infty\to1\) and \(E_M\to M/(M+1)\). This sharpness is a paper consequence.

## 3. Exact legal primitive remainder: paper identity

Let \(g_q(n)=(n\bmod q)/q\), and define
\[
F=\sum_{d\in S}Md\,c_d\,g_{Md},\quad
C=\sum_{d\in S}c_d,\quad (TF)(n)=F(n-1).
\]
Finite residue packets are bounded and \(F(0)=0\). Their exact jump is
\[
F-TF=C\mathbf1-V_M.
\]
The anchored shift has the full defect
\[
\|F\|^2-\|TF\|^2=\sum_{n\ge1}(w_n-w_{n+1})F(n)^2.
\]
Parallelogram and the sparse identity give
\[
\boxed{
4\|F\|^2+R_M
=E_\infty+C^2-2C\langle\mathbf1,V_M\rangle
+\|F+TF\|^2
+2\sum_{n\ge1}(w_n-w_{n+1})F(n)^2.
}
\]
The covariance, square remainder, and shift defect are all retained.
This assembled identity is a paper proof, not a new Lean declaration.

For \(C=0\), the displayed nonnegative terms imply
\[
\|F\|^2\ge\frac M{4(M+1)}E_\infty.
\]
In the squarefree divisor family, coefficient duality and the sparse inverse
diagonal bound then imply
\[
|c_d|^2\le4(1+1/M)\|F\|^2,\qquad
|Md\,c_d|^2\le4M(M+1)d^2\|F\|^2.
\]
The condition \(C=0\) is essential here. If \(M=1,d=1\), the legal column
\(g_1=0\); the unrestricted legal Gram is singular. Restricting to \(C=0\)
fixes that coefficient ambiguity.

There is no upper bound for all primitive remainders from sparse energy here.
For example, the existing primorial family satisfies
\[
F_Q(n)=n\prod_{p\mid Q}(1-1/p)
-M\,\#\{1\le k\le\lfloor n/M\rfloor:(k,Q)=1\}.
\]
This exposes the long drift interval behind the earlier orbit/primitive
obstruction. It is not being presented as a newly discovered RH obstruction.

## 4. Exact global prime-power elimination: formalized

The established integrated Ramanujan packets satisfy
\[
B_q=\sum_{d\mid q}\mu(q/d)d\,g_d,\qquad
\langle B_q,\mathbf1\rangle=\Lambda(q).
\]
These means and finite span inversion predate this development; see
IntegratedRamanujanHilbert.lean, RamanujanFiniteSpanBridge.lean, and
RamanujanVonMangoldtRoute20260919.md.

For a finite dictionary let \(\mathcal C\) span all its non-prime-power packets,
and let \(P_{\mathcal C}\) be orthogonal projection. Define
\(\widetilde B_q=(I-P_{\mathcal C})B_q\). The new checked identities are
\[
\langle\widetilde B_q,\mathbf1\rangle=\Lambda(q),\qquad
\langle\widetilde B_q,\widetilde B_r\rangle
=\langle B_q,B_r\rangle-
 \langle P_{\mathcal C}B_q,P_{\mathcal C}B_r\rangle.
\]
For every prime-power combination \(p\) and every \(c\in\mathcal C\),
\[
\boxed{\|\mathbf1-p-c\|^2
=\|\mathbf1-(I-P_{\mathcal C})p\|^2
+\|P_{\mathcal C}p+c\|^2.}
\]
Mixed conductors have been minimized exactly, retaining their covariance effect.

The endpoint **PrimePowerSchur.exists_exact_global_elimination** constructs
coefficients \(b\) solving screened normal equations with source \(\Lambda\).
For every competing prime-power vector \(a\) and mixed packet \(c\), it proves
\[
\boxed{
\|\mathbf1-p_a-c\|^2
=1-\sum_q b_q\Lambda(q)
+\|\widetilde p_a-\widetilde p_b\|^2
+\|P_{\mathcal C}p_a+c\|^2.
}
\]
Both square remainders are complete. The minimum is attained at \(a=b\) and
\(c=-P_{\mathcal C}p_b\). The formal result requires neither invertibility nor
uniqueness of coefficients.

When the displayed Gram blocks are invertible, this is the Schur formula
\[
S=K_{PP}-K_{PC}K_{CC}^{-1}K_{CP},\qquad
\min\|\mathbf1-p-c\|^2=1-\Lambda_P^{\mathsf T}S^{-1}\Lambda_P.
\]
Otherwise the checked projection and normal equations apply without inverses.

Using the existing finite-span bridge and an exhaustive legal dictionary,
the approximation target is that these exact minima tend to zero. This limit
is not proved here. The sparse CRT comparison cannot be substituted for control
of the original screened Gram.

## 5. Actual translated Weil kernel: formalized

Suppose an actual nontrivial zero is
\(\rho=\tfrac12+\delta+i\gamma\), \(\delta\ne0\), with multiplicity \(m>0\).
Write \(\rho^\star=1-\overline\rho\).
The existing single-zero tests construct a smooth superexponentially decaying
\(h\) whose centered transform is one at \(\rho,\rho^\star\) and zero at every
other actual nontrivial zero. The new translation theorem keeps
\(\tau_t h(x)=h(x-t)\) in that class.

**SignedWeilCorrelation.exists_smooth_translated_reflection_kernel** proves
the complete actual arithmetic pairing is
\[
\begin{aligned}
W(\tau_t h,\tau_u h)=m\big[&
\overline{\exp(-(\rho^\star-\tfrac12)t)}
 \exp(-(\rho-\tfrac12)u)\\
&+\overline{\exp(-(\rho-\tfrac12)t)}
 \exp(-(\rho^\star-\tfrac12)u)\big].
\end{aligned}
\]
This is the exact form of the Lean conclusion. Elementary simplification gives
\[
\boxed{W(\tau_t h,\tau_u h)=
2m e^{i\gamma(t-u)}\cosh(\delta(t-u)).}
\]
No prime, pole, or gamma term is removed from the full arithmetic pairing.
The actual off-line zero is an explicit input, not an established existence
claim.

## 6. Exact prime/CRT spectrum: paper consequence

Let \(Q\ge2\), index all positive divisors \(d\mid Q\), set \(t_d=\log d\), and
put \(N=\tau(Q)\). Define
\[
R_Q(\delta)=\prod_{p^a\parallel Q}
 \left(\sum_{k=0}^{a}p^{\delta(2k-a)}\right).
\]
The complete matrix \(A_{de}=W(\tau_{\log d}h,\tau_{\log e}h)\) has eigenvalues
\[
\boxed{m[N+R_Q(\delta)],\quad m[N-R_Q(\delta)],\quad
0\text{ with multiplicity }N-2.}
\]

Proof: let \(u_d=d^\delta\), \(v_d=d^{-\delta}\), and
\(D_{dd}=e^{i\gamma\log d}\). The checked kernel gives
\(A=D\,m(uv^{\mathsf T}+vu^{\mathsf T})D^*\).
Now \(u^{\mathsf T}v=N\), and the divisor involution gives
\[
\|u\|\|v\|=Q^{-\delta}\sum_{d\mid Q}d^{2\delta}=R_Q(\delta).
\]
The vectors \(u/\|u\|\pm v/\|v\|\) have eigenvalues \(m(N\pm R_Q)\);
their orthogonal complement is the kernel. Since \(Q\ge2,\delta\ne0\),
the vectors \(u,v\) are independent, so strict Cauchy--Schwarz gives \(R_Q>N\).

Thus the matrix has exactly one negative direction. For squarefree \(Q\),
\(R_Q=\prod_{p\mid Q}(p^\delta+p^{-\delta})\). For a single prime the determinant is
\[
\boxed{-m^2(p^\delta-p^{-\delta})^2
=-4m^2\sinh^2(\delta\log p)<0.}
\]
The explicit vector \(D(u/\|u\|-v/\|v\|)\) has full quadratic value
\(-2m(R_Q-N)^2/R_Q\).
For \(Q=1\), only the eigenvalue \(2m\) occurs.

These spectral assertions are paper proofs from the checked kernel, not Lean
matrix-spectrum declarations. They refine the classical off-line Weil
obstruction. This Weil matrix is not identified with the positive sparse
Pareto Gram matrix.

## 7. Research status

The synthesis supplies a controlled full sparse form, an exact legal
prime-power Schur reduction, and the explicit negative translation block that
a Weil positivity argument must exclude. The RH route remains a
**conditional research reduction**.

- **Open:** Prove that exhaustive legal screened minima tend to zero, or that
  the associated von Mangoldt inverse quadratic tends to one where the inverse
  formulation applies.
- **Open:** Control the complete primitive-energy and signed covariance terms
  connecting the sparse CRT model with legal optimization.
- **Open:** For the Weil route, prove positivity of the full actual arithmetic
  form on a sufficient class. The conditional negative witness does not supply
  that positivity.

No signed correction, primitive remainder, or covariance block is dropped to
close these obligations. No squarefree-only or raw prime-power-only dictionary
is substituted for the full legal span.

## Provenance

Research direction: the user's CRT and exact signed-identity program.
Foundations include the integrated Anthropic formal-math/zeta23 actual explicit
formula, WeilSingleZeroTest.lean, WeilConverse.lean, the existing Ramanujan
modules, and LinearAlgebra/FiniteHilbertSchur.lean.

Classical GCD-kernel background: C. Aistleitner, I. Berkes, K. Seip,
*GCD sums from Poisson integrals and systems of dilated functions*,
J. Eur. Math. Soc. 17 (2015), 1517–1546, Section 4,
[DOI 10.4171/JEMS/537](https://doi.org/10.4171/JEMS/537).
This supports the established kernel context, not a novelty claim for the
finite-\(M\) comparison.
