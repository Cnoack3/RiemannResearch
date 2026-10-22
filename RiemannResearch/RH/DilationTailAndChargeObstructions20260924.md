# RH attempt: dilation tails and two limitations of norm arguments

Date: 2026-09-24. Baseline: 8e8bd48e09586fc72408739f9400a713dbe0d157.

**Outcome: no unconditional proof of RH.** The new Lean results below have no
additional arithmetic hypotheses, but they do not force residual energy to
vanish. Section 2 is also established in Lean; Sections 3--4 are paper arguments,
not kernel-verified declarations.
No mathematical novelty is claimed.

## 1. Verified tail localization

Let H_P have squared norm sum_{k>=1} f(k)^2/[k(k+1)], with physical value
f(0)=0. Set (D_m f)(k)=m f(floor(k/m)).
The existing exact norm identity is ||D_m f||_P^2=m||f||_P^2.

Write T_N(f)=sum_{k>N} f(k)^2/[k(k+1)]. Since D_(N+1)g vanishes on
k<=N, restricting Cauchy--Schwarz to its support gives

\[
|\langle f,D_{N+1}g\rangle_P|^2
\le (N+1)\|g\|_P^2 T_N(f).
\]

Therefore

\[
\lim_{N\to\infty}
\frac{|\langle f,D_{N+1}g\rangle_P|^2}{N+1}=0.
\]

These are implemented in RH/ParetoDilationTailLocalization.lean.
For the actual orthogonal residual r, put E=||r||_P^2 and T_N=T_N(r).
RH/ResidualDilationTailBounds.lean also specializes the result and proves

\[
\left|\sum_{k=1}^{N}r(k)\right|
\le
2\sum_{j=1}^{N}\sqrt{jE T_{j-1}}
+N\sqrt{(N+1)E T_N}.
\]

The signed identity used before taking absolute values remains

\[
\sum_{k=1}^{N}r(k)
=2\sum_{j=1}^{N}\langle r,D_jr\rangle_P
-N\langle r,D_{N+1}r\rangle_P.
\]

The source is the support argument in
Residual_Abel_Obstruction_20260924.md, Section 1, extended here to two
arbitrary Hilbert vectors. The coherent Lean check
job_i-lCGXY-xMXctD5cpNL8d4dj0ktS4qz6 succeeded, exit 0, verified true,
4.225 seconds. SHA-256:
3257351affd7c87a8c88d51df53bea4e1ee98214b2cb94889d6ce83106eacfe9.
The principal axiom reports contain only propext, Classical.choice,
and Quot.sound. The installed module boundaries are separately checked by
the publication checkpoint.

The established residual primitive criterion requires summability of
|sum_{k<=N}r(k)| against (3+tau(N+1))/[(N+1)(N+2)].
A fixed power upper bound with exponent less than 1 suffices.
The new tail bound does not establish that summability.

## 2. Physical one-sided mass obstruction (Lean-verified)

Let g_d(k)=(k mod d)/d, and r be the actual residual, so
<r,g_d>_P=0 and <r,1>_P=E. Define r^+=max(r,0), r^-=max(-r,0).
If r is nonzero, then

\[
\sum_{k\ge1}\frac{r(k)^+}{k+1}
=\sum_{k\ge1}\frac{r(k)^-}{k+1}=+\infty.
\]

To prove this, suppose Q=sum r(k)^-/(k+1) is finite. For a finite set F
of positive integers choose d>=2 greater than every element of F.
With w_k=1/[k(k+1)], the bounds 0<=d g_d(k)<=k and equality on F give

\[
\sum_{k\in F}k r(k)^+w_k
\le \sum_{k\ge1}d g_d(k)r(k)^+w_k
=\sum_{k\ge1}d g_d(k)r(k)^-w_k
\le Q.
\]

The middle sums exist: r^+ and r^- are Hilbert vectors and g_d is a
Hilbert vector. Their equality is precisely orthogonality.
The finite-subsum criterion proves sum r(k)^+/(k+1)<=Q.
Thus sum |r(k)|/(k+1) is finite.

Use the actual raw residual
U_N(k)=1+sum_{2<=d<=N}mu(d)g_d(k).
Existing project providers give |U_N(k)|<=k for N>=1, and U_N(k)->0 for
every fixed k. Dominated convergence now yields <r,U_N>_P->0.
But <r,U_N>_P=E exactly, so E=0 and r=0.
Interchanging the positive and negative parts proves the other assertion.

This argument is implemented in RH/ResidualPhysicalSignMass.lean. The
coherent check job_gx4m_YwzFV0V7Qcc7-X67PF61Z8C5uzj succeeded, exit 0,
verified true, in 4.750 seconds. Its two principal axiom reports contain
only propext, Classical.choice, and Quot.sound. SHA-256:
18e48bc237c6af9b3d5a7bff6294d7dbcf1cd42a26f267782cbf4379bd687f67.
The conditional vanishing theorems keep their signed summability premise
explicit. The non-RH theorem proves nonsummability of both nonnegative
series; divergence follows from their nonnegativity.

Consequently a nonzero actual residual must have positive and negative
physical values arbitrarily far out. This concerns physical values, not
the Möbius-charge oscillation in MobiusResidualSignOscillation.lean.
It does not prove finiteness of either actual signed mass.

## 3. Hilbert-small legal vectors can have large periodic primitives

For q>=2 define

\[
f_q=\frac{2q}{q-1}g_q-\frac{2(q+1)}q g_{q+1}.
\]

Each scaled summand has period mean 1. Hence f_q has mean zero and is a
finite legal vector. The elementary bound
g_q(k)<=min(k/q,1), splitting at q, gives ||g_q||_P^2<=2/q.
The triangle inequality therefore proves ||f_q||_P->0.

Nevertheless put a=floor(q/2) and K=a(q+1). Exact summation of complete
periods and the last incomplete period gives

\[
\sum_{k=0}^{K-1}f_q(k)=-\frac{a(q-a)}{q-1}.
\]

Its absolute value is at least q/8 for q>=4. Thus strong Hilbert
convergence, even among mean-zero legal vectors, does not bound the
centered ordinary primitives. Applying such an inference to inverse-Gram
rows would require an additional arithmetic argument.

## 4. The prime-scale charge data do not force legal density

This abstract countermodel concerns the sufficiency of selected charge
data. It is not a counterexample to RH or to the full arithmetic model.

Fix p>=2, S>0 (in particular S=15/pi^2), and set

\[
H=\mathbb R e_0\oplus\ell^2(\mathbb N_{\ge1}),\quad
Ue_n=e_{pn},\quad c=\sqrt{S/(p^2+1)},\quad B=c(pI-U).
\]

The Neumann series
B^{-1}=(cp)^{-1}sum_{j>=0}p^{-j}U^j
converges in operator norm. Define

\[
q_n=n^{-1/2}e_0+(0,Be_n),\qquad
v_n=(0,(B^{-1})^*e_n),\qquad
g_d=\frac1d\sum_{n<d}v_n.
\]

Then <v_n,q_m>=delta_nm, so
v_n=(n+1)g_(n+1)-n g_n and

\[
\langle g_d,q_N\rangle=d^{-1}\mathbf1_{\{N<d\}}.
\]

The q_n are complete: orthogonality of (t,x) to every q_n would give
(B^*x)_n=-t/sqrt(n). Since B^*x belongs to l2 and (1/sqrt(n)) does not,
t=0 and then x=0. Biorthogonality proves minimality. They are weakly null.

For all i,j>=0,

\[
\langle q_{p^iN},q_{p^jN}\rangle
=S\delta_{ij}
-\frac{Sp}{p^2+1}\mathbf1_{\{|i-j|=1\}}
+\frac{p^{-(i+j)/2}}N.
\]

Thus the norm limit is S, and the limiting prime-scale Gram entries
are exactly the diagonal and adjacent entries in the arithmetic route.
For A_(K,N)=K^{-1}sum_{i<K}q_(p^i N), K>=1, the exact identity is

\[
\|A_{K,N}\|^2=
\frac{S((p-1)^2K+2p)}{(p^2+1)K^2}
+\frac{(1-p^{-K/2})^2}{NK^2(1-p^{-1/2})^2}.
\]

These averages tend strongly to zero even with N fixed.
Yet the closed span of all g_d is {0} direct-sum l2, and e0 is
orthogonal to it. Every finite best approximation squared error for e0
is exactly 1.

The moment interpolants
f_N=sum_{n<=N}n^{-1/2}v_n satisfy
<f_N,q_j>=<e0,q_j> for j<=N, but

\[
\frac{\sum_{n\le N}1/n}{c^2(p+1)^2}
\le \|f_N\|^2
\le \frac{\sum_{n\le N}1/n}{c^2(p-1)^2}.
\]

Their errors therefore diverge. This explicitly separates strong
cancellation of dual charges from bounded primal interpolation.
The model does not reproduce the arithmetic target moments log(d)/d
or the physical residue coordinates. Those additional structures remain
possible sources of a proof.

## 5. Exact remaining boundary

Current main at the start of this attempt already proved the logarithmic
Möbius mean and full fixed Gram-source decay. Fixed source decay is not
an estimate for G_N^{-1}(b_N+G_N mu_N).

No theorem in this continuation proves r=0, signed Schur saturation,
the actual primitive summability, or the required inverse-Gram correction
limits. These obligations remain open. The new estimates and the paper
obstructions specify where additional arithmetic cancellation is needed.
