---
title: "Independent primes, signed sieves, and the RH energy criterion"
subtitle: "Lean formalization and research continuation"
author: "Research note prepared for Christian Noack"
date: "October 7, 2026; Lean verification updated October 8"
fontsize: 11pt
geometry: margin=1in
---

# Scope and precise status

This continues *Independent Primes and Squarefree Approximation* (October 7,
2026). It contains no imported Mathematica tables. Exact finite identities,
weighted-energy comparisons, and the RH implication are the formalization
targets. A positive answer to the small-damping arithmetic question is **not**
claimed. **All 49 source candidates are now salvaged:** all 73 theorem bodies in
eight modules pass coherent Lean checks. Every public axiom report contains
only ordinary Lean foundations. The theorem statements are unchanged.
The detailed October 8 record below supersedes the earlier partial ledger;
small-damping energy and the stated analytic formalization obligations remain
Open.

The mathematical development below rules out the specific signed two-cutoff
proposal in the earlier research agenda. It also strengthens the bounded
pointwise approximation criterion. The complete asymptotic prime-sieve
obstruction and the strengthened Hilbert-space criterion are mathematical
proofs; their finite algebra is separated from the remaining formalization.

# Definitions and the existing analytic reduction

Write $Z=\zeta(2)=\pi^2/6$. On the positive integers use

$$
Q(K=k)=\frac1{Zk^2},\qquad P(K=k)=\frac1{k(k+1)},\qquad
g_d(k)=\frac{k\bmod d}{d}=\{k/d\}.
$$

The zero coordinate in the Lean sequence model has weight zero. This is a
convention for representing positive-integer sequences; it is not an extra
atom of either probability law. The two energy conditions are equivalent,
with the exact comparison

$$
\frac Z2\|f\|_Q^2\le\|f\|_P^2\le Z\|f\|_Q^2.
\tag{1}
$$

Let $C_{\rm sf}$ be the closed span in $L^2(Q)$ of the $g_d$ with $d\ge2$
squarefree. Bagchi's discrete squarefree theorem, together with (1), gives
the mathematical criterion

$$
\mathrm{RH}\quad\Longleftrightarrow\quad 1\in C_{\rm sf}.
$$

For the direction of particular concern, the repository already has
`SquarefreeTransfer.riemannHypothesis_of_squarefreeCenteredApproximation`.
It consumes explicit finite squarefree witnesses and their complete centered
errors; its proof has no external density assumption. The generic
`ComparableWeights.riemannHypothesis_of_weightedApproximation` transfers
inverse-square finite witnesses to RH. The converse in the corresponding
Lean equivalence still requires the explicit analytic input
`RiemannHypothesis → NaturalApproximation`. A literal theorem about the
infinite product probability space is not claimed here. Also, a
seed-and-dilation closure with squarefree *seeds* must not be confused with
the literal squarefree-only dictionary.

For $\varepsilon>0$ define

$$
A_\varepsilon(N)=\sum_{d\le N}\mu(d)d^{-\varepsilon}\lfloor N/d\rfloor,
\qquad C_\varepsilon=\frac1{\zeta(1+\varepsilon)},\qquad
F_\varepsilon(N)=A_\varepsilon(N)-NC_\varepsilon.
\tag{2}
$$

The coefficient $\mu(d)$ is zero when $d$ is not squarefree. Pointwise,
$F_\varepsilon=-\sum_{d\ge2}\mu(d)d^{-\varepsilon}g_d$. This identity does not
by itself assert convergence of the series in $L^2(Q)$.

**Existing formal theorem.** The repository already proves that if
$\varepsilon_j>0$, $\varepsilon_j\to0$, and for every $j$ there is a real center
$C_j$ such that

$$
\sum_{N\ge1}\frac{|A_{\varepsilon_j}(N)-NC_j|^2}{N(N+1)}<\infty,
\tag{3}
$$

then RH holds. There is no common bound on these energies and no hypothesis
that the profiles converge to one in norm. The declaration is
`RiemannResearch.RH.Pareto.riemannHypothesis_of_centered_damped_square_summable`
in `RH/BurnolFiniteEnergyReduction.lean`.

The new energy-transfer source candidate specializes this theorem to

$$
\forall\delta>0\ \exists\varepsilon\in(0,\delta)\ \exists C\in\mathbb R:
\quad \sum_{N\ge1}\frac{|A_\varepsilon(N)-NC|^2}{ZN^2}<\infty
\quad\Longrightarrow\quad\mathrm{RH}.
\tag{4}
$$

It also contains the sequence formulation with the canonical center in (2).
The formal normalizer is an arbitrary explicit $Z>0$; taking $Z=\zeta(2)$
gives the stated probability energy. The source-level definition is

```lean
def normalizedEnergy (Z : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((1 / (n : ℝ)^2) * (f n)^2) / Z
```

The proof imports the existing Mellin continuation and zero-isolation
argument. For $\Re s>1$ its cross-multiplied identity is

$$
s\zeta(s+\varepsilon)\mathcal M(F)(s)
=\zeta(s)\bigl(1-C\zeta(s+\varepsilon)\bigr).
\tag{5}
$$

Finite energy makes the left transform analytic in $\Re s>1/2$. If
$\rho$ is a zero with $1/2+\varepsilon<\Re\rho<1$, evaluation at
$s=\rho-\varepsilon$ forces $\zeta(\rho-\varepsilon)=0$. Isolated zeros exclude
this for every sufficiently small positive $\varepsilon$. This proves (4)
without dividing by zeta at a zero. Burnol's paper supplies the analytic
strategy; the repository supplies its arithmetic realization.

**Remaining RH obligation.** Establish the finiteness in (4), or its canonical
version, at arbitrarily small positive damping. The existing unconditional
formal result covers $\varepsilon\ge1/2$, including the endpoint. It supplies
no positive sequence tending to zero. Prime independence controls the source
$\prod_{p\mid n}(1-p^{-\varepsilon})$; it does not bound its centered cumulative
sum. This research question remains open here.

**An attempted estimate and its limit.** For $0<\varepsilon<1$, absolute
convergence of the coefficient series gives the exact signed split

$$
F_\varepsilon(N)
=-\sum_{d\le N}\mu(d)d^{-\varepsilon}\{N/d\}
-N\sum_{d>N}\mu(d)d^{-1-\varepsilon}.
$$

Dropping cancellation and comparing the two sums with integrals yields

$$
|F_\varepsilon(N)|\le
\sum_{d\le N}d^{-\varepsilon}
+N\sum_{d>N}d^{-1-\varepsilon}
\le \frac{N^{1-\varepsilon}}{\varepsilon(1-\varepsilon)}.
$$

Its $Q$-energy majorant is a constant times $\sum N^{-2\varepsilon}$, so
this route supplies only $\varepsilon>1/2$. Divergence of the majorant at or
below one half does **not** prove divergence of the actual energy. The
repository's endpoint argument improves the error to order
$\sqrt N/(6+\log N)^{3/4}$ at $\varepsilon=1/2$, but still does not approach
zero damping.

The precise obstacle to using independence is visible in the finite energy
identity. Put $b_\varepsilon(n)=\prod_{p\mid n}(1-p^{-\varepsilon})-C_\varepsilon$.
For every $H$,

$$
\sum_{N\le H}\frac{F_\varepsilon(N)^2}{N^2}
=\sum_{m,n\le H} b_\varepsilon(m)b_\varepsilon(n)
  \sum_{N=\max(m,n)}^H\frac1{N^2}.
$$

The additive-order kernel does not factor over prime coordinates. Moreover,
the raw summation operator $Tb(N)=\sum_{n\le N}b(n)$ is unbounded on $L^2(Q)$:
for $b=1_{\{m\}}$ its squared input norm is $1/(Zm^2)$, while its squared
output norm is $Z^{-1}\sum_{N\ge m}N^{-2}\ge1/(Zm)$. Thus bounded
multiplicative source moments alone cannot deliver the missing energy
estimate. These attempted bounds and the operator example are mathematical
arguments, not additional checked declarations.

# Exact finite prime-product layer

For a finite prime set $S$, the variables $B_p=1_{p\mid K}$ under $Q$ are
independent with success probability $p^{-2}$. Put

$$
L_p(B_p)=\begin{cases}p,&B_p=1,\\p/(p+1),&B_p=0,\end{cases}
\quad L_S=\prod_{p\in S}L_p,
\quad v_S=\prod_{p\in S}\frac p{p+1}.
$$

Exact two-point calculation and finite tensor factorization give

$$
E L_S=1,\qquad E L_S^2=2^{|S|}v_S,\qquad
E\left(L_S\prod_{p\in T}B_p\right)=\frac1{\prod_{p\in T}p}\quad(T\subseteq S).
\tag{6}
$$

Multiplication by $L_S$ changes the success probabilities from $p^{-2}$ to
$p^{-1}$. `RH/FinitePrimeLikelihood.lean` uses explicit masses on
$\{0,1\}^{S}$ and proves these identities by finite sums, rather than assuming
a factorization rule as an unproved premise. It allows real parameters
$p\ge1$; natural primes are particular instances. It does not construct the
infinite product probability space or prove the prime-exponent law anew.

For a finite legal combination $F=\sum_{d\in D}c_dg_d$ with every $d\mid P$,
the existing CRT theorem gives

$$
\operatorname{mean}_{P}F
=\frac12\left(\sum_{d\in D}c_d-\sum_{d\in D}\frac{c_d}{d}\right).
\tag{7}
$$

The new CRT energy source candidate retains the actual coefficients and derives the
first-period lower bound

$$
\|1-F\|_Q^2\ge\frac{|1-\operatorname{mean}_{P}F|^2}{ZP}.
\tag{8}
$$

This bound uses only the first $P$ coordinates and the finite variance
identity. Its explicit summability hypothesis avoids treating Lean's
totalized infinite sum as finite energy when the series diverges. The earlier
PDF obtains the stronger constant $1/P$ by using all periods; that stronger
constant is not asserted by this source candidate. A companion finite Boolean
source candidate contains divisibility moments, differentiated Gram entries,
exact diagonal norms, and orthogonality to the likelihood vector.
The complete finite derivative optimizer and its Fourier variance formula
are not fully formalized in this continuation.

# A negative solution of the two-cutoff research question

For real $t\ge2$ define

$$
P_t=\prod_{p\le t}p,\quad a_t=\prod_{p\le t}(1-1/p),\quad
F_t=-\sum_{d\mid P_t}\mu(d)g_d,\quad
B_t=\sum_{p\le t}\frac{\log p}{p-1},\quad U_t=1/a_t.
$$

Let $\ell(f)=E_P f$. As a functional on $L^2(Q)$,

$$
\ell(f)=Z E_Q\left[\frac K{K+1}f(K)\right],\qquad
\|\ell\|^2=Z(Z-1),\qquad \ell(F_t)=a_tB_t.
\tag{9}
$$

Indeed, $E_P g_d=(\log d)/d$ follows from finite Abel summation; differentiating
the finite Euler product gives the last equality. The norm follows by summing
$Z/(k+1)^2$ over $k\ge1$.

The proposed exact-head interpolant is

$$
H_{y,z}=\frac{a_yF_z-a_zF_y}{a_y-a_z},\qquad z>y\ge2,\quad a_z<a_y.
$$

It equals one at positive integers $k\le y$. Its mean, however, is the exact
secant slope

$$
\ell(H_{y,z})=\frac{B_z-B_y}{U_z-U_y}.
\tag{10}
$$

For a prime $p$, a subscript $p^-$ means the product over primes strictly less
than $p$. The jumps satisfy

$$
\Delta U_p=\frac{U_{p^-}}{p-1}>0,\qquad
\Delta B_p=\frac{\log p}{p-1},\qquad
\frac{\Delta B_p}{\Delta U_p}=a_{p^-}\log p=:r_p.
$$

Telescoping both differences gives

$$
\ell(H_{y,z})=\sum_{y<p\le z}w_pr_p,\qquad
w_p=\frac{\Delta U_p}{U_z-U_y}>0,\qquad\sum w_p=1.
\tag{11}
$$

Write $H_n=\sum_{k=1}^n1/k$ and
$\gamma=\lim_{n\to\infty}(H_n-\log n)>0$ for Euler's constant.
Mertens' product theorem says $a_t\log t\to c=e^{-\gamma}<1$. Therefore
$r_p=a_p\log p/(1-1/p)\to c$, without any prime-gap hypothesis. Set
$\eta_y=\sup_{p>y}|r_p-c|$; then $\eta_y\to0$. The convex identity (11) gives
the bound **uniformly in every admissible second cutoff**:

$$
|\ell(H_{y,z})-c|\le\eta_y.
$$

The exact head allows a sharper, localized bound. If any $F$ satisfies
$F(k)=1$ for $1\le k\le N$, the residual $r=1-F$ is supported on $k>N$.
Since $P(K>N)=1/(N+1)$, Cauchy--Schwarz under $P$ and (1) give

$$
|\ell(r)|^2\le\frac{\|r\|_P^2}{N+1}
\le\frac{Z\|r\|_Q^2}{N+1}.
$$

Take $N=\lfloor y\rfloor$ and $x_+=\max(x,0)$. It follows that

$$
\|1-H_{y,z}\|_Q^2\ge
\frac{\lfloor y\rfloor+1}{Z}(1-c-\eta_y)_+^2.
\tag{12}
$$

Consequently, for any $y_j\to\infty$ and any admissible $z_j>y_j$,

$$
\boxed{\liminf_j\frac{\|1-H_{y_j,z_j}\|_Q^2}{y_j}\ge
\frac{(1-e^{-\gamma})^2}{\zeta(2)}>0.}
\tag{13}
$$

Thus the squared error diverges at least linearly in the smaller cutoff,
uniformly over the larger cutoff. The endpoint in (12) follows from the
exact Pareto tail mass, so no tail integral approximation is needed.

Since the head residual vanishes, (13) is a diverging lower bound on the very
tail budget requested in Priority 3. That particular proposed construction
cannot succeed. This does not exclude general signed squarefree combinations.

There is a vector version. Define $G_p=pF_p-(p-1)F_{p^-}$. Direct normalization
gives

$$
\frac{F_p}{a_p}-\frac{F_{p^-}}{a_{p^-}}=\Delta U_p G_p,
\qquad H_{y,z}=\sum_{y<p\le z}w_pG_p,
\qquad \ell(G_p)=r_p.
\tag{14}
$$

Thus this signed two-cutoff expression is itself a convex average of prime
increments. Every $r_p<1$: expanding the finite Euler product gives
$U_{p^-}=\sum_{P^+(n)<p}1/n\ge H_{p-1}>\log p$. Since $r_p\to c<1$, their
supremum $c_*<1$. The functional $\ell$ therefore separates one from the
closed convex hull of all $G_p$, hence also all two-cutoff interpolants,
including families whose first cutoffs do not tend to infinity.

The secant algebra module proves the finite algebra and the following signed
bound, retaining the full coefficient variation. If
$J_y=\sum_{p>y}\alpha_pG_p$ is finite and $\sum\alpha_p=1$, then

$$
|\ell(J_y)-c|\le\eta_y\sum_p|\alpha_p|.
\tag{15}
$$

Hence $J_y\to1$ in $L^2(Q)$ forces $\sum|\alpha_p|\to\infty$. An explicit
Mertens error gives $\eta_y=O(1/\log y)$, so the necessary variation is at least
of order $\log y$. This is a restriction on possible signed constructions,
not an energy upper bound. The Lean algebra does not silently assume or
formalize Mertens' asymptotic theorem.

## Signed pairs of late prime increments also fail

The variation condition alone leaves open the possibility of correcting the
mean using one positive and one negative coefficient. That particular
possibility can also be ruled out. Let $p<q$ be primes and, for any real
$\alpha$, put

$$
J=\alpha G_p+(1-\alpha)G_q,\qquad
e=1-J,\quad E=\|e\|_Q^2,\quad C=1-r_q,\quad D=r_p-r_q.
$$

The rough-count formulas give $G_p(k)=1$ for $1\le k<p$,
$G_p(p)=2-p$, and $G_q(p)=1$. Thus $e$ vanishes below $p$,
$e(p)=\alpha(p-1)$, and $\ell(e)=C-\alpha D$. The distinguished coordinate
and the complete Pareto tail give, respectively,

$$
E\ge\frac{\alpha^2(p-1)^2}{Zp^2},\qquad
E\ge\frac pZ(C-\alpha D)^2.
$$

Combining these by the triangle inequality eliminates $\alpha$:

$$
E\ge
\frac{(1-r_q)^2}{
 Z\left(p^{-1/2}+\frac p{p-1}|r_p-r_q|\right)^2}.
\tag{16}
$$

This retains an error obstruction even when the mean is corrected exactly.
For sufficiently large $y$, it implies, uniformly over $y<p<q$ and every
$\alpha$,

$$
E\ge\frac{(1-c-\eta_y)^2}{
 Z\left(y^{-1/2}+\frac{2y}{y-1}\eta_y\right)^2}
\longrightarrow\infty.
\tag{17}
$$

The explicit Mertens error used above supplies the rate
$E=\Omega((\log y)^2)$.

One can retain the coordinate--tail interaction exactly. Set
$\delta_p=(p-1)/[p(p+1)]$. The signed identity
$C=\ell(e)+D e(p)/(p-1)$ is a single functional on errors supported on
$k\ge p$. Its squared Riesz norm gives

$$
E\ge
\frac{C^2}{
 Z\displaystyle\sum_{k\ge p+1}(k+1)^{-2}
 +\frac{Zp^2}{(p-1)^2}(D+\delta_p)^2}.
\tag{18}
$$

Here the square includes the full signed cross term. The tail sum is at most
$1/(p+1)$, if an elementary bound is desired. Formula (18), and hence (16),
is a mathematical result in this continuation; it is not a checked Lean
declaration. Constructions using more than two prime increments remain
outside this obstruction.

# A stronger bounded-pointwise criterion

Let $C$ be the closed span of any fixed legal residue dictionary in $L^2(P)$.
Suppose $F_n\in C$, $F_n(k)\to1$ for every $k\ge1$, and a subsequence has
$\|F_{n_j}\|_P\le B<\infty$. Then $1\in C$. Thus it is enough that

$$
\liminf_n\|F_n\|_Q<\infty,
\tag{19}
$$

instead of the earlier whole-sequence uniform norm bound.

**Proof.** Let $r=1-\operatorname{proj}_C1$. Orthogonality gives
$\langle r,1-F_{n_j}\rangle_P=\|r\|_P^2$. For each $M\ge1$, keep the finite
head signed and estimate only the tail:

$$
\begin{aligned}
\|r\|_P^2&\le
\left|\sum_{k=1}^M\overline{r(k)}(1-F_{n_j}(k))\frac1{k(k+1)}\right|\\
&\quad+\left(B+\frac1{\sqrt{M+1}}\right)
\left(\sum_{k>M}\frac{|r(k)|^2}{k(k+1)}\right)^{1/2}.
\end{aligned}
$$

For fixed $M$, send $j\to\infty$; the finite head tends to zero. Then send
$M\to\infty$; the residual tail tends to zero. Hence $r=0$. Comparison (1)
transfers the assertion to $Q$. Conversely, membership in the closed span
provides norm-convergent finite combinations, which are bounded and converge
pointwise because each coordinate evaluation is continuous.

For the squarefree dictionary, Bagchi's Theorem 1 and Remark 8 therefore give
an exact RH reformulation: existence of pointwise-to-one finite squarefree
combinations with finite norm liminf. The new proof does not construct such
a sequence. This infinite-dimensional criterion is proved mathematically
here; it is not claimed as a new checked Lean declaration.

# Research agenda after these results

1. **Small damping:** prove the actual centered cumulative energy finite at
   arbitrarily small positive damping. This remains the principal RH-strength
   arithmetic task. Neither independence nor the unconditional half-damping
   endpoint discharges it.
2. **Original norm optimization:** use the true residue Gram matrix. The finite
   likelihood identities help describe derivative geometry, but derivative
   minimization alone does not minimize the original energy. Retain the actual
   period mean and all Fourier contributions when testing coefficients.
3. **Signed cancellation:** abandon the two-cutoff family. For combinations
   of late prime increments with affine normalization, account for the required
   increasing coefficient variation and bound the complete signed tail.
   Signed pairs of late increments also fail by (17); a larger dictionary
   requires new cancellation estimates.
4. **Cofinal boundedness:** a pointwise legal sequence with just one cofinally
   bounded subsequence would suffice. The source question is to construct and
   bound that actual subsequence, not to assume compactness delivers it.
5. **Further formalization:** connect the explicit finite Boolean law to the
   infinite prime-exponent probability space; formalize the full derivative
   projection and the Mertens specialization of (13); then formalize the
   residual-tail proof of (19). No numerical table is needed for these tasks.

# References and provenance

- Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis*, arXiv:math/0607733. Theorem 1 and
  Remark 8 support the discrete and squarefree closure criterion.
  <https://arxiv.org/pdf/math/0607733>
- Jean-François Burnol, *On an analytic estimate in the theory of the Riemann
  zeta function and a theorem of Baez-Duarte*, arXiv:math/0202166. Lemma 4.3,
  Corollary 4.1, and Theorem 4.2 support the Mellin identity, shifted-zero
  argument, and small-damping implication.
  <https://arxiv.org/pdf/math/0202166>
- Jared Duker Lichtman, *Mertens' prime product formula, dissected*,
  arXiv:2002.03361, Theorem 1.1 and equation (1.4). These support the product
  asymptotic and the smooth-integer expansion.
  <https://arxiv.org/pdf/2002.03361>
- Mark B. Villarino, *Mertens' Proof of Mertens' Theorem*, arXiv:math/0504289,
  printed page 4, footnote 2. This supplies the optional explicit Mertens error
  used for the variation rate following (15).
  <https://arxiv.org/pdf/math/0504289>

Wolfram was used only to check the two rational normalization identities in
(10) and (14). It returned zero symbolic discrepancies. These checks are
supporting algebra checks, not substitutes for mathematical or Lean proofs.

# Exact verification and publication record

The October 8 salvage verifies all 49 previously unverified statements, in addition
to the historical group of 24 finite theorems. The mathematical sections above
retain their stated distinction between formalized identities and further
paper-level research results. No new RH proof is claimed.

See [the detailed salvage record](Salvage49ResearchStatus20261008.md),
[the kernel audit](Salvage49KernelVerification20261008.json), and
[the unchanged-statement audit](Salvage49StatementAudit.json).

## Kernel verification and publication procedure

All **73 theorem bodies** in the eight modules pass coherent Lean checks, including all **49 previously unverified candidates**. The final comparison preserves every original candidate statement and explicit section context. The union of all 73 public axiom reports is exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorryAx` dependencies. The complete-body checks in batches B, C, and D report no warnings; all batches return `verified = true` and exit code zero.

The environment is Lean `v4.33.0-rc2` with the project's pinned Mathlib. Isolated checks used repository baseline `04db1cc3090d06e1abd30261b4a5f4d27df8e189`. Each batch includes every theorem body. Batch A's output was truncated; batch D recovers its seven missing axiom reports. Together the retrieved reports cover all 73 distinct theorem names.

| Batch | Terminal check job | Seconds | Checked source SHA-256 |
|---|---|---:|---|
| A | `job_wk41K91c4aQH2-EAPpt39Q8T4XEg3IW4` | 5.028 | `896cfa8e76eb956c930ddca896c6ccc2c5ff4f40fc46ee2f40a28a7c7934a10b` |
| B | `job_C_INejVCm7_Dqt6daXQYLVzl9gQKWwgr` | 5.035 | `32d8aa76b7d0b84edffd5b1d11b04ac1ca0c89f6bdba3920a14603028146b7ec` |
| C | `job_G85sDFx8acfOV0DwWvosDbvwmYZQ8n4L` | 4.738 | `2f630e04ff0a95ebc20d409c69818ec58136b7ac9b46c070715d2d4d2dae1015` |
| D | `job_cBsr1B2TI7BHymD_4yeLT87DI4-2CDJt` | 4.961 | `4fa6911d1574610ed513f681f53771757d87d412df1d6442eeeab6629b79d6b6` |

`Salvage49KernelVerification20261008.json` records the report for every declaration. `Salvage49StatementAudit.json` records the original and final statement hashes and the final source digests. These records distinguish kernel verification from source comparison.

The retained dependency build was recovered as interrupted. Its incremental continuation reached completion but reported errors in two candidate modules. Four elaboration/tactic issues and redundant tactic warnings were then repaired. That failed preparation build is not reported as a successful full-project build. The subsequent coherent checks verify the repaired proof bodies.

All eight native modules are exported from `RiemannResearch.lean`. Final publication uses the workspace checkpoint, which audits and validates the affected native modules and their reverse dependents before committing and pushing. Its final commit and native validation outcome are supplied in the publication response and delivered verification manifest; an isolated check alone does not assert publication.
