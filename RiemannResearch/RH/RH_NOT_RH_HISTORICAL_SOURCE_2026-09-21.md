# What the failure of the Riemann Hypothesis would imply

Comprehensive historical research catalogue — Christian Noack — 21 September 2026

## Scope, evidence, and reading convention

This catalogue combines the recoverable RH chat history with current saved mathematical research records. The initial filename inventory contained 331 RH-related items, including duplicates, versions, computational artifacts, and records that were deliberately excluded. Additional differently named mathematical records were retrieved by topic. The chapter source ledgers identify 86 distinct saved-artifact references; some were read in full and others in the explicitly identified relevant sections. **An inventory is not a claim to have read every item.** The mathematical sources actually used are identified in the chapters. Historical searches reached back to the May–August work as well as the September program.

**No Lean service, project, repository, proof source, build, or verification was accessed.** Statements in earlier reports about formal verification are not treated here as newly checked evidence. This is an ordinary mathematical audit of the recovered history and saved arguments.

The available historical search does not provide a complete enumerable export of every chat. Consequently, this is a comprehensive catalogue of the recovered research, not a certified assertion that every message in the account was inspected. Duplicate versions were consolidated; later mathematical corrections take precedence. A few older claims that cannot be promoted to audited theorems are retained explicitly as historical or conditional statements.

There is no finite literal list of *all* logical consequences of a hypothesis: one can always take further logical combinations. Here “exhaustive” means covering every distinct recovered mathematical criterion, quantitative obstruction, tail restriction, limit, structural consequence, and important non-implication, with the relevant quantifiers retained.

Unless a paragraph says otherwise, all positive-gap and failure conclusions below are **conditional on not RH**. None is asserted to hold unconditionally. Standard identities and limitations that survive regardless of RH are marked as such. The catalogue does not establish that the joint obstruction is inconsistent.

### Four kinds of entry

1. **Equivalent obstruction:** an assertion equivalent to not RH, using the stated classical criterion.
2. **Necessary consequence:** proved from not RH, sometimes quantitatively from any particular off-line zero.
3. **Failure of a sufficient package:** if assumptions A, B, C together imply RH, not RH gives “at least one fails”; it does not give three separate failures.
4. **Historical correction or non-implication:** a conclusion that must not be inferred, including estimates already false independently of RH.

Quantifiers matter. The negation of a uniform bound is an unboundedness statement, not automatically convergence to infinity. An increasing energy *does* tend to infinity when it is unbounded. Failure of a rate may mean an unbounded limsup, not a lower bound for every large index. Cofinal means arbitrarily far out; it does not mean every index.

## Common notation and the central joint obstruction

Use
\[
w_n=\frac1{n(n+1)},\qquad H=\ell^2(\mathbb N_{\ge1},w),\qquad g_d(n)=\frac{n\bmod d}{d},
\]
\[
V=\operatorname{span}_{\mathrm{finite}}\{g_d:d\ge2\},\quad S=\overline V,\quad P=P_S,\quad Q=I-P.
\]
Here \(e_n\) denotes the coordinate indicator and \(\eta_n=e_n/\sqrt{w_n}\) the normalized coordinate. The sequence \(1\) is the constant vector, with norm one. The equivalent continuous model is the **unit-interval step-function subspace** of \(L^2([1,\infty),dx/x^2)\); density in this subspace does not mean density in the entire continuous space.

The foundational classical input is
\[
\mathrm{RH}\iff 1\in S\iff S=H,
\]
as stated in [Bagchi, Theorem 1](https://arxiv.org/pdf/math/0607733). The first-coordinate version follows from the legal dilation identity \(D_mg_d=g_{md}-g_m/d\), where \(D_mf(n)=f(\lfloor n/m\rfloor)\) and \(f(0)=0\).

Assume not RH. Define
\[
r=Q1,\qquad E=\|r\|^2>0,\qquad q^{\mathrm{vec}}=Qe_1,\qquad\delta=\|q^{\mathrm{vec}}\|^2>0.
\]
The symbol \(q^{\mathrm{vec}}\) is a vector, not the recent scalar \(q_N\). The arithmetic DPP kernel is
\[
K(i,j)=\langle\eta_i,P\eta_j\rangle,\qquad h_n=1-K(n,n).
\]
Write \(p_*=K(1,1)=1-2\delta\) and \(C\) for full-tail capacity. Then
\[
0<p_*<1,\qquad C=\delta^{-1}-2=\frac{2p_*}{1-p_*}<\infty,
\]
\[
z_*=2e_1-\delta^{-1}Qe_1,\qquad z_*(1)=0,\quad\langle g_d,z_*\rangle=1/d,\quad\|z_*\|^2=C.
\]
Thus the approximation defect, the DPP vacancy, and the finite-energy certificate belong to **the same fixed arithmetic projection**, not independently chosen examples.

For every finite legal \(f\),
\[
\|1-f\|^2=E+\|P1-f\|^2\ge E.
\]
Every actual zero \(\rho=\beta+i\gamma\), \(1/2<\beta<1\), supplies
\[
E\ge\frac{2\beta-1}{|\rho|^2}>0.
\]
The gap can nevertheless be small. For example the exact two-generator calculation gives
\[
E\le 1-b^*G^{-1}b=0.0957477839\ldots
\]
with \(G,b\) explicitly recorded in the Mellin-upper-estimate source. Small numerical upper bounds are compatible with a positive limit.

The later seven-generator record gives the stronger saved rational certificate
\[
E\le\frac{6061132763331737}{250000000000000000}<0.0242446.
\]
Its exact-certificate argument is recorded in the tail chapter; the arithmetic computation was not rerun in this audit. It supersedes the two-generator ceiling as a numerical upper bound, without deciding whether \(E=0\).

### Notation collisions in the history

| Historical symbol or phrase | Meaning here | Behavior under not RH |
|---|---|---|
| Recent trigamma \(q_N\) | Occupation of residue class 1 modulo the current period | Converges to \(p_*<1\); need not be monotone |
| First-site occupation | \(p_N=K_N(1,1)\) | Increases to \(p_*<1\) |
| Older vacancy \(q_N\) | \(1-p_N\) | Decreases to \(1-p_*>0\) |
| Older capacity \(q_N\), \(\widetilde q_N\), or \(C_N\) | Full-tail inverse-Gram capacity | Increases to finite \(C\) |
| First-site residual \(\delta_N\) | \(\|e_1-P_Ne_1\|^2\) | Decreases to \(\delta=1/(C+2)>0\) |
| Constant-target error \(E_N\), sometimes \(d_N^2\) | \(\|1-P_N1\|^2\) | Decreases to \(E>0\) |
| Exact-head energy \(\mathcal A_N\) | Minimum full norm squared with first \(N\) values equal to 1 | Diverges; polynomial lower bounds |
| Exact-head error \(\Delta_N\) | Minimum \(\|1-f\|^2\) under the same head constraint | Diverges; a different objective from \(\mathcal A_N\) |
| Reconstruction energy \(Q_N\) | Norm squared of ordered stabilized-coefficient reconstruction | Diverges; its own upper bounds and logarithmic multiplicity refinements |

The later chapters define any additional local notation. In particular, a capital \(C\) used for a conditional-expectation operator in an older source is not the scalar capacity above, and prime-power indices historically called \(q_i\) are not occupation probabilities.

## A compact map of the full catalogue

| Strand | Required behavior if RH fails |
|---|---|
| Zeros and analytic continuation | A conjugate/reflected off-line quartet; poles in reciprocal zeta and error Mellin transforms |
| Legal approximation | Positive global distance, variance and mean-one error floors; incomplete arithmetic orthonormal family |
| Exact growing heads | All legal families pay diverging full-tail energy, at least a zero-dependent power |
| Regression and Schur gains | Total relative gain is summable; no sufficient uniform gain or repair estimate can hold |
| Canonical tails | Finite capacity and a unique finite-energy certificate with \(\ell^2\) but not \(\ell^1\) primitive |
| Coefficients and escape | Non-Möbius coefficient defects arbitrarily far out; reconstruction norms diverge while normalized mass escapes |
| DPP | Positive hole probability at every site, failed saturation, divergent weighted expected vacancy, zero probability of full occupation |
| Fredholm | Damped full-occupation determinant tends to zero, although first-site occupation remains close to one |
| CRT/profinite | Algebra and finite interpolation survive; the required uniform Pareto energy and limit interchanges fail |
| Mellin/Hardy | Some positively damped arithmetic energies are infinite; legal Mellin transforms vanish at every off-line zero with multiplicity |
| Weil/spectral | Negative completed-form witnesses; failure of global positivity, Herglotz representation, and exact self-adjoint spectral realization |
| Historical proposed proofs | At least one unresolved RH-strength bridge in each valid sufficient package fails |
| Classical arithmetic | Failure of RH-scale prime and Möbius bounds; negative Li coefficient; Robin/Lagarias violations; positive Newman constant |

## Reading map

The report contains 315 numbered entries, additional thematic subsections and joint-obstruction formulas. Some formulations recur because their different normalizations and logical roles matter; the count is not a claim of 315 independent theorems.

- **Part I: Tail, capacity, reconstruction, and regression.**
- **Part II: DPP, occupation, Fredholm determinants, and profinite limits.**
- **Part III: CRT, two-seed interpolation, covariance, and sampling.**
- **Part IV: Probability, spectral coordinates, damping, and reflection.**
- **Part V: Joint zero constraints, complementary powers, and Mellin rigidity.**
- **Part VI: Earlier Weil, spectral, geometric, and prime-cover programs.**
- **Part VII: Classical analytic and arithmetic consequences.**

Within each part, source labels refer to that part’s own source ledger. Formulas are stated in the notation defined locally. In particular, both scaled and unscaled dilations occur in the historical records; their normalization is stated where used.


## Part I. Tail, capacity, reconstruction, and regression

### Source map

Labels below refer to the mathematical sections of these current saved notes. Several contain inherited verification-history paragraphs; those paragraphs provide no additional mathematical premise here.

| Label | Source |
|---|---|
| T1 | `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19(3).md`, full 2,205 lines read |
| T2 | `RH_Tail_Capacity_CRT_Boundary_and_Dilation_Continuation_2026-09-19.md`, full 2,158 lines read |
| T3 | `RH_False_Canonical_Obstructions_and_Contradiction_Audit_2026-09-19.md` |
| T4 | `RH_Canonical_Defect_Escape_and_Multiplicity_2026-09-19.md` |
| T5 | `RH_Weak_Compactness_Profinite_Escape_and_Arithmetic_2026-09-19.md` |
| T6 | `RH_Direct_Attempt_Linear_Upper_Bound_2026-09-19.md` |
| T7 | `RH_Combined_NotRH_Obstruction_and_Prime_Sieve_Attempt_2026-09-19.md` |
| T8 | `RH_Candidate_5_Canonical_Tail_Attempt_2026-09-20.md` |
| T9 | `RH_Weighted_Telescoping_Construction_and_Tail_Repair_2026-09-19.md` |
| T10 | `RH_Tail_Repair_Contradiction_Attempt_2026-09-19.md` |
| T11 | `RH_Tail_Numerator_Expansion_and_Covariance_2026-09-19.md` |
| T12 | `RH_Sparse_Gain_and_Quantitative_Head_Repair_2026-09-19.md` |
| T13 | `RH_First_Coordinate_and_Single_Point_Energy_Bridge_2026-09-19.md` (largely subsumed by T1) |
| T14 | `RH_Pareto_L2_Approximation_2026-09-18.md` |

### 1. Fixed notation and the common positive defects

Use real sequences anchored at zero, and define
\[
w_k=\frac1{k(k+1)},\quad H=\ell^2(w),\quad g_d(k)=\frac{k\bmod d}{d},\quad
V_N=\operatorname{span}\{g_2,\ldots,g_N\},\quad W=\overline{\bigcup_NV_N}.
\]
Let \(P=P_W\), \(\Pi=I-P\), \(e=\mathbf1_{\{1\}}\),
\[
r=\Pi\mathbf1,\quad E=\|r\|^2,\qquad q=\Pi e,\quad\delta=\|q\|^2.
\]
Here \(E\) and \(\delta\) are squared norms. The symbol \(q\) is a vector and is unrelated to an occupation probability \(q_N\).

Under not RH, the following hold simultaneously, using only the approximation-to-RH direction when deriving necessary conditions:

1. \(W\ne H\), \(\mathbf1\notin W\), \(e\notin W\), \(r\ne0\), \(q\ne0\), \(E>0\), and \(\delta>0\). Finite support interpolation remains possible, so failure occurs only in global energy control.
2. Every finite legal span has a nonzero error. The full projection errors obey
   \[E_N=\|\mathbf1-P_{V_N}\mathbf1\|^2\downarrow E>0.\]
   Strong convergence of the projections still holds: \(P_{V_N}\mathbf1\to P\mathbf1\), and the residuals converge strongly to \(r\).
3. Every \(f\in W\) satisfies
   \[\|\mathbf1-f\|^2=E+\|P\mathbf1-f\|^2\ge E.\]
4. The same defect yields the exact mean-one variance floor
   \[
   \inf_{f\in V,\ \langle1,f\rangle=1}\operatorname{Var}_w(f)
   =\inf_{f\in V,\ \langle1,f\rangle\ne0}
   \frac{\operatorname{Var}_w(f)}{\langle1,f\rangle^2}
   =\frac E{1-E}>0.
   \]
   The infimum of full mean-one energy is \(1/(1-E)\); its closed-space optimizer is \(P\mathbf1/(1-E)\).
5. Unscaled dilation \(D_mf(k)=f(\lfloor k/m\rfloor)\) remains legal on the closure and satisfies \(\|D_mf\|^2=\|f\|^2/m\). Therefore
   \[
   (1-2^{-1/2})^2E\le\delta\le(1+2^{-1/2})^2E,
   \]
   \[
   \frac{r(1)}2=E-\langle r,D_2r\rangle,
   \quad (2-\sqrt2)E\le r(1)\le(2+\sqrt2)E.
   \]
   In particular \(r(1)>0\), and \((P_{V_N}1)(1)\to1-r(1)<1\). This mixed Gram quantity need not be monotone. A zero first-coordinate residual at one finite stage says nothing: it already occurs at modulus two, where the full error is \(1-\log2\).
6. At least one finite-support coefficient Riesz vector fails to belong to \(W\): if all belonged, their totality would give \(W=H\). Totality alone does not prove infinitely many such missing vectors. Cofinally wrong **coefficients**, proved below, are a separate statement.
7. A simple witness gives \(E\le1-\log2\). The rational seven-generator witness in T14 improves this to
   \[0<E\le\frac{6061132763331737}{250000000000000000}<0.0242446.\]
   This upper bound is unconditional; under not RH the defect lies strictly above zero and below this finite numerical ceiling. It does not establish a zero defect.

Sources: T1 §§1–9; T7 §§1–2; T14 §§3–4. The seven-generator certificate is a saved exact rational certificate, not a new numerical computation in this audit.

### 2. Point capacity: all finite improvements exhaust only a finite budget

For \(2\le d,e\le N\), let
\[
G_N(d,e)=\langle g_d,g_e\rangle_H,\quad v_d=1/d,
\quad T_N=G_N-\tfrac12vv^T,
\quad \tau_N=v^TT_N^{-1}v,\quad\kappa_N=v^TG_N^{-1}v.
\]
All finite matrices are positive definite, including the full physical tail matrix \(T_N\). Put
\(\delta_N=\operatorname{dist}(e,V_N)^2\) and
\(\varepsilon_N=\min_{f\in V_N,f(1)=1}\sum_{k\ge2}w_kf(k)^2\).

8. Under not RH,
   \[
   \tau_N\uparrow\tau_\infty=\delta^{-1}-2\in(0,\infty),\quad
   \varepsilon_N\downarrow\varepsilon_\infty=1/\tau_\infty>0,
   \]
   \[
   \kappa_N\uparrow2-4\delta<2,\qquad
   \delta_N=\frac1{\tau_N+2}\downarrow\delta>0.
   \]
9. The constrained full norm tends to a strict floor:
   \[\min_{f\in V_N,f(1)=1}\|f\|^2=\frac1{\kappa_N}=\frac12+\frac1{\tau_N}
   \longrightarrow\frac12+\frac1{\tau_\infty}>\frac12.\]
10. The determinant ratio also has a finite positive limit:
    \[\frac{\det G_N}{\det T_N}=1+\frac{\tau_N}{2}\to\frac1{2\delta},
    \qquad\frac{\det T_N}{2\det G_N}\to\delta>0.\]
11. For any exhaustive sequence of old/new dictionary enlargements, define the actual screened tail source and covariance by
    \[\Sigma=T_A-B^TT_O^{-1}B,\quad s=v_A-B^TT_O^{-1}v_O.\]
    Its nonnegative capacity gain is
    \[\Gamma=s^T\Sigma^{-1}s=\tau_{O\cup A}-\tau_O.\]
    Hence
    \[\sum_j\Gamma_j=\tau_\infty-\tau_{\rm initial}<\infty,\qquad\Gamma_j\to0.\]
    Every signed trial gain \((s_j^Tx_j)^2/(x_j^T\Sigma_jx_j)\) is dominated by \(\Gamma_j\); its sum is finite too. For every \(c>0\), there are arbitrarily large \(j\) with \(\Gamma_j<c/(j+1)\). More strongly, the indices with \(\Gamma_j\ge c/(j+1)\) have finite harmonic mass.
12. In the full-Gram point projection, with screened reciprocal source \(t_j\) and full covariance \(S_j\), the total gain is strictly insufficient:
    \[\sum_jt_j^TS_j^{-1}t_j=2-4\delta-\kappa_{\rm initial}<2-\kappa_{\rm initial}.\]
13. No matrix singularity is required. Positive definiteness, well-defined finite inverse matrices, unique finite least squares, and nonnegative or even strictly positive finite gains are all compatible with this bounded-capacity alternative.

Sources: T1 §§5–6,12–15; T3 §3.

### 3. One canonical tail certificate must satisfy every obstruction simultaneously

Define
\[
z_*=2e-\delta^{-1}q,\qquad h=z_*-2e=-\delta^{-1}q.
\]
Then \(z_*(1)=0\), \(h(1)=-2\), and \(h\in W^\perp\).

14. The canonical finite-energy certificate satisfies every actual residue observation:
    \[\langle z_*,g_d\rangle=1/d\quad(d\ge2),\qquad
    \|z_*\|^2=\tau_\infty,\quad\|h\|^2=\tau_\infty+2=\delta^{-1}.\]
15. It is the unique minimum-norm certificate. Every other real certificate \(z\), with zero first coordinate and the same observations, satisfies
    \[\|z\|^2=\tau_\infty+\|z-z_*\|^2.\]
16. The finite dual representers
    \[z_N=\sum_{d=2}^N(T_N^{-1}v)_d\,g_d|_{k\ge2}\]
    converge strongly to \(z_*\), with exact error
    \[\|z_*-z_N\|^2=\tau_\infty-\tau_N\to0.\]
    For \(M\ge N\), \(\|z_M-z_N\|^2=\tau_M-\tau_N\), so their increments are orthogonal. This convergent family must not be confused with the divergent coefficient-defect reconstruction below.
17. The canonical head-one optimizer exists in the closure:
    \[F_*=e+z_*/\tau_\infty\in W,\quad
    \|F_*\|^2=\tfrac12+1/\tau_\infty.\]
    Finite normalized optimizers converge strongly to it. Both \(P_We\) and \(F_*\) satisfy
    \[\langle F_*,D_mF_*\rangle=0\quad(m\ge2).\]
18. The full canonical annihilator has a nonzero, quantitatively negative mean:
    \[-(2+\sqrt2)\le\langle h,1\rangle\le-(2-\sqrt2)<0.\]
    Equivalently \(\langle z_*,1\rangle\in[-1-\sqrt2,-1+\sqrt2]\). The negative interval applies to \(h\), not to arbitrary annihilators or to \(z_*\) itself.
19. Put
    \[A_n=\sum_{k\ge n}w_kz_*(k),\qquad Z(n)=\sum_{k=2}^nz_*(k).\]
    Then
    \[A\in\ell^2\setminus\ell^1,\quad
    \sum_{n\ge1}|A_n|^2\le4\tau_\infty,\quad\sqrt n\,A_n\to0,\]
    \[\sum_{n\ge1}n(n+1)|A_n-A_{n+1}|^2=\tau_\infty.\]
    Each individual signed primitive exists absolutely in its defining weighted tail, since \(\sum_kw_k|z_*(k)|<\infty\). Nonsummability concerns the further sum over starting points \(n\).
20. Canonical structure improves the constant independently of the defect:
    \[|A_n|\le\frac1{(1-2^{-1/2})\sqrt n}\quad(n\ge2).\]
    The stronger little-o statement above still holds for this fixed certificate. Neither is an \(\ell^1\) estimate.
21. With \(B_j=\sum_{2^j\le n<2^{j+1}}|A_n|\),
    \[\sum_jB_j=\infty,\qquad\sum_j2^{-j}B_j^2\le4\tau_\infty.\]
    Thus every summable proposed dyadic-block upper envelope must fail; for example \(B_j\le C(j+1)^{-1-\eta}\) cannot hold eventually for any \(\eta>0\).
22. Both signs occur arbitrarily far out, and more strongly
    \[\sum_{n\ge2}\frac{z_*^+(n)}{n+1}=\sum_{n\ge2}\frac{z_*^-(n)}{n+1}=\infty.\]
    The same two divergent first moments hold for every nonzero real annihilator in \(W^\perp\). An eventual one-sign property is impossible. Ordinary weighted mass remains absolutely summable, so these are first-moment divergences, not failure of \(H\)-membership.
23. The additive cancellation obstruction is
    \[\sum_{n\ge2}\frac{|Z(n)|}{n^2}=\infty.\]
    In exact quantifiers, for every \(\eta>0,C>0,N_0\), some \(n\ge N_0\) has
    \[|Z(n)|>Cn^{1-\eta},\]
    and some (possibly different) \(n\ge N_0\) has
    \[|Z(n)|>\frac{Cn}{(\log(2n))^{1+\eta}}.\]
    These are cofinal excursions, not lower bounds at every index and not a claim of one-sided growth. The Hilbert estimate \(Z(n)=O(n^{3/2})\) remains valid (indeed fixed-vector truncation improves it to \(o(n^{3/2})\)).
24. A quantitative version uses \(A^h_n=\sum_{k\ge n}w_kh(k)\), \(L_N=\sum_{n\le N}|A^h_n|\), \(H_0=\delta^{-1/2}\), and
    \[y=\left\lfloor\frac{\log N}{4\log2}\right\rfloor\ge2.\]
    Then
    \[L_N-L_y\ge\frac12-\frac{L_N}{4\log(y+1)}-H_0N^{-1/4}.\]
    If also \(N\ge(8H_0)^4\), either \(L_N\ge\tfrac12\log(y+1)\), or \(L_N\ge L_y+\tfrac14\). Since \(A^h\) and \(A\) differ only at site one, this is the same nonsummability obstruction up to a bounded additive discrepancy.
25. Every right-half-plane zero \(\rho\), with every derivative order \(j<\operatorname{mult}(\rho)\), constrains this same certificate:
    \[(\mathcal Mz_*)^{(j)}(\rho)=-\tau_\infty(\mathcal Me)^{(j)}(\rho),
    \qquad\mathcal Me(s)=\frac{1-2^{-s}}s.\]
    These simultaneous restrictions include all hypothetical zeros and multiplicities; they are not independent certificates chosen for different zeros.
26. For a finite conjugation-closed observation list \(i=(\rho,j)\), set
    \[\alpha_i(k)=\left.\partial_s^j\frac{k^{-s}-(k+1)^{-s}}s\right|_{s=\rho},\quad
    a_i=\alpha_i(1),\quad B_{i\ell}=\sum_{k\ge2}\frac{\alpha_i(k)\overline{\alpha_\ell(k)}}{w_k},\quad t=a^*B^\dagger a.\]
    A value evaluation ensures \(t>0\), and
    \[\tau_N\le\tau_\infty\le1/t,\qquad\delta_N\ge\frac{t}{1+2t}.\]
    All correlations matter. Yet every finite such list satisfies \(t\le\log2-\tfrac12\), because \(2g_2\) is an actual feasible head-one vector. Merely adding zero constraints cannot make these costs diverge.

Sources: T1 §§15,25–26; T2 §§23; T3 §§3–8; T7 §3; T8 §§1–8. Correction: a nonzero overlap with an off-line-zero mode does not establish a pointwise power-law asymptotic for the canonical primitive. Only the stated bounds and nonsummability are warranted.

### 4. The sieve boundary and noncommuting limits must survive

27. The certificate equations give, for each fixed \(d\ge2\),
    \[\lim_{M\to\infty}\left(\sum_{n\le dM}A_n-d\sum_{j\le M}A_{dj}\right)=1.\]
    Neither series need converge separately. A fixed-modulus limit cannot be upgraded to simultaneous modulus growth without an additional estimate.
28. Define for \(t>0\)
    \[S(t)=\sum_nA_ne^{-nt},\quad H_d(t)=\sum_n(1-d\mathbf1_{d\mid n})A_ne^{-nt}.\]
    All these Abel sums converge absolutely, and \(H_d(t)\to1\) for each fixed \(d\). For \(P_y=\prod_{p\le y}p\), \(c_y=\prod_{p\le y}(1-1/p)\), and \(m\ge2\), put
    \[K_{m,y}(t)=\sum_{(k,P_y)=1}A_{mk}e^{-mkt}-\frac{c_y}{m}S(t).\]
    The exact signed identity is
    \[K_{m,y}(t)=-\frac1m\sum_{d\mid P_y}\frac{\mu(d)}dH_{md}(t).\]
29. The two iterated limits are
    \[\lim_{y\to\infty}\lim_{t\downarrow0}K_{m,y}(t)=0,
    \qquad\lim_{t\downarrow0}\lim_{y\to\infty}K_{m,y}(t)=A_m.\]
    Some \(m\ge2\) necessarily has \(A_m\ne0\). Thus noncommutation is forced for at least one coordinate of the actual canonical certificate. Quantitatively,
    \[\liminf_{t\downarrow0}\sup_y|K_{m,y}(t)+c_y/m|\ge|A_m|.\]
30. The easy estimates cannot yield a diagonal passage: for \(0<t\le1\),
    \[|K_{m,y}(t)+c_y/m|\le(1+\sqrt\pi)\|z_*\|\,2^{\pi(y)}\sqrt t,
    \quad |S(t)|\le\frac{\|A\|_2}{\sqrt{e^{2t}-1}}.\]
    The competing majorants require both \(2^{\pi(y)}\sqrt t\) and \(c_y/\sqrt t\) small, but their product \(2^{\pi(y)}c_y\ge1\). This defeats those majorants, not every possible signed arithmetic estimate.
31. An alternative exact boundary formulation uses
    \[S_{n,y}(k)=\sum_{d\mid P_y}\mu(d)g_{nd}(k)=\frac{c_yk}{n}-R_y(\lfloor k/n\rfloor),\]
    where \(R_y(t)=\#\{j\le t:(j,P_y)=1\}\). For \(n\le K\le ny\), put \(m_K(k)=\min(k,K)\) and
    \[\mathscr R_{n,y,K}(k)=\mathbf1_{k>K}(S_{n,y}(k)-S_{n,y}(K)).\]
    Then every annihilator satisfies
    \[\sum_{k\ge n}w_kh(k)=\frac{c_y}{n}\langle h,m_K\rangle+\langle h,\mathscr R_{n,y,K}\rangle.\]
32. For the canonical \(h\), take \(n=1,K_y=\lfloor\log y\rfloor\). Then the ramp term tends to zero and the boundary pairing has the fixed nonzero limit
    \[\langle h,\mathscr R_{1,y,K_y}\rangle\longrightarrow\langle h,1\rangle
    \in[-(2+\sqrt2),-(2-\sqrt2)].\]
    Meanwhile \(\|\mathscr R_{1,y,K_y}\|^2\ge c_y^2y/16\to\infty\), even though its support escapes and its normalization converges weakly to zero. An elementary lower bound \(c_y\ge c y^{-4/15}\) gives growth at least \(c' y^{7/15}\). Thus tail smallness of \(h\) does not alone remove this pairing.

Sources: T7 §7; T1 §27; T2 §§24–25. These are necessities of the nonzero-defect alternative, not asserted contradictions.

### 5. Every growing exact-head repair must have divergent full error

Let \(t_N=\sum_{k>N}w_k|r(k)|^2\). Let \(\Delta_{N,L}\) be the **squared** minimum error among finite legal vectors supported in residue moduli through \(L+1\), with \(F(k)=1\) for \(k\le N\), where \(L\ge N\). Let \(\Delta_N=\inf_{L\ge N}\Delta_{N,L}\).

33. Under not RH, \(t_N>0\) at every finite \(N\), \(t_N\downarrow0\), and every legal exact-head vector has
    \[E^2\le t_N\|F-1\|^2.\]
    More exactly, with \(Q_N\) deleting the head and \(u=F-1+(E/t_N)Q_Nr\),
    \[\langle u,Q_Nr\rangle=0,\qquad t_N\|F-1\|^2=E^2+t_N\|u\|^2.\]
34. Consequently
    \[\Delta_{N,L}\ge\Delta_N\ge E^2/t_N\to\infty\]
    uniformly in every finite budget choice, including arbitrarily fast conductor enlargement. Growing exact heads cannot have even a bounded cofinal family of full errors.
35. The elementary Möbius telescope yields an unconditional upper estimate, so under not RH
    \[\frac{E^2}{t_N}\le\Delta_{N,L}\le4N+\frac1{N+1}.\]
    In particular
    \[t_N\ge\frac{E^2}{4N+1/(N+1)},\qquad\liminf_{N\to\infty}Nt_N\ge E^2/4.\]
    Thus the actual canonical residual tail cannot decay as \(o(1/N)\).
36. For every hypothetical right zero \(\rho=\beta+i\gamma\), \(1/2<\beta<1\), there is the budget-independent lower bound
    \[\Delta_{N,L}\ge\frac{2\beta-1}{|\rho|^2}(N+1)^{2\beta-1}.\]
    More sharply, with \(\alpha_\rho(k)=(k^{-\rho}-(k+1)^{-\rho})/\rho\),
    \[\Delta_{N,L}\ge\frac1{|\rho|^2\sum_{k>N}|\alpha_\rho(k)|^2/w_k}.\]
37. Multiple zeros yield simultaneous full Gram lower bounds, not a sum of separate scalar bounds. For distinct right zeros, with \(a=(N+1)^{-1}\),
    \[\mathcal G_N(i,j)=\frac{a^{\rho_i+\bar\rho_j-1}}{\rho_i+\bar\rho_j-1},\quad v_i=1/\rho_i,
    \qquad\Delta_{N,L}\ge v^*\mathcal G_N^{-1}v.\]
38. The unrestricted optimum is explicitly
    \[\Delta_N=\langle r,\mathcal T_N^{-1}r\rangle,\quad
    \mathcal T_N=\Pi Q_N|_{W^\perp},\quad t_N=\langle r,\mathcal T_Nr\rangle.\]
    Each fixed \(\mathcal T_N\) is positive and invertible; finite-head interpolation excludes a finitely supported annihilator. Increasing the budget approaches this optimum and does not remove it. Its minimum-norm error is \(-Q_N\mathcal T_N^{-1}r\).
39. For every prescribed budget schedule \(L(N)\ge N\),
    \[\liminf_N t_N\Delta_{N,L(N)}\ge E^2>0.\]
    The opposite zero-liminf assertion is equivalent to \(E=0\), not a weak automatic consequence of \(t_N\to0\).
40. Every cofinal subpower bound for these errors fails. Precisely, choose any right zero and \(0<p<2\beta-1\); then for every \(B\in\mathbb R\), eventually
    \[B(N+1)^p<\Delta_{N,L}\quad\text{for all }L\ge N.\]
    No fixed prescribed finite budget, nor the unrestricted infimum, can evade this conclusion.
41. The analogous full exact-head energy \(\mathfrak A_N=\inf\|F\|^2\), allowing all finite legal witnesses (and the two-seed subclass), obeys the sharper phase-sensitive inequality
    \[\mathfrak A_N\ge\frac N{N+1}+\frac{2\beta-1}{|\rho|^2}(N+1)^{2\beta-1}|1-(N+1)^{-\rho}|^2.\]
    For \(N\ge3\), it is at least \((2\beta-1)(N+1)^{2\beta-1}/(4|\rho|^2)\), hence diverges.
42. Multiplicity \(m\) strengthens this head-energy bound. Put \(T=N+1\),
    \[P_j(\ell)=\sum_{a=0}^j\binom ja\ell^{j-a}\frac{(-1)^aa!}{\rho^{a+1}},\quad
    H_j(T)=P_j(\log T)-\frac{(-1)^jj!T^{-\rho}}{\rho^{j+1}}.\]
    For \(0\le j<m\),
    \[\mathfrak A_N\ge\frac N{N+1}+\frac{(2\beta-1)^{2j+1}}{(2j)!}T^{2\beta-1}|H_j(T)|^2.\]
    Thus eventually \(\mathfrak A_N\ge c_{\rho,m}N^{2\beta-1}(\log N)^{2m-2}\).

Sources: T9 §6; T10 §§2–6; T4 §6. The phase factor belongs to full **head energy**; the simpler nonoscillatory bound belongs to **error energy**. Those are different quantities.

### 6. Tail covariance, sparse means, and Schur regression

For any exact-head packet \(F\), let \(K\) have probabilities \(w_k\), \(L=\mathbb E F(K)\), and \(v=\operatorname{Var}(F(K)\mid K>N)\). Then exactly
\[\|1-F\|^2=(N+1)(L-1)^2+\frac v{N+1}.\]

43. Under not RH this nonnegative sum is at least both \(E^2/t_N\) and \((2\beta-1)(N+1)^{2\beta-1}/|\rho|^2\). In particular both desired limits
    \[L-1=o((N+1)^{-1/2}),\qquad v=o(N+1)\]
    cannot hold together for any legal family. For arbitrary packets one must not claim covariance alone diverges: the mean term may carry the obstruction.
44. For the actual error-minimizing balanced-generator Schur packets \(F_{N,M}\), \(M\ge N+1\), put \(C_{N,M}=v/(N+1)\). The first available tail normal equation yields
    \[C_{N,M}\le\|1-F_{N,M}\|^2\le\frac2{\log3}C_{N,M}.\]
    Hence under not RH, uniformly for every allowed budget,
    \[C_{N,M}\ge\frac{\log3}{2}\frac{E^2}{t_N},\]
    \[C_{N,M}\ge\frac{(2\beta-1)\log3}{2|\rho|^2}(N+1)^{2\beta-1}\to\infty.\]
    The unscaled conditional variance grows at least like \((N+1)^{2\beta}\). Even a bounded cofinal covariance-energy selection is impossible.
45. For those minimizers the mean contribution remains controlled by covariance:
    \[(N+1)(L-1)^2\le(2/\log3-1)C_{N,M}.\]
    This is an upper comparison, not a lower bound for the mean mismatch. Exact or very accurate mean matching is compatible with the failure of RH; it cannot dispose of mixed-conductor covariance.
46. In finite Ramanujan packets \(F=\sum_qH_qB_q\), \(B_q=\sum_{d\mid q}\mu(q/d)(k\bmod d)\), the mean remains
    \[L=\sum_qH_q\Lambda(q)=\log2\sum_aH_{2^a}+\log3\sum_bH_{3^b}\]
    for the two-seed conductor class. All mixed conductors still enter the full covariance. The sparsity of \(\Lambda\) cannot imply covariance exhaustion.
47. For fixed head \(N\), successive tail regressions retain the exact gain identity
    \[\Delta_{N,M}=\|1-I_N\|^2-\sum_{j=N+1}^M\frac{|\langle1-F_{N,j-1},u_j\rangle|^2}{\|u_j\|^2}.\]
    Under not RH, the total sum falls short of initial error by \(\Delta_N>0\), and \(\Delta_N\to\infty\) as the head grows. Positive pivots, unique regression, and increasing budget do not force exhaustion.
48. The exact physical tail is a positive weighted finite-period sum
    \[\|1-F\|^2=\sum_{t=N+1}^{N+P}W_P(t)(1-F(t))^2,\quad
    \sum_{t=N+1}^{N+P}W_P(t)=1/(N+1).\]
    Under not RH, shrinking total tail mass therefore accompanies growing average squared error on that tail; it does not produce norm convergence.
49. For divisor charges \(D(m)=F(m)-F(m-1)\), the valid finite Green identity retains the boundary:
    \[\sum_{k=N+1}^Lw_k(1-F(k))^2
    =\sum_{m,n=N+1}^L\frac{D(m)D(n)}{\max(m,n)}-\frac{(1-F(L))^2}{L+1}.\]
    For each fixed packet, its periodic nonzero charge has \(\sum_{m>N}D(m)^2/m=\infty\), although the full signed error is finite. Thus diagonal and off-diagonal contributions cannot be split into separately convergent infinite sums. This is unconditional, and must not be listed as a special failure caused by not RH.

Sources: T11 §§1–12.

### 7. Stabilized coefficients must deviate forever, and their reconstruction escapes

For any \(f\in H\), define continuous Möbius coordinates
\[c_d(f)=-\sum_{j\mid d}\mu(d/j)(f(j)-f(j-1)),\quad d\ge2.\]
Let \(c_{\infty,d}=c_d(P1)\), \(b_d=-\mu(d)-c_{\infty,d}=c_d(r)\),
\[R_N=\sum_{d=2}^Nb_dg_d,\quad Q_N=\|R_N\|^2.\]

50. Every fixed finite projection coefficient still stabilizes unconditionally, but under not RH,
    \[\forall N\ \exists d>\max(N,1):c_{\infty,d}\ne-\mu(d).\]
    Infinitely many distinct moduli must retain a defect. This does not mean every modulus is wrong.
51. The ordered reconstruction diverges in the strong quantitative sense
    \[Q_N\to\infty.\]
    It has no bounded cofinal subsequence, no weakly convergent subsequence along cofinal indices, no ordinary ordered norm sum, and no unconditionally convergent sum. In contrast, the actual finite projections themselves converge strongly and remain bounded.
52. Its absolute coefficient norm must diverge:
    \[\sum_{d\ge2}|b_d|\|g_d\|=\infty,\qquad
    \sum_{d\ge2}\frac{|b_d|}{\sqrt d}=\infty.\]
53. Finite reconstruction has an exact slope discrepancy, not an exact head:
    \[R_N(k)-r(k)=k\lambda_N\quad(k\le N),\quad
    \lambda_N=\sum_{d=2}^Nb_d/d-r(1).\]
    Thus coefficient stabilization cannot be substituted for physical head equality.
54. Let
    \[L_N=N+1-H_{N+1},\quad J_N=\sum_{k\le N}\frac{r(k)}{k+1},\quad
    \eta_N^2=t_N+J_N^2/L_N.\]
    Then \(\eta_N\to0\) while
    \[E^2\le(E+Q_N)\eta_N^2,\quad Q_N\ge E^2/\eta_N^2-E.\]
    This denominator is the actual dual-coordinate projection error; its vanishing forces primal energy escape when the residual is nonzero.
55. A stronger residual-tail coupling is
    \[(Q_N+E)t_N\ge E^2\frac{L_N}{L_N+N+1},\qquad
    \liminf_NQ_Nt_N\ge E^2/2.\]
56. Every right zero \(\rho=\beta+i\gamma\) forces the explicit asymptotic bound
    \[\liminf_N\frac{Q_N}{(N+1)^{2\beta-1}}
    \ge\frac{(2\beta-1)|1-\rho|^2}{|\rho|^4}>0.\]
    The exact finite denominator is
    \[Q_N+E\ge\frac1{|\rho|^2D_N(\rho)},\quad
    D_N=\sum_{k>N}\frac{|\alpha_\rho(k)|^2}{w_k}
       +\frac{|\sum_{k\le N}k\alpha_\rho(k)|^2}{L_N}.\]
    It has asymptotic
    \[D_N=(N+1)^{1-2\beta}\left((2\beta-1)^{-1}+|1-\rho|^{-2}+o(1)\right).\]
    The rank-one head term is necessary because of the slope discrepancy.
57. If the zero has multiplicity \(m\), then eventually
    \[Q_N\ge c_{\rho,m}N^{2\beta-1}(\log N)^{2m-2},\]
    \[\sum_{d=2}^N\frac{|b_d|}{\sqrt d}\ge c'_{\rho,m}N^{\beta-1/2}(\log N)^{m-1}.\]
    An all-\(N\) version for \(j<m\) is
    \[Q_N+E\ge\frac{(N+1)^{2\beta-1}|P_j(\log(N+1))|^2}{C_{\beta,j}},\]
    \[C_{\beta,j}=\frac{(2j)!}{(2\beta-1)^{2j+1}}+\frac{4(j!)^2}{(1-\beta)^{2j+2}}.\]
58. Full simultaneous zero/derivative constraints give
    \[Q_N+E\ge u^*C_N^\dagger u,\quad u_i=(-1)^{j_i}j_i!/\rho_i^{j_i+1},\]
    where
    \[C_N(i,\ell)=\sum_{k>N}\frac{\alpha_i(k)\overline{\alpha_\ell(k)}}{w_k}
     +\frac{(\sum_{k\le N}k\alpha_i(k))\overline{(\sum_{k\le N}k\alpha_\ell(k))}}{L_N}.\]
    This keeps all correlations and the permitted head slope.
59. The best saved unconditional raw upper bound remains compatible with those lower bounds:
    \[Q_N\le K_NE,\quad K_N=N(4+2\sqrt{S_N})^2,\]
    \[S_N=\frac{H_N^2+H_N^{(2)}}2+2H_N-3,\qquad Q_N=o(N\log^2N).\]
    This supersedes the older \(o(N\log^3N)\) and \(o(N^2)\) statements.
60. With \((Cf)(t)=t^{-1}\sum_{k\le t}f(k)\), \(q_t=2/[(t+1)(t+2)]\), set \(A_N^{\rm sm}=\|CR_N\|_{\ell^2(q)}^2\). The best saved upper bounds are
    \[A_N^{\rm sm}\le484NE,\qquad A_N^{\rm sm}=o(N).\]
    Yet every right zero gives, eventually,
    \[A_N^{\rm sm}\ge\frac1{4C_\rho^2}N^{2\beta-1},\quad
    C_\rho=\sqrt3|\rho(\rho+1)|\left((1-\beta)^{-1}+(2\beta-1)^{-1/2}\right).\]
    Thus smoothing still leaves divergence under not RH. A fixed exponent strictly below one is compatible with \(o(N)\).
61. The cofinal subpower criterion necessarily fails for both actual raw and smoothed reconstructions. For raw energy,
    \[\liminf_N\frac{\log(1+Q_N)}{\log N}\ge2\beta-1>0\]
    for every right zero. Taking the supremum of their real parts strengthens the right side to \(2\sup\Re\rho-1\). It is not legitimate to replace this by a known absolute positive exponent independent of the hypothetical zeros.
62. Normalize \(U_N=R_N/\sqrt{Q_N}\) for sufficiently large \(N\). Then
    \[\|U_N\|=1,\quad U_N\rightharpoonup0,\]
    \[\sum_{k\le K}w_k|U_N(k)|^2\to0,\qquad
    \sum_{k>K}w_k|U_N(k)|^2\to1\quad\text{for every fixed }K.\]
    All normalized energy escapes every finite physical head. The energies \(|U_N|^2\) are not uniformly integrable under the Pareto probability measure, even along any cofinal subsequence.
63. The exact CRT/Ramanujan rewrite of \(Q_N\) is unchanged:
    \[Q_N=b^TG_Nb=\sum_{a=1}^{L}W_L(a)\left(\sum_{d=2}^Nb_d\frac{a\bmod d}{d}\right)^2.\]
    Under not RH this actual positive weighted energy diverges. A finite coordinate change, Haar orthogonality of jumps, or the uniform Green operator bound \(\|[1/\max(i,j)]\|\le4\) does not make it small. The jump sequence is periodic and is not in unweighted \(\ell^2\), so the naive infinite Hardy upper estimate is infinite.
64. Profinite compactness does not contradict this escape. The actual energy measure is the atomic Pareto measure \(\nu=\sum_kw_k\delta_k\), not additive Haar. Every normalized \(|U_N|^2\nu\) is a probability measure and has profinite weak-star cluster points; weak limits of functions and measures need not preserve the original Hilbert profile. It is not justified to assert every such cluster measure is singular from finite-site escape alone.
65. Extend \(b_1=-r(1)\), put \(a_n=\Delta r(n)\). The defect Dirichlet series, initially absolutely convergent for \(\Re s>3/2\), satisfies
    \[\sum_{n\ge1}b_nn^{-s}=-\frac{s\mathcal Mr(s)}{\zeta(s)}.\]
    At every right zero \(\rho\) of multiplicity \(m\), \(s\mathcal Mr(s)=1+O((s-\rho)^m)\). Therefore its meromorphic continuation has the **same principal part as** \(-1/\zeta(s)\), with an uncancelled pole of order \(m\). The exact signed von Mangoldt convolution remains valid and does not erase the pole.

Sources: T3 §5; T4 §§2–10; T5 §§3–11; T6 §§1–8. The raw/smoothed upper estimates are for the fixed actual residual; uniform subpower bounds for reconstruction operators on all inputs are already false for elementary reasons.

### 8. Every proposed nonsummable gain provider must fail

66. For any increasing legal projection walk \(W_n\), starting at \(\{0\}\), write \(d_n=\operatorname{dist}(1,W_n)^2\), \(\gamma_n=(d_n-d_{n+1})/d_n\). Then under not RH
    \[\sum_n-\log(1-\gamma_n)\le\log(1/E),\qquad
    \sum_n\gamma_n\le\log(1/E)<\infty.\]
    Equality in the logarithmic identity holds for a walk exhausting \(W\). Hence \(\gamma_n\to0\); infinitely many uniformly positive fractional contractions are impossible.
67. In the two-seed dyadic spaces, let \(d_j=D_{2^j}\), and let a screened legal trial have gain \(q_j=(h_j^Tx_j)^2/(x_j^TS_jx_j)\), with null trials assigned zero. Then
    \[\sum_jq_j/d_j<\infty.\]
    For every \(C>0\), the good set
    \[\mathcal G_C=\{j:q_j/d_j\ge1/[C(j+1)]\}\]
    has finite harmonic mass \(\sum_{j\in\mathcal G_C}1/(j+1)<\infty\), hence natural density zero. This also holds for the optimal full gain \(q_j=d_j-d_{j+1}\).
68. A correlation-normalized legal witness with \(\langle e_j,w_j\rangle=d_j\) and \(\|w_j\|^2\le Cd_j(j+1)\) can therefore occur only on a set of finite harmonic mass. Merely infinitely many good scales remains compatible with not RH. Any such good set of divergent harmonic mass would contradict it.
69. When the enlargement splits into transported old directions and a fresh coprime-to-six CRT block,
    \[D_M-D_{2M}=\Delta_{U,M}+z_M^TK_M^{-1}z_M,\]
    the sum of normalized transported-plus-fresh trial gains is finite under not RH. The source must be screened against the entire transported space; replacing it by unscreened means invalidates the conclusion.
70. For first-coordinate normalized optimizers on \(N_j=m^jN_0\), put \(\epsilon_j=1/\tau_{N_j}\), \(u_j=F_j-F_{j+1}\), \(\Delta_j=\epsilon_j-\epsilon_{j+1}\), \(c_j=\langle F_j,D_mF_j\rangle\). Then
    \[c_j=-\langle u_j,D_mu_{j-1}\rangle,\quad |c_j|^2\le\Delta_{j-1}\Delta_j/m.\]
    Under not RH \(\epsilon_j\to\epsilon_\infty>0\), and every stronger proposed lower-gain series must converge, in particular
    \[\sum_j\frac{m c_j^2}{\epsilon_j^2\Delta_{j-1}}<\infty\]
    with zero conventions when denominators vanish. The fully screened quantities \(c_j^2/(\epsilon_j^2\lambda_j)\) also have finite sum, where \(\lambda_j=\|(I-P_{U_j})D_mF_j\|^2\).
71. For jointly screened trial blocks with source \(d_j\), Gram \(H_j\), and energy gain \(\Lambda_j=d_j^TH_j^\dagger d_j\), the capacity-gain lower bounds satisfy
    \[\sum_j\frac{\Lambda_j}{\epsilon_j(\epsilon_j-\Lambda_j)}<\infty.\]
    This excludes every valid provider asserting divergence of that exact signed series.
72. A positive angle alone is insufficient. Even maximal alignment is compatible with a positive limiting \(\epsilon_\infty\), because \(\sum_j\Delta_j/\epsilon_j^2<\infty\). What fails is the divergent **absolute gain** assertion, not necessarily every local alignment lower bound.
73. For any operator \(T\) fixing \(1\), preserving means, and contracting mean-zero vectors by \(\kappa<1\), every legal mean-one orbit must have recurrent repair cost
    \[\limsup_n\|F_{n+1}-TF_n\|\ge(1-\kappa)\sqrt{E/(1-E)}.\]
    For the project’s Gibbs contraction, \(\kappa=\pi/4\). Thus asymptotically exact legal repair of that contractive orbit is impossible under not RH. This statement retains the stated contraction hypotheses.

Sources: T7 §2; T12 §§1–5; T2 §§27–29; T1 §29.

### 9. Facts that must not be misreported as special consequences of not RH

74. The natural fixed-coefficient Möbius telescope already fails in the original and conditional-Cesàro norms because of critical-line zeros. Its failure persists even if RH is true. Under not RH the exact-head lower bounds additionally force its full error to diverge.
75. The corrected telescope directions satisfy \(\|Ch_j\|^2\asymp1/j\), with saved constants \(1/(45j)\le\|Ch_j\|^2\le60/j\). Their weighted increment series can be square summable while not convergent. Square-summable increments, pointwise convergence, and exact growing heads do not constitute norm convergence.
76. The primorial point approximants can have every fixed coefficient converge correctly and every physical coordinate converge to the point target, while tail energy diverges. A one-atom primorial exact-head repair has error at least \(c_y^3(y+1)/64\to\infty\), independently of RH. This defeats the specified witness, not the optimized legal infimum.
77. Omitting one prime modulus \(p\) (in the stated prime-omission argument, \(p\ge3\) so both tested coordinates lie in the tail) creates an unconditional barrier \(\tau\le2p^2\), \(\delta\ge1/[2(p^2+1)]\). Restricted-dictionary failure is not itself evidence of not RH.
78. Burnol’s logarithmic finite-approximation lower bound and the resulting point-error logarithmic barrier are unconditional. A fixed fractional error improvement at every modulus doubling is therefore an invalid target even if RH is true. Slower nonsummable gains remain the relevant issue.
79. The \(1/\epsilon\) critical Chebyshev-energy blowup from critical-line zeros is also unconditional. Not RH adds **infinite** energy at positive damping exponents at or below the rightmost relevant zero; absence of a uniform zero-damping bound alone does not distinguish RH from its negation.
80. No reviewed tail/capacity identity clashes with not RH. A hypothetical actual off-line zero explicitly constructs a nonzero finite-energy annihilator and a feasible tail certificate. The canonical minimizer then exists by Hilbert projection. General minimum norm, all dilation orthogonality equations, finite signed Gram positivity, CRT uniqueness, compactness, and fixed-coordinate stabilization do not eliminate that alternative.

Sources: T9; T1 §§18–19,28; T2 §§26–29; T12 §6; T3 §8; T10 §§4,7.

### 10. Audit cautions and strongest combined conclusion

- Do not conflate the constant projection error \(E_N\), point error \(\delta_N\), point-tail energy \(\varepsilon_N\), exact-head error \(\Delta_{N,L}\), full head energy \(\mathfrak A_N\), coefficient reconstruction energy \(Q_N\), or smoothed reconstruction energy \(A_N^{\rm sm}\). Under not RH some converge to positive finite limits, some remain bounded capacities, and others diverge.
- Do not say every atom, coefficient, covariance, or boundary term must individually fail. The necessary statements concern specified sums, common canonical objects, cofinal quantifiers, or actual minimizers.
- Do not interpret a constrained witness’s unconditional failure as the failure of the unrestricted RH criterion.
- The source descriptions of two-seed spaces allow every positive integer dilation of seeds 2 and 3. Restricting moduli to the semigroup \(2^a3^b\) would change the statements.
- The source-wide “all Riesz vectors iff density” gives at least one missing Riesz vector under not RH; it does not directly give infinitely many missing Riesz vectors. The infinitely many wrong stabilized coefficient statement is independently proved.

The strongest combined tail conclusion is that not RH forces one coherent positive-defect geometry: a bounded tail capacity and strongly convergent canonical dual representers; a finite-energy, sign-changing canonical certificate whose signed primitive is square summable but never absolutely summable; persistent noncommuting sieve/Abel limits and a nonzero canonical boundary correlation; uniformly diverging exact-head repair costs at every budget; and actual stabilized-defect reconstructions growing at a positive zero-dependent power, with multiplicity logarithms, while their normalized energies escape every finite physical head. The proved upper estimates remain compatible with these lower estimates. None of the reviewed arguments proves that this simultaneous alternative is impossible.


## Part II. DPP, occupation, Fredholm determinants, and profinite limits

### Normalization, avoiding three different q's

Set \(w_n=1/[n(n+1)]\), \(H=\ell^2(\mathbb N_{\ge1},w)\), \(g_d(n)=(n\bmod d)/d\), \(S_N=\operatorname{span}\{g_2,\dots,g_{N+1}\}\), \(S=\overline{\bigcup_NS_N}\). Let \(P_N,P\) be the projections. In counting coordinates \(Uf(n)=\sqrt{w_n}f(n)\), set \(Q_N=UP_NU^{-1}\), \(Q=UPU^{-1}\), and \(R=I-Q\). Let \(\Xi_N,\Xi_\infty\) be their DPPs.

Use \(p_N=Q_N(1,1)\), \(\nu_N=1-p_N\), and \(p=Q(1,1)\), \(\nu=1-p\). Reserve \(q_N\) for the finite changing-residue-class inclusion probability, \(q_N=2W_{L_N}(1)p_N\), where \(L_N=\operatorname{lcm}(2,\dots,N+1)\). Its limit is \(q_*=p\). Reserve \(C_N\) for the full signed tail capacity, historically also called q or modified q in some chats. In particular a probability does not diverge to infinity.

The exact residue-class masses are
\[
 W_L(r)=\sum_{k\ge0}\frac1{(r+kL)(r+kL+1)}
 =\frac{\psi((r+1)/L)-\psi(r/L)}L,
 \qquad 1\le r\le L,
\]
where ψ denotes the digamma function, not the Chebyshev prime-counting function. If ψ_1 is trigamma, there is a uniquely determined intermediate point \(\alpha_{r,L}\in(r/L,(r+1)/L)\) with
\[
 \psi_1(\alpha_{r,L})=\int_0^1\psi_1((r+t)/L)\,dt,
 \qquad W_L(r)=L^{-2}\psi_1(\alpha_{r,L}).
\]
Consequently \(q_N=W_{L_N}(1)b_N^*G_N^{-1}b_N\). The intermediate-point identity itself does not imply monotonicity of the entire changing inverse-matrix expression.

For Gram matrices \(G_N=\sum_{n\ge1}w_nv_N(n)v_N(n)^*\), \(b_N=(1/d)_{d=2}^{N+1}\), and \(T_N=G_N-\tfrac12b_Nb_N^*\), write \(C_N=b_N^*T_N^{-1}b_N\). Let \(e=\delta_1\), whose norm squared is \(1/2\). For the constant target distinguish \(r^{\rm c}=(I-P)\mathbf1\), \(D=\|r^{\rm c}\|^2\) from the point residual \(r^{\rm p}=(I-P)e\), whose squared norm is \(\nu/2\).

Every consequence below is conditional on NOT RH. The persistent background statements near the end hold regardless of RH and therefore must not be listed as things that fail.

### A. Projection, Gram basis, coefficient, and capacity endpoints

1. \(S\ne H\), \(P\ne I\), \(Q\ne I\), and the hole projection \(R\ne0\). The residue orthonormal sequence remains a complete orthonormal basis of S, but not of H. There is a nonzero orthogonal complement.
2. The constant is not in S; its Gram–Schmidt series reconstructs \(P\mathbf1\), not \(\mathbf1\). If \(\alpha_j=\langle\mathbf1,e_j\rangle\), then \(\sum_{j\ge2}|\alpha_j|^2=1-D<1\), \(D>0\), and \(\|\mathbf1-P_N\mathbf1\|^2\downarrow D\).
3. With \(m_N=(\log d/d)\), \(m_N^*G_N^{-1}m_N\uparrow1-D<1\). The augmented Gram determinant ratio \(\det\begin{psmallmatrix}G_N&m_N\\m_N^*&1\end{psmallmatrix}/\det G_N\downarrow D>0\).
4. The constant residual has a strictly positive first coordinate. In fact \((2-\sqrt2)D\le r^{\rm c}(1)\le(2+\sqrt2)D\), obtained using the unscaled dilation \((D_2f)(n)=f(\lfloor n/2\rfloor)\), f(0)=0, from \(r^{\rm c}(1)=2D-2\langle r^{\rm c},D_2r^{\rm c}\rangle\), \(\|D_2r^{\rm c}\|^2=D/2\). Thus \(b_N^*G_N^{-1}m_N\to(P\mathbf1)(1)=1-r^{\rm c}(1)<1\).
5. Stabilized coefficients still exist and their orthonormal-coordinate sums converge absolutely. But at least one d has \(c_{\infty,d}\ne-\mu(d)\). Equivalently the exact Möbius defect \(\sum_{k\mid d}\mu(d/k)[r^{\rm c}(k)-r^{\rm c}(k-1)]\) is nonzero for some d. This does not say that every coefficient differs or that stabilization fails.
6. \(e\notin S\), and in fact \(\delta_n\notin S\) for every fixed n (see explicit zero modes below). Point residuals converge strongly: \((I-P_N)e\to r^{\rm p}\ne0\). Their first coordinates satisfy \(r_N^{\rm p}(1)=\nu_N\downarrow\nu=r^{\rm p}(1)>0\).
7. \(K_N:=b_N^*G_N^{-1}b_N=\sum_{j=2}^{N+1}|e_j(1)|^2\uparrow2p<2\). Hence \(\sum_{j\ge2}|e_j(1)|^2=2(1-\nu)<2\), and \(\|e-P_Ne\|^2\downarrow\nu/2>0\).
8. The capacity has a finite limit: \(C_N\uparrow C_\infty=2p/\nu<\infty\). The exact identities are \(p_N=C_N/(C_N+2)\), \(\nu_N=2/(C_N+2)\), and \(\det T_N/\det G_N=\nu_N\downarrow\nu>0\).
9. The best full tail-energy constant is strictly positive: \(\varepsilon_*=1/C_\infty=\nu/(2p)>0\). For every finite legal F, \(\sum_{n\ge2}w_n|F(n)|^2\ge\varepsilon_*|F(1)|^2\). This is a uniform inequality retaining every cross term, not just positive diagonal energy.
10. Minimum one-site interpolation energies converge to \(1/(2p)=1/2+1/C_\infty>1/2\). Their minimizing vectors converge strongly to \(Pe/p\), which differs from e. The unconditional upper bound \(1/(2p_N)\le\log2\) survives; bounded one-site interpolation is insufficient for density.
11. Tail Schur increments are summable: \(C_{j+1}-C_j=\eta_j^2/\sigma_j\ge0\), \(\sigma_j>0\), and \(\sum_{j\ge0}\eta_j^2/\sigma_j=C_\infty<\infty\). Every remaining innovation tail \(\sum_{j\ge J}\eta_j^2/\sigma_j=C_\infty-C_J\to0\).
12. The canonical finite dual tail certificates z_N (z_N(1)=0, \(\langle z_N,g_d\rangle=1/d\) for the first dictionary) have \(\|z_N\|^2=C_N\) and \(\|z_M-z_N\|^2=C_M-C_N\). They converge strongly to a finite-energy z satisfying all constraints. Then \(2e-z\in S^\perp\) and \((2e-z)(1)=2\). Finite certificates do not need another compactness theorem once the capacity is bounded.

### B. q_N and trigamma limits: what fails and what survives

13. \(p_N\uparrow q_*<1\), \(q_N\to q_*<1\), and \(\nu_N\downarrow1-q_*>0\). The residue probabilities q_N remain nonmonotone; their convergence does not fail.
14. The newest source, `RH_Qn_Continuation_2026-09-21.md`, reports an exact rational finite certificate \(q_*>0.961347977071\), improving the older independently recomputed \(0.900915\) certificate. Thus the reported newest range under NOT RH is \(0.961347977071<q_*<1\), and \(0<\nu<0.038652022929\). **Audit qualification:** this audit read the displayed rational bound and proof method but did not retrieve/rerun its separate certificate program; call this a reported exact finite certificate, not newly independently verified here. Its rational lower bound is \(166669166675000000000000000000/173370278660963892075988904889\).
15. Normalization error still vanishes: \(0\le q_N-p_N\le\pi^2/(3L_N^2)\). In the decomposition of site vacancy into omitted class plus wrong lift, only the wrong-lift probability is automatically negligible. The omitted changing class retains limiting probability \(\nu>0\).
16. All future downward variation still satisfies \(\sum_{j\ge N}(q_j-q_{j+1})_+\le\log(2W_{L_N}(1))\le\pi^2/(3L_N^2)\). Decreases remain possible only when N+2 is a prime power. Neither this nor bounded total variation implies the limiting value 1.
17. The one-sided overshoot bound \(q_N-q_*\le\pi^2/(3L_N^2+\pi^2)\) survives. It is not a two-sided rate to q_*, and certainly not a rate to 1.
18. The explicit geometric-mean trigamma replacement \(\widehat q_N\) satisfies \(|\widehat q_N-q_N|\le\zeta(3)/(4L_N^2)\), hence it also converges to the same strict subunit q_*. Controlled replacement of mean-value points does not remove the arithmetic gap.
19. The optimized energy outside the entire changing residue class, \(\mathcal T_N=W_{L_N}(1)(1-q_N)/q_N\), converges to \((1-q_*)/(2q_*)=\varepsilon_*>0\). The class deletion determinant ratio \(\det(G_N-W_{L_N}(1)b_Nb_N^*)/\det G_N=1-q_N\to\nu>0\).

### C. Explicit right-half-strip zero modes and quantitative probability bounds

Fix any hypothetical nontrivial zero \(\rho=\beta+i\gamma\), \(1/2<\beta<1\). Such a zero follows from NOT RH by functional-equation symmetry. Put \(a=2\beta-1\in(0,1)\), \(\Delta_\rho(n)=n^{-\rho}-(n+1)^{-\rho}\), and \(A_\rho=\sum_{n\ge1}n(n+1)|\Delta_\rho(n)|^2\). Then \(0<A_\rho\le|\rho|^2/a\).

20. The counting-space vector \(u_\rho(n)=\sqrt{n(n+1)}\,\overline{\Delta_\rho(n)}\) belongs to ker Q and every ker Q_N. Indeed \(\sum_ng_d(n)\Delta_\rho(n)=(d^{-1}-d^{-\rho})\zeta(\rho)=0\).
21. The hole kernels dominate its rank-one projection: \(I-Q_N\succeq u_\rho u_\rho^*/A_\rho\), \(R\succeq u_\rho u_\rho^*/A_\rho\). Consequently, simultaneously for every n,N,
\[
\Pr(n\notin\Xi_N),\ \Pr(n\notin\Xi_\infty)
\ge\frac{n(n+1)|\Delta_\rho(n)|^2}{A_\rho}
\ge\frac{a\,n(n+1)|\Delta_\rho(n)|^2}{|\rho|^2}>0.
\]
Each fixed site's marginal occupation is strictly less than one. Every individual site's probability-one occupation is itself an RH criterion.
22. At site 1 this yields \(\nu_N\ge2|1-2^{-\rho}|^2/A_\rho\ge2a|1-2^{-\rho}|^2/|\rho|^2\), so \(C_N+2\le |\rho|^2/[a|1-2^{-\rho}|^2]\).
23. The newest exact-head argument supplies another bound. Put \(\kappa_\rho=a|2^\rho-1|^2/|\rho|^2\). Then \(p_N\le1/(1+\kappa_\rho)\), \(q_N\le2W_{L_N}(1)/(1+\kappa_\rho)\), \(q_*\le1/(1+\kappa_\rho)<1\), and \(\nu\ge\kappa_\rho/(1+\kappa_\rho)\). Combining any finite lower certificate p>c with this only forces \(\kappa_\rho<(1-c)/c\). It does not exclude zeros arbitrarily close to the critical line or at large height.
24. The zero mode defines a one-hole law \(\Pr(J_\rho=n)=n(n+1)|\Delta_\rho(n)|^2/A_\rho\) stochastically dominated by the actual hole DPP, in a coupling with \(\{J_\rho\}\subseteq\mathbb N\setminus\Xi_\infty\).
25. Its tail is explicit:
\[
\Pr(J_\rho=n)=\frac{|\rho|^2}{A_\rho}n^{-2\beta}(1+O_\rho(n^{-1})),\quad
\Pr(J_\rho>M)\sim\frac{|\rho|^2}{aA_\rho}M^{-a}.
\]
Thus \(\Pr(\text{some hole exceeds }M)\ge\Pr(J_\rho>M)\), and \(\sum_{n>M}R(n,n)\ge\Pr(J_\rho>M)\). This is a lower tail, not an assertion that all holes have this law.
26. For every real \(b\ge a\), \(\mathbb E\sum_{n\notin\Xi_\infty}n^b=\infty\); in particular \(\mathbb E\sum_{n\notin\Xi_\infty}n=\infty\). The corresponding moment of the rank-one witness is finite for \(b<a\), but no such upper bound is established for the full hole process.
27. The conjugate zero gives an independent second complex mode, so \(\operatorname{rank}R\ge2\) and the actual hole process has at least two points almost surely by domination by their rank-two projection DPP. With multiplicities/finite families use the independent mode span. This is a direct deduction; it does **not** establish infinitely many holes. If rank R=k<∞, the hole DPP has exactly k points a.s.; if rank R=∞ it has infinitely many a.s. The above weighted moment divergence is compatible with finite random hole count.

### D. Increasing-head interpolation, conditional sampling, and compactness

Let \(\mathcal B_M=\inf\{\|F\|^2:F\in\bigcup_NS_N,\ F(n)=\delta_{n1}\ (n\le M)\}\), and let \(\mathcal B_{M,N}\) be the corresponding finite-dictionary minimum for N≥M.

28. \(\mathcal B_M\uparrow\infty\). This strengthens mere failure of convergence to 1/2. The exact dichotomy in the source says RH gives \(\mathcal B_M=1/2\) for every M (an infimum over unrestricted finite dictionaries); NOT RH gives divergence.
29. If \(t_M=\sum_{n>M}w_n|r^{\rm p}(n)|^2\), then every t_M is positive and tends to zero, and
\[
\mathcal B_M\ge\tfrac12+\frac{\nu^2}{4t_M}\to\infty.
\]
The finite-energy residual itself has vanishing tail, while forcing exact initial agreement against that residual makes interpolating witnesses' tail energy blow up.
30. The sharper zero-specific bound holds for every exact interpolant, regardless of number or signs of coefficients:
\[
\|F\|^2\ge\tfrac12+
\frac{a|1-2^{-\rho}|^2}{|\rho|^2}(M+1)^a.
\]
Its proof uses \(\sum_{n>M}|\Delta_\rho(n)|^2/w_n\le(|\rho|^2/a)(M+1)^{-a}\). Thus \(\mathcal B_M\) is not subpolynomial; any upper bound \(O(M^\varepsilon)\) with \(\varepsilon<a\) fails. The elementary O(M) upper construction remains compatible.
31. Finite families \(\rho_i\) yield the stronger exact matrix lower bound \(\mathcal B_M\ge1/2+z(M+1)^*\mathsf C^{-1}z(M+1)\), with \(\mathsf C_{ij}=1/(\rho_i+\overline{\rho_j}-1)\), \(z_i(X)=(1-2^{-\rho_i})X^{\rho_i-1/2}/\rho_i\). At X=2 this gives \(q_*\le[1+2z(2)^*\mathsf C^{-1}z(2)]^{-1}\). Part V gives the full all-site and multiplicity version.
32. With \(K_{M,N}=Q_N[1{:}M]\), \(\mathcal B_{M,N}=\tfrac12(K_{M,N}^{-1})_{11}=1/(2\theta_{M,N})\), where \(\theta_{M,N}=\Pr(1\in\Xi_N\mid2,\dots,M\in\Xi_N)\). These conditioning events are positive for N≥M.
33. Fixed M limits exist, and \(\theta_M:=\Pr(1\in\Xi_\infty\mid2,\dots,M\in\Xi_\infty)=1/(2\mathcal B_M)\downarrow0\). Quantitatively \(\theta_M\le[1+2a|1-2^{-\rho}|^2(M+1)^a/|\rho|^2]^{-1}\). A high unconditional first-site probability coexists with conditional inclusion tending to zero.
34. There cannot be a fixed c>0 such that for every M one can find N≥M with \(\theta_{M,N}\ge c\). Nor can there be any uniformly H-bounded sequence of legal functions converging coordinatewise to e. More strongly, every such coordinatewise-approximating sequence has norms tending to infinity: a bounded subsequence would yield e∈S by weak compactness.
35. Random legal interpolants sampled from the DPP still exist, with \(\mathbb EF_N=P_N\mathbf1\), \(\mathbb E\|F_N-\mathbf1\|^2\le(N+1)D_N\), and averaging m independent draws yields upper bound \((1+N/m)D_N\), \(D_N=\|\mathbf1-P_N\mathbf1\|^2\). Under NOT RH every legal realization and every legal average has error at least D_N≥D>0. Averaging removes sampling variation but cannot remove projection bias. Monte Carlo estimates and fixed-stage Markov-chain mixing do not alter this lower bound.
36. The Fock/Slater construction remains valid. The squared norm for creation of the constant mode above the filled rank-N state is D_N; under NOT RH it tends to D>0. First-site creation norm similarly tends to ν>0. This is a persistent unoccupied component, not a failure of fermionic formalism.

### E. Coupling, entrance times, hazards, window filling, and weighted vacancy

37. Nested couplings \(\Xi_N\subset\Xi_{N+1}\) remain available and add one site per stage. Their union is a proper subset of positive integers almost surely, even though it is infinite. All-site filling probability is zero, not merely below one.
38. The site-1 entrance time \(\tau_1\) has \(\Pr(\tau_1=\infty)=\nu>0\), \(\Pr(\tau_1=N)=\tfrac12|e_{N+1}(1)|^2\), and \(\Pr(\tau_1>N)=\nu_N\downarrow\nu\). Every fixed site n has a positive probability of never entering; this does not mean any particular site is absent with probability one.
39. Entrance hazards \(h_N=(C_{N+1}-C_N)/(C_{N+1}+2)\) satisfy \(\prod_{N\ge0}(1-h_N)=\nu>0\), \(\sum_Nh_N<\infty\), and \(\sum_N-\log(1-h_N)=-\log\nu<\infty\). For every j, the remaining conditional probability of never entering is \(\nu/\nu_j>0\); the remaining chance of eventual entrance tends to zero as j→∞.
40. For each finite head A_M={1,…,M}, the full-inclusion determinant \(D_M^{\rm occ}=\det Q[A_M]\) is strictly positive, but \(D_M^{\rm occ}\downarrow0\) as M→∞. Finite interpolation feasibility persists while global filling fails. The conditional inclusion probabilities in the product factorization of these determinants consequently have a divergent sum of deficits. These spatial conditional deficits must not be confused with the summable temporal entrance hazards above.
41. A new quantitative consequence of the same zero modes: \(D_M^{\rm occ}\le\sum_{n>M}|u_\rho(n)|^2/A_\rho=O_\rho(M^{-a})\); using the conjugate pair and the determinant of their tail Gram gives \(D_M^{\rm occ}=O_\rho(M^{-2a})\). Also \(\lambda_{\min}(Q[A_M])\le\sum_{n>M}|u_\rho(n)|^2/A_\rho=O_\rho(M^{-a})\). This follows from rank-one/two Loewner domination followed by the finite determinant lemma, with no estimate of the entire defect required.
42. For \(V=\sum_nw_n\mathbf1_{\{n\notin\Xi_\infty\}}\), one has \(V>0\) a.s., \(0<\mathbb EV=\sum_nw_nR(n,n)\le1\), and \(\mathbb EV\ge\nu/2>0\). Under nested coupling, V_N↓V almost surely and in every finite L^p; convergence is to a positive variable. The same positivity holds for any strictly positive summable site weights.
43. The random weighted hole measure is nonzero a.s.; its expectation has a strictly positive atom at every integer. Weighted occupied measures fail to equal the Pareto base measure. The weighted-vacancy Laplace transform \(\mathbb E e^{-\lambda V}\to0\) as λ→∞.

### F. Three different Fredholm constructions

44. The physical single-site determinant \(\det(I-\mathbf1_{\{1\}}Q_N\mathbf1_{\{1\}})=\nu_N\) tends to ν>0. Its Mellin-conjugated rank-one version has the same positive limit. This is different from a frequency-interval gap.
45. For \(A_t=\operatorname{diag}(e^{-tn/2})\), define the damped hole determinant \(F(t)=\det_F(I-A_tRA_t)\). Under NOT RH, \(0<F(t)<1\) for every t>0 and \(F(t)\downarrow0\) as t↓0. Its probability meaning is \(\mathbb E\prod_{n\notin\Xi_\infty}(1-e^{-tn})\), or the probability that no hole remains after independent position-dependent thinning.
46. Its endpoint zero–one law is exactly the global event: \(\lim_{t\downarrow0}F(t)=\Pr(\Xi_\infty=\mathbb N)=0\). It does not imply the local probability p is zero or one. All-site occupancy is bounded above by p, so p>0.96 supplies no positive lower bound for that endpoint.
47. With the zero above, \(F(t)=O_\rho(t^a)\). The conjugate pair improves this to \(F(t)\le C_\rho t^{2a}=C_\rho t^{4\beta-2}\). The source explicitly bounds \(\sum_n(1-e^{-tn})|u_\rho(n)|^2\le2|\rho|^2\Gamma(1-a)t^a/a\), and uses the determinant of the two-mode damped Gram matrix.
48. Hence \(\liminf_{t\downarrow0}[-\log F(t)]/\log(1/t)\ge4\beta-2>0\). Every uniform positive lower bound near zero fails; every proposed all-ε subpower lower bound \(F(t)\ge c_\varepsilon t^\varepsilon\) fails for ε<4β−2; any logarithmic lower bound \([\log(1/t)]^{-A}\) fails. No sequence tending to zero can make that logarithmic decay exponent tend to zero.
49. The marginal-derived bounds remain consistent:
\[
[1-e^{-t}\nu]\prod_{n\ge2}(1-e^{-tn})\le F(t)\le1-e^{-t}\nu.
\]
The lower bound decays faster than every fixed power and does not contradict the polynomial upper bound.
50. Finite rank determinants \(F_N(t)=\det(I-A_t(I-Q_N)A_t)\) increase to F(t) at fixed t. Their exact matrix formula is \(F_N(t)=\mathcal E(t)\det J_N(t)/\det G_N\), where \(\mathcal E(t)=\prod_{n\ge1}(1-e^{-tn})\), \(J_N(t)=\sum_nw_n v_N(n)v_N(n)^*/(1-e^{-tn})\). Under NOT RH no rank choice N(t), however large, can give a uniform positive lower bound as t↓0, because F_N(t)≤F(t)→0.
51. The rank-only upper bound \(F_N(t)\le\prod_{n>N}(1-e^{-tn})\le\exp[-e^{-t(N+1)}/(1-e^{-t})]\) remains true. The necessary rank scale \(N(t)\gtrsim t^{-1}\log(1/t)\) for a positive lower determinant was never sufficient; under NOT RH no scale succeeds.
52. The different Pareto-damped **occupied** determinant \(B_N=\det(I-W^{1/2}Q_NW^{1/2})\) decreases to \(B_\infty>p_*\), where \(p_*=\prod_n(1-w_n)=\sin(\pi(\sqrt5-1)/2)/\pi\). Bounds: \(p_*\nu\le B_\infty-p_*\le\mathbb EV\). It remains positive and strictly above its RH benchmark; it is not the F(t) above.
53. The undamped global occupied determinant at finite rank remains \(\det(I-zQ_N)=(1-z)^N\), with \(\det(I-Q_N)=0\) even under NOT RH. The undamped infinite Q has infinite rank and is not trace class, so its ordinary global Fredholm determinant is not available.

### G. Profinite limits, classes, and escape of witnesses

Assume valid common conductors M_N with d|M_N for all dictionary d, M_N|M_{N+1}, and cofinal divisibility; let C_N={1+kM_N:k≥0}.

54. The class/site relation \(p_N=w_1q_N/W_{M_N}(1)\) and \(0\le q_N-p_N\le2/(M_N+1)\) still hold. The limit is p<1, despite the lift error tending to zero.
55. If R_N^{\rm per} projects onto all M_N-periodic functions, then \(R_N^{\rm per}\to I\) strongly while P_N→P≠I. For the normalized first coordinate \(\eta_1=\sqrt2\delta_1\), \(\|R_N^{\rm per}\eta_1-P_N\eta_1\|^2\to\nu>0\). The exact decomposition is \(1-p_N=[1-w_1/W_N]+[w_1/W_N](1-q_N)\); its first term vanishes and second persists.
56. Nevertheless every fixed arithmetic progression contains infinitely many occupied sites almost surely, simultaneously over all progressions. Thus the occupied set has full profinite closure even under NOT RH. CRT separation, exhaustive fixed-class coverage, orbit-stabilizer identities, and infinitely many conjugacy classes all survive.
57. For H_{j,N}=Pr(\Xi_N∩C_j≠∅), the iterated limits differ: \(\lim_j\lim_NH_{j,N}=1\), whereas \(\lim_N\lim_jH_{j,N}=p<1\); the compatible diagonal limit is also p. A uniform interchange/diagonal saturation estimate fails.
58. The limiting base measure remains \(\nu_{\rm base}=\sum_nw_n\delta_n\) on the profinite integers, purely atomic with full support and mass 1/2 at 1. It is not Haar measure. Rank-N modular DPP laws are not automatically projectively consistent; quotienting later configurations can introduce multiplicities.
59. The expected hole mass in the shrinking profinite cylinders around 1 tends to \(\nu/2>0\), with error at most 1/(M_j+1). This is the precise failure of the cylinder-vacancy vanishing criterion.
60. Let Z_j be the smallest occupied ordinary integer in C_j. It exists almost surely, and Z_j→1 profinitely. On {1 occupied}, Z_j=1 for all j; on {1 vacant}, probability ν>0, one has Z_j≥1+M_j→∞ in ordinary integers. For each fixed R≥1, \(\Pr(Z_j>R)=\nu\) eventually. Hence this family is not tight in the ordinary discrete topology, although it converges profinitely.
61. Infinite-rank point counts in profinite cylinders remain infinite, so the profinite counting measure is not locally finite. Weighted occupied/hole measures still converge in total variation. Normalized empirical counting measures can lose fixed-site information; no Haar or unique empirical limit follows from these facts.

### H. Mellin, reflection, Dyson, and tail constructions

62. Mellin–Plancherel still transports projections isometrically. The transformed legal closure is a proper subspace of the Mellin image of H. It omits the constant transform 1/s and every individual coordinate transform \([n^{-s}-(n+1)^{-s}]/s\). At the hypothetical zero ρ every transformed legal function vanishes, whereas these targets do not.
63. The transformed constant-target projection error tends to D>0 and the transformed point-target rank-one determinant tends to ν>0. Unitarly adding the reflected/conjugate copy does not eliminate these normalized defects.
64. Unrestricted reflected boundary approximants in the upper-estimate note may still converge to 1/s in boundary L². Under NOT RH their meromorphic extensions have uncancelled poles at ρ−ε for sufficiently small positive ε, including after subtraction of the known pole at 1+ε. They therefore cannot be substituted as legal Hardy/arithmetic approximants.
65. The damped Möbius candidate \(-\sum_{d\ge2}\mu(d)d^{-\varepsilon}g_d\), though pointwise well defined and tending coordinatewise to 1, is not in H for all sufficiently small ε>0 below β−1/2: its initially valid Mellin formula has a genuine right-half-plane pole at ρ−ε. Pointwise convergence survives while the required Hilbert-space assertion fails.
66. The canonical constant-head repair L_N in the upper-estimate note has exact error equal to its full signed tail T_N. Under NOT RH each such error is at least D, and in particular T_N cannot tend to zero. This is a necessary failure of that sufficient route; no RH converse for this particular family was established.
67. The unmodified Möbius candidate has exact head error \(m_N^2(N+1-H_{N+1})\). The historical statement m_N→0 does not control that growing head energy. NOT RH forces failure of any proved full-error vanishing route, not necessarily failure of m_N→0 itself.
68. The finite arithmetic Mellin DPPs remain valid. On every fixed bounded positive-length frequency interval, their expected counts still diverge and their gap probabilities still tend to zero unconditionally. The infinite undamped Mellin projection remains non-locally-trace-class, irrespective of RH. These limits do not fail when RH fails and cannot certify RH.
69. For physical cutoff R_M and Mellin isometry \(\mathcal U\), the exact covariance defect is \(\mathcal UR_MPR_M\mathcal U^*=\mathcal UR_M\mathcal U^*-\mathcal UR_M(I-P)R_M\mathcal U^*\). The expected number of cutoff continuum particles is \(M-\operatorname{tr}(R_M(I-P)R_M)<M\); its eigenvalue count law is Bernoulli-sum, not fixed M. The removed trace is at least ν for every M≥1 and tends to rank(I−P), finite or infinite.
70. The ambient coordinate-cutoff sine-kernel limit remains valid. NOT RH does **not** imply that the corresponding leading arithmetic Dyson limit fails. Every fixed finite-rank defect is invisible after division by log M, and each individual off-line-zero mode gives an O(1/log M) contribution at that scale. The whole infinite defect requires a separate bound; vanishing of each fixed contribution cannot justify exchanging an infinite sum and the limit.
71. In the source's unfolded notation, the actual sine-limit obstruction is the positive local trace \(\Delta_M(B)=(\log(M+1))^{-1}\int_B\|(I-P)v_M(t_M(x))\|^2dx\). Its vanishing is sufficient for transfer of the ambient sine limit, but NOT RH alone does not force nonvanishing of that scaled trace. Sine universality, Montgomery pair correlation of actual zeros, and Hilbert–Pólya identification are distinct assertions; no contrapositive about the latter two comes from this construction alone.
72. Fixed-rank integer-DPP maxima retain their unconditional Pareto tail \(\Pr(\max\Xi_N>M)=a_N^{\rm tail}/M+O_N(M^{-2})\), so \(\mathbb E\max\Xi_N=\infty\) at every fixed rank. This neither disproves nor proves an N-dependent Airy/KPZ scaling. An auxiliary Airy/KPZ or Dyson limit would still require a bridge to fixed-site saturation.

### I. Important nonconsequences and logical safeguards

- NOT RH does not make finite G_N or T_N singular. It does not invalidate Gram–Schmidt, coefficient stabilization, exact CRT identities, Schur identities, positivity, DPP existence, negative association, sampling algorithms, or nested coupling.
- It does not force q_N to oscillate without a limit, force q_*=0, invalidate the large finite lower certificate, or yield a universal positive vacancy gap independent of the location of an off-critical zero.
- It does not make all sites absent, specify which fixed site is absent almost surely, or by the rank-one argument alone imply infinitely many holes. Spatial tail triviality does not make a fixed-site occupation probability zero or one.
- A large marginal, finite-window invertibility, almost-sure infinite occupation of each fixed congruence class, and profinite density are all compatible with global nonsaturation.
- Negative association usually bounds conditional inclusions from above, not by the lower bound needed for the interpolation argument. Generic one-hole projection examples with p arbitrarily close to one but F(t)→0 refute that probabilistic shortcut; they are not counterexamples to RH or identifications of the arithmetic projection.
- The growing-head interpolation energy diverges under NOT RH, while the norm of the fixed point residual stays finite and its own tail vanishes. These are different vectors and different limits.
- The total finite capacity bounds here are conditional consequences of NOT RH. Producing such a bound unconditionally would disprove RH, while disproving the bounded-capacity consequences would prove RH. Conjoining valid consequences is not itself a contradiction.

### Source inventory and coverage

Eighteen current Library artifacts were retrieved; sixteen mathematical Markdown records plus two Python demonstrations. Duplicate copies of the complete q_N record and Fredholm note were not separately counted. The complete q_N record required two pages and both were obtained. Mathematical source proofs were read; embedded historical formalization snippets were not used as verification or as a mathematical dependency.

| Key | Current source | Main coverage |
|---|---|---|
| D01 | RH_Qn_Continuation_2026-09-21.md | Latest reported rational certificate; sharpened zero/head bounds; multiple-zero matrix; coefficient constraints |
| D02 | RH_Qn_Fredholm_Combined_Analysis_2026-09-21.md | Quantitative Fredholm exponent; finite matrix formula; necessary rank scale |
| D03 | RH_Qn_Complete_Chat_Research_Record_2026-09-21.md | Probability/capacity distinctions; interpolation dichotomy; conditional DPP; all trigamma formulas |
| D04 | RH_Fredholm_Zero_One_Law_and_Occupation_Bound_2026-09-21.md | Endpoint zero–one law; rank-one counterexample; marginal gap |
| D05 | RH_Direct_Trigamma_Sequence_Analysis_2026-09-21.md | Oscillation, variation, one-sided rate, trigamma sensitivity |
| D06 | RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md | Uniform tail gap, strong convergence of finite dual certificates; restricted spectral obstruction |
| D07 | RH_Mellin_Upper_Estimate_Attempt_2026-09-21.md | Full signed tail, damped Möbius poles, reflected boundary approximants |
| D08 | RH_Infinite_DPP_Dyson_Sine_Limit_2026-09-21.md | Actual covariance defect, sine scaling, non-RH limitations |
| D09 | RH_Profinite_DPP_Limits_and_Saturation_2026-09-20.md | Three limit orders, atomic profinite measure, escaping occupied witnesses |
| D10 | RH_DPP_Residue_Quotients_and_Orbits_2026-09-20.md | Residue quotient; unit orbits vs conjugacy; no saturation from orbit counts |
| D11 | RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction_2026-09-20.md | All-site vacancy, one-hole domination, divergent hole position moment |
| D12 | RH_Mellin_DPP_Transform_and_Local_Trace_Obstruction_2026-09-19.md | Finite continuum DPP, interval trace divergence, physical rank-one determinant |
| D13 | RH_Fredholm_Determinants_and_KPZ_Assessment_2026-09-19.md | Pareto-damped benchmark determinant, maximum tail, KPZ distinctions |
| D14 | RH_Residue_Determinantal_Point_Process_2026-09-19.md | Existence, exact law, conditional lifts, coupling, hazards |
| D15 | RH_Orthonormal_Projection_Gram_Capacity_Equivalences_2026-09-19.md | Exact equivalence chain, first-coordinate gap, coefficients |
| D16 | RH_Residue_Orthonormal_Basis_2026-09-19.md | Basis and Parseval defect |
| D17 | rh_dpp_random_interpolation.py | Unbiased interpolation, error/averaging bounds |
| D18 | rh_dpp_three_constructions.py | Reversible walks, basis exchange, Fock creation norm |

Part V uses `RH_Combined_Obstruction_Matrix_and_Complementary_Powers_2026-09-21.md` for all-site matrix domination, multiplicity derivatives, and further weighted product bounds.

Audit corrections: the latest certificate supersedes 0.9009, but is not independently recomputed here. Old source q_N sometimes means vacancy; every formula above is renormalized consistently. The example conditional probability m/(m+1) in D04 only applies for m≥2; at m=1 it is p. No other substantive mathematical error was found in the formulas used above. All-source Gram matrices preserve full tails and signed mixed terms.

### Addendum: fixed Pareto-weight determinant, logarithmic vacancy bounds, and spectral tails

This supplements item 52 with the stronger inequality recovered in historical chat context. It is proved below directly, so it does not depend on a historical verification claim. To preserve the chapter's notation, Q_N is the counting-space occupied projection kernel (the historical message calls it K_N), and Q is its strong limit. **Do not confuse the operators in this addendum with the hole projection R=I−Q or the exponentially damped F(t).**

Set
\[
 W=\operatorname{diag}(w_n),\qquad w_n=\frac1{n(n+1)},
 \qquad A_N=W^{1/2}Q_NW^{1/2},\qquad A=W^{1/2}QW^{1/2}.
\]
These are the operators called R_N in the recovered history. Define
\[
 B_N=\det_F(I-A_N),\qquad B_\infty=\det_F(I-A),
 \qquad p_0=\det_F(I-W)=\prod_{n\ge1}(1-w_n)>0,
\]
\[
 \mu_N=\operatorname{tr}(W-A_N)
 =\sum_{n\ge1}w_n(1-Q_N(n,n)),\qquad
 \mu_\infty=\sum_{n\ge1}w_n(1-Q(n,n)).
\]
Thus B_N is the fixed-weight determinant called F_N in that history; it equals the B_N of item 52 here. One has \(0\le A_N\le A\le W\), \(\|W\|=1/2\), \(\operatorname{tr}W=1\), and all determinants are strictly positive.

**73. Exact logarithmic comparison with total weighted vacancy.** For every N, and for the infinite-rank limit,
\[
 \boxed{\mu_N\le\log\frac{B_N}{p_0}\le2\mu_N,\qquad
 \mu_\infty\le\log\frac{B_\infty}{p_0}\le2\mu_\infty.}
\]
Proof: put \(D_N=W-A_N\ge0\) and \(A_N(s)=A_N+sD_N\), 0≤s≤1. Differentiation of the trace-class determinant gives
\[
 \log\frac{B_N}{p_0}
 =\int_0^1\operatorname{tr}\bigl((I-A_N(s))^{-1}D_N\bigr)\,ds.
\]
Since \(0\le A_N(s)\le W\le I/2\), one has \(I\le(I-A_N(s))^{-1}\le2I\). Taking the trace against positive D_N bounds the integrand between tr D_N=μ_N and 2μ_N. This argument does not require W and Q_N to commute. The same reasoning applies to A.

Consequently \(p_0e^{\mu_N}\le B_N\le p_0e^{2\mu_N}\), together with the independent bound B_N≤1. Equivalently,
\[
 \tfrac12\log(B_N/p_0)\le\mu_N\le\log(B_N/p_0).
\]

**74. Precise rank-limit relation, without an asserted effective arithmetic rate.** Dominated convergence gives
\[
 \mu_N\downarrow\mu_\infty,\qquad
 \|A-A_N\|_1=\operatorname{tr}(A-A_N)=\mu_N-\mu_\infty\to0,
 \qquad B_N\downarrow B_\infty.
\]
Applying the interpolation argument to the segment from A_N to A yields
\[
 \boxed{\mu_N-\mu_\infty\le
 \log\frac{B_N}{B_\infty}\le2(\mu_N-\mu_\infty).}
\]
This quantitatively compares two errors but supplies no independent decay rate in N. Under NOT RH,
\[
 \mu_\infty\ge w_1\Pr(1\notin\Xi_\infty)=\nu/2>0,
 \qquad \boxed{B_\infty\ge p_0e^{\mu_\infty}>p_0.}
\]
Therefore none of μ_N→0, B_N→p_0, or log(B_N/p_0)→0 can hold. Conversely any of them implies saturation because all w_n are strictly positive, and hence RH via the residue-span equivalence.

**75. Eigenvalue domination and summable spectral tails survive NOT RH.** Let the eigenvalues of A_N or A be listed in nonincreasing order as λ_1,λ_2,…, with zero padding for finite rank. By the compact-operator minimax principle and A_N,A≤W,
\[
 \boxed{0\le\lambda_j\le w_j=\frac1{j(j+1)},\qquad
 \sum_{j>r}\lambda_j\le\frac1{r+1}.}
\]
For the spectral determinant cutoff \(B^{[r]}=\prod_{j=1}^r(1-\lambda_j)\), and the corresponding full determinant B, these bounds give
\[
 0\le\log\frac{B^{[r]}}B
 =\sum_{j>r}-\log(1-\lambda_j)
 \le2\sum_{j>r}\lambda_j\le\frac2{r+1},
\]
\[
 \boxed{e^{-2/(r+1)}B^{[r]}\le B\le B^{[r]},\qquad
 0\le B^{[r]}-B\le1-e^{-2/(r+1)}\le\frac2{r+1}.}
\]
These are unconditional, uniform spectral truncation bounds, including the infinite-rank operator. They control the number of retained eigenvalues r, not the arithmetic dictionary dimension N; no claim that \(\mu_N-\mu_\infty=O(1/N)\) is warranted.

The benchmark is \(p_0=\sin(\pi(\sqrt5-1)/2)/\pi\), as in item 52. Under NOT RH the spectral determinant remains perfectly well defined and efficiently tail-controlled, but converges to a value strictly above this benchmark.


## Part III. CRT, two-seed interpolation, covariance, and sampling

### Conventions and the principal distinction

Let
\[
w_n=\frac1{n(n+1)},\quad H=\ell^2(w),\quad b(n)=1,
\quad g_d(n)=\{n/d\},\quad S=\overline{\operatorname{span}_{\rm finite}\{g_d:d\ge2\}}^H.
\]
The two-seed legal space is generated by
\[
g_{p,m}(n)=m\lfloor n/m\rfloor-pm\lfloor n/(pm)\rfloor,
\qquad p\in\{2,3\},\ m\ge1.
\]
For statements involving that space, the source uses its proved/classical target-approximation criterion. In all quantitative implications below a single zero to the right of the line suffices, independently of any claimed exhaustive description of the annihilator. Write
\[
\rho=\sigma+i\tau,\quad\zeta(\rho)=0,\quad \tfrac12<\sigma<1,
\quad a=2\sigma-1>0.
\]
Not RH supplies such a zero by symmetry. Full *projection errors* decrease to a positive number under not RH; *minimum energies of functions forced to equal 1 on a growing head* diverge. These are different optimization problems and must never be identified.

### 1. Growing exact heads have an unavoidable polynomial tail cost

For every finite legal F satisfying F(n)=1 for n<M, the full error is entirely a tail, and
\[
\int_M^\infty(1-\widetilde F(x))x^{-\rho-1}\,dx=\frac1\rho,
\qquad
\|1-F\|_H^2\ge\frac{a}{|\rho|^2}M^a.
\tag{C1}
\]
Here \(\widetilde F(x)=F(\lfloor x\rfloor)\). This bound is uniform over all support sizes, signed coefficient choices, conductor enlargements, and both seed channels. Allowing arbitrarily many tail corrections does not remove it.

If the *Pareto mean* is also exactly 1, centering the Mellin test sharpens the constant:
\[
\|1-F\|_H^2\ge\frac{a}{|\rho-1|^2}M^a.
\tag{C2}
\]
This mean is \(\langle b,F\rangle_H\), not uniform period mean. The conditional tail variance then obeys
\[
\operatorname{Var}(F\mid n\ge M)=M\|1-F\|_H^2
\ge\frac{a}{|\rho-1|^2}M^{2\sigma}.
\tag{C3}
\]
Consequently every such head sequence has
\[
\liminf_{M\to\infty}\frac{\log(1+\|1-F_M\|_H^2)}{\log M}\ge a.
\]
Uniform boundedness, subpolynomial full energy, subpolynomial tail variance after division by M, and every \(O(M^\theta)\) estimate with \(\theta<a\) must fail, even along an unbounded subsequence and even if the family is allowed to depend on \(\theta\). The correct negation is not merely that one chosen construction fails: no legal family can achieve those rates.

For the unrestricted exact-head infimum \(E_h=\inf_F\|F-1\|^2\), optionally with Pareto mean one imposed, the notes prove a zero-or-divergence dichotomy: either target density holds and \(E_h=0\) at every fixed finite h, or \(E_h\to\infty\). Under not RH the second alternative holds, quantitatively by C1 or C2. A finite positive limiting plateau is impossible. This dichotomy need not hold for a preassigned finite budget such as M=h.

Sources: [S1] §§4–6; [S2] §§4–5; [S3] §7; [S4] §§11–12.

### 2. The exact dual certificate measures centered tails of every annihilator

For \(h\in S^\perp\) with \(\langle b,h\rangle\ne0\), put
\[
\tau_N(h)=\sum_{n>N}w_n|h(n)|^2
-(N+1)\left|\sum_{n>N}w_nh(n)\right|^2.
\]
Every exact-head, Pareto-mean-one legal witness obeys
\[
\|1-F\|^2\ge\frac{|\langle b,h\rangle|^2}{\tau_N(h)}.
\tag{C4}
\]
The denominator is the full centered tail norm, not its diagonal substitute. It is positive for separating h and tends to zero. The unrestricted minimum is exactly the supremum of these ratios over the relevant annihilators, and the supremum is attained when the minimum is positive. Thus not RH forces these dual costs to diverge, even without selecting a particular zero mode. Nothing here proves that zero modes exhaust all annihilators.

Sources: [S1] §5; [S3] §7.

### 3. Multiple zeros and multiplicities strengthen the head-energy obstruction

For finitely many distinct right-hand zeros \(\rho_i\), normalized mean-one exact-head energy satisfies
\[
\mathcal E\ge v_M^*C^{-1}v_M,\quad
(v_M)_i=M^{\rho_i-1/2},\quad
C_{ij}=\frac{(\rho_i-1)(\overline{\rho_j}-1)}{\rho_i+\overline{\rho_j}-1}.
\tag{C5}
\]
The exact discrete Gram matrix is a positive-semidefinite subtraction from the corresponding continuous matrix; using it strengthens C5. Relative zero ordinates enter all off-diagonal phases. They cannot be discarded or modeled as independent.

If \(\rho\) has multiplicity q, then
\[
\liminf_{M\to\infty}
\frac{\mathcal E}{M^{2\sigma-1}(\log M)^{2(q-1)}}
\ge
\frac{(2\sigma-1)^{2q-1}}{((q-1)!)^2|\rho-1|^2}.
\tag{C6}
\]
For q=1, C2 gives the nonasymptotic form. Thus multiplicity forces extra logarithmic growth; simple zeros already force a positive power. These are relaxed necessary moment bounds, not claims that the minimizing tails are realizable legally.

Source: [S2] §5.

### 4. Every legal L1 approximation must pay a polynomial L2 price

Let \(\epsilon=\|1-F\|_{L^1(w)}\), \(\beta=1-\sigma\), and \(p=(2\sigma-1)/(1-\sigma)>0\). For
\(0<\epsilon\le a/|\rho|\), the historical optimized clipping calculation proves
\[
\|1-F\|_H^2\ge
\frac{2\sigma a}{|\rho|^2}
\left(\frac{a}{|\rho|\epsilon}\right)^p
=:C_\rho\epsilon^{-p}.
\tag{C7}
\]
Also
\[
\|F\|_H^2\ge C_\rho\epsilon^{-p}+1-2\epsilon.
\tag{C8}
\]
Therefore every legal family with \(\epsilon_j\to0\) has diverging full energy and
\(\liminf\epsilon_j^p\|F_j\|^2\ge C_\rho\). No such family has energy \(\epsilon_j^{-o(1)}\). In the historical construction with \(\epsilon_N=O(1/\log N)\), the proposed full-energy bound \((\log N)^{o(1)}\) is impossible under not RH.

More generally, an energy upper bound \(O(\epsilon^{-A})\) excludes zeros with \(\sigma>(A+1)/(A+2)\); little-o at exponent A excludes equality as well (for A>0). Hence a hypothetical zero imposes a minimum admissible accuracy-versus-energy exponent. C7 is sharp for the single-moment relaxation, not proved sharp within the legal arithmetic class.

Source: [S5] §§1–4; [S6] §§16–18.

### 5. Strong regularity of any nonzero annihilator is impossible

The updated historical note proves unconditional density of the two-seed legal span in
\[
Y_{c,\theta}=L^1\!\left(w_n e^{c(\log n)^\theta}\right),
\qquad c>0,\quad0<\theta<3/5.
\]
Consequently every nonzero two-seed annihilator h satisfies, for every such \(\theta\),
\[
\limsup_{n\to\infty}
\frac{\log(1+|h(n)|)}{(\log n)^\theta}=\infty.
\tag{C9}
\]
It cannot be bounded by any fixed power of \(1+\log n\), by \(\log n/\log\log n\), or by any one envelope \(C e^{c(\log n)^\theta}\). Not RH makes the canonical target residual a nonzero annihilator and forces all these failures. In tail notation \(A_h(n)=\sum_{k\ge n}w_kh(k)\), the equivalent forbidden upper estimate is
\[
n(n+1)|A_h(n)-A_h(n+1)|
\le C e^{c(\log n)^\theta}.
\]
The older little-o logarithmic endpoint is superseded, not the strongest current statement.

The proof's legal approximants to tail differences converge in these weighted L1 spaces, but under a right-hand zero they cannot converge in H: the zero functional is zero on each approximant and nonzero on its limit. Thus not RH forces failure of this specific upgrade from weighted L1 convergence to H convergence.

Source: [S6] §§23–27.

### 6. Canonical primitive tails must be square summable but not absolutely summable

For the first-site residual \(r=(I-P_S)e\), \(e=\mathbf1_{\{1\}}\), \(\delta=\|r\|^2>0\), define
\[
z_*=2e-\delta^{-1}r,
\qquad A_f(n)=\sum_{k\ge n}w_kf(k).
\]
Under not RH, the canonical certificate exists and satisfies
\[
z_*(1)=0,\quad\langle z_*,g_d\rangle=1/d,\quad
\|z_*\|^2=\delta^{-1}-2.
\]
Its primitive has the simultaneous properties
\[
\sum_n|A_{z_*}(n)|=\infty,\quad
\sum_n|A_{z_*}(n)|^2\le4(\delta^{-1}-2),\quad
|A_{z_*}(n)|\le\frac1{(1-2^{-1/2})\sqrt n}\ (n\ge2).
\tag{C10}
\]
If \(B_j=\sum_{2^j\le n<2^{j+1}}|A_{z_*}(n)|\), then
\[
\sum_jB_j=\infty,
\qquad \sum_j2^{-j}B_j^2\le4(\delta^{-1}-2).
\]
Thus every summable dyadic-block estimate, including \(B_j\le C(j+1)^{-1-\eta}\), must fail.

There is a quantitative nonsummability alternative. For \(h=z_*-2e\), \(H_0=\delta^{-1/2}\), \(L_N=\sum_{n\le N}|A_h(n)|\), and \(y=\lfloor\log N/(4\log2)\rfloor\ge2\),
\[
L_N-L_y\ge\frac12-\frac{L_N}{4\log(y+1)}-H_0N^{-1/4}.
\tag{C11}
\]
For sufficiently large N, either \(L_N\ge\tfrac12\log(y+1)\) or \(L_N\ge L_y+1/4\). This is stronger than simply asserting divergence.

Every nonzero real annihilator also obeys
\[
\sum_n\frac{h^+(n)}{n+1}
=\sum_n\frac{h^-(n)}{n+1}=\infty.
\tag{C12}
\]
The canonical certificate therefore cannot be eventually nonnegative or eventually nonpositive. Hilbert-space minimum-norm uniqueness does not provide absolute primitive summability. A nonzero overlap with a hypothetical zero mode does not justify asserting an uncancelled pointwise asymptotic power term.

Source: [S7] §§1–8.

### 7. Exact finite sieve identities still hold, but their signed tails cannot be discarded

For \(h\in S^\perp\), define \(B_N=\sum_{n\le N}A_h(n)\), \(E_N=\sum_{n>N}w_nh(n)^2\), and
\[
D_d(N)=B_N/d-\sum_{k\le N/d}A_h(kd).
\]
Then
\[
D_d(N)=\sum_{n>N}w_nh(n)(g_d(N)-g_d(n)),\quad
|D_d(N)|\le\sqrt{E_N/(N+1)}.
\]
For squarefree P,
\[
\sum_{\substack{k\le N/m\\(k,P)=1}}A_h(mk)
=\frac{\varphi(P)}{mP}B_N-\sum_{d\mid P}\mu(d)D_{md}(N).
\tag{C13}
\]
The elementary error is at most \(2^{\omega(P)}\sqrt{E_N/(N+1)}\). Under not RH this system has a nonzero canonical solution despite each fixed-d error tending to zero. Any proposed joint limit that also suppresses the surviving sifted tails sufficiently to force h=0 must fail. The obstruction is not a failure of finite CRT or inclusion–exclusion; it is insufficient uniformity when sieve complexity and tail cutoff both grow.

Source: [S7] §§5–6.

### 8. Dyadic and multirange gains are summable in the relevant normalization

Let \(V_M\) be the nested canonical two-seed spaces, \(r_M=b-P_{V_M}b\), \(D_M=\|r_M\|^2\), and
\[
\Delta_M=D_M-D_{2M}=h_M^TS_M^\dagger h_M,
\quad S_M=K_M-C_M^TA_M^\dagger C_M,
\quad h_M=d_M-C_M^TA_M^\dagger a_M.
\tag{C14}
\]
All signed source and covariance subtractions are essential. Under not RH,
\[
D_M\downarrow D_\infty\ge a/|\rho|^2>0.
\]
On \(M_j=2^jM_0\), this forces
\[
\sum_j\frac{\Delta_{M_j}}{D_{M_j}}<\infty,
\quad
\prod_j\left(1-\frac{\Delta_{M_j}}{D_{M_j}}\right)
=\frac{D_\infty}{D_{M_0}}>0,
\quad
\sum_j\Delta_{M_j}=D_{M_0}-D_\infty<D_{M_0}.
\tag{C15}
\]
In particular the relative gain tends to zero. For every c>0 there are arbitrarily large dyadic M with
\(\Delta_M<cD_M/\log(2M)\); equivalently \(\liminf_{j\to\infty}\log(2M_j)\Delta_{M_j}/D_{M_j}=0\). This does not say the logarithmic target fails at every sufficiently large M.

If \(\mathcal E_M\) is the least norm squared of an innovation w with \(\langle r_M,w\rangle=D_M\), then \(\mathcal E_M=D_M^2/\Delta_M\), with \(+\infty\) if infeasible. Thus no eventual bound \(\mathcal E_M\le C D_M\log(2M)\) can hold; the ratio is unbounded along a subsequence.

Sources: [S8] §§5–10; [S9] §§14,16; [S10] §7.

### 9. Reciprocal-error gains and centered reconstruction costs have a stronger exact budget

After adding selected cells, let X be the old-plus-cell space and \(D_X=\|b-P_Xb\|^2\). The fully centered arithmetic Schur problem has source \(\alpha\) and positive covariance \(\mathsf T\), with
\[
\kappa_{\rm miss}=\alpha^T\mathsf T^{-1}\alpha
=1/D_{2M}-1/D_X,
\quad
D_{2M}=\frac{D_X}{1+D_X\kappa_{\rm miss}}.
\tag{C16}
\]
For the whole block \(\kappa_M=1/D_{2M}-1/D_M\). Under not RH,
\[
\sum_{j<J}\kappa_{M_j}
\le\frac{|\rho|^2}{a}-\frac1{D_{M_0}},
\qquad\sum_j\kappa_{M_j}<\infty.
\tag{C17}
\]
The same bound applies to missing-source increments alone.

The minimum centered variance among the relevant legal functions of mean one is \(\mathcal R_M=1/\kappa_{\rm miss}\), or infinity. Every witness schedule with \(\sum_j1/L_j=\infty\) must fail to satisfy \(\mathcal R_{M_j}\le L_j\) on a set with that divergent reciprocal sum. In particular, an eventual O(log M) centered-cost bound is impossible; \(\mathcal R_{M_j}/\log(2M_j)\) is unbounded along a subsequence. This reciprocal-error criterion is weaker than the earlier relative-gain target and must not be conflated with it.

Source: [S9] §§12–16.

### 10. Resonance-blind patterns are actual annihilator-compatible patterns, not arbitrary graphs

The historical corrected model gives an actual nonzero limiting residual under not RH. Put
\(a_\infty(n)=r_\infty(n)/[n(n+1)]\). Then
\[
a_\infty\in\ell^1,
\quad\sum_nn(n+1)|a_\infty(n)|^2<\infty,
\quad\sum_na_\infty(n)=\|r_\infty\|^2>0,
\]
while for every p=2,3 and m≥1,
\[
m\sum_{n\ge m}a_\infty(n)
\left(\lfloor n/m\rfloor\bmod p\right)=0.
\tag{C18}
\]
Thus the proposed unique-continuation assertion that C18 plus these summability conditions forces zero total charge is false under not RH. This is a precise all-scale failure pattern compatible with the constant-target normal equations.

The two-lemma dyadic chord mechanism requires BOTH a signed synthesis/Bessel bound \(\lambda_{\max}(H_M)\le B\log(2M)\) AND actual-source charge \(\|y_M\|^2\ge cD_M\) eventually. Under not RH this conjunction is impossible. One cannot infer which input fails without an independent proof of the other. A failed cell-only estimate can occur even under RH and does not itself disprove RH.

Corrections preserved in the notes: raw difference packets have Pareto mean zero and their span has distance exactly 1 from b; they are not the canonical legal space. The complete packet space has two algebraic charges, not zero charges. Finite selected cells have genuine omitted components; a spanning-tree/anchor completion repairs their algebraic span, but not automatically their quantitative source cost.

Sources: [S11] §§26–28; [S9] §§9–14.

### 11. Source-weighted small eigenvalues retain positive mass

For nested legal V_N interpolating the first N coordinates, let Q_N truncate to that head, P_N project onto V_N, and \(T_N=Q_NP_NQ_N\) on the head. With \(T_Ne_i=\lambda_i e_i\), let
\(\nu_N=\sum_i|\langle Q_Nb,e_i\rangle|^2\delta_{\lambda_i}\).
The note proves, unconditionally,
\[
\nu_N\xrightarrow{w^*}d^2\delta_0+(1-d^2)\delta_1,
\quad d^2=\operatorname{dist}(b,S)^2.
\tag{C19}
\]
For every fixed \(0<\eta<1\), \(\nu_N([0,\eta))\to d^2\). Thus under not RH a positive atom forms at zero in the *source-weighted* spectral limit, even though every finite \(T_N\) is positive definite and omitted-tail leakage tends to zero.

The finite exact-head norm is \(\widehat E_N=\int\lambda^{-1}d\nu_N\), which diverges; C1 and the reverse triangle inequality give \(\widehat E_N\ge(\sqrt{a}|\rho|^{-1}(N+1)^{a/2}-1)_+^2\). Fixed-threshold cutoff witnesses remain uniformly bounded and converge strongly to \(P_Sb\), not b. Compactness, vanishing leakage, and finite invertibility all survive not RH; low-eigenvalue source mass does not vanish.

Source: [S12] §§1–5.

### 12. Diagonal interpolation is governed by the full target-specific inverse cost

For a diagonal exact-head/mean-one class, let \(d_h^2\) be its unconstrained optimum, e_* its residual, C a growing Mellin constraint matrix, G its full Pareto Gram matrix, and r the target defect. If feasible, the constrained minimum is exactly
\[
\mathcal E_{h,S}=d_h^2+r^*(CG^{-1}C^*)^\dagger r
=d_h^2+\sum_{\lambda_j>0}\frac{|\langle r,v_j\rangle|^2}{\lambda_j}.
\tag{C20}
\]
If the defect is outside the constraint range, the cost is infinity. Under not RH every feasible such construction has at least the C2 polynomial floor. Thus an adequate subpower bound for the *entire* cost cannot hold. It does not follow that the inverse-correction term alone diverges: the base error d_h^2 may already carry the obstruction.

The note separately proves unconditional instability of sufficiently dense growing spectral grids, superpolynomial cost for superlogarithmic matching at fixed linear conductor budget, and failure of all-data inverse bounds. These are restrictions on overstrong interpolation ansätze, not consequences exclusive to not RH. They do not prove that the actual unrestricted legal optimum is large without a zero obstruction.

Sources: [S13] §§4–5,9–17; [S3] §§15–18.

### 13. CRT enlargement retains invisible coarse error, imperfect fit, and innovation variance

For conductor enlargement Q|L, the screened correction map splits into conditional mean A and within-fiber innovation U. With D=U*U>0,
\[
S=A^*A+D,\quad d=A^*e_Q,
\quad E_L=E_Q-d^*S^{-1}d
=\langle e_Q,(I+AD^{-1}A^*)^{-1}e_Q\rangle.
\tag{C21}
\]
The exact surviving error is
\[
E_L=\|e_\perp\|^2+\|e_\parallel-Ab\|^2+b^*Db.
\]
The gain is zero iff A*e_Q=0; positive definite new directions alone do not imply nonzero target gain. Under not RH on an exhausting chain, the actual residual-weighted fractions
\[
\gamma_j=E_{Q_j}^{-1}\sum_i\frac{\lambda_{ji}}{1+\lambda_{ji}}
|\langle v_{ji},e_{Q_j}\rangle|^2
\]
are summable. No actual spectral-mass lower bounds \(\theta_j,\alpha_j\) can satisfy
\(\sum_j\theta_j\alpha_j/(1+\alpha_j)=\infty\). The full weighted covariance, including signed off-diagonal terms, is unchanged by the truth value of RH.

Source: [S10] §§3–7.

### 14. Strict improvement forever does not conflict with not RH

The far-dilation note proves that every finite-stage periodic actual residual admits strict improvement from every sufficiently large binary dilation divisible by its period. Such improvements can coexist with not RH. Their normalized total is then summable; no uniform nonsummable rate follows.

For a fixed old period L and corrections activated only at n≥K, put
\[
A(L,K)=(L+1)/K+L(L+1)/K^2<1.
\]
Even allowing infinitely many such new columns, the maximum gain is at most
\(A(L,K)D(V)/(1-A(L,K))\). It tends to zero relative to D(V) as K/L→∞. This is unconditional and invalidates summing far-column gains as if independent.

The source gives an actual restricted family (initial binary and ternary seeds, additional indices m>6) with perpetual strict improvements but permanent error at least 1/42 because every legal member vanishes at coordinate 6. Omitting one prime ℓ from packet conductors likewise creates the unconditional floor 1/[2(ℓ²+1)]. These restricted-class obstructions are not evidence for not RH and do not apply to two seeds with all integer dilations.

Sources: [S14] §§6–8; [S10] §6.

### 15. Cesàro smoothing and shared-latent sampling do not erase the obstruction

Let \(q_t=2/[(t+1)(t+2)]\), \(J=\ell^2(q)\), and \((\mathsf CF)(t)=t^{-1}\sum_{n\le t}F(n)\). Under the model
\(P(T=t)=q_t\), \(K_i\mid T=t\) i.i.d. uniform on 1,…,t, every K_i has law w. For deterministic legal F,
\[
\mathbb E\left|r^{-1}\sum_{i=1}^rF(K_i)-1\right|^2
=r^{-1}\mathbb E\operatorname{Var}(F(K_1)\mid T)
+\|\mathsf CF-1\|_J^2.
\tag{C22}
\]
Define
\(b_\rho(n)=n[n^{-\rho}-2(n+1)^{-\rho}+(n+2)^{-\rho}]\),
\(D_\rho=\sum_n|b_\rho(n)|^2/q_n<\infty\).
It gives \(\Lambda_\rho(\mathsf CF)=0\), \(\Lambda_\rho(1)=1\). Hence under not RH,
\[
\|\mathsf CF-1\|_J^2\ge D_\rho^{-1}>0,
\]
and the same lower bound holds for the sample-average error for every row count. Averaging removes conditional variance only; it cannot remove latent conditional-mean bias.

Almost surely T is finite and is eventually recovered as the sample maximum. Every realized infinite exponent matrix has finitely many active prime columns, despite its full-support marginal. Prime columns within a row remain dependent. Conditional-i.i.d. rows, exchangeability of rows, positive Gram matrices such as log gcd, and law-of-large-numbers convergence all remain true under not RH.

Sources: [S15] §§2–6; [S16] §§2–4.

### 16. Smoothed exact-head energy has an exact positive zero-induced tail floor

For a balanced finite floor witness F with \(F(n)=1\) through Y, put \(M_n=\mathsf CF(n)\), \(E(F)=\sum_nq_nM_n^2\), and
\[
\kappa_n(s)=\frac{n[n^{-s}-2(n+1)^{-s}+(n+2)^{-s}]}{s(s+1)},
\quad h_Y(s)=\sum_{n\le Y}\kappa_n(s),
\quad K_Y(\rho)=\sum_{n>Y}|\kappa_n(\rho)|^2/q_n.
\]
Then
\[
E(F)-\frac{Y}{Y+2}\ge\frac{|h_Y(\rho)|^2}{K_Y(\rho)}
\sim\frac{2(2\sigma-1)}{|\rho(\rho+1)|^2}Y^{2\sigma-1}.
\tag{C23}
\]
A simple uniform version for all sufficiently large Y is
\[
E(F)-Y/(Y+2)\ge
\frac{2\sigma-1}{12|\rho(\rho+1)|^2}Y^{2\sigma-1}.
\]
For finitely many zeros, replace the scalar ratio by
\(\mathbf h_Y^*\mathbf K_Y^{-1}\mathbf h_Y\), with all mixed zero correlations retained. Every admissible tail splits orthogonally into this fixed zero-constrained component plus a removable component. All present and future legal gains are at most the removable component's energy. Thus under not RH, exhaustive multirange optimization leaves a positive tail floor at each sufficiently large fixed head and a polynomially growing floor as the head grows.

The multirange Schur identity still telescopes exactly. Its total gains cannot exhaust the initial tail, and no schedule reaches subpower total energy. A purported uniform fractional reduction of the entire remaining tail through arbitrarily many ranges is impossible for these heads.

Sources: [S17] §§5–6; [S18] §§6,9–10; [S19] §§10–12.

### 17. A fixed compact target already has a positive tail capacity

The later fixed-target formulation uses
\[
v=(1,1/4,0,\ldots),\qquad \|v\|_q^2=11/32,
\quad P(s)=(1-2^{-s})(1-2^{-s-1}).
\]
For finite real balanced b with b₁=1, b₂=−5/2, let
\(T_*(b)=\sum_{n\ge3}q_nM_n^2\). The source proves RH iff
\(\mathfrak T_*:=\inf_bT_*(b)=0\). Under not RH,
\[
\mathfrak T_*\ge
\frac{|P(\rho)|^2}{|\rho(\rho+1)|^2\sum_{n\ge3}|\kappa_n(\rho)|^2/q_n}>0,
\quad\inf_bE(b)>11/32.
\tag{C24}
\]
The finite-zero matrix strengthens this floor. All gain-exhaustion, zero-capacity, and signed-output convergence formulations of this fixed target therefore fail. It is a different finite optimization problem from a growing head fixed to 1.

The logarithmically tapered explicit family has an exact signed commutator output \(\mathcal C_L\), with T*→0 iff \(\|\mathcal C_{\log N}\|_2\to0\). Not RH prevents this vanishing. The proposed sufficient estimate
\(\mathcal A(N)=\sum_{d<N}(\beta_d^*)^2=o((\log N)^2)\)
must fail as well. It is stronger than RH alone: it would also imply simple zeros. Moreover \(\mathcal A(N)\to\infty\) and \(\mathcal A(N)\not=o(\log N)\) already hold unconditionally because of known critical-line zeros; these are not extra consequences exclusive to not RH.

Source: [S17] §§16,27–31.

### 18. Canonical residual reconstructions remain polynomially expensive after smoothing

For the actual residual r=b−P_Sb, define the finite Möbius-recovered legal reconstruction R_N(r) as in the source. It has prefix
\(R_N(k)=r(k)+k\lambda_N\) for k≤N, and the unconditional upper bound
\(\|R_N\|^2\le\|r\|^2N H_N^2(4+H_N)\).
Put \(\mathcal A_N=\|\mathsf CR_N\|_J^2\). Under a right-hand zero,
\[
\|\mathsf CR_N\|_J+\|\mathsf Cr\|_J\ge c_\rho N^{\sigma-1/2},
\quad\mathcal A_N\ge c'_\rho N^{2\sigma-1}
\]
eventually. Explicitly, one may take \(c_\rho=K_\rho^{-1}\), \(c'_\rho=(4K_\rho^2)^{-1}\), where \(K_\rho=\sqrt3|\rho(\rho+1)|[(1-\sigma)^{-1}+(2\sigma-1)^{-1/2}]\). Thus no bounded cofinal subsequence and no subpower cofinal bound exists. With N² shared-latent sample rows the sampling energy \(\mathcal S_N\) obeys
\[
0\le\mathcal S_N-\mathcal A_N
\le\|r\|^2 H_N^2(4+H_N)/N\to0.
\]
Sampling variance disappears while the arithmetic mean energy diverges. The corresponding critical-line Mellin integral of \(\zeta(s)P_N(s)/(s(s+1))\) has the same subpower obstruction through the source's norm comparison.

Source: [S16] §§1–5.

### 19. Schur error minimizers must have polynomially growing conditional covariance

For exact-head F_N, let \(L_N=\langle b,F_N\rangle\) and \(v_N=\operatorname{Var}(F_N\mid K>N)\). Exactly,
\[
\|1-F_N\|^2=(N+1)(L_N-1)^2+v_N/(N+1).
\tag{C25}
\]
For the actual finite-budget Schur error minimizers with at least the next canonical correction available,
\[
C_{N,M}:=v_N/(N+1)\le E_{N,M}\le(2/\log3)C_{N,M}.
\tag{C26}
\]
Consequently not RH forces, for every budget schedule M_N≥N+1,
\[
C_{N,M_N}\ge\frac{(2\sigma-1)\log3}{2|\rho|^2}(N+1)^{2\sigma-1}.
\tag{C27}
\]
The covariance cannot merely approach a positive constant: it diverges at a positive power. Even uniform boundedness along an unbounded subsequence would contradict not RH. For these minimizers, covariance vanishing alone would force the required mean rate; for arbitrary witnesses, mean and variance must both be controlled. Merely L_N→1 is insufficient.

Source: [S4] §§3,9–12.

### 20. Coefficients still stabilize, but not all Möbius limits can be correct

For projections \(P_Nb=\sum_{d=2}^Nc_{N,d}g_d\), every fixed coefficient converges unconditionally. Under not RH the limit differs from the Möbius target for at least one m≥2:
\[
c_{\infty,m}=-\mu(m)+\sum_{k\mid m}\mu(m/k)
[r_\infty(k)-r_\infty(k-1)],
\qquad\exists m:\ c_{\infty,m}\ne-\mu(m).
\tag{C28}
\]
The residual correction is bounded in modulus by C_m\(\|r_\infty\|\), with the explicit finite functional norm in the source. Not RH does not force failure of coefficient stabilization, does not identify which coefficient is wrong, and does not imply divergence of every coefficient. An infinite expansion using the stabilized coefficients is not established merely by coordinatewise coefficient convergence.

Source: [S20].

### 21. Ramanujan coordinates and exact mean repair survive; neither removes the signed obstruction

The cumulative Ramanujan atoms T_q give an invertible finite legal change of basis. Their *uniform-period* covariance is diagonal, \(\operatorname{Cov}_Q(T_p,T_q)=\mathbf1_{p=q}J_2(q)/12\), but their Pareto covariance is not diagonal. Under not RH the full Pareto approximation floor persists in every coordinate system. This does not force any failure of uniform CRT covariance, Ramanujan orthogonality under the uniform measure, or CRT itself.

A concrete legal dyadic family has uniform-period error 1/(k+1)→0 while its Pareto error tends to 1; that failure is unconditional. It rules out the inference that uniform-period approximation or profinite Haar convergence supplies the weighted criterion.

Likewise, delayed legal square waves \(H_A=2g_{2A}-g_A\) have period mean 1/2 and norm squared (log2)/A. Subtracting 2mH_A removes any prescribed period mean at arbitrarily small cost while preserving a fixed head. Thus unrestricted and zero-period-mean exact-head infima coincide even under not RH. Period mean is not a continuous functional in H or J; failure of RH cannot be attributed simply to a nonzero period mean.

Exact positive polygamma expansions give uniform relative enclosures of the full mean-zero energy, with all signed coefficients inside the square. Under not RH the enclosed optimum also violates subpower growth; positivity of the expansion does not force small energy. Enlarging the CRT period without changing the witness leaves its energy exactly unchanged.

Sources: [S21]; [S22] §§1–6 and appendix.

### 22. Conductor and multiplicative restrictions can fail independently of RH

The audit must not list the following as consequences exclusive to not RH:

- One seed has permanent Mellin obstructions on Re s=1 and linear head-energy cost, regardless of RH.
- A fixed finite supplement to the binary channel, a fixed finite dilation template, and certain canonical single-anchor completions cannot provide bounded growing-head energy.
- All-data stability on overly dense spectral grids is false; finite positive pivots are insufficient for uniform inverse control.
- The original uniform normalized Bessel estimate was refuted. A valid weighted adjacent-repair Bessel replacement exists; the refuted estimate must not reappear as an open RH-equivalent target.
- Restricted prime-only/contrast-only corrections can miss actual coordinates or charges. Missing one prime produces an explicit finite-coordinate separating vector.
- Every finite multiplicative balanced witness for the compact fixed target has the unconditional floor T*>4/15625. A certified nonmultiplicative support-64 witness beats that floor. Thus finite multiplicativity is too restrictive even if RH is true; prime-power convolution-log structure may emerge only in the limiting coefficients.
- Finite sets of zero ordinates have legal invisible corrections, and ordinary ordinate mean-square norms do not control the arithmetic energy. Finite sampling blindness is unconditional.
- The target harmonic-sum input is not square summable even under RH; cancellation in the zeta-multiplier output is essential.

Sources: [S1] §§1,6–8; [S3] §§5–6,15–18; [S13]; [S17] §§8–10,24,30; [S14] §8.

### 23. Route 6: exact signed prime-power covariance must diverge positively

Let \(\psi(x)=\sum_{n\le x}\Lambda(n)\), \(E(x)=\psi(x)-x\), and for s>1 set
\[
I_s(X)=\int_1^XE(x)^2x^{-s-1}dx,\quad B_s(X)=X^{-s}E(X)^2,
\quad D_s(X)=\sum_{2\le n\le X}\Lambda(n)^2n^{-s},
\]
\[
C_s(X)=\sum_{2\le n\le X}\Lambda(n)E(n-)n^{-s}
-\int_1^XE(x)x^{-s}dx.
\]
Exactly,
\[
sI_s(X)+B_s(X)=1+D_s(X)+2C_s(X),\qquad D_s(\infty)<\infty.
\tag{C29}
\]
A zero with real part σ>1/2 forces \(I_s(\infty)=\infty\) for every 1<s<2σ. Therefore
\[
C_s(X)\to+\infty\qquad(1<s<2\sigma).
\tag{C30}
\]
No eventual upper absorption estimate \(C_s(X)\le(s/2-\eta)I_s(X)+K\), η>0, can hold even on a cofinal set of X; the exact difference is at least ηI_s(X)−O(1). No cofinal C_s≤0 sequence exists for those s. Consequently the RH-equivalent criterion of cofinal nonpositive covariance for s_j↓1 fails.

For dyadic increments i_k,c_k and boundary b_k, every proposed inequality
\(c_k\le(s/2-\eta)i_k+a_k\) with nonnegative summable a_k must fail. The local condition also requires finite total boundary variation, which is an extra requirement and cannot simply be inferred from finite energy on one fixed mesh.

The exact discrete unit-cell version has D_n=ψ(n)−n(n+1)log(1+1/n), positive weights h_ε(n)=n^{-ε}/[n(n+1)], and increments
\(\delta_n=\Lambda(n)-1-q_n\) for n≥2, with q_n≥0 summable. It gives
\[
J_{\varepsilon,N}=A_{\varepsilon,N}+2M_{\varepsilon,N},
\quad A_{\varepsilon,N}\to A_\varepsilon<\infty.
\]
Under not RH, for 0<ε<2σ−1 the full energy J diverges, and hence the *signed mixed drift* M tends to +∞. Its diagonal stays finite. The absolutely valued Green double series already diverges unconditionally for 0<ε≤1; this is not a new failure caused by not RH.

The centered Selberg operator has quadratic form unbounded below on compactly supported unit vectors unconditionally, even far from the origin. Universal positivity is refuted, not an unproved property that would be forced to fail only under not RH. At a simple zeta zero the leading double poles in −L′+L² cancel irrespective of its real part; the Selberg identity alone yields no sign contradiction.

Sources: [S23] §§1–3,8–10; [S24] §§2–4.

### Source register

[S1] RH_After_Bessel_Bounded_Interpolation_2026-09-09.md.

[S2] RH_Subpolynomial_Legal_Energy_Continuation_20260911.md.

[S3] RH_Three_Steps_Exact_Interpolation_and_Energy_Obstructions_2026-09-14.md, current expanded version.

[S4] RH_Tail_Numerator_Expansion_and_Covariance_2026-09-19.md.

[S5] RH_False_Energy_Consequences_20260912.md.

[S6] RH_Canonical_Correlations_and_Spectral_Obstruction_Continued.md, including §§21–27.

[S7] RH_Candidate_5_Canonical_Tail_Attempt_2026-09-20.md.

[S8] RH_Dyadic_Two_Seed_Pareto_Residual_Gain_Work_Handoff_2026-09-18(1).md.

[S9] RH_Resonance_Blind_Directions_Exact_Continuation_2026-09-16(2).md.

[S10] RH_Controlled_Conductor_Schur_2026-09-10.md.

[S11] RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md.

[S12] RH_Source_Weighted_Spectral_Mass_2026-09-15.md.

[S13] RH_Diagonal_Boundary_Continuation_2026-09-14.md.

[S14] RH_Arithmetic_Improvement_and_Far_Dilation_2026-09-15.md.

[S15] Conditional_IID_Cesaro_Nyman_RH_Handoff_2026-09-16.md.

[S16] RH_IID_V_Ordinates_and_Affine_Bridge_2026-09-19.md.

[S17] RH_V_Mellin_Additive_Balance_and_Multiplicative_Obstruction_2026-09-19.md, full 2372-line version.

[S18] RH_Multi_Range_Divisor_Corrections_2026-09-18.md.

[S19] RH_Random_Prime_Powers_CRT_Multi_Range_2026-09-19.tex.

[S20] RH_Coefficient_Stabilization_Theorem_2026-09-18.md.

[S21] RH_Ramanujan_Legal_Basis_2026-09-18.md.

[S22] RH_Exact_CRT_Energy_Mean_Repair_2026-09-18.md.

[S23] RH_Route6_Covariance_Selberg_Continuation_2026-09-20.tex.

[S24] RH_Route6_Signed_Energy_Attempt_2026-09-20.tex.

Additional sources inspected: RH_Prime_Matrix_CRT_Complete_Chat_Handoff_2026-09-18.md; RH_Growing_Family_Construction_2026-09-18.md; RH_Conditional_IID_Research_Agenda_2026-09-18.md; RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md; earlier bounded-cancellation/prime-boundary/threshold notes retained locally for cross-checking but not independently restated where superseded.

### 24. Earlier four-channel amplification and inverse-free capture: a safe conditional reconstruction

The August 24–25 historical-context extract records a 4×4 combined Gram certificate, inverse-free overlap bound, amplification \(m|t|^2/[1+(m-1)\varrho]\), second-moment participation, and a joint capture/cross-flux product criterion. The full original definitions were not recovered in this subaudit, so their named G3 endpoint and arithmetic hypotheses must be labeled historical, not silently promoted to present theorems.

There is nevertheless a precise consequence in the shared projection setting that does not depend on those missing definitions. If r is the current residual, \(D=\|r\|^2\), z_i are any legal innovations, G is their Gram matrix and \(h_i=\langle z_i,r\rangle\), then
\[
\mathrm{gain}=h^*G^\dagger h\le D-D_\infty,
\qquad D_\infty>0\quad\text{under not RH}.
\]
The inverse-free Cauchy bound, when h≠0, is
\[
\frac{\|h\|_2^4}{h^*Gh}\le h^*G^\dagger h\le D-D_\infty.
\tag{C31}
\]
Thus any proven second-moment or participation estimates must respect
\(h^*Gh\ge\|h\|^4/(D-D_\infty)\). In a normalized equal-correlation design where the amplification lower bound is genuinely applicable, it follows that
\[
\frac{m|t|^2}{1+(m-1)\varrho}\le D-D_\infty.
\tag{C32}
\]
These statements do not identify which arithmetic ingredient must fail: sample correlations, Gram overlap, conductor realization, legal synthesis, and cofinal capture can compensate. What must fail is any conjunction that makes the accumulated normalized captures nonsummable or removes more than D−D∞.

The August 4 extract records a full-span reverse-Riccati target
\[
F_K-F_{2K}\ge cK F_{2K}^2,
\quad\mathcal E_K\le F_K-F_{2K},
\quad\mathcal E_K\ge cK F_{2K}^2.
\tag{C33}
\]
If, as in that historical formulation, F_K is the actual decreasing nonnegative approximation error with positive limit under not RH, C33 cannot persist for any fixed c>0: its left side tends to zero and its right side grows at least linearly. The source-specific marked-Gram realization and notation still need the original record before this is labeled more strongly than a historical target implication. Generic completed-Weil positivity does not imply that marked gain; source-null packets were already identified as counterexamples to that inference.

Additional historical cautions: August notes distinguish full exact-head/tail energy from the uncancellable fixed-taper head and impose an extra normalization rate on a prescribed taper. Failure of that extra normalization can occur for the taper alone. The late September unrestricted signed-tail criteria supersede claims that one fixed taper or a fixed finite-degree architecture is necessary for RH.

Historical evidence: recovered conversations of 24–25 August, 4 August, and 2 August 2026. C31 is a direct finite Gram consequence proved here; C32 is conditional on the stated design hypotheses; C33 is retained with its historical scope.


## Part IV. Probability, spectral coordinates, damping, and reflection

### Source index

- **PS1:** `RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md`, complete 413 lines.
- **PS2:** `RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`, complete 2726 lines. Parts III–IV correct and strengthen Parts I–II.
- **PS3:** `RH_Multiplicative_Random_Integers_Operator_Zeta_Handoff_2026-09-16_Advanced.md`, complete 1237 lines. The earlier handoff was also read.
- **PS4:** `RH_Source_Weighted_Spectral_Mass_2026-09-15.md`, complete 435 lines.
- **PS5:** `RH_Canonical_Correlations_and_Spectral_Obstruction_Continued.md`, complete 2006 lines. Sections 21–27 supersede weaker earlier weighted-density and growth targets.
- **PS6:** `RH_False_Energy_Consequences_20260912.md`, complete 648 lines; analytic Sections 1–6 supply the sharper constants.
- **PS7:** `RH_Pareto_Orthonormal_Bases_20260914_Continued.md`, complete 2549 lines.
- **PS8:** `RH_Ramanujan_Laguerre_Schur_Continuation_20260911.md`, complete 469 lines.
- **PS9:** `RH_Balkanova_Frolenkov_Reflection_Defect_20260911.md`, complete 521 lines.
- **PS10:** `RH_Total_Variance_Prime_Phase_Obstruction_and_Legal_Synthesis_2026-09-07.md`, complete 851 lines.
- **PS11:** `RH_Total_Variance_Geometric_Mixture_and_Hankel_Gap_2026-09-07(1).md`, complete 479 lines.
- **PS12:** `RH_Connes_Inverse_Repair_Advanced.md`, complete 2377 lines. Sections 23–31 materially alter the earlier open-status claims. The earlier handoff was also read.

### A. Fixed signed arithmetic energy and Hardy-space consequences

Use a distinct symbol \(p_i^*\) for the increasing prime powers, to avoid confusing them with the user's occupancy \(q_N\). Let
\[
I_i=[p_i^*,p_{i+1}^*),\quad
m_i=\frac{\log(p_{i+1}^*/p_i^*)}{(p_i^*)^{-1}-(p_{i+1}^*)^{-1}},\quad
c_i=\psi(p_i^*),\quad D_i=c_i-m_i.
\]
Put \(m=0\) on \([1,2)\), \(D=\psi-m\), \(G=m-x\), and \(E=\psi-x=D+G\). Set \(a_i=D_i-D_{i-1}\), with \(D_{-1}=0\). The critical accumulated energy and its damped versions are
\[
A(X)=\int_1^X |D(x)|^2x^{-2}\,dx,
\qquad K(\varepsilon)=\int_1^\infty|D(x)|^2x^{-2-\varepsilon}\,dx.
\]
PS1 supplies the geometric input \(G\in L^2(x^{-2}dx)\) from the cited classical prime-gap results. Thus finiteness of a damped energy of \(D\) and \(E\) is equivalent for positive damping.

Assume not RH, and choose a zero \(\rho=\beta+i\gamma\), \(1/2<\beta<1\), of multiplicity \(m_\rho\).

1. **Whole interval of infinite damped energies, including its endpoint:**
   \[
   \int_1^\infty |\psi(x)-x|^2x^{-s-1}\,dx
   =\int_1^\infty |D(x)|^2x^{-s-1}\,dx=+\infty
   \quad(1\le s\le2\beta).
   \]
   In particular \(K(\varepsilon)=\infty\) for every \(0<\varepsilon\le2\beta-1\). This is stronger than merely saying one damping fails. The boundary case follows from the nonzero residue and the energy point-evaluation bound; it is not omitted.

2. **Finite signed quadratic energies tend to infinity:** for each such \(s\),
   \[
   B_N(s)=\sum_{i<N}\frac{(p_i^*)^{-s}-(p_{i+1}^*)^{-s}}s\,|D_i|^2\uparrow\infty.
   \]
   The complete signed formula remains
   \[
   B_N(s)=\frac1s\sum_{j,k<N}a_j\overline{a_k}
   \bigl(\max(p_j^*,p_k^*)^{-s}-(p_N^*)^{-s}\bigr).
   \]
   It is this full expression, including terminal subtraction and cross terms, which diverges. Individual terms need not be positive.

3. **Critical energy cannot have subpolynomial growth:** there exists \(\delta>0\) such that
   \[
   \sup_{X\ge1}\frac{A(X)}{X^\delta}=\infty,
   \qquad
   \sup_N\frac{A(p_N^*)}{(p_N^*)^\delta}=\infty.
   \]
   More quantitatively, for every \(0<\delta<2\beta-1\), these suprema are infinite. If an \(O(X^\delta)\) bound held, choose \(\delta<\varepsilon\le2\beta-1\) in the exact identity
   \[
   K(\varepsilon)=\varepsilon\int_1^\infty A(X)X^{-1-\varepsilon}\,dX.
   \]
   The contradiction gives the stated range. This argument does **not** establish a lower bound \(A(X)\ge cX^\delta\) for every large \(X\), nor an endpoint non-O statement at \(\delta=2\beta-1\).

4. Consequently every logarithmic or polylogarithmic critical-energy upper bound, and every bound \(K(\varepsilon)=O(\varepsilon^{-r})\) valid for all sufficiently small positive \(\varepsilon\), fails. The issue is actual infinitude at positive damping, not just an excessive blow-up rate as damping tends to zero.

5. **Mellin obstruction with exact residue:** the filled-in meromorphic continuation
   \[
   M(z)=-\frac{\zeta'(z)}{z\zeta(z)}-\frac1{z-1},\qquad M(1)=-1-\gamma_{\rm Euler},
   \]
   has a genuine simple pole at \(\rho\), even when the zero has higher multiplicity, and
   \[
   \operatorname{Res}_{z=\rho}M(z)=-m_\rho/\rho\ne0.
   \]
   The continuation of \(\mathcal MD=M-\mathcal MG\) has the same residue, since \(\mathcal MG\) is holomorphic there. Thus the geometric correction cannot cancel the zero pole.

6. **Hardy membership and canonical correction convergence fail:** for \(1\le s\le2\beta\), neither initial arithmetic Mellin transform extends to an element of \(H^2(\Re z>s/2)\). The canonical finite corrections \(C_N=-D\mathbf1_{[1,p_N^*)}\) have
   \[
   \|C_N\|_{L^2(x^{-s-1})}^2=\|\mathcal MC_N\|_{H^2(\Re z>s/2)}^2=B_N(s)\to\infty.
   \]
   They are not Cauchy in those norms. No local uniform holomorphic limit on a domain containing \(\rho\), agreeing with the original Mellin transform, can exist. Do not infer failure of every possible local convergence on smaller pole-free domains.

7. **Not a discriminant:** the critical energy \(K(0)=\infty\) and the critical Hardy norm are already infinite even under RH, because zeros on or right of the critical line exist. A uniform bound down to zero damping was therefore an impossible target unconditionally; it must not be presented as something uniquely forced by not RH. Likewise \(B_N(1)\to\infty\) itself is unconditional; not RH supplies positive-damping divergence and failure of every subpolynomial bound.

### B. Universal energy cost of legal weighted-L1 approximation

Let \(H=\ell^2(w)\), \(w_n=1/[n(n+1)]\), and \(\mathcal V\) be the actual finite legal two-seed span. For any \(F\in\mathcal V\), set
\[
\epsilon=\|1-F\|_{L^1(w)},\quad Q(F)=\|F\|_H^2,\quad E(F)^2=\|1-F\|_H^2.
\]
For the same zero, write \(d=2\beta-1\), \(b=1-\beta\), \(c=|\rho|\), and
\[
P_\rho=\frac{2\beta-1}{1-\beta}>0,\qquad
C_\rho=\frac{2\beta d}{c^2}\left(\frac d c\right)^{P_\rho}>0.
\]
PS6, analytic Sections 2–4, proves by optimized clipping of the exact Mellin moment:

8. \(\epsilon>0\), and for \(0<\epsilon\le d/c\),
   \[
   E(F)^2\ge C_\rho\epsilon^{-P_\rho},\qquad
   Q(F)\ge C_\rho\epsilon^{-P_\rho}+1-2\epsilon.
   \]
   This controls the whole aggregate signed Gram energy, regardless of how its coefficients are decomposed.

9. For **every** legal family with \(\epsilon_n\to0\),
   \[
   Q(F_n)\to\infty,\qquad
   \liminf_n \epsilon_n^{P_\rho}Q(F_n)\ge C_\rho.
   \]
   No bounded subsequence exists. For every \(0<A<P_\rho\), \(Q(F_n)\epsilon_n^A\to\infty\). At \(A=P_\rho\), the liminf is positive rather than necessarily infinite.

10. Every squared-energy rate \(Q(F_n)=O(\epsilon_n^{-A})\) with \(A<P_\rho\), and every little-o rate at \(A=P_\rho\), fails. Equivalently a proved \(O(\epsilon^{-A})\) rate would exclude zeros with \(\Re\rho>(A+1)/(A+2)\); not RH need not rule out every fixed power rate, only those too small for its actual zeros.

11. If a known legal construction has \(\epsilon_N\le C/\log N\), then eventually \(Q(F_N)\ge c_\rho(\log N)^{P_\rho}\). In particular the desired \((\log N)^{o(1)}\) energy target fails. Stronger unconditional L1 accuracy rates give the corresponding stronger forced lower bounds by substituting the rate for \(\epsilon_N\).

12. L1 density remains valid. In fact PS5, Sections 23–26, proves density in weights \(w_n\exp(a(\log n)^\theta)\) for every \(a>0\), \(0<\theta<3/5\). Failure of RH therefore forces a failure of the **quadratic-energy upgrade**, not a failure of the proved weaker-norm convergence.

13. Every nonzero actual two-seed annihilator \(h\), including the canonical residual under not RH, satisfies
   \[
   \limsup_{n\to\infty}\frac{\log(1+|h(n)|)}{(\log n)^\theta}=\infty
   \quad\text{for each }0<\theta<3/5.
   \]
   Thus it is unbounded, is not \(O((1+\log n)^A)\) for any fixed \(A\), and is not \(O(\exp(a(\log n)^\theta))\) for any fixed \(a,\theta\) in this range. Earlier logarithmic and little-o endpoint obstructions are superseded by this. This does not prove a polynomial lower growth rate for the actual canonical residual.

### C. Source-weighted spectral mass and stable cutoffs

PS4 works with nested finite legal spaces \(V_N\) exhausting \(V\), each interpolating the first \(N\) coordinates. Put \(b=1\), \(b_N=Q_Nb\), and let \(P_N\) project onto \(V_N\). On the head let
\[
T_N=Q_NP_NQ_N,\quad T_Ne_{i,N}=\lambda_{i,N}e_{i,N},\quad
\nu_N=\sum_i|\langle b_N,e_{i,N}\rangle|^2\delta_{\lambda_{i,N}}.
\]
Every finite eigenvalue satisfies \(0<\lambda_{i,N}\le1\). Under not RH,
\(\delta=\operatorname{dist}(b,V)^2>0\).

14. **A persistent source-weighted atom at zero:**
   \[
   \nu_N\xrightarrow{w^*}\delta\,\delta_0+(1-\delta)\,\delta_1,
   \qquad \nu_N([0,\eta))\to\delta\quad(0<\eta<1).
   \]
   This is a limit statement about weights in the source direction, not the empirical eigenvalue distribution. It does not assert that all eigenvalues approach zero or count the dimension of the small-eigenvalue subspace.

15. Therefore \(\lambda_{\min}(T_N)\to0\), and for every \(a>0\),
   \[
   \int\lambda^{-a}\,d\nu_N(\lambda)\to\infty.
   \]
   The proof chooses a fixed small \(\eta\), uses \(\eta^{-a}\nu_N([0,\eta))\), and then lets \(\eta\downarrow0\). Similarly \(\int\log(1/\lambda)d\nu_N\to\infty\). These are direct additional consequences of the sourced measure limit.

16. The minimum norm for exact head matching in this particular finite budget diverges:
   \[
   \widehat E_N=\langle b_N,T_N^{-1}b_N\rangle\to\infty.
   \]
   Distinguish this from the unrestricted exact-head infimum. An arbitrary chosen budget can have excessive energy even under RH; the not-RH conclusion applies to every such cofinal budget, but the converse for a prescribed budget was never claimed.

17. **Leakage vanishes anyway:**
   \[
   L_N=\|(I-Q_N)P_Nb_N\|^2=\int\lambda(1-\lambda)d\nu_N\to0,
   \]
   while \(\int(1-\lambda)d\nu_N\to\delta>0\). Thus small tail leakage, spectral compactness, and endpoint concentration do not eliminate the defect.

18. For every fixed cutoff \(0<\eta<1\), the actual legal vectors
   \[
   h_{N,\eta}=\sum_{\lambda_{i,N}\ge\eta}
   \frac{\langle b_N,e_{i,N}\rangle}{\lambda_{i,N}}P_Ne_{i,N}
   \]
   satisfy \(h_{N,\eta}\to P_Vb\) strongly and
   \[
   \|b-h_{N,\eta}\|^2\to\delta>0,
   \qquad \|h_{N,\eta}\|^2\to1-\delta.
   \]
   Their uniform norm bound survives; omitted source mass, not blow-up of these cutoff vectors, is the obstruction.

19. For cofinal projections \(D_j=\|b-P_{V_j}b\|^2\downarrow\delta\), and innovation gains \(g_j=D_j-D_{j+1}\), the total available remaining gain is \(D_j-\delta\). Any lower bounds \(g_j\ge\kappa_jD_j\), \(0\le\kappa_j\le1\), must have \(\sum\kappa_j<\infty\). More exactly \(\sum g_j/D_j<\infty\), because \(D_j\ge\delta\) and \(\sum g_j=D_0-\delta\). This is the source-specific obstruction; a uniform gap on all vectors is neither needed nor implied.

### D. Orthonormal and Laguerre coordinates

20. In the Pareto tail-adapted basis of PS7, write the actual canonical residual as mean \(\mu=\|r\|^2>0\) and nonconstant coefficients \(b_k\). Its coordinates still obey
   \[
   \sum_{k\ge1}|b_k|^2=\mu-\mu^2,
   \quad r(n)=\mu-\sum_{j<n}b_j+nb_n.
   \]
   Under not RH, the cumulative coefficient tail condition must fail:
   \[
   \sum_{k\ge1}\frac{|\mu-\sum_{j<k}b_j|}{k}=\infty.
   \]
   Exact block correlations and both seed-annihilation equations continue to hold. Square-summable orthonormal coordinates are fully compatible with this divergence.

21. The explicit zero annihilator has particularly simple coefficients:
   \[
   h_\rho(n)=n(n+1)(n^{-\rho}-(n+1)^{-\rho}),\qquad
   c_k(h_\rho)=k^{1-\rho}-(k+1)^{1-\rho}.
   \]
   It remains a legitimate Hilbert vector, has mean 1, tail \(k^{-\rho}\), and grows in magnitude like \(|\rho|n^{1-\beta}\). Therefore orthonormalization does not remove the Mellin obstruction. The simultaneous adjoint-dilation eigenvalues are \(m^{1-\rho}\), in the normalization used in PS7.

22. **Exponential cost of Laguerre moment matching:** for a finite legal mean-one packet \(F\) whose Laguerre coefficients \(A_1,\ldots,A_K\) vanish, set
   \[
   z_\rho=1-1/\rho,\qquad r_\rho=|z_\rho|<1.
   \]
   Then PS8 proves
   \[
   \operatorname{Var}(F)\ge(1-r_\rho^2)r_\rho^{-2(K+1)}.
   \]
   It holds for every finite dilation range, not just the proposed \(M_K=2^K\) sequence. The explicit matrix minimum
   \[
   V_K=e_0^T(\mathsf A_KG_K^{-1}\mathsf A_K^T)^{-1}e_0-1
   \]
   therefore diverges at least exponentially under not RH, although the first numerical values decreased. Neither monotonicity nor a bounded variance conclusion follows from that finite table.

23. The generating function \(\mathcal A_F(z)=\sum A_k(F)z^k\) vanishes at \(z_\rho\) for every legal \(F\), while the target is the constant function 1. Factoring \(\mathcal A_F-1=z^{K+1}H\) gives \(H(z_\rho)=-z_\rho^{-K-1}\). This is the exact Hardy point-evaluation obstruction underlying the exponential bound.

24. Any purported family of legal errors with all successively matched Laguerre moments and uniformly bounded variance fails. The boundedness would permit a subsequence whose finite legal averages have variance at most \(B/m+4/m^2\to0\). The subsequence selection is essential; no claim about full ordinary Cesàro means follows from weak convergence alone.

### E. Conditional variance, the Hankel gap, and smoothing

In PS11, \(T\) is uniform on \((0,1)\) and \(N\mid T=t\) has the geometric law \((1-t)t^{n-1}\). This yields the same Pareto weights. Let \(A f=\mathbb E[f(N)\mid T]\), \(P=A^*A\), and
\[
\mathscr D(F)=\mathbb E\operatorname{Var}(F(N)\mid T),\qquad
\mathscr B(F)=\operatorname{Var}(\mathbb E[F(N)\mid T]).
\]
The published Hankel spectrum gives \(\operatorname{Spec}(P)=[0,\pi/4]\cup\{1\}\), with the constant eigenspace at 1, and the exact/uniform comparison
\[
\operatorname{Var}(F)=\mathscr D(F)+\mathscr B(F),\qquad
(1-\pi/4)\operatorname{Var}(F)\le\mathscr D(F)\le\operatorname{Var}(F).
\]

25. Under not RH, for every legal mean-one \(F\) in the relevant full closure with distance defect \(\delta>0\),
   \[
   \operatorname{Var}(F)\ge\frac\delta{1-\delta},\qquad
   \mathscr D(F)\ge(1-\pi/4)\frac\delta{1-\delta}>0.
   \]
   Thus neither conditional-variance optimization nor an exact digit-martingale decomposition can make this energy vanish. The spectral gap itself remains true under not RH.

26. In a nested full remainder basis, let \(H_{{\rm cond},N}\) be the actual conditional covariance and \(m_N\) its mean vector. Then the conditional capacity
   \[
   C_N^{\rm cond}=m_N^TH_{{\rm cond},N}^{-1}m_N
   \]
   cannot tend to infinity; it is increasing and bounded above by
   \[
   \frac{1-\delta}{(1-\pi/4)\delta}.
   \]
   Consequently its limit is finite. Here \(\delta\) is the distance defect for the full remainder closure. Restricted-family formulations were only sufficient unless a separate equivalence was supplied.

27. There is also an explicit zero-based conditional-energy floor from PS10. For \(q_\rho\) the conjugate-normalized zero annihilator with mean 1,
   \[
   \mathscr D(F)\ge
   \left[\sum_{j\ge0}\langle q_\rho-1,P^j(q_\rho-1)\rangle\right]^{-1}>0
   \]
   for every mean-one legal \(F\). The series is nonnegative and finite because the centered operator has norm \(\pi/4<1\). It is the exact dual denominator for the conditional metric.

28. **Even one smoothed seed stays outside the legal closure:** let \(W\) be the full remainder closure and \(g=PR_2\). PS10 proves
   \[
   g\in W\iff1\in W\iff\mathrm{RH}.
   \]
   Therefore \(\operatorname{dist}(g,W)>0\) under not RH. Quantitatively, for \(a=4\log2-2\), \(a_m=g(m-1)-g(m)>0\), and \(\alpha=\sum_{m\ge2}a_m/\sqrt m<a\),
   \[
   (a-\alpha)\operatorname{dist}(1,W)
   \le\operatorname{dist}(g,W)
   \le(a+\alpha)\operatorname{dist}(1,W).
   \]
   Thus the Markov smoothing has a universal variance contraction but does not preserve this legal closure on the seed under not RH. More generally every nonzero bounded nonnegative decreasing sequence lies outside \(W\), by PS10's norm-convergent inverse argument.

### F. Reflection identities: what necessarily fails, and what does not

PS9 retains the full Pareto covariance, cotangent weights, endpoint, and infinite tail. For an even period \(Q\), a legal mean-one packet satisfies
\[
\operatorname{Var}(F)=\mathcal A_Q(F)+\mathcal R_Q(F),\qquad
\frac{\pi^2}{6Q}U_Q(F)\le\mathcal R_Q(F)\le\frac{\pi^2}{2Q}U_Q(F),
\]
where \(U_Q\) is the uniform-period centered variance and \(\mathcal A_Q\) is the signed ordinary-head expression.

29. Under not RH, every such total variance is at least \(\delta/(1-\delta)>0\). Therefore no legal sequence can satisfy **both** \(\mathcal A_Q(F_Q)\to0\) and \(U_Q(F_Q)/Q\to0\). The disjunction is the correct contraposition; neither term individually is compelled to fail. The signed head may have either sign.

30. After optimizing actual mean-zero controls, the exact reflected covariance Schur expression is
\[
V(a)=a^TS_Ka-\frac{(a^Tu)^2}{1-\kappa},\qquad \kappa<1.
\]
For every nonzero signal mean \(a^Tm_X\), not RH forces
\[
\frac{V(a)}{(a^Tm_X)^2}\ge\frac\delta{1-\delta}.
\]
Thus the required normalized cancellation cannot be asymptotically complete. This does not imply separately that \(\kappa\to1\), \(u\) is unbounded, or either positive term diverges.

31. Reflection of a fixed witness, or replacing its common period by a larger multiple, cannot improve its actual error. The cotangent remainder can tend to zero merely because the period grows while the signed head tends to an unchanged positive variance. This phenomenon is unconditional and is not an independent contradiction under not RH.

### G. Fixed-width discrepancy, finite matrices, and layer-cake concentration

Part VI covers the completed Weil form's general spectral growth. The following refinements are unique to PS2's latest continuation.

Fix \(h=(\log2)/4\), let \(\phi_h(x)=(1-|x|/h)_+\), \(g_h=\phi_h*\widetilde\phi_h\), and define
\[
G_h(s)=h^2\left(\frac{\sinh(hs/2)}{hs/2}\right)^4,
\qquad m_h^2=G_h(1/2),
\]
\[
\mathcal E_h(x)=\sum_{p^k}\frac{\Lambda(p^k)}{p^{k/2}}g_h(x-\log p^k)-m_h^2e^{x/2}.
\]
The exact Laplace transform is
\[
\int_0^\infty e^{-sx}\mathcal E_h(x)dx
=-G_h(s)\frac{\zeta'}{\zeta}(s+1/2)-\frac{G_h(1/2)}{s-1/2}.
\]
The pole at \(s=1/2\) cancels; at \(s=\rho-1/2\) the residue is \(-m_\rho G_h(\rho-1/2)\ne0\), since all zeros of \(G_h\) lie on the imaginary axis.

32. **Two-sided unbounded excursions at every smaller exponent:** for every \(0\le a<\beta-1/2\),
   \[
   \limsup_{x\to\infty}e^{-ax}\mathcal E_h(x)=+\infty,
   \qquad
   \liminf_{x\to\infty}e^{-ax}\mathcal E_h(x)=-\infty.
   \]
   PS2's Landau argument proves that either one-sided \(O(e^{ax})\) bound would exclude this zero. Failure of a bound on a compact initial interval is impossible, so the unbounded excursions occur at arbitrarily large \(x\). This strengthens merely saying \(\mathcal E_h\) is unbounded. No endpoint claim at \(a=\beta-1/2\) is supplied by this argument.

33. Consequently neither upper nor lower polynomial bound \(\pm C(1+x)^A\) is possible for any fixed finite \(A\). In particular neither a finite upper bound nor a finite lower bound exists.

34. The completed form on just the two-hat family already detects the failure:
   \[
   f_x^+=\phi_h+\tau_x\phi_h,\qquad
   \mathcal Q[f_x^+]=2\mathcal Q[\phi_h]-2\mathcal E_h(x)-2\mathcal J_h(x),
   \]
   with bounded nonnegative \(\mathcal J_h\) for large \(x\), fixed \(\|f_x^+\|_2^2=4h/3\), and uniformly bounded positive reference energy \(\mathcal D[f_x^+]\). Thus arbitrarily negative values, exceeding every polynomial in separation, occur even in this one explicit family.

35. For PS2's nested exact hat matrices \(\mathsf W_j\), mass matrices \(\mathsf M_j\), and positive-energy matrices \(\mathsf D_j\), define
   \[
   \lambda_j=\inf_{c\ne0}\frac{c^*\mathsf W_jc}{c^*\mathsf M_jc},\qquad
   \mu_j=\inf_{c\ne0}\frac{c^*\mathsf W_jc}{c^*\mathsf D_jc}.
   \]
   Under not RH,
   \[
   \lambda_j\downarrow-\infty,\quad\mu_j\downarrow-\infty,\qquad
   \inf_j\frac{\lambda_j}{(1+j)^A}
   =\inf_j\frac{\mu_j}{(1+j)^A}=-\infty\quad(A\ge0).
   \]
   For fixed \(A\), the corresponding liminf is also \(-\infty\), since each finite prefix has finite values. A limit of these ratios to \(-\infty\) is **not** proved: the unscaled sequences are monotone, the scaled ones need not be.

36. Therefore for every \(C,A\ge0\) there are arbitrarily large \(j\) such that
   \[
   \mathsf W_j+C(1+j)^A\mathsf D_j\not\succeq0,
   \]
   and likewise with \(\mathsf M_j\). Every eventual polynomial-tolerance matrix certificate fails. Exact signed matrices, not entrywise magnitudes or an arbitrary discretization, are essential here.

37. Cofinal approximate positivity fails in both full and interior forms. There can be no \(L_j\to\infty\), \(\epsilon_j\to0\) with
   \[
   \mathcal Q_{L_j}[f]\ge-\epsilon_j\mathcal D[f]\quad\text{for every supported admissible }f.
   \]
   The same holds after omitting shifts longer than \(L_j-\Delta_j\), whenever \(L_j-\Delta_j\to\infty\), while keeping the same archimedean and pole terms. A single fixed negative test eventually survives every such truncation unchanged.

38. **Layer-cake concentration certificate must fail at all sufficiently large windows.** Use the corrected completed multiplier
   \[
   c_L(t)=a(t)+4\int_0^L\cosh(u/2)\cos(tu)du
   -2\sum_{\log q\le L}\frac{\Lambda(q)}{\sqrt q}\cos(t\log q),
   \]
   with \(a(t)=\Re\psi(1/4+it/2)-\log\pi\). For \(\tau>0\), let
   \(S_{L,s}=\{t:c_L(t)<\tau-s\}\) and
   \(\mathcal C_L(S)=\mathcal F_{I_L}^*1_S\mathcal F_{I_L}\).
   The sourced inequality is
   \[
   T_{c_L}\ge\tau I-\int_0^\infty\mathcal C_L(S_{L,s})ds.
   \]
   Fix a normalized compact negative Weil witness with value \(-\eta<0\). Once its support fits, it implies the stronger necessary inequality
   \[
   \int_0^\infty\|\mathcal C_L(S_{L,s})\|ds\ge\tau+\eta>\tau.
   \]
   Thus no cofinal family of the proposed strict \(<\tau\) certificates exists. This conclusion concerns concentration operators; a failure of ordinary one-point density or large-deviation estimates does not follow.

39. Unconditional sparse positivity and entrywise remainder estimates still hold. Their validity under not RH means the negative directions must use collective signed interactions outside the controlled sparse regime. It does not mean every individual entry becomes large or any finite-dimensional covariance loses positive semidefiniteness.

### H. Random Euler operators and Connes inverse repair: necessary exclusions

40. Independent prime exponents in the zeta law for \(\Re s>1\), its compound-Poisson representation, Euler factorization there, and theta/Tate continuation remain valid under not RH. They are structural identities, not positivity of the completed Weil form.

41. PS3's unbounded multiplication realization of the operator-valued Euler product on the infinite torus has full complex spectrum in its asserted strip, and its gauge-limit Hamiltonian is unitarily equivalent to the free operator. These facts hold without RH. Neither supplies a Hilbert–Pólya realization of the arithmetic zeros. The bounded-operator continuation barrier at \(\Re s=1\) is likewise unconditional.

42. In the zero-label realization, the involution \((\mathcal Rv)_\rho=v_{1-\bar\rho}\) is not the identity under not RH. An off-line reflected pair gives the indefinite block \(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\), with eigenvalues \(+1,-1\). Thus the exact arithmetic pairing \(\langle\mathcal Jf,\mathcal R\mathcal Jf\rangle\) cannot simply be declared a covariance norm. A Gaussian covariance construction using the full completed arithmetic form fails because a covariance must be positive semidefinite. Positive covariance for an altered independent-prime model does not identify it with that form.

43. PS12's latest continuation **proves** one broad p-free simultaneous repair with \(O(1)\) shell energy and \(O((\log q)^3)\) full unnormalized energy. It introduces primes beyond the old prime set and may require a common conductor with \(\log L=O(q2^{\pi(q)})\). Its mean tends to zero. Therefore not RH does not contradict this proved repair: dividing by the squared signal mean, preserving the old-prime support, enforcing the intended common-conductor budget, and supplying the final approximation bridge remain necessary. Do not list failure of the bare O(1) shell bound as a not-RH implication—it is already true in the broadened family.

44. The exact simultaneous-shell minimax formula survives:
   \[
   \min_c\max_j\{E_j+2c^Th_j+c^TG_jc\}
   =\max_{\lambda\in\Delta_J}
   \{E_\lambda-h_\lambda^TG_\lambda^\dagger h_\lambda\}.
   \]
   Any RH-sufficient common-predictor budget must fail in at least one **mixture of shell metrics**, after all original legality, normalization, conductor, and limiting hypotheses are imposed. It is invalid to infer failure of an individual-shell minimum: all vertices can pass while an interior mixture fails. It is also invalid to infer that this specific unfinished conjecture is necessary for RH when no bridge was proved for its restricted subfamily.

45. Closed old-prime legality requires the full valuation condition
   \(\Delta F(k)=\Delta F(l)\) whenever \(k_S=l_S\), not just the p-dilation relation. The source explicitly constructs a very small residual satisfying the weaker invariant and mean constraint that violates true old-prime admissibility. Small norm plus a necessary invariant cannot eliminate not RH without actual legal membership.

46. Canonical squarefree Euler resonance, failure of the inverse correction to remain in the old centered space, and global dyadic aliasing are **unconditional obstructions to specific methods**, not deductions unique to not RH. A two-prime polynomial correction removes exact one-prime periodicity but has no proved full signed energy bound. Its mixed-conductor subfamily is explicitly not identified with the full two-seed criterion allowing all integer dilations. Preserve that distinction in the exhaustive catalogue.

### Interpretation cautions

- Keep the occupancy \(q_N\), prime powers \(p_i^*\), closure defect \(\delta\), and critical arithmetic energy \(A(X)\) distinct.
- The two-seed older sources often proved only the implication to RH; later sources may supply the full equivalence. Every assertion above used only the direction needed: not RH forces a positive two-seed defect because density would imply RH.
- A nonzero defect supplies positive lower bounds for **all** legal mean-one witnesses. Failure of a proposed sufficient package must be stated as failure of the conjunction unless a quantitative lower bound singles out one member.
- Do not describe unconditional impossibilities (critical undamped bounded energy, individual near-conductor L2 repairs, exact positive-kernel frequency reproduction, small eigenvalues disappearing under mere compactness) as new consequences specific to not RH.
- PS2's completed pole term is indefinite rank two, not positive. Earlier layer-cake formulas must be read with the correction in its Section 21.
- PS9 has a typographical switch between `u` and `nu` in its Schur definition; the mathematically consistent vector is \(u=d_X-K_{XZ}K_{ZZ}^{-1}d_Z\).


## Part V. Joint zero constraints, complementary powers, and Mellin rigidity

This chapter records consequences that combine several historical strands. Sources: *RH_Combined_Obstruction_Matrix_and_Complementary_Powers_2026-09-21.md*, *RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md*, *RH_Disproof_Attempt_Uniform_Gap_and_Mellin_Mode_Obstruction_2026-09-21.md*, and *RH_Mellin_Upper_Estimate_Attempt_2026-09-21.md*. Their mathematical arguments were read directly; no verification-status assertion is used as a substitute for the argument.

#### J01. Every zero acts on the same arithmetic space

For \(\Re s>1/2\), define
\[
\mathcal Mf(s)=\sum_{n\ge1}f(n)m_s(n),\qquad
m_s(n)=\frac{n^{-s}-(n+1)^{-s}}s.
\]
It is the Mellin transform of the associated step function. Its exact generator identity is
\[
\mathcal Mg_d(s)=\frac{\zeta(s)}s(d^{-1}-d^{-s}).
\]
If \(\rho\) is a right-half-strip zero of multiplicity \(m\), every \(f\in S\) satisfies
\[
(\mathcal Mf)^{(j)}(\rho)=0\quad(0\le j<m).
\]
These are bounded linear functionals on \(H\). In particular, \(\mathcal M(P1)\) vanishes there, whereas
\[
(\mathcal Mr)^{(j)}(\rho)=\left(\frac{d}{ds}\right)^j\frac1s\Big|_{s=\rho}
=\frac{(-1)^j j!}{\rho^{j+1}}.
\]
The residual carries exactly the target's missed zero data, including multiplicity.

#### J02. A matrix obstruction with all cross terms

Choose any finite set \(F\) of zero-and-derivative observations, and let \(J_F\) be their joint evaluation map. Put \(G_F=J_FJ_F^*\). Then
\[
Q\succeq J_F^*G_F^\dagger J_F.
\]
The right side is the orthogonal projection onto the span of their representers. The Moore–Penrose inverse handles dependent observations. Enlarging the collection enlarges the projected subspace.

Taking all finite collections gives \(Q\succeq P_{\mathcal Z}\), where \(\mathcal Z\) is the closed span of every right-half-strip zero-derivative representer. **Equality is not supplied by the history:** completeness of zero modes inside the arithmetic annihilator is an additional theorem.

For ordinary evaluations the exact discrete Gram entries are
\[
(G_F)_{ij}=\sum_{n\ge1}\frac{m_{\rho_i}(n)\overline{m_{\rho_j}(n)}}{w_n},
\]
and
\[
G_F\preceq\left(\frac1{\rho_i+\overline{\rho_j}-1}\right)_{i,j}.
\]
The difference is a within-cell variance matrix. Replacing the discrete matrix by a continuous Cauchy bound can weaken the obstruction.

#### J03. Joint holes and defect correlations

For finitely many sites \(A\), let \(B_{F,A}\) have columns \(J_F\eta_n\). Then
\[
I-K_A\succeq B_{F,A}^*G_F^\dagger B_{F,A}.
\]
Consequently,
\[
\Pr(A\cap X=\varnothing)=\det(I-K_A)
\ge\det(B_{F,A}^*G_F^\dagger B_{F,A}).
\]
The determinant lower bound can be zero when rank is insufficient; the formula is not an assertion that every prescribed finite set can simultaneously be vacant with positive probability.

With \(a=J_F1\), \(b=J_Fe_1\),
\[
\begin{pmatrix}E&r(1)/2\\r(1)/2&\delta\end{pmatrix}
\succeq[a\ b]^*G_F^\dagger[a\ b].
\]
Thus the two defects are jointly constrained, not merely bounded one at a time. The canonical certificate satisfies
\[
J_Fz_*=-Cb,
\]
so
\[
(\mathcal Mz_*)^{(j)}(\rho)
=-C\left(\frac{d}{ds}\right)^j\frac{1-2^{-s}}s\Big|_{s=\rho}.
\]

#### J04. Exact-head matrix lower bounds

Let \(R_N\) delete the first \(N\) coordinates, \(u_N=\sum_{n\le N}e_n\), and
\[
a_{F,N}=J_Fu_N,\qquad G_{F,N}=J_FR_NJ_F^*.
\]
The full-norm exact-head minimum and the target-error minimum obey
\[
\mathcal A_N\ge\frac N{N+1}+a_{F,N}^*G_{F,N}^\dagger a_{F,N},
\qquad
\Delta_N\ge a^*G_{F,N}^\dagger a.
\]
For ordinary evaluations,
\[
(a_{F,N})_i=\frac{1-(N+1)^{-\rho_i}}{\rho_i},\qquad
(G_{F,N})_{ij}=\sum_{n>N}\frac{m_{\rho_i}(n)\overline{m_{\rho_j}(n)}}{w_n}.
\]
Taking the supremum over finite \(F\) gives the optimum under all zero constraints at each fixed \(N\). It does not by itself identify that optimum with the legal arithmetic optimum.

For the finite-constraint optimization interpretation, the prescribed vector must lie in the range of \(G_{F,N}\); otherwise its cost is \(+\infty\), not the displayed pseudoinverse quadratic form. Actual feasible legal heads automatically satisfy the range requirement.

#### J05. One zero gives two complementary powers

Fix \(\rho=\beta+i\gamma\), put \(p=2\beta-1\in(0,1)\), and set
\[
G_\rho=\sum_{n\ge1}|m_\rho(n)|^2/w_n,\qquad 0<G_\rho\le1/p.
\]
The exact discrete lower bound is
\[
h_n\ge\frac{|m_\rho(n)|^2}{w_nG_\rho},\qquad
\liminf_{n\to\infty}n^{2\beta}h_n\ge G_\rho^{-1}.
\]
Let \(W_N=\sum_{n\le N}nh_n\). Then
\[
\liminf_{N\to\infty}\frac{W_N}{N^{1-p}}
\ge\frac1{(1-p)G_\rho}>0.
\]
At the complementary exact-head scale,
\[
\mathcal A_N\ge\frac N{N+1}+
\frac p{|\rho|^2}(N+1)^p|1-(N+1)^{-\rho}|^2,
\qquad
\Delta_N\ge\frac p{|\rho|^2}(N+1)^p.
\]
Therefore
\[
\liminf_{N\to\infty}\frac{\mathcal A_NW_N}{N}
\ge\frac p{|\rho|^2(1-p)G_\rho}
\ge\frac{p^2}{|\rho|^2(1-p)}>0,
\]
and the same holds with \(\Delta_N\). These bounds hold for every actual right-half-strip zero, not just one selected zero.

More generally, for \(\alpha\ge p\),
\[
\sum_n n^\alpha h_n=\infty.
\]
At \(\alpha=p\), partial sums have liminf after division by \(\log N\) at least \(G_\rho^{-1}\). At \(\alpha>p\), division by \(N^{\alpha-p}\) gives liminf at least \(1/((\alpha-p)G_\rho)\). This is an expected weighted-hole assertion, not an almost-sure assertion of infinitely many holes.

#### J06. The same two defects are quantitatively comparable

The legal dilation \(D_2\) has norm \(2^{-1/2}\), and
\[
Qe_1=r-QD_2r.
\]
Thus
\[
(1-2^{-1/2})^2E\le\delta=\frac1{C+2}\le(1+2^{-1/2})^2E.
\]
Moreover
\[
\frac{r(1)}2=E-\langle r,D_2r\rangle,\qquad
(2-\sqrt2)E\le r(1)\le(2+\sqrt2)E.
\]
Both use the actual common projection and hence cannot be bypassed by choosing unrelated residuals and certificates.

#### J07. A zero supplies an explicit finite-energy certificate, but an arbitrary parameter does not

For \(1/2<\Re s<1\), put
\[
u_s(n)=n(n+1)(n^{-s}-(n+1)^{-s}),\qquad
z_s=2e_1-\frac{u_s}{1-2^{-s}}.
\]
It has finite \(H\)-energy and vanishing first coordinate. Its primitive for \(n\ge2\) is
\[
\sum_{k\ge n}w_kz_s(k)=-\frac{n^{-s}}{1-2^{-s}}.
\]
The exact arithmetic defect is
\[
\sum_nw_nz_s(n)g_d(n)=\frac1d-
\frac{(d^{-1}-d^{-s})\zeta(s)}{1-2^{-s}}.
\]
An actual off-line zero makes this a certificate. Arbitrary \(s\) meets several analytic tail conditions but misses the arithmetic equations. Finite energy and \(\ell^2\setminus\ell^1\) primitive alone do not prove the existence of an annihilator.

#### J08. Restrictions on representations of the nonzero annihilator

If a finite complex measure \(\mu\) on \([-T,T]\) produces
\[
v(n)=\int u_{\sigma+it}(n)\,d\mu(t),\qquad1/2\le\sigma<1,
\]
and \(v\) annihilates every \(g_d\), then
\[
\zeta(\sigma+it)\,d\mu(t)=0.
\]
Thus the measure is supported on actual zeros in that finite segment, and the mixture reduces to a finite zero-mode sum. The proof uses the exponentially dense zero set \(\{\log d\}\) of an entire function of exponential type; such a nonzero function can have only \(O(R)\) zeros in a radius-\(R\) disk.

On the critical line a nonzero finite sum has
\[
\sum_{n\le N}w_n|v(n)|^2
=\left(\sum_j|a_js_j|^2\right)\log N+O(1),\qquad s_j=1/2+i\gamma_j.
\]
It therefore cannot be the finite-energy nonzero annihilator required by not RH.

For a countable critical-line mixture with distinct ordinates and \(\sum_j|a_js_j|<\infty\),
\[
\lim_{N\to\infty}\frac1{\log N}\sum_{n\le N}w_n|v(n)|^2
=\sum_j|a_js_j|^2.
\]
Again a nonzero mixture has infinite energy. The remainder is only \(o(\log N)\) in this countable case. Unbounded-frequency continuous mixtures and conditionally convergent expansions are not excluded by these statements.

#### J09. Damped Möbius and reflected boundary approximants must miss legality or Hilbert membership

The damped Möbius series in the saved Mellin estimate has transform
\[
\frac{\zeta(s)}s\left(\frac1{\zeta(s+\varepsilon)}-
\frac1{\zeta(1+\varepsilon)}\right).
\]
For sufficiently small positive \(\varepsilon\), an off-line zero \(\rho\) yields a genuine pole at \(\rho-\varepsilon\) in \(\Re s>1/2\). Hence the actual damped candidate cannot then belong to \(H\). Its pointwise convergence to one does not become Hilbert convergence.

The reflection-based boundary candidate
\[
B_\varepsilon(s)=\frac{\zeta(s-\varepsilon)}{(s-\varepsilon)\zeta(s+\varepsilon)}
\]
converges on the critical-line boundary in \(L^2\) to \(1/s\), after the harmless stated pole correction as well. This remains compatible with not RH: the meromorphic formula has the extra pole \(\rho-\varepsilon\), so it is not the requisite holomorphic Hardy transform. Boundary convergence does not supply legal arithmetic approximants.

#### J10. The one-gap formulation is exact

Let
\[
\varepsilon_*=
\inf_{\substack{c\text{ finite}\\\sum c_d/d=1}}
\sum_{n\ge2}w_n\left|\sum_dc_dg_d(n)\right|^2.
\]
Then not RH is equivalent to \(\varepsilon_*>0\), with \(\varepsilon_*=1/C\). Equivalently there is a fixed \(\varepsilon>0\) such that for **every** finite complex coefficient family,
\[
\sum_{n\ge2}w_n\left|\sum_dc_dg_d(n)\right|^2
\ge\varepsilon\left|\sum_dc_d/d\right|^2.
\]
If \(z_M\) is the canonical certificate for the first \(M\) observations, then
\[
\|z_M-z_L\|^2=C_M-C_L\quad(M\ge L).
\]
Under not RH, \(C_M\uparrow C<\infty\), so \(z_M\to z_*\) strongly and \(\|z_*-z_M\|^2=C-C_M\). The finite-certificate compactness issue is completely settled once the uniform bound is given; obtaining that bound unconditionally would itself disprove RH.

#### J11. Finite-stage tail mass does not distinguish the two possibilities

For every fixed finite generator stage, periodicity gives
\[
K_L(n,n)=O_L(n^{-2}),\qquad
\sum_{n\le R}n(1-K_L(n,n))=\frac{R(R+1)}2-O_L(\log R).
\]
This happens whether RH is true or false. The infinite-generator limit must precede any use of weighted vacancy as an RH criterion. Likewise finite \(C_L\) gives a lower bound on limiting capacity but only an upper bound on the unknown positive-gap candidate \(1/C\).


## Part VI. Earlier Weil, spectral, geometric, and prime-cover programs

### Source ledger

- **O1**, *off_line_zero_identifier.tex*, 29 June 2026. Full read.
- **O2**, *gns_spectral_triples_pick_boundary_selfcontained.tex*, 6 July 2026. Full read.
- **O3**, *weil_kms_corner_note.tex*, 9 July 2026. Full read.
- **O4**, *spectral_triples_master_addendum.tex*, 2 August 2026. Full read. This is the corrected determinant/RC audit.
- **O5**, *combined_audited_manuscript.tex*, 2 August 2026. Relevant Riesz, prime-cover, NB/CRT, Selberg, Li, and correction sections read. The source calls its assertions proved/classical-equivalent/conditional/open/false; those distinctions are retained.
- **O6**, *RH_Weil_Signed_Bounds_Continuation_2026-09-16.md*. Full read, including Theorems 19–34 and both continuations. Strongest spectral statements below were proof-audited rather than accepted merely from status labels.
- **O7**, *rh_master_g86_g92_audited_synergy.tex*, 4 August 2026. Full read.
- **O8**, *rh_cross_route_synergy_audited.tex*, 4 August 2026. Full read.
- **O9**, *rh_master_audit_cross_route_synthesis_2026-08-02.tex*. Full read.
- **O10**, *synergistic_rh_transporter_desieving_note.md*, updated 11 August 2026. Full read.
- **O11**, *section6_weighted_compactness_rh_audit.tex*, 14 August 2026. Full read. Corrects O10's net-level compactness and normalization.
- **O12**, *crt_nyman_beurling(13).tex*, version 10, 21 July 2026. Relevant scope, atom reuse, Green, dyadic, smooth-gap and legality sections read.
- **O13**, *CRT_Ramanujan_sure_certificate_audit_2026-07-24.tex*. Relevant exact Schur, Mellin, correction, numerical and conjecture sections read.
- **O14**, *crt_nyman_beurling_updated.tex*, 18 July 2026. Pair obstruction, exact-head and scope sections read.
- **O15**, *rh_euler_archimedean_step.md*; *rh_program_adversarial_audit.md*. Full read.
- Root historical retrieval: 9 July CWK/Herglotz corrections; 18 July hard Möbius/pair corrections; 21 July smooth-gap/atom reuse corrections; 24 July affine-tail retraction. These are history evidence, distinguished from mathematical files.

Throughout write a hypothetical off-line zero as \(\rho=\beta+i\gamma\), with \(1/2<\beta<1\), obtained by functional-equation reflection if necessary. Let \(\delta=\operatorname{dist}(1,\overline{\mathcal N})^2>0\) in the standard normalized NB Hilbert space. The standard Mellin witness gives \(\delta\ge (2\beta-1)/|\rho|^2\) in its continuous normalization. Do not transfer this constant to a differently scaled discrete target without its normalization factor.

### A. Off-line identifier and analytic geometry

1. Some centered zero \(z_\rho=(\rho-1/2)/i=\gamma+i(1/2-\beta)\) is nonreal. The analytic symmetry orbit \(\{\rho,\bar\rho,1-\rho,1-\bar\rho\}\) has four distinct elements; on-line orbits have two. Their multiplicities agree. This does not refer to algebraic Galois conjugacy. [O1,O5]
2. The locally finite signed measure
   \[
   \omega_\zeta=\sum_\rho m_\rho(\delta_{z_\rho}-\delta_{\Im\rho})
   \]
   is nonzero. There is a compact disk disjoint from the real axis on which it has positive mass. [O1]
3. For **every** strip width \(a>1/2\), there exists an even holomorphic strip-Schwartz test \(G\in\mathscr S_a^{ev}\) such that
   \[
   \Omega(G)=\sum_\rho m_\rho[G(z_\rho)-G(\Im\rho)]\ne0.
   \]
   The sums converge absolutely. The document supplies an explicit finite-interpolation Gaussian separation argument. [O1]
4. Thus for some such \(G\), the following precise prime/zero-counting identity fails:
   \[
   2G(i/2)=\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\widehat G(\log n)
       +2\int_0^\infty G(t)\,dS(t).
   \]
   Its difference is exactly \(\Omega(G)\), not an unknown remainder. Here \(S=N-1-\theta/\pi\) with the specified right-continuous convention. [O1]
5. The usual explicit formula itself does **not** fail. It includes full complex zero coordinates. Replacing them by ordinates is what loses the off-line identifier. [O1]

### B. Pick, Herglotz, de Branges and RC determinant obstruction

Let \(\Xi(z)=\xi(1/2+iz)\), \(G_\Xi=-\Xi'/\Xi\), and
\(\Theta=\sup_\rho(\Re\rho-1/2)=\sup_\rho|\Re\rho-1/2|>0\).

6. \(G_\Xi\) cannot be a global real-axis Pick/Nevanlinna logarithmic derivative: it has a nonreal pole of nonzero integer residue. [O2]
7. The exact attainable shifted Pick boundary is \(\Im z=-\Theta\). More precisely, Pick positivity relative to \(\Im z=-\eta\) holds iff every zero obeys \(\Re\rho\le1/2+\eta\), hence iff \(\eta\ge\Theta\). Every \(\eta<\Theta\) fails. [O2]
8. Consequently no sequence of valid Pick-positive boundary lines \(\eta_j\downarrow0\) exists. Every such proposed sequence eventually enters a forbidden boundary level; a single zero with displacement \(\beta-1/2\) forbids every \(\eta<\beta-1/2\). [O2]
9. At a forbidden boundary level, some finite Pick test fails (or encounters the interior pole); checking every finite subset of any fixed dense test set would detect the obstruction. In O2's normalization,
   \[
   K_\eta(z,w)=\frac{G_\Xi(z)-\overline{G_\Xi(w)}}{z-\bar w+2i\eta}
   \]
   cannot be positive semidefinite on all finite sets in \(\Im z<-\eta\). [O2]
10. No nonzero locally uniform limit of real-rooted entire determinants on the whole relevant complex domain can equal \(\Xi\). A disk around one nonreal zero, disjoint from \(\mathbb R\), gives a direct Rouché/Hurwitz obstruction. [O3,O4]
11. The **conjunction** of self-adjoint finite determinants, correct normalized Euler-half-plane convergence, and uniform Riemann–Cartwright control fails along every cofinal subsequence. The RC conditions are real spectra, a uniform origin gap, \(N_j(T)\le CT\log(2+T)\), and controlled genus-one affine normalization. The corrected O4 derives the needed normality using the basepoint \(C^1\) fit. [O4]
12. Equivalently, no RC-spectralizing cofinal subsequence can have the source's nonnegative fitting errors \(\varepsilon^{RC}_{j_\ell}\to0\). For a fixed correctly defined error sequence/class, \(\liminf_j\varepsilon_j^{RC}>0\) (allowing \(+\infty\)); otherwise a subsequence tending to zero would exist. This is a fit obstruction **within that constrained class**, not a universal numerical lower constant across all different constructions. [O3,O4]
13. The RC spectral tails need not individually fail. They satisfy
   \[
   \sum_{\gamma\in\Gamma_j,\ |\gamma|>R}\gamma^{-2}
      \ll \log(2R)/R
   \]
   whenever the stipulated counting bound holds. Under not RH, one cannot simultaneously retain those bounds, self-adjointness and identify the determinant limit with \(\Xi\). [O4]
14. If the exact normalized factorization
   \[
   (D_j-z)(D_j-z_*)^{-1}=L_j(z)(I+\mathcal M_j(z)),
   \qquad \det L_j=F_j(z)/F_j(z_*)
   \]
   and the RC/self-adjoint hypotheses are established, then
   \[
   \sup_{z\in K}\|\mathcal M_j(z)\|_1\not\longrightarrow0
   \]
   for at least one compact \(K\) in the Euler half-plane. Trace-norm-small determinant defects are ruled out as a complete package. [O4]
15. A zero-independent positive polarized cohomological realization with the correct zeta spectrum and adjoint relation \(\Theta_{\mathrm{op}}^*=I-\Theta_{\mathrm{op}}\) cannot exist. If all non-positivity/identification hypotheses are independently secured, positive definiteness must fail. Functional-equation symmetry alone can still give an indefinite/Krein polarization. [O4]
16. Weighted resolvent fits with arbitrary signed/complex coefficient observables may still converge in the Euler half-plane. They are not unit-residue self-adjoint determinant fits. Not RH does not refute their existence. [O2]
17. Raw LC/CWK Pick positivity and the old strict Cartwright claim were already retracted in history. Strict Cartwright/exponential-type counting \(O(T)\) is incompatible with \(N_\Xi(T)\asymp T\log T\), regardless of RH. The raw \(m_j^{LC}\) one-point test had imaginary part \(\le-\vartheta(x_j)\sim-x_j\). These are unconditional route failures, not distinctive consequences of not RH.

### C. Completed Weil form: strong quantitative spectral consequences

Use exactly the pole-neutral test class
\[
\mathscr D_0=\{g\in C_c^\infty(\mathbb R):G_g(1/2)=G_g(-1/2)=0\},
\quad G_g(z)=\int g(u)e^{zu}\,du,
\]
and \(C_g(v)=\int g(u)\overline{g(u-v)}\,du\). Put
\[
a(t)=-\log\pi+\Re\psi(1/4+it/2),\quad
a_0=-\log\pi-\gamma_E-\pi/2-3\log2,
\quad K(v)=\frac{e^{-v/2}}{1-e^{-2v}}.
\]
The exact signed form and its positive reference energy are
\[
Q(g)=\mathcal A(g)-2\Re\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}C_g(\log n),
\quad
\mathcal A(g)=\frac1{2\pi}\int a(t)|\widehat g(t)|^2dt,
\]
\[
\mathcal E(g)=\mathcal A(g)+(1-a_0)\|g\|_2^2
=\|g\|_2^2+\int_0^\infty K(v)\|g-T_vg\|_2^2dv.
\]
Every mixed term and both exponential moments remain. For support length \(L\), only \(n\le e^L\) occur, exactly. [O6]

18. There is an admissible \(g\) with \(Q(g)<0\): completed Weil positivity fails. This concerns the complete form, including archimedean and polar normalization, not finite primes in isolation.
19. More strongly, for **every** \(C<\infty\), there is \(g\in\mathscr D_0\) with
   \(Q(g)<-C\|g\|_2^2\).
20. For **every fixed** nonnegative integer \(m\) and every \(C<\infty\), there is \(g\in\mathscr D_0\) with
   \(Q(g)<-C\|g\|_{H^m}^2\).
   Thus no support-independent lower bound with any fixed finite Sobolev loss survives.
21. The signed prime correlation necessarily defeats every proposed global archimedean allowance:
   \[
   \forall C<\infty\ \exists g\in\mathscr D_0:
   2\Re\sum_n\Lambda(n)n^{-1/2}C_g(\log n)>
   \mathcal A(g)+C\|g\|_2^2,
   \]
   and analogously with a fixed Sobolev norm.
22. Let \(\mathscr D_{0,L}\) have support in \(I_L=(-L/2,L/2)\), and
   \[
   \lambda(L)=\inf_{g\ne0}\frac{Q(g)}{\|g\|_2^2}.
   \]
   Then \(\lambda(L)\) is nonincreasing and \(\lambda(L)\to-\infty\). A bounded negative defect is impossible.
23. Nevertheless **each fixed window** still has a densely defined closed semibounded form with compact resolvent and only finitely many negative eigenvalues. Not RH forces worsening bottom eigenvalues as the window grows; it does not by itself force infinitely many negative eigenvalues in any one fixed window.
24. Let \(B_L\ge I\) be the reference-energy operator and
   \[
   V_L=(1-a_0)I+\sum_{n\le e^L}\frac{\Lambda(n)}{\sqrt n}
      J_L^*(T_{\log n}+T_{-\log n})J_L,
   \quad
   \mathcal K_L=B_L^{-1/2}V_LB_L^{-1/2}.
   \]
   The extension/compression \(J_L^*\) includes projection onto the two-moment subspace. \(\mathcal K_L\) remains compact self-adjoint.
25. Its **top spectral value** \(\kappa(L)=\sup\operatorname{Spec}\mathcal K_L\) is nondecreasing and tends to \(+\infty\). This is about the top spectrum, not merely operator norm; negative eigenvalues do not obstruct positivity of \(Q\).
26. The sharper exact growth law is
   \[
   \boxed{\limsup_{L\to\infty}\frac{\log(2+\kappa(L))}{L}=\Theta>0.}
   \]
   For every \(0<a<\Theta\),
   \(\limsup_{L\to\infty}e^{-aL}\kappa(L)=+\infty\).
   Conversely \(\kappa(L)\le1+C_\epsilon e^{(\Theta+\epsilon)L}\).
27. Thus every polynomial upper bound, every bound \(Ce^{\sqrt L}\), and every subexponential upper envelope fail. Precise negation: it is false that \(\forall\epsilon>0\exists C_\epsilon\forall L\ge1:\kappa(L)\le C_\epsilon e^{\epsilon L}\).
28. A proposed lower estimate
   \(Q(g)\ge-C_\epsilon e^{\epsilon L}\|g\|_{H^m}^2\)
   for every \(\epsilon>0\), all support lengths and all legal \(g\), fails for every fixed \(m\).

#### One universal test already detects the failure

Set \(\eta=1/128\), \(a_j=\eta2^{-j}\), let \(\phi\) be the density of the sum of independent uniforms on \([-a_j,a_j]\), and \(h=(D^2-1/4)\phi\). Then \(h\) is even smooth, supported in \([-\eta,\eta]\), satisfies both moments, and
\[
H(z)=G_h(z)=(z^2-1/4)\prod_{j\ge1}\frac{\sinh(a_jz)}{a_jz}.
\]
This transform is nonzero at every hypothetical off-line nontrivial \(\rho-1/2\). Let \(d=1/64,\ell=1/32\), \(q_0=Q(h)>0\), \(E_0=\mathcal E(h)>0\), and \(q(r)=\mathcal T(T_rC_h)\). [O6]

29. \(q(r)\) is real, even, and
   \[
   Q(h\pm T_rh)=2q_0\pm2q(r),\qquad
   q(r)=\sum_\rho m_\rho H(\rho-1/2)^2e^{r(\rho-1/2)}.
   \]
   The coefficients are **complex squares**, not modulus squares.
30. Its exact logarithmic growth exponent is
   \[
   \limsup_{r\to\infty}\frac{\log(2+|q(r)|)}r=\Theta.
   \]
   In particular, for any \(0<a<\Theta\), \(|q(r)|/e^{ar}\) is unbounded.
31. Therefore among the two legal tests \(h+T_rh\) and \(h-T_rh\), the lesser value \(2q_0-2|q(r)|\) becomes arbitrarily negative. Their \(L^2\) norms and every fixed Sobolev norm are constant for separated supports. This directly proves items 19–23 without relying solely on the distribution-semiboundedness argument.
32. Both two-translate tests cannot remain nonnegative for all \(r\); cannot share any constant lower bound; and cannot share lower bounds of all exponential rates \(e^{\epsilon r}\).
33. For \(r>d\), the exact arithmetic obstruction is
   \[
   q(r)=e(r)-\sum_{e^{r-d}\le n\le e^{r+d}}
       \frac{\Lambda(n)}{\sqrt n}C_h(\log n-r),
   \quad
   e(r)=-\sum_{j\ge1}e^{-(2j+1/2)r}H(2j+1/2)^2
          =O_h(e^{-5r/2}).
   \]
   Thus the **signed sum after summation**, in a fixed-width logarithmic prime-power window, must have positive exponential limsup growth; the decaying archimedean cross term cannot hide it.
34. Equivalently, the exact signed discrepancy integral
   \[
   S_h(r)=-\int_1^\infty(\Psi(x)-x)x^{-3/2}
   [C_h'(\log x-r)-\tfrac12C_h(\log x-r)]\,dx
   \]
   cannot have subexponential size. Its continuous main term vanishes exactly by the two moments; that cancellation remains true under not RH.
35. The Laplace transform of \(q\) has a genuine pole at each right off-line \(z_\rho=\rho-1/2\), residue \(m_\rho H(z_\rho)^2\ne0\). This is why smoothing cannot discard the obstruction.
36. The unconditional Vinogradov–Korobov bound still permits
   \[
   |q(r)|\ll_h\exp\{r/2-c_hr^{3/5}/(\log r)^{1/5}\}.
   \]
   Its logarithmic growth upper exponent is \(1/2\), so it is compatible with not RH and insufficient to contradict it.

#### Complete signed Schur complements

37. For \(F_{L,k}=kB_L-V_L\), choose \(P_N\) from eigenvectors of \(B_L\), and write
   \(A_{N,k}=P_NF_{L,k}P_N\),
   \(C_N=P_NV_L(I-P_N)\),
   \(D_{N,k}=(I-P_N)F_{L,k}(I-P_N)\).
   Whenever \(D_{N,k}>0\),
   \[
   \kappa(L)\le k\iff A_{N,k}-C_ND_{N,k}^{-1}C_N^*\succeq0.
   \]
38. Under not RH, for **every** positive subexponential threshold \(k(L)\), there are arbitrarily large \(L\) at which the complete Schur complement has a negative direction for **every** chosen \(N\) with positive complementary block. Increasing trial dimension cannot make the actual obstruction disappear while the exact Schur relation is retained.
39. A positive finite trial matrix \(A_{N,k}\) may still occur. Not RH may be witnessed in the complement correction. Deleting \(C_ND_{N,k}^{-1}C_N^*\) invalidates the claim.
40. The global zero-evaluation form \(Q(g)=\langle\mathcal Jg,\mathcal R\mathcal Jg\rangle\), where \(\mathcal R\) exchanges \(\rho\) and \(1-\bar\rho\), remains an exact indefinite representation. A positive covariance/GNS Hilbert realization of **that complete form on all legal tests** fails; arbitrary unrelated GNS spaces do not fail.

Proof audit for items 18–40: centered support length \(L\) gives the upper exponential factor \(e^{|\sigma|L}\), not \(e^{2|\sigma|L}\); local zero counting and subharmonic disk estimates bound \(\sum_\rho|G_g(\rho-1/2)|^2\) by \(C_\epsilon e^{(\Theta+\epsilon)L}\mathcal E(g)\). The lower bound uses the explicit universal \(H\), its noncanceling Laplace poles, and the unchanged reference-energy Rayleigh quotient. These are research-derived analytic theorems, not claims of independent publication.

### D. Prime-cover, Riesz and fermionic tails/rates

Define
\[
C(t)=\sum_{n\ge1}\mu(n)n^{-2}e^{-t/n^2},\quad
D(t)=\sum_{n\ge1}\mu(n)^2n^{-2}e^{-t/n^2},
\quad \beta(t)=C(t)/D(t).
\]
Here \(D(T^2)\sim3/(\pi^{3/2}T)\). [O5]

41. The Riesz bound \(C(t)=O_\epsilon(t^{-3/4+\epsilon})\) for **every** \(\epsilon>0\) fails. Its Mellin transform \(\Gamma(s)/\zeta(2-2s)\) has an uncanceled pole at \(s=(2-\rho)/2\).
42. More precisely, for a specified \(\beta>1/2\), \(C(t)\ne O(t^{-3/4+\epsilon})\) whenever \(0<\epsilon<(\beta-1/2)/2\); otherwise its Mellin integral would be holomorphic at that pole.
43. For \(X_t=\mu(A_t)\), with \(\Pr(A_t=n)=\mu(n)^2 n^{-2}e^{-t/n^2}/D(t)\), and the prime-cover sigma-field \(B_Q=A_t/(A_t,Q)\), the exact energies
   \(E_t(Q)=\|\mathbb E(X_t\mid B_Q)\|_2^2\)
   continue to decrease to \(|\beta(t)|^2\) as \(Q\) exhausts primes, at each fixed \(t\). The reverse martingale and total-variance telescope remain valid under not RH.
44. What fails is the **joint scale** rate. With \(Q_T=\prod_{p\le T^{2+\eta}}p\), fixed \(\eta>0\),
   \[
   |\beta(T^2)|^2\le E_{T^2}(Q_T)
     \le|\beta(T^2)|^2+O(T^{-1-\eta})
   \]
   remains true, but \(E_{T^2}(Q_T)=O_\epsilon(T^{-1+\epsilon})\) for every \(\epsilon>0\) fails.
45. For any specified off-line zero \(\beta>1/2\), the rate \(E_{T^2}(Q_T)=O(T^{-1+\epsilon})\) fails for every \(0<\epsilon<2\beta-1\). This follows by the sandwich and Mellin holomorphy, not by asserting a pointwise zero asymptotic.
46. The fermionic supertrace \(C(t)=\operatorname{Str}(e^{-2H}e^{-te^{-2H}})\) still exists and equals the same scalar. Not RH changes its required cancellation rate, not the trace identity.
47. The discrete counterpart
   \[
   c_k=\sum_n\frac{\mu(n)}{n^2}(1-n^{-2})^k,\quad
   d_k\sim\frac3{\pi^{3/2}\sqrt k},\quad \beta_k=c_k/d_k
   \]
   fails \(c_k=O_\epsilon(k^{-3/4+\epsilon})\) for all \(\epsilon>0\), equivalently fails the all-\(\epsilon\) normalized rate \(\beta_k=O_\epsilon(k^{-1/4+\epsilon})\). [classical discrete Riesz criterion recorded O5]

### E. CRT optimizer, common coefficients and mixed source amplitude

Let \(J_q=\sum_{m\mid q}\mu(q/m)r_m\), \(r_m(k)=k\bmod m\), \(\nu(k)=1/[k(k+1)]\), and
\[
Z_x=\sum_{p\le x}(\log p)J_p,\quad
H_x=\sum_{p\le x}(\log p)^2\asymp x\log x,
\]
\[
V_x(\mathcal M)=\inf_b\|Z_x-H_x-\sum_{q\in\mathcal M}b_qJ_q\|^2.
\]
All competitors are legal NB combinations. [O5,O9]

48. Under not RH,
   \[
   V_x(\mathcal M)\ge\delta H_x^2
   \]
   for every finite conductor family. Hence no cofinal choice can have \(V_x=o(H_x^2)\).
49. In particular \(V_x/(x^2\log x)\to+\infty\) uniformly over such choices, because its lower bound has order \(\delta\log x\). The target \(O(x^2\log x)\) is impossible even if conductors are unrestricted.
50. For any common-coefficient partition decomposition
   \[
   V_x=\sum_j\rho_{j,x}+\Gamma_x,
   \]
   the nonnegative local residual sum and optimizer-gluing penalty cannot **both** be \(O(x^2\log x)\). At least one is \(\ge\delta H_x^2/2\) at each scale. It is invalid to assert that each separately must fail.
51. If one of the two \(O(x^2\log x)\) estimates is independently proved, the other must carry the missing macroscopic residual. In particular perfect fits on each separate fiber can coexist with a large global common-coefficient penalty.
52. The exact graph Green/Schur decompositions of \(\Gamma_x\) remain true; their actual residualized signal cannot satisfy a joint energy estimate strong enough to make the global residual vanish. A direction-free bound is not interchangeable with an actual-signal estimate.
53. For the constrained dyadic optimizer \(F_K=(d^0_{2^K})^2\), not RH gives \(F_K\downarrow F_\infty\ge\delta>0\). Thus \(I_K=F_K-F_{2K}\to0\), and the normalized reverse-Riccati quotient obeys the stronger statement
   \[
   \frac{I_K}{K F_{2K}^2}\longrightarrow0.
   \]
54. Every legal fully residualized packet synthesis \(\mathcal A_K\) obeys
   \[
   b_K^*G_K^\dagger b_K\le I_K,\quad
   G_K=\mathcal A_K^*\mathcal A_K,\quad b_K=\mathcal A_K^*f_K.
   \]
   Consequently \(b_K^*G_K^\dagger b_K/(K F_{2K}^2)\to0\), for **every** such family, including perfectly capturing families.
55. Hence no eventual uniform lower sampling estimate \(b_K^*G_K^\dagger b_K\ge cK F_{2K}^2\) survives. Full packet capture alone can hold; the requisite amplitude cannot.
56. In the density-module normalization \(Y_K^*Y_K=F_{2K}^2 I\), \(\eta_K=F_{2K}^{-2}Y_K^*u_K\), the identity \(\Xi_K=F_{2K}^2\|\eta_K\|^2\le I_K\) implies \(\|\eta_K\|^2\to0\) under not RH **when these objects truly represent that actual optimizer window**. Thus a \(q_K\asymp K\) seed law cannot have nonzero fixed seed amplitude, nor centered coefficient energy \(\gg K\).
57. Strict Pick positivity, cyclicity, density Plancherel, KKT identities, or the number of available channels may all hold nevertheless. O7 constructs explicit abstract countermodels; they do not supply the missing mixed-source measure \(\sigma_{v,u}\) or its amplitude. A positive diagonal measure \(\mu_v\) does not enforce nonzero cross-Gram data.

### F. Atom reuse, tail dispersion, and regularized Pareto repair

In O12, \(P=P_x=\prod_{p\le x}p\), \(\mathcal F_x=\{n<P:(n,P)>x\}\), \(Y_n(r)=1_{n\le r<P}\), \(A_d=\sum_{(n,P)=d}Y_n\), and \(V_{\rm atom}\subset V_{\rm occ}\). The exact finite decomposition is
\[
\Delta_x^2=\omega_P(P)+q_x^{occ}+\mathcal A_x,\quad
\mathcal A_x=\operatorname{dist}(P_{\rm occ}C,V_{\rm atom})^2.
\]
O12's analytic occurrence estimate is
\(q_x^{occ}\ll(\log x)^{-2}+x^{-1/8}\), and \(\omega_P(P)=O(P^{-2})\).

58. The legal approximation error \(\Delta_x^2\ge\delta\) for every \(x\). Assuming the source's audited occurrence estimate, \(\liminf_{x\to\infty}\mathcal A_x\ge\delta>0\). Thus the obstruction persists in reusing a single coefficient across returns, after the independently reset occurrence error has disappeared.
59. The exact Green cost
   \[
   \mathcal A_x=\min_u(c^*-Bu)^*H_P(c^*-Bu),\quad
   (H_P)_{nm}=\sum_{r\ge\max(n,m)}^{P-1}\omega_P(r)
   \]
   stays bounded away from zero. Neither decreasing Green diagonals nor \(x^{o(1)}\) returns per atom imply its vanishing.
60. Because
   \[
   \mathcal A_x\le\kappa_0\inf_u\sum_j2^{-j}
      \Big(\sum_{n\in\mathcal F_x\cap[2^j,2^{j+1})}
       |c_n^*-u_{(n,P)}|\Big)^2,\quad
   \kappa_0=\frac{1+2^{-1/2}}{1-2^{-1/2}},
   \]
   the optimized dyadic \(\ell^1\)-dispersion sum has liminf at least \(\delta/\kappa_0\). No choice of shared atom coefficients makes that sum \(o(1)\).
61. Likewise
   \[
   \mathcal A_x\le(4+\zeta(2)/2)\inf_u\sum_{n\in\mathcal F_x}
           |c_n^*-u_{(n,P)}|^2
   \]
   forces a positive liminf for the optimized occurrence coefficient \(\ell^2\) mismatch, at least \(\delta/(4+\zeta(2)/2)\).
62. Any proposed collection of mesoscopic and far-shell estimates that jointly makes the dyadic dispersion sum vanish must fail as a package. It is not justified to select one particular shell range as the culprit without additional estimates.
63. In O13's growing-face moment-null correction,
   \[
   \Sigma_x=\inf_{r\in\mathcal N_x}\{\|n_x+\mathcal G_xr\|_\nu^2+\|r\|_T^2\}
   =\langle n_x,(I+\mathcal G_x\mathcal G_x^*)^{-1}n_x\rangle,
   \]
   the target \(\Sigma_x\ll x^2\log x\) fails. More precisely the reconstructed residual equals a legal approximant minus \(H_x\), so its first term is \(\ge\delta H_x^2\); hence \(\Sigma_x/(x^2\log x)\to\infty\).
64. Therefore no moment-null correction can simultaneously have CRT/Haar coefficient cost and fixed-origin Pareto residual \(O(x^2\log x)\). The exact ridge optimizer still exists uniquely; existence and formula do not bound its value.
65. The equivalent scalar Schur, weighted CRT, shorted packet, Pareto primitive and ridge versions all fail at that same sufficient scale. They are representations of one obstruction, not independent contradictions.

Important scope: O12 explicitly says its primorial exact-head/atom-reuse target is **sufficient**, not proved equivalent to RH. Squarefree primorials omit every prime square and are not divisibility-cofinal. This does not affect the contrapositive not RH => target fails.

### G. Li coefficients and conjugate-paired divergence

Let
\[
\lambda_n=\sum_{\Im\rho>0}2\Re[1-(1-1/\rho)^n],\quad
M_N=\max(1,|\lambda_1|,\dots,|\lambda_N|).
\]
The conjugate-paired series converges absolutely for each \(n\). [O5]

66. At least one Li coefficient is negative by the standard Li equivalence (and the stronger classical oscillation facts may be supplied separately).
67. Put \(r=\min_\rho|1-1/\rho|<1\), attained at finitely many distinct poles \(z_1,\dots,z_q\) of the Li generating function. There is \(r_2>r\) such that
   \[
   \lambda_n=-\sum_{j=1}^q m_jz_j^{-n}+O(r_2^{-n}).
   \]
68. Cancellations cannot make the whole finite consecutive block small:
   \[
   \max_{0\le k<q}|\lambda_{n+k}|\ge c\,r^{-n}
   \]
   for all sufficiently large \(n\), by a fixed Vandermonde inverse.
69. In particular \(M_N\ge c_1r^{-N}\) eventually, so
   \[
   \sum_{N=1}^\infty\frac1{M_N}<\infty.
   \]
   Every polynomial upper bound for this running maximum fails.
70. The exact but intentionally tautological defect
   \(D_0(T)=\sum_{0<\Im\rho\le T}|\bar\rho-(1-\rho)|^2\)
   is eventually bounded below by a positive number, hence
   \(\sum_{n\ge1}e^{-\alpha nD_0(n)}<\infty\) for every \(\alpha>0\).
71. In contrast, \(\sum_{0<\Im\rho\le T}(\rho+\bar\rho)=N(T)\to\infty\) remains true independently of RH. Raw divergence of conjugate sums or infinitely many zero orbits is not an RH distinction.

### H. Weighted compactness, transporters and geometric positivity packages

72. Under the exact CCM self-adjoint determinant/eigenvector hypotheses, the transported, correctly normalized ground states cannot converge to the \(\Xi\)-kernel in every exponentially weighted \(L^2_a\), \(a<1/2\). Such convergence gives locally uniform Mellin convergence and contradicts a nonreal zero. [O10,O11]
73. More sharply, if an off-line zero has centered imaginary displacement \(d=|\beta-1/2|\), convergence in a weight \(L^2_a\) with \(d<a<1/2\) already provides uniform transform convergence on a small disk about that zero, impossible for real-rooted determinants. Thus for every such admissible weight the particular normalized approximant family fails to converge to the target.
74. The full repaired package fails: weighted equicoercivity on **one common directed tail**; local distributional or countable Mellin uniqueness-set convergence; fixed closed normalization; exact determinant identity and real spectrum. One may not conclude that every ingredient fails.
75. If all spectral and local-identification hypotheses are established, some exponential-tail/Sobolev equicoercivity requirement must fail. If weighted equicoercivity and all spectral requirements are established, local identification or normalization must fail.
76. Exact finite Euler–Möbius inversion and coherent common gauges can still hold. The difficulty is the amplified boundary/cusp/resieving error. Algebraic inverse identities alone give no uniform cofinal bound.
77. The Selberg-to-Connes completed positivity package cannot hold: a criterion-determining test algebra, nonnegative geometric forms \(Q_j\), positive scaling factors \(a_j\), and exact full completed convergence \(a_jQ_j(T_jf)\to Q_W(f)\) for every test. Not RH supplies an \(f\) with negative target value, impossible as a limit of nonnegative numbers. [O5]
78. Therefore, **if** a claimed global geometric construction has genuine positivity, it must fail the full completed Weil identification/convergence on at least one admissible test; if identification and convergence are valid, positivity must fail.
79. Local finite-prime scattering positivity, compact Jacquet maps, asymptotic scalar Tate factors, and finite conductor identities may all remain correct. They do not by themselves constitute the missing completed global positive form.
80. Euler–Archimedean passivity with exact full Weil realization and a uniform cofinal closure fails as a package. The local one-state Blaschke/AR(1) identities can survive; there is no conclusion that local factors cease to be inner.

### I. Retractions and unconditional no-go results that must not be mislabeled as consequences special to not RH

- **Pair-only CRT** already has \(\operatorname{dist}(1,V_x^{(2)})^2\ge1/2604\), signal/noise \(\mathcal R_x^{(2)}\le2603\), and
  \(\operatorname{tr}S_x^{(2)}\ge\sum_{p\le x}(\log p)^2/2603\sim x\log x/2603\).
  The exact \(\mathcal L_{30}\) certificate was read in O14. Thus the old pair-only little-o trace target is false even if RH holds. History reported an erroneous broader fixed-degree certificate; do not promote that stale generalization. O13 separately proves a **single homogeneous conductor-degree** feasibility obstruction, which is a different statement.
- **Undamped full Boolean Möbius cube** satisfies \(\|\chi-F_Y\|_2^2\gg Y/(\log Y)^2\to\infty\) unconditionally. Damping/cofinal redesign is essential.
- **Hard exact-head Möbius truncations** were historically corrected as nonconvergent even on RH; do not list their failure as distinctive to not RH.
- **Affine-tail Pareto bound** was retracted as an established claim. O13's dramatic resonance table is finite double-precision evidence, explicitly not an infinite-subsequence proof. Only the CRT/Haar affine bound survives; the regularized growing-face target remains open.
- **Naive within-atom pseudorandomness**, worst-cut shortcuts and certain short-interval reduced-residue assertions are already false unconditionally. They cannot be inputs to a contradiction under not RH.
- **Absolute-value prime correlations** do not admit a support-independent reference-energy bound even if RH holds; O6 proves legal \(g_R\) with \(\mathcal E(g_R)\to1\) but \(\sum_n\Lambda(n)n^{-1/2}|C_{g_R}(\log n)|\to\infty\).
- **Individual signed prime forms** take both signs even on the pole-neutral class:
  \(B_p(h\pm T_{\log p}h)=\mp2(\log p)p^{-1/2}\|h\|^2\).
  Thus independent-positive-covariance interpretations of each original signed prime term are invalid regardless of RH.
- **Positive local Selberg scattering boundaries** require divergent diagonal terms; subtracting those terms yields an indefinite prime distribution. Positive summands cannot simply be summed and renormalized while preserving positivity.
- **The critical prime-jump Hamiltonian** has a canonical self-adjoint gauge limit unitarily equivalent to the free logarithmic-position operator. It does not give a discrete zeta-zero spectrum, regardless of RH. Its coordinate-core action diverges, even after scalar counterterms.
- **The operator-valued Euler multiplier** has no bounded continuation beyond \(\Re s>1\); its closed unbounded realization for \(1/2<\Re s\le1\) does not identify scalar zeta zeros. Trivial-character evaluation is not continuous in the Haar \(L^2\) norm.
- **Finite Hermitian spectral triples** exist without RH. Their axioms alone have no limiting zero-identification content.
- **The symmetric noncommuting pairwise formula for optimizer gluing** was false; use the exact common-coefficient norm/Schur/graph formula in O9.
- **Fixed-window positivity** is not full RH. O15 corrects the \(D=.9825\) certificate to the codimension-two moment-neutral subspace and corrects the polar Fourier sign to \(+2S_0^D\). Its \(D=1.2\) tiny Schur eigenvalues were numerical, not rigorous lower enclosures. A phrase about “odd-sector positivity alone” must retain a global-support theorem's quantifiers; no finite-support certificate is promoted here.
- **Fock transport** magnifies singular-value mismatch: \(\|\Gamma_{\le N}(C)\|=\max(1,s_{\max}(C)^N)\). This is an unconditional analytic cost, not itself forced by not RH. A successful determinant bridge needs the full scale-sensitive matching or a suitable relative quotient.
- **Prime torus density, CRT independence under Haar, finite quotient coverage, local variance identities and positive Gram matrices** need not fail when RH is false. They supply structure but not the required actual arithmetic source coupling.

### Audit interpretation

The older program contains many genuinely distinct manifestations of the same potential defect: nonreal logarithmic-derivative poles; failed positive completion; exponentially growing signed support-window spectrum; nonvanishing legal approximation distance; missed mixed-source amplitude; nonvanishing shared-coefficient atom-reuse cost; failed critical Riesz cancellation; and exponential Li growth. None clashes logically with the others. Their coexistence is exactly what a hypothetical off-line zero would enforce.

The strongest items here are 26, 30, 38, 49, 54, 58, 63, and 68–69. They go beyond simply negating a proposed sufficient inequality, but each retains the correct quantifiers and normalization.


### J. Additional May–August chat-history implications and cautions

The following material was recovered in historical searches dated May–June and August; where a precise model was not retrieved, this is explicitly a historical consequence/caveat, not a new theorem claimed from an unseen construction.

81. **Random integer expectation (9 June).** In the earlier random-integer construction with the proved identity \(\mathbb E\log X_x=\psi(x)\), not RH means that \(\mathbb E\log X_x-x\) cannot satisfy \(O(\sqrt x\log^2x)\). A centered CLT for \(\log X_x-\mathbb E\log X_x\) may still hold; it does not control the arithmetic drift.
82. **Compensated rational LIL (13 June).** If the exact decomposition \(\log R_x=\psi(x)-x+\text{centered noise}\) is retained, a zero-centered LIL cannot be deduced from the LIL for the centered noise alone. Any hypothesized pathwise cancellation theorem whose deterministic conclusion is the RH-scale prime error fails under not RH. The historical stronger-than-RH LIL proposal has extra hypotheses; not RH does not identify the behavior of an unspecified noise model.
83. **Möbius character/adjoint convergence (14 June).** The family of Dirichlet partial sums
    \(\sum_{n\le N}\mu(n)n^{-s}\)
    cannot converge locally uniformly throughout \(\Re s>1/2\) to a holomorphic reciprocal \(1/\zeta(s)\). At the off-line zero that reciprocal has a pole. Therefore any exactly equivalent adjoint-operator convergence on all \(\xi_s(n)=n^{-s}\) fails somewhere in that half-plane. Finite inversion identities remain valid.
84. **Radial versus phase data (26 June).** The zero \(\rho=\beta+i\gamma\) has \(|p^{-\rho}|=p^{-\beta}\ne p^{-1/2}\). Its phase still encodes only \(\gamma\). Two distinct primes give an injective exact real-ordinate phase map by irrationality of \(\log p/\log q\), independently of RH. Such injectivity, or fixed finite-prime phase equidistribution, does not identify \(\beta\) and need not fail under not RH.
85. **Formal V-factor (25 June; regularization unresolved).** The historical expression \(A_{p,m}=\mathrm{PV}\sum_\rho p^{m\rho}/\rho\) assigned poles \(z=p^{-\rho}\) and \(s=\rho+2\pi ik/\log p\). A right off-line zero would produce a radius \(p^{-\beta}<p^{-1/2}\) and a normalized mode \(p^{m(\beta-\sigma)}\) growing whenever \(\sigma<\beta\). Exact coefficient-limsup, uncanceled-pole and Hardy-space assertions must retain the analytic regularization/identification hypotheses; these were not recovered as a fully audited theorem here.
86. **Critical Stieltjes proposal (9 June).** There is a direct reliable consequence behind the historical notation: \(F(x)=\xi(1/2+\sqrt x)\) is entire in \(x\), by the evenness of \(\xi(1/2+z)\). An off-line zero gives a nonreal zero \(x_\rho=(\rho-1/2)^2\), so \(F'(x)/F(x)\) has a nonreal pole and cannot be a Stieltjes function with singularities confined to the nonpositive real axis. The old history conflated “Stieltjes” with ordinary complete monotonicity; the latter is weaker, so no standalone claim that a specific complete-monotonicity inequality must fail is made without its additional representation theorem. Ordinary Gibbs entropy monotonicity for real \(\sigma>1\) remains unconditional.
87. **Smoothed logarithmic autocorrelation (10 June).** Positivity of an ordinary autocorrelation's Fourier transform, \(\widehat\Phi=|\widehat r|^2|\sum_n(\log_*f)(n)n^{it}|^2\ge0\), survives not RH. If the chosen smoothed arithmetic family is proved criterion-determining for the completed Weil form, then not RH forces at least one negative completed evaluation \(W_\zeta(\Phi_{f,r})<0\); criterion-determining density cannot be omitted.
88. **Type-II/type-III operator-algebra speculation (28 June).** Historical claims assigned Radon–Nikodym ratios \(p^{1-2\beta}\), suggesting semifinite/type-II behavior only at \(\beta=1/2\) and type-III\(_1\) behavior off-line. A ratio-group calculation is not a full factor-type classification without the action, ergodicity, ratio set and measure-class hypotheses. These remain conditional/model-dependent historical proposals and must not be catalogued as proved consequences of not RH.
89. **Simplicity (29 June).** Not RH does not imply multiple zeros. A simple quartet off the line is compatible with every functional-equation symmetry.
90. **Prime-cover cutoff (2 August).** Historical lower bound \(E_{T^2}(Q(R))\gg T/(R\log R)\) shows a prime cutoff \(R=T^{\alpha+o(1)}\), \(\alpha<2\), is too short for the desired \(T^{-1+\epsilon}\) rate even on RH. This is an unconditional budget obstruction, not a special not-RH consequence.
91. **Branching/profinite and local geometric models (1–2 August).** Fixed-radius split–merge rejection floors, a noncompact infinite-rank branching remainder, and failed all-directions/fixed-degree approximation architectures were already unconditional no-go findings. Under not RH the exact global signed homotopy/Gram bound must fail, but the local rejection or Schatten obstruction must not be counted as additional evidence for not RH.
92. **Combined gain (24 August).** Four-channel Gram certificates, inverse-free overlap bounds and second-moment participation do not change the not-RH consequence in items 53–56: the gain of the **joint** legal residualized packet space is at most the full optimizer increment, so its RH-normalized amplitude tends to zero. Separately computed overlapping gains cannot be added without the common Gram matrix.


## Part VII. Classical analytic and arithmetic consequences

### Standing witness

Assume not RH. Fix a nontrivial zero

\[
\rho=\beta+i\gamma,\qquad \tfrac12<\beta<1,\quad \gamma>0,
\]

of multiplicity \(m\ge1\). Such a choice follows from conjugation and the functional equation. Write

\[
M(x)=\sum_{n\le x}\mu(n),\quad
\psi(x)=\sum_{n\le x}\Lambda(n),\quad E(x)=\psi(x)-x.
\]

Here \(\Lambda(n)\) is von Mangoldt, not the de Bruijn–Newman constant below. The quartet \(\rho,\bar\rho,1-\rho,1-\bar\rho\) consists of four distinct zeros, all of multiplicity \(m\). Functional symmetry, the critical strip, and the absence of real nontrivial zeros are unchanged. [NIST DLMF, zeros](https://dlmf.nist.gov/25.10), [reflection formulas](https://dlmf.nist.gov/25.4).

### Direct poles and unavoidable growth

1. **Right-half-plane zero-freeness fails.** In particular, the supremum \(\Theta=\sup_{\zeta(\rho')=0,\ 0<\Re\rho'<1}\Re\rho'\) satisfies \(\Theta>1/2\). The supremum need not be attained.

2. **Reciprocal zeta has a genuine pole.** At the fixed witness, \(1/\zeta(s)\) has order \(m\), leading coefficient \(m!/\zeta^{(m)}(\rho)\). No globally holomorphic extension of \(1/\zeta\) to \(\Re s>1/2\) exists.

3. **The logarithmic derivative has a signed simple pole.**
\[
-\frac{\zeta'}{\zeta}(s)=-\frac m{s-\rho}+O(1).
\]
The multiplicity increases its residue; it does not create a higher-order logarithmic-derivative pole.

4. **Möbius cancellation must fail at every smaller power.** For every \(1/2<a<\beta\), every real \(B\), and every starting point \(X\),
\[
\sup_{x\ge X}\frac{|M(x)|}{x^a(\log x)^B}=\infty.
\]
Thus there is a particular \(\varepsilon>0\) for which \(M(x)=O(x^{1/2+\varepsilon})\) is false. This is a statement with an existential epsilon, not failure for every positive epsilon.

5. **Prime-power discrepancy must fail at every smaller power.** Under the same quantifiers,
\[
\sup_{x\ge X}\frac{|\psi(x)-x|}{x^a(\log x)^B}=\infty.
\]
In particular \(\psi(x)-x=O(\sqrt{x}\log^2x)\) fails.

6. **The ordinary prime-counting and theta bounds also fail.** For \(\vartheta(x)=\sum_{p\le x}\log p\), and \(\operatorname{li}_2(x)=\int_2^xdt/\log t\), the same infinite-supremum statement holds with \(M\) replaced by \(\vartheta(x)-x\) or \(\pi(x)-\operatorname{li}_2(x)\). In particular the RH bound \(\pi(x)-\operatorname{li}_2(x)=O(\sqrt{x}\log x)\) is impossible. Proof: prime powers beyond primes contribute \(O(\sqrt{x}\log^2x)\); partial summation turns a putative \(\pi\) bound of exponent \(a<\beta\) into a theta bound with at most another logarithm. Absorb every fixed log power into \(x^{a'-a}\) for \(a<a'<\beta\).

7. **Explicit absolute-value boundary lower bounds.** The following deductions retain the multiplicity:
\[
\limsup_{x\to\infty}\frac{|\psi(x)-x|}{x^\beta}\ge\frac m{|\rho|},
\]
\[
\limsup_{x\to\infty}
\frac{|M(x)|}{x^\beta(\log x)^{m-1}}
\ge\frac{m}{|\rho|\,|\zeta^{(m)}(\rho)|}>0.
\]
These are unsigned limsup statements. They do not by themselves prove two-sided \(\Omega_\pm\) with these constants, nor a single-zero asymptotic for the whole error.

8. **Endpoint weighted tail energies diverge.** For every \(X>1\) and every real \(a\le\beta\),
\[
\int_X^\infty\frac{|M(x)|^2}{x^{2a+1}}dx=\infty,
\qquad
\int_X^\infty\frac{|\psi(x)-x|^2}{x^{2a+1}}dx=\infty.
\]
In particular both energies with denominator \(x^2\) diverge. Multiplicity gives the stronger endpoint statement
\[
\int_X^\infty\frac{|M(x)|^2}{x^{2\beta+1}(\log x)^{2m-2}}dx=\infty.
\]
At \(a<\beta\), inserting any fixed power of \(\log x\) in the denominator still leaves divergent energy: otherwise one obtains finite energy at an intermediate exponent \(a'<\beta\). These conclusions concern the classical summatory functions, not the project's separate Pareto Gram energy.

9. **No suitable dominating envelope can validate the forbidden Mellin continuation.** Any argument assuming these finite weighted energies, or a uniform integrable bound sufficient to make the corresponding Mellin transform holomorphic across \(\rho\), must fail. This identifies an actual domination obstruction, not merely failure of a proposed proof technique.

#### Proof of items 4–9

Initially for \(\Re s>1\), summation by parts gives
\[
\frac1{\zeta(s)}=s\int_1^\infty M(x)x^{-s-1}dx,
\quad
-\frac{\zeta'}{\zeta}(s)-\frac{s}{s-1}
=s\int_1^\infty E(x)x^{-s-1}dx.
\]
An \(O(x^a(\log x)^B)\) envelope gives a holomorphic integral for \(\Re s>a\), contradicting the pole at \(\rho\) whenever \(a<\beta\). Local boundedness upgrades failure of a global big-O to infinite supremum on every tail.

For item 7, a finite limsup \(L\) gives an eventual bound by \((L+\delta)x^\beta\), respectively \((L+\delta)x^\beta(\log x)^{m-1}\). Approach \(s=\rho+\epsilon\), \(\epsilon\downarrow0\), multiply the integral identity by \(\epsilon\), respectively \(\epsilon^m\), and use
\(\int_1^\infty x^{-\epsilon-1}(\log x)^{m-1}dx=(m-1)!\epsilon^{-m}\).
The stated constants follow from the pole coefficients. If the limsup is infinite, the inequalities are automatic.

For item 8 at \(a<\beta\), Cauchy–Schwarz makes the integral holomorphic on \(\Re s>a\). At \(a=\beta\), finite energy bounds the integral at \(\rho+\epsilon\) by \(O(\epsilon^{-1/2})\), contradicting the pole. With the log-weighted Möbius energy the bound is \(O(\epsilon^{-m+1/2})\), still too small for order \(m\). Contributions from a fixed finite interval are entire and cannot remove poles. This proof supplies all tail quantifiers.

### Approximation and annihilators: continuum normalization only

10. **A positive approximation gap is classical.** In \(L^2(0,\infty)\), the indicator \(\chi_{(0,1]}\) is outside the closed span of \(\{\{1/(nx)\}:n\in\mathbb N\}\). Consequently its distance from that closed span is strictly positive; finite best-approximation errors decrease to that positive number. This is the contrapositive of Báez-Duarte's Theorem 1.1. [Original paper](https://arxiv.org/pdf/math/0202141).

11. **An explicit annihilator exists in the original \(L^2(0,1)\) model.** Put
\[
g_d(x)=\{1/(dx)\}-d^{-1}\{1/x\},\qquad d\ge2.
\]
Then for \(0<\Re s<1\),
\[
\int_0^1g_d(x)x^{s-1}dx
=-\frac{\zeta(s)}s(d^{-s}-d^{-1}).
\]
The vector \(h_\rho(x)=x^{\bar\rho-1}\) is in \(L^2(0,1)\), annihilates every \(g_d\), and pairs nontrivially with \(1\). Its squared norm is \((2\beta-1)^{-1}\). Thus every legal finite combination \(G\) satisfies
\[
\|1-G\|_2^2\ge\frac{2\beta-1}{|\rho|^2}>0.
\]
This is an independent elementary Mellin/Cauchy–Schwarz deduction, not an assertion that this bound equals the project's discrete \(v(\rho)\) bound.

12. **Multiplicity creates logarithmic annihilators.** For \(0\le j<m\), the vectors \(x^{\bar\rho-1}(\log x)^j\) also annihilate all these \(g_d\), by differentiating the transform identity. The families from any finite list of distinct right-half-plane zeros are linearly independent. Hence the complex orthogonal complement has dimension at least the sum of their multiplicities. In particular the conjugate pair gives at least \(2m\) dimensions. This assertion is for the continuum closed span and requires a separate transfer argument for other models.

### Positivity, spectral, and coefficient consequences

13. **The completed Weil form has a negative compactly supported witness.** With \(f\in C_c^\infty(0,\infty)\), \(F(s)=\int_0^\infty f(x)x^{s-1}dx\), define the usual zero-side Weil form
\[
Q(f)=\sum_\rho F(\rho)\overline{F(1-\bar\rho)}.
\]
It is real; the sum is absolutely convergent. Weil's positivity criterion implies that not RH forces \(Q(f)<0\) for some such \(f\). Consequently a finite logarithmic support window already contains a negative witness; for every larger nested window the infimum of normalized Rayleigh quotients is at most this same negative quotient. Homogeneity gives \(Q(cf)=|c|^2Q(f)\to-\infty\) as \(|c|\to\infty\), but does **not** show that unit-norm Rayleigh quotients are unbounded below. The full signed prime-power and archimedean terms must remain in the explicit formula. [Connes, discussion of Weil positivity and explicit formulas](https://arxiv.org/pdf/math/9811068).

14. **A fully exact self-adjoint Hilbert–Pólya realization is impossible.** The function \(\Xi(z)=\xi(1/2+iz)\) has the nonreal zero \(z=\gamma-i(\beta-1/2)\). A self-adjoint operator cannot have this as an eigenvalue. Thus self-adjointness and an exact correspondence with **all** transformed zeros cannot both hold. An operator having only the ordinates \(\gamma\), or only critical-line zeros, as spectrum is not ruled out. In Connes's framework noncritical zeros are resonances, so their existence does not invalidate every spectral interpretation. [Connes](https://arxiv.org/pdf/math/9811068).

15. **Negative Li coefficients occur.** For
\[
\lambda_n=\frac1{(n-1)!}
\left.\frac{d^n}{ds^n}\big[s^{n-1}\log\xi(s)\big]\right|_{s=1},
\]
not RH implies \(\lambda_n<0\) for some \(n\), in fact infinitely many. The standard criterion and its strengthened exponential formulation are reproduced and extended in [Sekatskii, Theorems 1–3](https://arxiv.org/pdf/1304.7895).

16. **A precise Li generating-series radius is smaller than one.** Independently deduced from the generating function:
\[
\frac{d}{dz}\log\xi\!\left(\frac1{1-z}\right)
=\sum_{n\ge1}\lambda_nz^{n-1},
\quad
R=\min_{\Re\rho'>1/2}\left|1-\frac1{\rho'}\right|<1.
\]
The minimum is attained because the moduli tend to one with the zero ordinate. The poles cannot cancel, since their residues are positive multiplicities. Thus
\[
\limsup_{n\to\infty}|\lambda_n|^{1/n}=R^{-1}>1.
\]
In fact both positive and negative parts have that exponential limsup:
\[
\limsup(\max(\lambda_n,0))^{1/n}
=\limsup(\max(-\lambda_n,0))^{1/n}=R^{-1}.
\]
Proof of the last strengthening: if one part had a larger convergence radius than \(R\), the other would have radius \(R\); Pringsheim's theorem would give a singularity at positive real \(R\). The original logarithmic derivative is holomorphic there because \(1/(1-R)>1\). This is impossible. In particular eventual positivity and eventual negativity both fail.

17. **The de Bruijn–Newman constant is strictly positive.** In the standard heat-deformation normalization, not RH is equivalent to \(\Lambda_{\mathrm{dBN}}>0\). Consequently the deformed function still has nonreal zeros for every \(0\le t<\Lambda_{\mathrm{dBN}}\). Rodgers–Tao's unconditional \(\Lambda_{\mathrm{dBN}}\ge0\) makes RH equivalent to equality zero, but does not exclude strict positivity. [Rodgers–Tao, introduction and Theorem 1](https://arxiv.org/pdf/1801.05914).

### Elementary integer witnesses

18. **Infinitely many quantitatively large Robin violations.** For every \(b\) with \(1-\beta<b<1/2\), some \(C>0\) satisfies
\[
\sigma(n)\ge e^{\gamma_E}n\log\log n
+C\frac{n\log\log n}{(\log n)^b}
\]
for infinitely many integers \(n\). Thus there are counterexamples beyond every cutoff to Robin's inequality for \(n>5040\).

19. **Infinitely many Lagarias violations.** With \(H_n=\sum_{j=1}^n1/j\),
\[
\sigma(n)>H_n+e^{H_n}\log H_n
\]
holds infinitely often. Deduction: the Robin excess above dominates the \(O(n/\log n)\) difference between these thresholds. At least one counterexample can be chosen colossally abundant. These claims and Robin's quantitative theorem are given in [Lagarias, Proposition 3.2 and proof of Theorem 1.1](https://arxiv.org/pdf/math/0008177). (Source-derived prose across items 18–19 is under 200 words.)

### Necessary qualifications: what not RH does not establish

20. It does not invalidate the prime number theorem: \(\psi(x)\sim x\), \(\vartheta(x)\sim x\), and \(\pi(x)\sim x/\log x\) remain unconditional theorems. Likewise \(M(x)=o(x)\) remains true. These coexist with all smaller-power failures above.

21. It does not by itself supply infinitely many off-line zeros, positive density of off-line zeros, zeros with real parts approaching one, or a largest real part attained by a zero. Do not promote one witness or its fourfold symmetry into any such claim.

22. It does not imply that all zeros leave the critical line, or that a particular critical-line zero is multiple. Nor does it imply failure of the functional equation, analytic continuation, Euler product in \(\Re s>1\), zero counting asymptotics, or elementary CRT.

23. A statistical limit that discards a finite or zero-density exceptional set can coexist with off-line zeros. Therefore a GUE/Dyson law for the ordinates, without an exact all-zero identification, is not automatically contradicted. No claim that RH alone proves the full GUE conjecture is being made.

24. From \(A\Rightarrow\mathrm{RH}\), infer \(\neg\mathrm{RH}\Rightarrow\neg A\). From only \(\mathrm{RH}\Rightarrow A\), no such inference is valid. In particular not RH does not automatically refute Lindelöf, every conditional estimate, or every consequence conjecturally associated with RH.

25. A failure of a universal quantitative assertion requires correct negation of its constants: not \(\forall\epsilon>0\,\exists C_\epsilon\,\forall x\,|E(x)|\le C_\epsilon x^{1/2+\epsilon}\) means \(\exists\epsilon>0\,\forall C>0\,\exists x\) violating it. Local boundedness then makes violations arbitrarily far out. Negating a limit zero gives a subsequence bounded away from zero, unless monotonicity or another theorem strengthens it to a positive full limit. Negating a joint sufficient criterion forces at least one conjunct to fail, not every conjunct.


## Final logical boundary

The recovered obstructions are coherent consequences of a hypothetical off-line zero. The strongest synthesis is that the **same arithmetic orthogonal complement** must simultaneously carry a positive approximation gap, positive site vacancies, finite tail capacity, an irregular finite-energy certificate, and all zero-and-multiplicity observations. The corresponding growing interpolation costs diverge, while several normalized gains are summable and certain signed analytic spectral quantities grow without bound.

No contradiction between these facts has been established. To prove RH by this route, one must rule out at least one genuinely necessary member of this joint system. Merely proving more identities among its members does not do that. Conversely, independently constructing the actual nonzero arithmetic annihilator, a positive uniform tail gap, or a uniformly bounded full-tail capacity would disprove RH.

This distinction also separates the two opposite compactness tasks: bounded exact-head **primal approximants** would imply RH; bounded normalized **dual annihilator certificates** would imply not RH. Both have finite-stage solutions. The unresolved issue is which family has the necessary uniform bound.
