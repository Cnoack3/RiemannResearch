---
title: "Assuming RH is false"
subtitle: "New conditions and a contradiction agenda"
date: "October 1, 2026"
lang: en-US
---

# Research result and status

Assuming the Riemann hypothesis is false forces one arithmetic projection defect to survive an unusually restrictive collection of tests. This report integrates the cofinal conditions, the unbounded inverse Gram matrices, integer and Mellin determinantal processes, their coupling, and Bagchi's density equivalence with Li coefficients, screw functions, Hilbert kernels and Connes's spectral programs.

**No contradiction or proof of RH has been obtained.** What has advanced is the reduction of several broad programs to explicit estimates: a centered transfer bound for actual screened gaps; a heavy-tail obstruction for the furthest DPP hole; a directional inverse-Gram saturation target; a positive Mellin-window defect; one-sided exponential Li obstruction; and quantitative errors that must persist in any proposed real-zero spectral approximation. Each open estimate below, with its stated hypotheses, would contradict failure if proved.

The report distinguishes three levels of evidence. **Formal results** are Lean declarations checked with the usual logical foundations. **Ordinary proofs** are written mathematical arguments using the identified established results. **Open estimates and conjectures** are unproved research targets. A research route is not a new theorem merely because its completion would imply RH. No claim of priority or established mathematical breakthrough is made.

## Common-zero notation and exact indexing

Throughout a hypothetical right zero is

$$\rho=\beta+i\gamma,\qquad \tfrac12<\beta<1,\qquad
\delta=\beta-\tfrac12,\qquad\alpha=2\delta=2\beta-1,\qquad R=|\rho|.$$

The functional equation converts any off-line zero into such a right zero. All estimates labeled by $\rho$ concern the same zero; one may not change witnesses to optimize unrelated conditions. The projection space is

$$H=\ell^2\!\left(\mathbb N_{\ge1},\frac1{k(k+1)}\right),\qquad
 g_d(k)=\frac{k\bmod d}{d},\qquad
 V=\overline{\operatorname{span}}\{g_d:d\ge2\}.$$

Write $D=\|(I-P_V)1\|^2$ for the constant defect and $\Delta$ for the physical first-point defect. They are distinct. The inverse matrix $G_N$ on conductors $2,\ldots,N$ has rank $N-1$. By contrast, the DPP notation $K_n$ below has rank $n$, conductors $2,\ldots,n+1$, and the corresponding full Gram matrix has those same $n$ conductors. A physical site $k\ge1$ corresponds to the repository's zero-based site $k-1$.

## Ten concrete contradiction routes

Each row records an open sufficient estimate, rather than an assertion that the estimate is true. Several rows are alternative formulations of the same underlying obstruction; they are not statistically independent evidence. Cofinal requirements must hold at the same indices when more than one quantity is involved.

| Route | Open sufficient estimate | Contradiction under failure |
|---|---|---|
| A. Screened arithmetic model | Divergent exact model gap energy and summable full centered transfer error | Actual gap energy is finite |
| B. Moving remainders | Exact Hilbert remainder representation, summable total variation, and divergent model gaps | Bessel/Minkowski gives the forbidden transfer |
| C. DPP range | Joint rank/window pairs with bounded truncated maximum-hole moment | Every rank has a positive power lower bound |
| D. Inverse direction | Joint rank/site pairs with bounded full directional deficit | Same-zero deficit grows as $k^{1-\alpha}$ |
| E. Mellin window | Actual unscaled deficit tends to zero cofinally on one positive finite frequency window | That same window has a positive floor |
| F. Li negative part | A lower bound $\lambda_n\ge-C_\varepsilon e^{\varepsilon n}$ for every $\varepsilon>0$ | Negative subsequence has exponential growth |
| G. Screw energy | For every $\varepsilon>0$, bounded cofinal weighted screw-energy integrals | A pole forces divergence when $\varepsilon<\delta$ |
| H. Hilbert/Weil certificates | Cofinal exact positive matrices or vanishing-error Gram matching | A fixed strict negative witness persists |
| I. Connes generators | Simple-even true generators and the actual weighted Mellin approximation rate | Rouché forces a positive approximation floor |
| J. Weil noncrossing | Full-window asymptotic positivity, or an integrable relative differential bound on the actual bottom eigenvalue | Failure gives a persistent negative window floor |

The central arithmetic task remains to obtain a lower bound for the **actual signed** survivor or contrast energy, or a quantitatively correct model with all growing inverse-Gram remainders controlled. Prime density and source lower bounds alone do not supply that signed estimate.

# Actual screened energy and inverse-direction obstructions

The existing exact capacity split under failure makes the actual weighted prime-gap energy finite. The following deductions identify precisely what an arithmetic model, a moving-vector argument, and a DPP filling program must overcome. Their analytic components are ordinary proofs. The scalar squared-energy transfer in the first proof and a strict Li contraposition have additionally passed Lean verification; the full number-theoretic providers remain open.

### Exact centered transfer from a tractable model to the actual screened gaps

For an actual prime Schur row write

$$w_p=\delta_{p-3}^2/\sigma_{p-2}>0,\qquad y_p=\operatorname{error}_{p-3}/\delta_{p-3}.$$

In the disjoint dyadic parent window $B_j=L_j\sqcup R_j$, put $U_A=\sum_{p\in A}w_p$ and let $\bar y_A$ denote the $w$-weighted mean. Thus the actual screened gap is $G_j=\bar y_{R_j}-\bar y_{L_j}$. Let $m_p$ be any proposed model, retaining the same actual weights, and write $\widetilde G_j=\bar m_{R_j}-\bar m_{L_j}$ and $\varepsilon_p=y_p-m_p$. Define

$$\kappa_j=\frac{U_{L_j}U_{R_j}}{U_{L_j}+U_{R_j}},\qquad
E_j=\sum_{p\in B_j}w_p(\varepsilon_p-\bar\varepsilon_{B_j})^2.$$

**Proved transfer identity and inequality.** The full weighted variance split gives

$$E_j=\sum_{p\in L_j}w_p(\varepsilon_p-\bar\varepsilon_{L_j})^2+
\sum_{p\in R_j}w_p(\varepsilon_p-\bar\varepsilon_{R_j})^2+
\kappa_j(G_j-\widetilde G_j)^2.$$

Consequently $\kappa_j(G_j-\widetilde G_j)^2\le E_j$. All moving screening errors appear in $\varepsilon$; the two child scatters are retained in the equality. An arbitrary block-common shift in the error disappears exactly, which makes this criterion strictly more flexible than demanding summability of the uncentered row error.

**Proved contradiction reduction.** If $\sum_j E_j<\infty$ and $\sum_j\kappa_j\widetilde G_j^2=\infty$, then $\sum_j\kappa_jG_j^2=\infty$. Otherwise, $\widetilde G_j^2\le2G_j^2+2(G_j-\widetilde G_j)^2$ makes the model series summable. Under negated RH the exact split-tree budget makes $\sum_j\kappa_jG_j^2$ finite, so these two explicit model inputs contradict failure. No upper bound on $\kappa_j$ is needed; this avoids a hidden lower estimate for the screened pivot. If using the simpler weight $2^j$, the established $\kappa_j\gg2^j$ suffices to transfer square-summable error, but a model divergence statement with $\kappa_j$ is the cleanest target.

**Open arithmetic program A.** Construct an explicit CRT/adjacent-residue model $m_p$ for which a lower signed estimate proves $\sum_j\kappa_j\widetilde G_j^2=\infty$, and prove the full centered screening-energy estimate $\sum_jE_j<\infty$. Positive source estimates or an upper large-sieve inequality do not provide the model lower bound. Computing a tractable model without the second estimate is insufficient.

The actual weights must also be retained: the available source lower bound $w_p\gg\log p$ is not an asymptotic equality for the screened pivot weight. If a tractable calculation instead uses proxy weights $v_p$, their replacement incurs a further explicit error. On each block $A$ let $P_p=w_p/U_A$, $Q_p=v_p/V_A$, and $\mu_Q=\sum Q_pm_p$. Then

$$|\sum P_pm_p-\mu_Q|^2\le
\left[\sum_p\frac{(P_p-Q_p)^2}{Q_p}\right]
\left[\sum_pQ_p(m_p-\mu_Q)^2\right].$$

This is weighted Cauchy applied to the full centered mean difference. Those errors must be included in the square-summable transfer budget. Replacing the actual screened weight by $\log p$ using only a lower floor would be unjustified.

### A moving-vector bounded-variation provider for that transfer

Let $h_p$ be the actual mutually orthogonal Schur innovation vectors with $\|h_p\|^2=\sigma_{p-2}$. Suppose the exact row discrepancy has a single Hilbert-vector representation on each parent window,

$$\operatorname{error}_p-\operatorname{error}^{\rm model}_p=\langle R_j,h_p\rangle\quad(p\in B_j).$$

Here $R_j$ must represent the complete moving remainder, including the full growing inverse-Gram screening correction and every model truncation error. An assumed representation is a hypothesis, not a removal of those terms. Define

$$v_j=\sqrt{\kappa_j}\left[
\frac1{U_{R_j}}\sum_{p\in R_j}\frac{\delta_{p-3}}{\sigma_{p-2}}h_p-
\frac1{U_{L_j}}\sum_{p\in L_j}\frac{\delta_{p-3}}{\sigma_{p-2}}h_p\right].$$

**Proved:** the $v_j$ form an orthonormal family, because parent windows are disjoint and

$$\|v_j\|^2=\kappa_j(1/U_{R_j}+1/U_{L_j})=1.$$

Also $\sqrt{\kappa_j}(G_j-\widetilde G_j)=\langle R_j,v_j\rangle$. If

$$\sum_j\|R_{j+1}-R_j\|<\infty,$$

then

$$\boxed{\sum_j\kappa_j(G_j-\widetilde G_j)^2\le
\left(\|R_0\|+\sum_j\|R_{j+1}-R_j\|\right)^2<\infty.}$$

Proof: write $R_j=R_0+\sum_{i<j}(R_{i+1}-R_i)$, use Bessel for each fixed vector against the appropriate subfamily of the $v_j$, and use Minkowski in $\ell^2$. One first obtains the same bound for every finite collection of levels, then takes the monotone limit. This handles genuinely moving vectors and preserves the complete signed remainder.

The stated complete row representation gives more: if $\Pi_j$ projects onto the innovations in $B_j$, its ranges are pairwise orthogonal and $\|\Pi_jR_j\|^2=\sum_{p\in B_j}w_p\varepsilon_p^2$. The same Bessel--Minkowski proof therefore bounds the sum of these full uncentered row energies by $(\|R_0\|+\sum_i\|R_{i+1}-R_i\|)^2$. Hence the full centered error sum $\sum_jE_j$ is finite as well. The earlier paired-only limitation was unnecessarily weak.

The scalar analytic bound and its conditional signed CRT application are now formalized in Analysis/MovingOrthogonalEnergy.lean and RH/ParetoMovingRemainderTransfer.lean. See [MovingRemaindersVerificationAndResearch20261001.md](MovingRemaindersVerificationAndResearch20261001.md) for the block proof, explicit arithmetic assumptions, inverse-pivot restriction, countermodel and reproducible Wolfram diagnostics.

**Open arithmetic program B.** Derive an exact model-remainder representation and an unconditional bound on its total Hilbert variation. Alternatively, directly control $\sum_j|\langle R_j,v_j\rangle|^2$; that is weaker and may be more attainable. If its companion model has the nonsummable signed gap energy in A, the proved reduction yields a contradiction.

### A quantitative DPP range obstruction and a new synchronized cutoff target

This deduction starts from the already constructed limiting integer DPP; it does not require a coupling provider. Let its kernel be $K_\infty$, let $Y$ be its complement, and put $L=\sup Y$ with $\sup\varnothing=0$ and $L=\infty$ allowed. For any monotone spatial coupling, $Y$ has the law of its permanent-hole set, because the finite-site inclusion determinants converge to those of $K_\infty$.

For a hypothetical zero $\rho=\beta+i\gamma$, write $\alpha=2\beta-1\in(0,1)$ and $R=|\rho|$. The repository's `critical_weight_mul_site_floor_lower` gives the explicit physical-site lower bound

$$q_k:=1-K_\infty(k,k)\ge c_\rho(k+1)^{-2\beta},\qquad
c_\rho=\frac{\alpha\beta^2}{2R^2}>0.$$

The index here is physical $k=n+1$, rather than the repository's zero-based index $n$. This exact constant is weaker than a height-sensitive refined discrete Gram floor, but already suffices.

For a finite block $B$, $Y$ is the complement DPP, with compressed kernel $Q_B=(I-K_\infty)|_B$. Thus

$$\mathbb P(Y\cap B=\varnothing)=\det(I-Q_B)
\le \exp(-\operatorname{tr}Q_B).$$

The determinant is retained in the exact equality; the inequality uses each eigenvalue $0\le\lambda\le1$ and $1-\lambda\le e^{-\lambda}$. For $B=[N,2N]$, the vacancy floor gives $\operatorname{tr}Q_B\ge a_\rho N^{-\alpha}$, where $a_\rho=c_\rho3^{-2\beta}$. Hence, for all integer $N\ge1$,

$$\boxed{\mathbb P(L\ge N)\ge1-e^{-a_\rho N^{-\alpha}}
\ge\frac{a_\rho}{1+a_\rho}N^{-\alpha}.}$$

By the tail integral/sum formula, $\mathbb E L^s=\infty$ for every $s\ge\alpha$, including the critical endpoint. In particular $\mathbb E L=\infty$. This does not assert that there are infinitely many holes almost surely; a finite random hole set can have such a heavy range tail.

Now let $K_n$ be a finite-rank arithmetic DPP kernel and define its exact truncated maximum-hole moment

$$\mathcal R(n,M)=\sum_{m=1}^M\left[1-\det(K_n|_{[m,M]})\right]
=\mathbb E\left[\max(Y_n\cap[1,M])\right].$$

The equality is the integer tail-sum formula. It retains every determinant and every Gram interaction; no infinite range of a finite-rank DPP is used. Compression order $K_n\le K_\infty$ implies that finite-rank block hole probabilities are at least their limiting counterparts.

Take $B_M=[\lceil M/2\rceil,M]$. It contains at least $M/2$ sites, and each vacancy is at least $c_\rho(2M)^{-1-\alpha}$. Thus, with $A_\rho=c_\rho2^{-2-\alpha}$,

$$\operatorname{tr}(I-K_\infty)|_{B_M}\ge A_\rho M^{-\alpha}.$$

At least $M/2$ of the tail-sum terms contain this last block. Using $1-e^{-x}\ge x/(1+x)$ yields the explicit uniform bound

$$\boxed{\mathcal R(n,M)\ge
\frac{A_\rho}{2(1+A_\rho)}M^{1-\alpha}}
\qquad(n\ge0,\ M\ge1).$$

Since $1-\alpha=2-2\beta>0$, this diverges regardless of how the rank is increased.

**Open arithmetic program C.** Construct synchronized pairs $(n_j,M_j)$ with $M_j\to\infty$ and $\sup_j\mathcal R(n_j,M_j)<\infty$. This directly contradicts the displayed power lower bound. The target only asks a bounded truncated maximum-hole first moment; it is weaker than asking bounded expectation of the total linearly weighted hole mass, since $\max(Y\cap[1,M])\le\sum_{k\le M}k\mathbf1_{k\in Y}$. The rank and physical window must be chosen jointly. A bound at one sequence of ranks and an unrelated window estimate on another cofinal set does not establish the target.

Conditional converse audit: if the Bagchi density implication gives $K_n\to I$, then for each fixed $M$, $\mathcal R(n,M)\to0$. A diagonal choice can therefore achieve $\mathcal R(n_j,j)\le1/j$. This is an equivalence after that classical density input, not an unconditional construction of the required ranks. The useful advance is the exact finite determinant target and the same-zero power obstruction, rather than a claim that the remaining arithmetic construction is proved.

### A cofinal inverse-direction corollary

For physical site $k$, let $a_{n,k}$ be the full legal feature vector $(g_d(k))_{2\le d\le n+1}$ and retain the exact full Gram inverse. Write $\Gamma_n=\operatorname{Gram}(g_2,\ldots,g_{n+1})$ for this rank-$n$ matrix, so $\Gamma_n=G_{n+1}$ in the conductor notation. The diagonal identity is

$$K_n(k,k)=\frac{a_{n,k}^{T}\Gamma_n^{-1}a_{n,k}}{k(k+1)}.$$

Define the nonnegative directional deficit

$$\mathcal L(n,k)=k(k+1)-a_{n,k}^{T}\Gamma_n^{-1}a_{n,k}.$$

The same uniform zero floor and $K_n\le K_\infty$ give, for every rank $n$,

$$\boxed{\mathcal L(n,k)\ge c_\rho k(k+1)^{-\alpha}
\ge c_\rho2^{-\alpha}k^{1-\alpha}.}$$

Thus a single synchronized cofinal sequence of pairs $(n_j,k_j)$ with $k_j\to\infty$ and $\sup_j\mathcal L(n_j,k_j)<\infty$ contradicts every off-line zero. Equivalently, it suffices to produce vacancy $1-K_{n_j}(k_j,k_j)=O(k_j^{-2})$ on that one sequence. This is a concrete directional saturation target for $\Gamma_n^{-1}$; its unconditional operator-norm growth does not provide the required almost-maximal quadratic form. No rate of rank growth is assumed or asserted.

**Open arithmetic program D.** Use the exact adjacent-residue or CRT features to construct legal trials that leave a bounded full inverse-direction deficit at a cofinal sequence of physical sites. All inverse correlations are included in $a^T\Gamma_n^{-1}a$. Independently cofinal rank and site estimates do not suffice unless they give actual joint pairs. As in the cutoff criterion, classical RH density implies feasibility at each fixed site, but does not constitute an unconditional construction.

Primary DPP reference: Russell Lyons, *Determinantal probability measures*, Publ. Math. IHES 98 (2003), 167-212, DOI 10.1007/s10240-003-0016-0; https://arxiv.org/abs/math/0204325. The finite void determinant follows directly by inclusion-exclusion from the defining inclusion determinants; projection-order stochastic domination is supplied by Lyons's theorem. The manuscript proves the displayed deductions; they should not be attributed as quotations from Lyons.


# Mellin-window and Cauchy-generator obstructions

### Exact source definitions and physical indexing

The relevant sources are `RH/MellinCoordinateDefect.lean`, `RH/MellinZeroProfile.lean`, `RH/MellinDeficitRHTest.lean`, and `RH/MellinFrequencyMeasure.lean`.

The repository's natural coordinate $k$ corresponds to physical cell $[k+1,k+2]$. To simplify formulas, use physical integers $n\ge1$ throughout this note. Put

$$
w_n=\frac1{n(n+1)},\qquad
a_s(n)=\int_n^{n+1}x^{-s-1}\,dx
=\frac{n^{-s}-(n+1)^{-s}}s.
$$

The integral formula also supplies the removable value at $s=0$. We will only need $\Re s>0$, so division by zero does not arise.

For a fixed $\rho$ with $\beta=\Re\rho>1/2$, put

$$
\delta=\beta-\tfrac12>0,\qquad \alpha=2\beta-1=2\delta.
$$

The repository's actual zero-profile is

$$
F_\rho(t)=\sum_{n\ge1}n(n+1)\overline{a_\rho(n)}a_{1/2+it}(n).
$$

Indeed the coordinate feature equals $a_{1/2+it}(k+1)/\sqrt{w_{k+1}}$; substituting that formula into `zeroProfile` gives the expression above, with both square-root weights retained. Its first `M` cells are denoted $F_{\rho,M}$.

Frequency measure is the actual repository normalization

$$
d\mu(t)=\frac{dt}{2\pi}.
$$

The coordinate-window deficit $W_M(I)$ is an integral of the squared defects of the real and imaginary coordinate heads under the completed arithmetic projection. It is a physical-coordinate cutoff of the completed projection, not a finite arithmetic-rank cutoff.

### Proved ordinary analytic provider: uniform convergence with constants

For $\Re s=\sigma>0$, monotonicity of the positive power function gives

$$
|a_s(n)|\le\int_n^{n+1}x^{-\sigma-1}dx\le n^{-\sigma-1}.
$$

Consequently

$$
n(n+1)|a_\rho(n)a_s(n)|\le2n^{-\beta-\sigma}.
\tag{2.1}
$$

On the critical line this becomes $2n^{-1-\delta}$, independent of both frequencies. The integral test proves, for every integer $M\ge1$,

$$
\boxed{\sup_{t\in\mathbb R}|F_\rho(t)-F_{\rho,M}(t)|
\le\frac2\delta M^{-\delta}.}
\tag{2.2}
$$

Thus the provider's `profile_converges` field follows, in fact uniformly on the whole real frequency axis. Also

$$
\sup_t|F_\rho(t)|\le2\left(1+\frac1\delta\right).
\tag{2.3}
$$

No zeta-zero assumption is used in these estimates. In particular, this proof addresses the provider as typed, which quantifies over **all** complex $\rho$ with $\Re\rho>1/2$, not only zeros in the critical strip.

For holomorphy, introduce the complex variable version

$$
\mathcal F_\rho(s)=\sum_{n\ge1}n(n+1)\overline{a_\rho(n)}a_s(n),
\qquad
\Omega_\rho=\{s:\Re s>\max(0,1-\beta)\}.
$$

Each summand is entire in $s$, by the integral over a compact positive cell. For a compact set $K$ in $\Omega_\rho$, let $\sigma_0=\min_{s\in K}\Re s>\max(0,1-\beta)$. Then $p=\beta+\sigma_0>1$, and

$$
\sup_{s\in K}\sum_{n>M}|n(n+1)\overline{a_\rho(n)}a_s(n)|
\le\frac2{\beta+\sigma_0-1}M^{-(\beta+\sigma_0-1)}.
\tag{2.4}
$$

This proves locally normal convergence and holomorphy on the connected half-plane $\Omega_\rho$. The critical line is contained in that half-plane. For actual right off-line zeta zeros, $1/2<\beta<1$, so $\Omega_\rho$ is simply $\Re s>1-\beta$.

### Nonvanishing and positive window mass

Set $h_1=2\overline{a_\rho(1)}$. Since $\beta>0$, $|2^{-\rho}|=2^{-\beta}<1$, so

$$
h_1=2\overline{\frac{1-2^{-\rho}}\rho}\ne0.
$$

For real $\sigma>0$, the first-cell contribution obeys

$$
\sigma\mathcal F_\rho(\sigma)
=h_1(1-2^{-\sigma})
+\sigma\sum_{n\ge2}n(n+1)\overline{a_\rho(n)}a_\sigma(n).
$$

Whenever $\beta+\sigma>1$, the absolute value of the second term is at most

$$
2\sigma\left[2^{-\beta-\sigma}
+\frac{2^{1-\beta-\sigma}}{\beta+\sigma-1}\right],
$$

which tends to zero as $\sigma$ tends to positive infinity. Therefore

$$
\boxed{\lim_{\sigma\to+\infty}\sigma\mathcal F_\rho(\sigma)=h_1\ne0.}
\tag{3.1}
$$

Hence $\mathcal F_\rho$ is not identically zero. Its zeros are discrete in $\Omega_\rho$; the zeros on each compact critical-line segment are finite, and the whole critical-line zero set is countable. Thus $F_\rho(t)$ is nonzero for almost every real $t$.

For every measurable $I$ with $\mu(I)>0$,

$$
\boxed{m_I:=\int_I|F_\rho(t)|^2d\mu(t)>0.}
\tag{3.2}
$$

This proves the provider's `window_mass_pos` field: its `zeroWindowMass` is $\alpha m_I/2$. It holds for every positive-measure measurable set, not only an interval. When $\mu(I)<\infty$, (2.3) also proves

$$
0<m_I\le4(1+1/\delta)^2\mu(I)<\infty.
$$

The statement for arbitrary positive-measure sets only needs positivity; their mass may be infinite.

### Same-zero lower bound for every sufficiently large cutoff

Now assume that $\rho$ is an actual zeta zero with $\Re\rho>1/2$ and $\rho\ne1$. `MellinZeroProfile.zeroProfilePartial_cauchy_bound` is already a Lean theorem already present in the source for the complete coordinate defect:

$$
\frac\alpha2|F_{\rho,M}(t)|^2\le\operatorname{diagonalDefect}(M,t).
\tag{4.1}
$$

Its proof retains the real and imaginary head defects and every signed mixed term; its factor `1/2` is the explicitly weaker Cauchy constant rather than an unproved sharp Riesz constant.

Let $I$ have positive finite frequency measure, and let $e_M=2M^{-\delta}/\delta$. Integrating (4.1), then using (2.2) and the reverse $L^2$ triangle inequality, gives

$$
\boxed{W_M(I)\ge\frac\alpha2
\left(\sqrt{m_I}-e_M\sqrt{\mu(I)}\right)_+^2.}
\tag{4.2}
$$

In particular,

$$
\boxed{\liminf_{M\to\infty}W_M(I)\ge\frac\alpha2m_I>0.}
\tag{4.3}
$$

The explicit sufficient cutoff condition

$$
M^\delta\ge\frac{4\sqrt{\mu(I)}}{\delta\sqrt{m_I}}
$$

ensures

$$
\boxed{W_M(I)\ge\alpha m_I/8.}
\tag{4.4}
$$

The existing `zeroWindowMass_le_liminf` declaration instead reaches (4.3) via Fatou once profile convergence is supplied. These ordinary proofs close **both analytic fields** of `ZeroModeWindowProvider`. Their Lean formalization remains to be written. This ordinary analytic advance removes the two provider fields as mathematical conjectures; it does not remove the remaining arithmetic vanishing estimate. The unproved arithmetic obligation is now cofinal vanishing of the **unscaled** $W_M(I)$ for one positive-measure window.

### Cauchy-mixture failure mechanism: exact integration audit

`CauchyAnnihilatorRH.not_RH_iff_exists_finite_energy_cauchy_annihilator` is an unconditional source theorem about Mathlib RH. Under failure it supplies a single concrete nonzero mixture, of positive finite Pareto energy, annihilating every legal residue generator. `CauchyMixtureEscape` identifies it with the Mellin mode at $s=1/2+\delta+i\gamma$, and proves the actual pairing formula

$$
\operatorname{Pairing}(h_s,g_d)=(d^{-1}-d^{-s})\zeta(s).
$$

The $d=2$ multiplier cannot vanish when `Re(s)<1`; hence `riemannHypothesis_iff_cauchy_generator_detected` is a genuine unconditional equivalence. Detection itself remains open.

This failure witness is a continuous Cauchy mixture over **unbounded** critical frequencies. Its representing measure is not countably supported and has infinite first critical-frequency moment. It has finite energy although each individual critical-frequency mode has infinite energy. These facts are all explicit declarations in `CauchyMixtureEscape.lean`. Thus neither compact-frequency exclusions nor finite-first-moment exclusions can be applied to it, and exchanging modewise energy with mixture energy would be invalid.

The same zero drives the profile lower bound above, all-site DPP vacancies, and the Cauchy annihilator. The conditions refer to different realizations of the **same arithmetic zero**, rather than unrelated abstract obstructions.

### Bagchi, closed generator spaces, and DPP audit

The classical Bagchi criterion in this weighted sequence space is

$$
RH\iff1\in V\iff V=H,
\qquad V=\overline{\operatorname{span}\{g_d:d\ge2\}}.
$$

Primary source: Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, Theorem 1 (2006), DOI 10.1007/BF02829783, <https://arxiv.org/pdf/math/0607733>.

The repository's `ResidueClosureDensity.closedSpace_eq_top_iff_one_mem` proves the second equivalence without an RH converse. `odd_carry_iff_closedSpace_eq_top` proves density iff every actual odd doubling carry belongs to the closure. `ArgumentDoublingGenerators.exists_odd_carry_not_mem_of_not_RH` therefore supplies a carry outside the closure under failure. Its `doubled_three_not_mem_finiteSpan` is a different unconditional statement and cannot substitute for closure nonmembership.

The exact missing Lean reverse provider is still an RH-to-residue-density/natural-approximation theorem, as documented in `RHToDensityDependencyAudit20260921.md` and exposed by the `hDensity` argument of `MellinDeficitRHTest.riemannHypothesis_iff_windowTest`. The September 27 Baez-Duarte normalization bridge is proved; the analytic RH-to-natural-approximation implication remains a formalization dependency. The forward density-to-RH and Mellin obstruction directions used here do not require that missing provider.

In this paragraph alone, the kernel arguments use the repository's zero-based indexing: $K_\infty^{\rm repo}(n-1,n-1)=K_\infty^{\rm phys}(n,n)$. Thus `IntegerDPPAllSiteObstruction` proves, for the same zero,

$$
0<\frac{\alpha|a_\rho(n)|^2}{w_n}
\le1-K_\infty^{\rm repo}(n-1,n-1),\qquad n\ge1.
\tag{6.1}
$$

The same lower bound holds at every finite arithmetic stage. Every site saturation would imply RH. These are operator statements requiring neither a DPP existence theorem nor a coupling.

For any supplied monotone spatial DPP coupling, the repository identifies

$$
\mathbb P(n\text{ never enters})=1-K_\infty^{\rm repo}(n-1,n-1).
\tag{6.2}
$$

Thus changing the coupling cannot improve the one-site probabilities in (6.1). The known all-site lower bound also implies

$$
\sum_{n\ge1}n\,\mathbb P(n\text{ never enters})=\infty
$$

under failure. `SpatialCouplingStatus.md` explicitly separates the established compactness/gluing machinery and never-enters identity from the unproved Lean provider `SpatialWindowFeasible`. The classical Lyons stochastic-domination/Strassen route constructs the spatial coupling mathematically; its signed-minor/Hall and finite-transport formalization is still required. Scalar first-site coupling is separately established. Coupling alone does not establish filling.

The frequency DPP and integer DPP must also remain distinct. The old finite-rank frequency kernels have a common zeta factor and vanish at critical-line zeros; the coordinate-window deficit here is the completed arithmetic projection tested on physical-coordinate Mellin heads. Scaling a frequency kernel or increasing arithmetic rank does not automatically prove cofinal vanishing of this coordinate deficit.

### Contradiction agenda with proved bridges and open providers

1. **Formalization task:** encode (2.2), the locally normal series, (3.1), and positive-window mass, thereby constructing `ZeroModeWindowProvider`. These are supplied ordinary proofs, not new conjectures.
2. **Open arithmetic provider:** for one fixed positive finite-measure window, prove $\forall\varepsilon>0\ \forall N\ \exists M\ge N:\ W_M(I)<\varepsilon$. Under failure, choose $\varepsilon<\alpha m_I/8$ and a cutoff beyond (4.4); the two inequalities contradict. Separately cofinal estimates must be synchronized at the same indices.
3. **Equivalent generator route:** construct full-Pareto-norm approximants for every actual odd doubling carry. The failure carry outside the closure then contradicts this provider. Exact finite interpolation and small head errors without physical-tail bounds do not suffice.
4. **Equivalent DPP route:** prove saturation at one fixed site, or sufficient weighted summability of permanent-hole probabilities. Equations (6.1)-(6.2) then contradict the same-zero floor or weighted divergence. Completing the spatial coupling formalization alone does not complete this provider.
5. **Equivalent Cauchy route:** prove the actual $d=2$ pairing detects every positive-scale strip Cauchy mixture. Its exact multiplier identity then contradicts the annihilator supplied by failure. The unbounded-frequency witness must remain admissible.

Completion of any one open arithmetic provider yields a contradiction. Combining the established obstructions alone does not establish a contradiction; each missing provider is stated explicitly, and none is claimed to follow from generic Hilbert-space positivity.


# Li coefficients, screw functions and Hilbert kernels

### A stronger one-sided quantitative Li obstruction

Define the usual real Li coefficients $\lambda_n$ and $F(w)=\sum_{n\ge0}\lambda_{n+1}w^n$. The exact generating identity is

$$
F(w)=\frac{1}{(1-w)^2}\frac{\xi'}{\xi}\!\left(\frac{1}{1-w}\right).
$$

Assume not RH and set

$$
r=\min_{\xi(\rho)=0}\left|1-\frac1\rho\right|<1.
$$

This minimum is attained: an off-line reflected pair supplies a point with modulus below one, while these moduli tend to one as zero height tends to infinity. $F$ has a genuine pole at every transformed zero, so its Taylor radius is exactly $r$. It is nevertheless analytic in a neighborhood of the positive real point $r$, since $1/(1-r)>1$ and $\xi$ is nonzero there.

Let $m_n=\max(0,-\lambda_n)$ and define the indexed negative and positive part series

$$M(w)=\sum_{n\ge0}m_{n+1}w^n,\qquad
P(w)=\sum_{n\ge0}\max(0,\lambda_{n+1})w^n=F(w)+M(w).$$

Then

$$
\boxed{\limsup_{n\to\infty}m_n^{1/n}=r^{-1}>1.}
$$

Proof. The negative-part series $M$ has radius at least $r$ because its coefficients are bounded by the absolute Li coefficients. If its radius were greater than $r$, the positive-part series $P=F+M$ would have radius exactly $r$ and nonnegative coefficients but be analytic at $r$. Pringsheim's theorem forbids this. Thus $M$ has radius $r$, giving the conclusion by Cauchy-Hadamard. In particular, for every $1<q<1/r$, $\lambda_n<-q^n$ infinitely often.

For any particular right zero $\rho=\beta+i\gamma$, retain $\alpha=2\beta-1$ and $R=|\rho|$. Then

$$
r^{-1}\ge\frac{R}{\sqrt{R^2-\alpha}},\qquad
\log(r^{-1})\ge\frac{\alpha}{2R^2}.
$$

This gives a complete contradiction endpoint weaker in appearance than proving every Li coefficient positive:

**Open one-sided arithmetic estimate L.** For every $\varepsilon>0$, there is $C_\varepsilon$ such that $\lambda_n\ge-C_\varepsilon e^{\varepsilon n}$ for all $n$. Completion implies RH by the proved exponential negative-subsequence obstruction. It is still RH-strength; equivalent positivity criteria do not provide it. Positivity on an arbitrary sparse cofinal subsequence of $n$ does not suffice.

### Ordinary proof of the exact screw normalization

For $t\ge0$, Suzuki defines

$$
\begin{aligned}
\Psi(t)={}&4(e^{t/2}+e^{-t/2}-2)
-\sum_{n\le e^t}\frac{\Lambda(n)}{\sqrt n}(t-\log n)\\
&+\frac t2\left[\psi(1/4)-\log\pi\right]
+\frac14\left[C-e^{-t/2}\Phi(e^{-2t},2,1/4)\right],
\end{aligned}
$$

where $C=\pi^2+8G=\Phi(1,2,1/4)$, with $G$ Catalan's constant, and extends $\Psi$ evenly. The paper uses $g=-\Psi$ and the anchored kernel

$$
K_\xi(t,u)=g(t-u)-g(t)-g(-u)+g(0).
$$

The repository has

$$
g_{\rm ar}(t)=-4(e^{t/2}+e^{-t/2}-2)
+\sum_n\frac{\Lambda(n)}{\sqrt n}(|t|-\log n)_+
+c|t|-4\sum_{k\ge0}\frac{1-e^{-(4k+1)|t|/2}}{(4k+1)^2},
$$

with $c=(\gamma_E+\pi/2+3\log2+\log\pi)/2$. This is exactly $-\Psi$ in ordinary mathematics. Indeed,

$$
e^{-t/2}\Phi(e^{-2t},2,1/4)=16\sum_{k\ge0}\frac{e^{-(4k+1)t/2}}{(4k+1)^2},
\quad C=16\sum_{k\ge0}(4k+1)^{-2},
$$

and $\psi(1/4)=-\gamma_E-\pi/2-3\log2$. The prime sum is finite on each bounded support, including hinge endpoints with zero contribution. All series are absolutely convergent. These rewrites fix every sign, polar term, constant, and archimedean tail.

For completeness, the digamma constant follows from reflection and duplication: $\psi(3/4)-\psi(1/4)=\pi$ and $\psi(1/4)+\psi(3/4)=2\psi(1/2)-2\log2=-2\gamma_E-6\log2$. The Lerch constant follows by separating odd reciprocal squares: the sums over $4k+1$ and $4k+3$ have sum  $\pi^2/8$  and difference Catalan, giving $16\sum_{k\ge0}(4k+1)^{-2}=\pi^2+8G$.

The repository's formal documentation correctly leaves this Lerch/digamma identification open. The ordinary proof above does not claim that formal gap has been discharged. Relevant modules are ArithmeticScrewKernel, ScrewArchimedeanSeries, ArithmeticScrewQuadraticDecomposition, ArithmeticDyadicPositivityTransfer, and ArithmeticFiniteApproxPositivity.

### Cofinal weighted screw-energy obstruction

Suzuki's unconditional transform identity is

$$
\int_0^\infty\Psi(t)e^{izt}\,dt
=-z^{-2}\frac{\xi'}{\xi}(1/2-iz),\qquad\Im z>1/2.
$$

For $\varepsilon>0$ define $A_\varepsilon(T)=\int_0^T e^{-2\varepsilon t}|\Psi(t)|^2dt$. Any right zero $\rho=1/2+\delta+i\gamma$ forces

$$
\boxed{A_\varepsilon(T)\longrightarrow\infty
\quad\text{for every }0<\varepsilon<\delta.}
$$

Proof. If $A_\varepsilon(\infty)$ were finite, Cauchy-Schwarz gives absolute locally uniform convergence of the transform on $\Im z>\varepsilon$, hence an analytic function there. By continuation of the displayed identity, the meromorphic function on its right would have no pole in that half-plane. But $z_\rho=i(\rho-1/2)=-\gamma+i\delta$ is a genuine log-derivative pole; the factor $z^{-2}$ cannot remove it. Contradiction.

Thus the following is an individually sufficient open estimate:

**Open cofinal arithmetic estimate S.** For every $\varepsilon>0$, $A_\varepsilon(T)$ is bounded along an unbounded sequence of $T$. Since $A_\varepsilon$ is monotone, this is equivalent to global boundedness, and completion yields RH. One fixed $\varepsilon$ only excludes zeros to the right of $1/2+\varepsilon$. The unconditional bound $\Psi(t)\ll e^{t/2-c\sqrt t}$ does not establish S.

The same analytic-pole argument proves $\limsup_{t\to\infty}t^{-1}\log|\Psi(t)|\ge\delta$ for every right zero. This links the logarithmic screw scale to the same $\alpha=2\delta$ appearing in raw Möbius polynomial-energy growth, without asserting that their signed energies are identical.

### Finite negative witnesses and cofinal kernel certificates

Under not RH, Suzuki's pointwise criterion gives some $t$ with $\Psi(t)<0$, hence $K_\xi(t,t)=2\Psi(t)<0$. Continuity permits rational $t$ and a strict rational negative margin. More generally a strict finite negative matrix quadratic persists after rational perturbations of all coordinates and coefficients. These are finite witnesses, although no useful bound on their first scale follows merely from the criterion.

A finite negative quadratic also persists under sufficiently accurate dyadic L² approximation on a fixed compact window. In fact, a pointwise witness $\Psi(t)<0$ supplies mean-zero smooth tests explicitly: for a smooth unit-mass bump $\phi_h$ supported near zero, take $u_h(x)=\phi_h(x-t)-\phi_h(x)$. By continuity, its convolution quadratic for $g$ tends to $2g(0)-g(t)-g(-t)=2\Psi(t)<0$. Thus a sufficiently narrow bump already has negative quadratic. Approximate this fixed bump difference in L² by exact mean-zero dyadic averages. Therefore, after the exact normalization above, not RH forces some exact arithmetic Haar matrix to possess a negative direction. Its dimension/window may be large. The proved repository density/continuity transfer supplies the ordinary contrapositive argument.

**Open cofinal kernel certificate K.** For each fixed window $R$, exhibit exact finite approximation PSD certificates on a cofinal sequence of Haar levels. Nesting of the Haar spaces propagates positivity down to every fixed level; density gives all mean-zero tests; normalization and Suzuki give RH. All cutoffs, prime powers, cosh/sinh polar terms, primitive terms, and archimedean tails must be included. A few successful finite levels or separately cofinal cutoffs do not suffice.

An alternative ordinary formulation uses windows $R_j\to\infty$ and global mesh $\Delta_j=2R_j/2^{m_j}\to0$, with PSD certificates on those mean-zero cell spaces. Every compact mean-zero smooth test can be approximated by its cell averages while remaining mean-zero. Kernel quadratic continuity then gives global positivity. These coupled exhaustion conditions prevent a large-window/coarse-mesh quantifier error.

### Negative witness transfer to proposed Hilbert generators

Suppose a finite target Hermitian matrix $K$ is approximated by genuine Hilbert Gram matrices $B_N=(\langle h_{N,i},h_{N,j}\rangle)$. If $\|K-B_N\|_{\rm op}\to0$ cofinally, then $K$ is PSD, because for every coefficient vector $c$,

$$
c^*Kc\ge-\|K-B_N\|_{op}\|c\|^2\longrightarrow0.
$$

Conversely, if $c^*Kc=-\eta\|c\|^2<0$, every such Gram realization has $\|K-B_N\|_{\rm op}\ge\eta$. In particular, a negative screw diagonal demands error at least $-2\Psi(t)>0$. This is an exact obstruction to converting an always-positive Pareto/DPP Gram matrix into the desired zeta kernel. The kernel matching error must be proved to vanish; Gram positivity alone is automatic.

**Open generator estimate G.** Construct legal Pareto/DPP feature vectors whose exact Gram matrices approximate every finite screw-kernel target in operator norm, cofinally with vanishing error. Completion individually implies RH. This is a concrete bridge hypothesis, not an unconditional consequence of DPP coupling or RKHS terminology.

### Hermite-Biehler diagonal witness from the same off-line zero

Let $A(z)=\xi(1/2-iz)$, $E(z)=A(z)+iA'(z)=\xi(1/2-iz)+\xi'(1/2-iz)$, and $E^\sharp(z)=A(z)-iA'(z)$. The de Branges numerator kernel is

$$
K_E(z,w)=\frac{E(z)\overline{E(w)}-E^\sharp(z)\overline{E^\sharp(w)}}{2\pi i(\bar w-z)}.
$$

Set $Q(z)=i(\xi'/\xi)(1/2-iz)$. At a right zero of multiplicity $m$, let $z_0=i(\rho-1/2)$. Then

$$
Q(z)=-\frac m{z-z_0}+O(1).
$$

At $z=z_0-ih$, with $h>0$ small enough to remain in the upper half-plane, $\Im Q(z)=-m/h+O(1)<0$. Away from the zero, $E=A(1-iQ)$ and $E^\sharp=A(1+iQ)$, so

$$
|E|^2-|E^\sharp|^2=4|A|^2\Im Q,
\quad K_E(z,z)=\frac{|A(z)|^2\Im Q(z)}{\pi\Im z}<0.
$$

This remains valid at any multiplicity by choosing $h>0$ rather than evaluating exactly at the zero. It produces an open set of negative upper-half-plane diagonal witnesses, thus a rational complex witness. It explains why simply naming $E$ as a Hilbert-space generator cannot supply a positive kernel under not RH.

**Open diagonal generator estimate H.** Prove $|E(z)|^2\ge|E^\sharp(z)|^2$ for every rational complex $z$ in the upper half-plane. Continuity and the explicit pole witness exclude every right zero, so completion implies RH. The 2025 chain-construction theorem requires generator/operator conditions; it does not prove H for $E_\xi$.


### Multiplicity-safe confluent Hilbert-kernel obstruction

The repository's `HilbertPolyaKernelTarget` uses the entire function $X(z)=\xi(1/2-iz)$ and target

$$L(z,w)=\frac{X'(z)X(\bar w)-X(z)X'(\bar w)}{\pi(\bar w-z)}.$$

This is a holomorphic/antiholomorphic kernel, with its removable diagonal values understood. A right zero gives $z_0=-\gamma+i\delta$ in the upper half-plane. Let its multiplicity be $m\ge1$, and choose real $w$ with $X(w)\ne0$. Apply the two evaluation functionals: the $(m-1)$st derivative at $z_0$, and ordinary evaluation at $w$. Their confluent target matrix is exactly

$$\begin{pmatrix}0&b\\\bar b&L(w,w)\end{pmatrix},\qquad
b=\frac{X^{(m)}(z_0)X(w)}{\pi(w-z_0)}\ne0.$$

Its determinant is $-|b|^2<0$. To check the upper-left zero, differentiate the kernel in both variables through order $m-1$. In every numerator term at least one factor remains a derivative of $X$ of order below $m$, hence vanishes at $z_0$ or $\bar z_0$. The denominator is nonzero there because $z_0$ is nonreal. For the cross entry, only the term differentiating $X'$ exactly $m-1$ times survives. This proof therefore includes multiple zeros.

Every PSD holomorphic Gram kernel has PSD confluent evaluation matrices: derivative functionals are limits of finite difference quotients, or follow directly from Cauchy integrals and continuity of the kernel. Consequently, locally uniform approximation of $L$ on complex compact sets by genuine arithmetic Gram kernels would contradict the displayed determinant.

**Open jet-generator estimate.** Construct actual arithmetic Hilbert features, including the required derivatives or divided differences, and prove locally uniform Gram convergence to $L$. The kernel identity and its tails remain provider obligations. Mere existence of a Hilbert space or a positive arithmetic Gram matrix does not supply this convergence.

There is an exact mismatch that prevents a shortcut. At a simple critical zero with ordinate $\gamma$, the Mellin-DPP diagonal is zero, while

$$L(\gamma,\gamma)=\frac{X'(\gamma)^2}{\pi}>0.$$

The derivative is real because $X$ is real on the real axis. Scalar reweighting of the vanishing Mellin diagonal cannot identify these kernels; derivative or divided-difference features are required. This comparison is an ordinary argument, and the actual arithmetic matching estimate remains open.

### Hankel constraints and a concrete first inequality

Define $\mu_n=\frac14\int_0^\infty e^{-t/2}\Psi(t)t^n dt$. The exact low-degree transformation is

$$
\mu_0=\lambda_1,\quad\mu_1=6\lambda_1-\lambda_2,
\quad\mu_2=46\lambda_1-14\lambda_2+2\lambda_3.
$$

Consequently the first moment determinant is

$$
\mu_0\mu_2-\mu_1^2
=10\lambda_1^2-2\lambda_1\lambda_2+2\lambda_1\lambda_3-\lambda_2^2.
$$

RH failure forces a negative determinant of one finite ordinary or shifted Hankel matrix in Suzuki's criterion. Hence some finite polynomial with rational coefficients has a strictly negative weighted square moment. Finite positive Li coefficients alone do not imply these matrix inequalities. All these formulations encode the same RH obstruction in different coordinates; they are not probabilistically independent assumptions.

### Latest finite-window spectral barrier

Suzuki's 2026 v3 proves the actual lowest Weil eigenvalue $\lambda(a)$ continuous and positive for sufficiently small $a$; not RH gives $\lambda(a)<0$ somewhere and thus a finite zero. No inference from continuity prevents that crossing. Shifting by a value below $\lambda(a)$ constructs a positive metric regardless of RH.

A useful individually sufficient provider is a genuine relative noncrossing estimate: if $\lambda$ is locally absolutely continuous while positive and $\lambda'(a)\ge-C(a)\lambda(a)$, with $C$ integrable on every finite interval including any possible first-zero endpoint, Gronwall gives $\lambda(a)\ge\lambda(a_0)\exp(-\int_{a_0}^aC)>0$. Thus no finite zero exists, and RH follows. The regularity and inequality for the actual Weil operator remain open; excluding a blowup of $C$ at the first zero is essential.

Corollary 1.6 instead gives a conditional analytic limit: suitably renormalized finite self-adjoint characteristic functions must converge compact-uniformly in the upper half-plane to $\xi/(\xi+\xi')$. That limit is RH-strength, rather than a consequence of finite self-adjointness.


# Connes and full Weil positivity

### Trusted source statements and sign conventions

Connes-Consani, *Weil positivity and Trace formula: the archimedean place*, Selecta Mathematica 27 (2021), DOI 10.1007/s00029-021-00689-4, introduction equations (1)-(4), uses multiplicative Fourier transform

$$
\widehat f(s)=\int_0^\infty f(u)u^{-is}\,\frac{du}{u}.
$$

For a smooth compactly supported generator $g$, use the involution $g^*(u)=\overline{g(u^{-1})}$. Define

$$
Q_W(g)=-\sum_v W_v(g*g^*),\qquad \widehat g(i/2)=\widehat g(-i/2)=0.
$$

Their equation (4) is the Weil equivalence $RH\iff Q_W(g)\ge0$ for every such generator. A generator supported in $[e^{-T},e^T]$ produces a convolution supported in $[e^{-2T},e^{2T}]$; only prime powers $p^m\le e^{2T}$ contribute. The prime distribution is

$$
W_p(f)=(\log p)\sum_{m\ge1}p^{-m/2}\bigl(f(p^m)+f(p^{-m})\bigr).
$$

All orientations, prime powers, pole constraints, and the complete archimedean distribution must be retained. Their Theorem 6.11 gives a Sonin-compression lower bound with an explicit rank-one correction for generators supported in $[2^{-1/2},2^{1/2}]$. It establishes a restricted-window result, not positivity for arbitrary support involving primes.

Source: <https://alainconnes.org/wp-content/uploads/Selecta.pdf>.

Connes-Consani-Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1 (November 27, 2025), Theorems 3.6 and 5.10, constructs lower-bounded discrete-spectrum window operators and real-zero spectral generators. The latter theorem explicitly assumes the smallest finite Weil eigenvalue is simple and its eigenvector is even. Its determinant is, up to a nonvanishing phase, the multiplicative Fourier transform of that eigenvector. Lemma 7.3 proves convergence of an independently constructed prolate/Riemann-kernel candidate $\widehat k_\lambda\to\Xi$ on closed substrips of $|\operatorname{Im}z|<1/2$. Section 8 leaves two steps open: the simple-even property and sufficiently accurate approximation of the true eigenvector by that candidate. Subtracting the smallest eigenvalue makes the quotient form positive by construction and does not establish positivity of the original Weil form.

Source: <https://arxiv.org/pdf/2511.22755>.

The older Connes trace paper proves local and semilocal trace formulas; it leaves the global trace passage open. Its precisely stated Theorem VIII.5 in the fetched version is formulated for positive-characteristic global fields, with the number-field analogue subsequently discussed. Therefore a report should not silently transfer that theorem's literal statement to $\mathbb Q$ or treat a global trace limit as already proved for zeta. Geometric prime terms stabilizing for a fixed compact test function does not establish convergence of the compressed spectral traces or the disappearance of every remainder.

Source: <https://arxiv.org/pdf/math/9811068>.


### Formal Weil witness and a complete matrix-matching barrier

The repository's `RH/WeilConverse.lean` establishes the equivalence between RH and positivity of the actual arithmetic Weil pairing. Under failure, the existing reflected smooth-test construction yields a two-dimensional block

$$\begin{pmatrix}0&m\\m&0\end{pmatrix},$$

where $m$ is the multiplicity of the selected off-line zero. Its negative eigenvalue is $-m$, and its determinant is $-m^2$. This witness requires no simplicity assumption. The construction retains all pole, prime-power and archimedean terms in the actual Weil form.

If genuine Hilbert Gram matrices $B_j$ approximated this target block in operator norm, the fixed negative eigenvector would force $\|B_j-M\|_{\rm op}\ge m$ for every $j$. Thus an arithmetic Gram approximation with error tending to zero would contradict failure. Positivity of the completed Nyman tests alone cannot provide such a bridge: their Weil matrices are identically zero unconditionally. The correct target is the full Weil form on all legal tests.

### Proven new deduction: cofinal approximate Weil positivity suffices

Write $h(t)=g(e^t)$, and let $\mathcal J_T$ consist of the smooth functions supported in $(-T,T)$ satisfying

$$
\int h(t)e^{t/2}\,dt=\int h(t)e^{-t/2}\,dt=0.
$$

Define the actual Rayleigh infimum

$$
\kappa(T)=\inf_{0\ne h\in\mathcal J_T}
\frac{Q_W(h)}{\|h\|_{L^2(dt)}^2}.
$$

Here $Q_W(h)$ means the same exact Weil form after logarithmic change of variables; it does not refer to the Pareto Gram matrix. Since $\mathcal J_{T_1}\subset\mathcal J_{T_2}$ for $T_1<T_2$, $\kappa(T)$ is nonincreasing. This holds for the Rayleigh infimum without needing a claim that every chosen discretization captures its bottom eigenvalue.

**Proposition W1.** If there are $T_j\to\infty$ and $\varepsilon_j\to0$, $\varepsilon_j\ge0$, such that

$$
Q_W(h)\ge-\varepsilon_j\|h\|_2^2
\quad\text{for every }h\in\mathcal J_{T_j},
$$

then RH holds.

**Proof.** Fix a legal smooth compactly supported $h$. For all sufficiently large $j$, it belongs to $\mathcal J_{T_j}$, so the displayed bound holds. The left side and its norm are fixed. Letting $j\to\infty$ yields $Q_W(h)\ge0$. Apply Weil's criterion. No interchange of a zero sum with a moving family is used. $\square$

**Failure condition.** Under $\neg RH$, Weil's criterion supplies a nonzero $h_*$ with $Q_W(h_*)=-\delta\|h_*\|_2^2$, $\delta>0$. Consequently

$$
\boxed{\kappa(T)\le-\delta\quad\text{for every sufficiently large }T.}
$$

Thus failure requires a persistent negative window floor. An independent research target is to prove $\limsup_{T\to\infty}\kappa(T)\ge0$, or the weaker cofinal estimates in W1. The required estimates must control the full window form, including mixed terms and all higher-frequency directions. Small positive eigenvalues in a finite numerical compression do not suffice.

### Proven new deduction: a quantitative obstruction to real-zero approximation

Let

$$
\Xi(z)=\xi(1/2+iz),\qquad
\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
$$

Assume a zero $\rho=\beta+i\gamma$ with $\beta>1/2$. It gives the nonreal zero

$$
z_0=\gamma-i(\beta-1/2)
$$

of $\Xi$. Put $a=\beta-1/2$. Choose

$$
0<r<\min\{a,\,1/2-a\}
$$

with no $\Xi$-zero on the circle $C_r=\{|z-z_0|=r\}$. This is possible by discreteness of zeros. Define

$$
m_r=\min_{z\in C_r}|\Xi(z)|>0,
\qquad \sigma=a+r<1/2.
$$

**Proposition C1 (Rouché obstruction).** Every function $A$ holomorphic on a neighborhood of the closed disk, and having no zeros in its interior, satisfies

$$
\boxed{\sup_{z\in C_r}|A(z)-\Xi(z)|\ge m_r.}
$$

In particular this holds for every nonzero entire real-zero spectral generator.

**Proof.** If the supremum were less than $m_r$, then $|A-\Xi|<|\Xi|$ on $C_r$. Rouché's theorem would give the same strictly positive number of disk zeros for $A$ and $\Xi$, contradicting the hypothesis on $A$. $\square$

This converts failure into an explicit, nonvanishing approximation-error floor near each off-line zero. It is stronger information than the bare assertion that compact convergence must fail. The floor may be extremely small for a high zero close to the critical line.

### Proven weighted Mellin rate and a concrete open spectral provider

Use actual finite eigenvectors $\xi_j$ at common cofinal pairs $(\lambda_j,N_j)$, $\lambda_j\to\infty$, for which the explicit simple-even hypotheses of Theorem 5.10 hold. Extend $\xi_j$ and $k_{\lambda_j}$ by zero outside $[\lambda_j^{-1},\lambda_j]$. Choose nonzero scalars $c_j$ and put

$$
e_j=c_j\xi_j-k_{\lambda_j},\qquad
A_j(z)=c_j\widehat\xi_j(z).
$$

Each $A_j$ has only real zeros. For $|\operatorname{Im}z|\le\sigma$,

$$
|\widehat e_j(z)|
\le\int |e_j(u)|(u^\sigma+u^{-\sigma})\,\frac{du}{u}
\le W(\lambda_j,\sigma)\|e_j\|_2,
$$

where Cauchy-Schwarz gives the exact factor

$$
\boxed{
W(\lambda,\sigma)^2
=\frac{\lambda^{2\sigma}-\lambda^{-2\sigma}}{\sigma}
+4\log\lambda.}
$$

For every fixed $\sigma>0$, $W(\lambda,\sigma)\sim\lambda^\sigma/\sqrt\sigma$. The case $\sigma=0$ has $W^2=8\log\lambda$ by its continuous limit.

**Proposition C2.** Under the explicit real-zero hypotheses and $\widehat k_{\lambda_j}\to\Xi$ locally uniformly in the open strip, the actual estimate

$$
\boxed{\|c_j\xi_j-k_{\lambda_j}\|_{L^2(du/u)}
=O(\lambda_j^{-1/2})}
$$

implies RH.

**Proof.** For every fixed $0<\sigma<1/2$, the preceding bound is $O(\lambda_j^{\sigma-1/2})\to0$. Thus $A_j\to\Xi$ uniformly on every compact subset of $|\operatorname{Im}z|<1/2$. If $\Xi$ had any off-real zero, C1 would forbid that convergence on a small surrounding circle. All nontrivial zeros lie in this strip, so RH follows. $\square$

It is enough instead to prove $\|e_j\|_2=o(\lambda_j^{-\sigma})$ for every $0<\sigma<1/2$, or directly prove the weighted $L^1$ errors tend to zero. A cofinal sequence suffices. The simple-even property and approximation estimate must hold at the **same** pairs $(\lambda_j,N_j)$.

**Quantitative failure condition.** Let $\eta_j=\sup_{C_r}|\widehat k_{\lambda_j}-\Xi|\to0$. C1 and the triangle inequality imply

$$
m_r\le W(\lambda_j,\sigma)\|e_j\|_2+\eta_j,
$$

hence

$$
\boxed{\liminf_{j\to\infty}
\lambda_j^\sigma\|c_j\xi_j-k_{\lambda_j}\|_2
\ge m_r\sqrt\sigma>0.}
$$

This is the independent stringent condition supplied by the spectral route: if RH fails, then either the required simple-even generators cannot be obtained cofinally, or their true weighted Mellin approximation must retain the displayed positive floor. Plain unweighted approximation without a sufficiently strong rate, or convergence only on the real axis, does not close the route.

**Open conjecture C.** Obtain actual simple-even minimal eigenvectors at common cofinal pairs and establish the C2 error rate after a specified normalization. The two assertions are a joint program. The first assertion alone does not imply RH. No proof of either missing assertion has been found here.

### A finite certificate design retaining all correlations

For any Hermitian block matrix

$$
M=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},
\qquad C\succeq cI, c>0,
$$

the following elementary sufficient condition preserves the complete off-diagonal block:

$$
\boxed{A-c^{-1}BB^*\succeq0\ \Longrightarrow\ M\succeq0.}
$$

Indeed, for vectors $x,y$, its quadratic form is bounded below by

$$
\langle(A-c^{-1}BB^*)x,x\rangle
+c\|y+c^{-1}B^*x\|^2.
$$

The exact condition when $C$ is positive invertible is the Schur condition $A-BC^{-1}B^*\succeq0$. In a rigorous compact-window Weil computation, $A$ represents a finite test core, $B$ its actual coupling to the remaining directions, and $C$ the high-frequency form. Establishing a valid tail lower bound and the Schur condition is a concrete way to certify a whole window. Merely checking diagonal entries or a finite head discards the obstruction in $B$. To invoke W1, such certificates need a proved cofinal schedule with error tending to zero; finitely many individually certified windows are insufficient.

### A spectral-gap estimate reducing the approximation provider

The proposed rate can be attacked through a finite, exact energy estimate rather than assuming convergence of zero sets. Let $A_j$ be the actual Hermitian finite Weil compression at $(\lambda_j,N_j)$, with simple lowest eigenvalue $\epsilon_j$, unit eigenvector $\xi_j$, and a certified gap $g_j>0$ to every other eigenvalue. Let $P_j$ be the ambient orthogonal projection onto this finite test space and put $q_j=P_j k_{\lambda_j}$. Define

$$
\mathcal E_j
=\langle A_jq_j,q_j\rangle-\epsilon_j\|q_j\|_2^2\ge0.
$$

**Proposition C3.** With $c_j=\langle k_{\lambda_j},\xi_j\rangle$, using the inner-product convention that makes $c_j\xi_j$ the orthogonal projection,

$$
\boxed{\|k_{\lambda_j}-c_j\xi_j\|_2^2
\le\|(I-P_j)k_{\lambda_j}\|_2^2
+\frac{\mathcal E_j}{g_j}.}
$$

**Proof.** Expand $q_j$ in an orthonormal eigenbasis of $A_j$. Every coefficient outside the bottom eigenspace contributes at least $g_j$ times its square to $\mathcal E_j$. The truncation remainder $(I-P_j)k_{\lambda_j}$ is orthogonal to the finite test space, so its squared norm adds exactly. $\square$

An explicit sufficient open provider is therefore

$$
\boxed{\|(I-P_j)k_{\lambda_j}\|_2^2
+\mathcal E_j/g_j=O(\lambda_j^{-1}),}
$$

at common cofinal pairs with the required simple-even property and $c_j\ne0$. It yields C2 and contradicts every off-line zero. The quantity $\mathcal E_j$ uses the complete actual quadratic form and the actual smallest eigenvalue, rather than a guessed positive eigenvalue or a diagonal approximation. The gap must be certified; a tiny energy excess is insufficient when the gap is even smaller. Under failure, C1-C2 force this combined certificate to violate the required rate whenever its real-zero hypotheses hold.


# Methods, verification and provenance

The investigation used primary-source web searches, current GitHub source, parallel read-only mathematical audits, and Wolfram symbolic evaluation. A dedicated callable Deep Research endpoint was not available. The work therefore reports its actual source-based investigation, rather than attributing results to such an endpoint. Unverified claimed RH proofs and inaccessible certificate claims were excluded.

Wolfram's context endpoint eventually responded, but supplied no research-level theorem used here. Its language evaluator checked finite identities: weighted square completion, a Hermitian determinant, the Li transformed-zero modulus, the digamma constant, the termwise Lerch rescaling, the first Hankel polynomial, the Hermite-Biehler numerator, and the exact Connes weighted Mellin norm factor. Exact zero outputs certify those finite algebraic or special-function rewrites only. They do not prove analytic continuation, infinite-series estimates, density, operator convergence, or RH.

## Formal additions in this continuation

The checked addition to `Analysis/WeightedScalarEnergy.lean` proves the exact identity

$$2wg^2+2w(g-m)^2=wm^2+w(2g-m)^2$$

and the associated nonnegative weighted summability transfer. Its consumer theorem `actual_square_not_summable_of_model` says a nonsummable model plus a summable full error envelope forces nonsummability of the actual series. This is the generic scalar part of route A; the prime model and error estimates have not been formalized or proved.

The checked module `RH/LiFailureWitness.lean` proves `not_RH_exists_negative_li` from the existing unconditional theorem `LiCriterion.li_criterion_rh_iff`. Its Taylor index $n$ denotes the usual coefficient $\lambda_{n+1}$. The existing Xi-order bridge discharges the order/factorization requirements; no new external theorem is inserted as a local axiom. The ordinary exponential negative-subsequence proof in this report is stronger than that new formal contraposition, and is not presented as a Lean theorem.

The coherent candidate completed with exit code 0 and `verified: true`, job `job_qZe6NTYrJc0bp7EmLO3M5l3K03D7POrD`, code SHA-256 `72807b790983f0ff2a1f32ef8e4e44648ed63f9e43681e4a13d509da48eda01c`. Axiom inspection reported only `propext`, `Classical.choice`, and `Quot.sound` for the inspected additions. The publication checkpoint receipt is recorded separately after it reaches terminal status; a queued job is not publication evidence.

The imported Li theorem retains its upstream source attribution to Nicholas Bulka's `li-criterion-rh-equivalence-lean` project, Apache 2.0, pinned by the repository fidelity record at commit `35df682f3b709ffe5fbcfdd452dfa964bd622b87`. The source-to-Taylor normalization is separately documented in the repository. Upstream source: <https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean/blob/main/Lc/LiCriterion/XiOrderBridge.lean>.

## Source history and scope

The repository reviewed for this continuation is `Cnoack3/RiemannResearch` at `e8a91f1f62c4ac996df53ac64db2c0bf8af51b84`. The previous signed-intersection report began from `52d13f4fd91907fd499273bda0e5dac2c8b75077` and was subsequently expanded and published. Its full conditions, including the cofinal/inverse/DPP/Mellin/coupling/Bagchi coverage audit, are carried forward below. The present PDF is a new report, rather than a replacement of that earlier artifact.

The earlier raw and inverse growth candidate completed Lean with exit code 0, `verified: true`, job `job_sFBEZ1nAf8AhlkKJHGb3sJXTJkhDCG36`, SHA-256 `ad1b7c76133e9c37b03703e753d68c686b7026ceae3600ffdee857fd2e61980c`. The common-joint candidate likewise completed successfully, job `job_7FkdpQUWJ5Uch9WLm9OaYdhunB3dM-WI`, SHA-256 `634836e419e9d5f8c40889e05c5c4fd24763f3eaa9982909dca4c6d115f27663`. Their inspected declarations also used only the three standard foundations. These historical candidate receipts are evidence for those declarations, rather than a claim that every source in the repository was rebuilt during this continuation.

# Complete conditions carried forward

This appendix preserves the previous conditions and their assumption boundaries. References to numbered sections in the carried-forward text concern this appendix's original order.

### 1. Keep the two projection problems distinct

Let

$$H=\left\{f:\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)}<\infty\right\},\qquad
g_d(n)=\frac{n\bmod d}{d},\qquad V=\overline{\operatorname{span}}\{g_d:d\ge2\}.$$

For the constant target, put

$$r=1-P_V1,\qquad D=\|r\|^2=1-q_\infty.$$

For the physical first-point target, write $r_{\rm pt}$ for its closed residual and $\Delta=\|r_{\rm pt}\|^2$. Under $\neg RH$, both are positive, and the canonical tail certificate $z$ satisfies

$$C_N\longrightarrow C_\infty=\|z\|^2=\Delta^{-1}-2<\infty,
\qquad z_N=\operatorname{tailMinimum}(N)\longrightarrow z.$$

These two residual energies are different. Likewise, `ProjectionSchur.schurEta/schurSigma` and `TailCapacity.schurEta/schurSigma` are different families. The former telescope captured constant energy; the latter telescope tail capacity. Equating them would fabricate a contradiction.

For every genuine residue-tail certificate $w$, the repository proves

$$\|w\|^2=C_N+\|w-z_N\|^2,$$

and, under failure,

$$\|w\|^2=\|z\|^2+\|w-z\|^2.$$

Thus the same canonical certificate must satisfy all its tail, sign, interpolation and moment constraints. It is not permissible to choose a different favorable witness for each condition.

### 2. Inventory of the relevant criterion families

The inventory groups equivalent formulations rather than counting renamed versions as independent obstructions. Discovery used bounded declaration searches, source ranges, existing obstruction notes and the current GitHub branch. It is a research inventory, not a claim that every declaration in the large repository was newly rebuilt or every historical proposed criterion accepted.

### Constant projection, captured energy, fixed coefficients, Gram correction

Representative modules: `ParetoNormClosure`, `MobiusCoefficientStabilization`, `ResidueGramMobiusCorrection`.

Necessary consequence: $D>0$; captured energy tends to $1-D<1$; some fixed coefficient targets fail, with cofinally wrong coefficients.

Assumption audit: Many formulations describe the same residual. Several formal RH converse directions still take a density or Baez-Duarte provider explicitly. The directions used for contraposition are unconditional.

### Constant-projection Schur saturation

Representative modules: `ResidueSchurLimits`, `ResidualGainObstruction`.

Necessary consequence: Total captured gain $1-D$; relative gains summable; exact logarithmic budget $\log(e_0/D)$.

Assumption audit: These are constant-projection gains, not capacity gains.

### Residual tails

Representative modules: `ResidualTailPNT`, `ExactHeadResidualTail`.

Necessary consequence: $t_N\to0$ but $Nt_N\to\infty$; quantitative lower bound $t_N\gtrsim D^2\log N/(N\log\log N)$.

Assumption audit: The classical PNT premise is discharged in this repository result. A cofinally bounded normalized tail remains an open arithmetic provider.

### Exact heads and L1 approximation

Representative modules: `ParetoExactHeadResidual`, `RHFalseEnergyConsequences`.

Necessary consequence: Every legal exact-head error has a same-zero polynomial energy floor; legal L1-convergent approximants cannot have the required subpower energy savings.

Assumption audit: Full norms and physical tails remain.

### Natural Mobius correction

Representative modules: `NaturalMobiusResidualEscape`, `RawMobiusFiniteWindowCriterion`.

Necessary consequence: Actual inverse source energy diverges, with the sharper same-zero lower bound in Section 4.

Assumption audit: Small fixed components before inversion do not control a growing inverse matrix.

### Signed raw Gram sums

Representative modules: `RawMobiusSignedGramEnergy`.

Necessary consequence: Signed off-diagonal energy has a positive polynomial lower bound.

Assumption audit: Both orientations and signs of all pairs remain. A subpower signed upper bound is not established.

### Tail averages and centered primitives

Representative modules: `ParetoTailAverageCriterion`, `NaturalMobiusCenteredPrimitiveTests`.

Necessary consequence: For every $L$, the centered tail-average square sum diverges, although the consecutive-difference square sum is $D-D^2$; every stated logarithmic primitive saving fails.

Assumption audit: Square-summable differences do not imply convergence or square-summable deviations from a constant.

### Regularized shifted minima

Representative modules: `NoorRegularizedApproximation`.

Necessary consequence: Unscaled minima may tend to zero, while divided minima retain a lower limit at least $D$.

Assumption audit: The missing unscaled/divided rate cannot be removed.

### Weighted approximations and moving Hardy edges

Representative modules: `ParetoWeightedApproximationRH`, `ExactHeadMovingHardyRH`.

Necessary consequence: A zero creates a positive weighted-energy floor for each weight below its threshold; uniform bounds as edges approach $1/2$ fail.

Assumption audit: Existing convergence toward the line $1$ does not give the necessary moving boundary near $1/2$.

### First-site capacity, trials and certificates

Representative modules: `ParetoTailCapacityDuality`, `IntegerDPPVacancyCertificates`, `IntegerDPPCertificateCutoffBridge`.

Necessary consequence: Finite capacity, positive first-site vacancy and a genuine canonical certificate.

Assumption audit: Finite trial optimizers and cutoff equivalences are not constructions of arbitrarily small errors.

### All-site holes, hazards, damped determinants

Representative modules: `IntegerDPPAllSiteObstruction`, `IntegerDPPPowerWeightedHoles`, `IntegerDPPDampedConvergence`.

Necessary consequence: One common zero supplies positive holes at every site; suitable weighted hole series diverge; hazards are summable; damped limit is strictly above its benchmark.

Assumption audit: Offsite and physical-tail contributions remain.

### Capacity prime budgets

Representative modules: `ParetoFirstSitePrimeBudget`, `ParetoFirstSitePrimeAlignment`.

Necessary consequence: $A_N/U_N\to-1$; $V_N-U_N=o(\sqrt{U_N})$, $U_N+X_N=o(\sqrt{U_N})$; prime and nonprime survivors have finite total energy.

Assumption audit: The positive source diverges, but its actual signed cancellation is retained.

### Angular blocks, complete trees and CRT tests

Representative modules: `ParetoFirstSitePrimeBlocks`, `ParetoFirstSitePrimeMultiscale`, `ParetoFirstSiteAdjacentContrasts`.

Necessary consequence: Actual block scatter, complete internal split trees, historical drift and all chosen normalized contrast series are summable.

Assumption audit: Fixed-vector and finite-column transfer applies only to fixed objects. Growing full-dictionary screening remains.

### One-sided arithmetic and physical masses

Representative modules: `MobiusResidualOneSidedMass`, `ResidualPhysicalSignMass`, `MobiusResidualSignOscillation`.

Necessary consequence: Both signs occur cofinally; both charge masses and both signed physical first moments diverge.

Assumption audit: No absolute convergence or one-sided positivity can be silently imposed.

### Two optimal coefficients

Representative modules: `OptimalTwoCoefficientCriterion`.

Necessary consequence: $4-3c_{\infty,2}-c_{\infty,3}\ge(23/24)D>0$.

Assumption audit: The exact norm-square remainder is retained.

### Damped moving heads

Representative modules: `DampedMobiusSparseHeadDichotomy`.

Necessary consequence: At every sufficiently small positive damping, every moving cutoff has divergent actual signed off-diagonal energy.

Assumption audit: The consequence concerns actual centered damped rows, not independent random signs.

### Strip zeros and Chebyshev Mellin continuation

Representative modules: `RiemannHypothesisRightHalfStrip`, `ChebyshevMellinRH`.

Necessary consequence: A common right-half-strip zero and a pole of the continued Chebyshev error transform.

Assumption audit: Analyticity of the continuation is distinct from convergence of a proposed integral.

### Burnol products and Li norms

Necessary consequence: Positive zero-product defect; failure of at least one RH-equivalent norm identity.

Assumption audit: `hBurnol` is explicit in formal projection consequences. An RH-equivalent positive norm identity cannot be imported as unconditional.


The existing `RHFalseJointObstruction.lean` already combines the canonical certificate, common-zero site floors, head barriers, wrong coefficients, norm escape, sign excursions and determinant defect. This continuation preserves that theorem and adds the newer signed-screening constraints.

### 3. Exact capacity accounting under failure

Use the capacity Schur variables. At budget row $n$, the prospective conductor is $p=n+3$. Put

$$a_n=\operatorname{factorialPrimeDelta}(n)>0,\quad
b_n=\operatorname{factorialPrimeError}(n),\quad
w_n=\frac{\mathbf1_{p\ \mathrm{prime}}}{\sigma_{n+1}}.$$

Then $\eta_{n+1}=a_n+b_n$ at prime rows. Define the complete cumulative source, error and cross energies $U_N,V_N,X_N$, and the nonprime gain budget $J_N$. Exactly,

$$C_{N+1}=C_1+U_N+V_N+2X_N+J_N.$$

The signed mixed term is indispensable. The alignment identity rewrites this as

$$C_{N+1}=C_1+R_N+S_N+J_N,$$

where $R_N=(U_N+X_N)^2/U_N$ and $S_N=V_N-X_N^2/U_N$ are nonnegative. Under failure, $R_N\to0$, $S_N$ has a finite limit, and $J_N$ has a finite limit. In particular,

$$V_N-U_N=o(\sqrt{U_N}),\qquad U_N+X_N=o(\sqrt{U_N}),\qquad A_N/U_N\to-1.$$

For any finite future window, the checked identity is

$$\|z-z_{N+1}\|^2=
\sum_{i<k}\mathrm{primeGain}_{N+i}
+\sum_{i<k}\mathrm{nonprimeGain}_{N+i}
+\|z-z_{N+k+1}\|^2.$$

All nonprime rows and the final remaining error are visible. Let

$$T_N=\|z-z_{N+1}\|^2=C_\infty-C_{N+1}\longrightarrow0.$$

Every actual future prime survivor window is bounded by this single $T_N$, independently of the length or of how the window is selected.

### 4. The same zero forces signed raw and inverse growth

Select $\rho=\beta+i\gamma$, $1/2<\beta<1$, with $\zeta(\rho)=0$, and write $\alpha=2\beta-1>0$. The checked Lean assembly gives, eventually,

$$\boxed{O_N\ge\frac{\alpha}{96|\rho|^2}(N+1)^\alpha-2H_N-\frac13,}$$

where $O_N$ is the full signed raw Mobius off-diagonal Gram sum. It is not the sum of absolute values, and both pair orientations remain.

For the actual inverse source quadratic form, the same zero gives, for $n\ge2$,

$$\boxed{I_n\ge\frac{\alpha}{96|\rho|^2}(n+2)^\alpha-e_0-\frac13.}$$

Here $I_n=(b_n+G_n\mu_n)^TG_n^{-1}(b_n+G_n\mu_n)$ with the repository's matrix indexing. The proof uses the exact equality between the natural and physical raw residuals, and the exact norm split $\|A_n\|^2=e_n+I_n$.

For every legal $f$ agreeing with $1$ through physical coordinate $N$, the same zero also gives

$$\|1-f\|^2\ge\frac{\alpha}{|\rho|^2}(N+1)^\alpha.$$

These are constraints on the same actual zero, not unrelated existential witnesses. They coexist with finite screened capacity because raw and adaptively screened quantities differ.

### 5. Rigidity of the actual prime survivors

For prime $p=n+3$, define

$$s_p=\frac{\eta_{p-2}}{\delta_{p-3}}
=1+\frac{\operatorname{error}_{p-3}}{\delta_{p-3}}.$$

The checked harmonic floor gives

$$\frac{s_p^2}{4H_{p-1}}\le\mathrm{primeGain}_{p-3}.$$

Consequently, under failure,

$$\sum_p\frac{s_p^2}{H_{p-1}}<\infty.$$

For the finite exceptional set $B(N,k,\varepsilon)$ of actual prime rows in $[N,N+k)$ with $|s_p|\ge\varepsilon$, Lean proves

$$\boxed{\frac{\varepsilon^2\,|B(N,k,\varepsilon)|}
{4H_{N+k+1}}\le T_N.}$$

This works for every length, including adaptively chosen lengths. It yields the ordinary consequence that fixed-$\varepsilon$ exceptions up to $X$ number $o(\log X)$.

#### Stronger source estimate: the exceptions are actually finite

The exact factorial coprime reciprocal-square mass is

$$M_p=\prod_{q\ge p,\ q\ \mathrm{prime}}(1-q^{-2})^{-1},\qquad
\delta_{p-3}=\frac{M_p}{p^2(M_p-1)},\qquad
0<\sigma_{p-2}\le\frac{H_{p-1}}{p^2}.$$

This uses the actual reciprocal-square mass from `ParetoEulerProduct` and `ParetoCoprimePrimeObservation`. It does not replace the Pareto norm or delete a tail.

Partial summation and classical PNT give

$$\sum_{q\ge p}q^{-2}\sim\frac1{p\log p},\qquad
M_p-1\sim\frac1{p\log p},\qquad
\delta_{p-3}\sim\frac{\log p}{p}.$$

For clarity, partial summation gives

$$\sum_{q\ge p}q^{-2}=-\frac{\pi(p^-)}{p^2}
+2\int_p^\infty\frac{\pi(t)}{t^3}\,dt,$$

and the two leading terms combine to $1/(p\log p)$. The logarithm of the Euler product differs from this sum by $O(\sum_{q\ge p}q^{-4})$, which is smaller. Therefore

$$\frac{\delta_{p-3}^2}{\sigma_{p-2}}\ge(1-o(1))\log p.$$

An explicit upper prime-count estimate alone suffices for a weaker constant. Dusart's unconditional $\pi(t)\le t/(\log t-1.1)$ above $60184$ implies $\pi(t)\le2t/\log t$ for $t\ge60200$. Thus

$$\sum_{q\ge p}q^{-2}\le\frac4{p\log p},\quad
\log M_p\le\frac8{p\log p},\quad
M_p-1\le\frac{16}{p\log p}$$

for $p\ge60200$. Since $H_{p-1}\le2\log p$ there,

$$\boxed{\delta_{p-3}\ge\frac{\log p}{16p},\qquad
\frac{\delta_{p-3}^2}{\sigma_{p-2}}\ge\frac{\log p}{512}.}$$

Comparison with the summable actual prime gain proves

$$\boxed{\sum_p(\log p)s_p^2<\infty.}$$

Thus $s_p\sqrt{\log p}\to0$ along every prime, and each fixed-$\varepsilon$ exceptional prime set is finite. This analytic assembly is an ordinary proof, not a newly formalized Dusart or Euler-tail provider. The asymptotic source calculation was already recorded in `AdjacentSchurResearch20260930.md`; the sharpened failure consequences are the new assembly here.

For prime blocks $[X,2X)$, let $T(X)$ denote the corresponding remaining canonical capacity error. PNT and the stronger source floor give

$$\operatorname{mean}_{X\le p<2X}s_p^2\ll\frac{T(X)}X=o(X^{-1}).$$

Pointwise small survivors alone are not a contradiction: a divergent gain series can have every term tending to zero. The decisive distinction is aggregate summability.

### 6. Stronger necessary condition on the actual pooled gap

Take $N=2^j$. On the two consecutive budget windows $[2N,3N)$ and $[3N,4N)$, define the actual pooled error slopes $X_L/U_L$ and $X_R/U_R$, and let

$$G_j=X_R/U_R-X_L/U_L.$$

Prime conductors differ from budget indices by the exact shift $p=n+3$. The constant aligned component cancels in this difference. The complete split equality is

$$S_{\rm parent}=S_L+S_R+
\frac{U_LU_R}{U_L+U_R}G_j^2.$$

Using the source asymptotic above and $\vartheta(x)\sim x$ gives

$$U_L,U_R\ge(1-o(1))N,\qquad
\frac{U_LU_R}{U_L+U_R}\ge(1-o(1))\frac N2.$$

For example, eventually both sources exceed $N/4$, so $S_{\rm parent}\ge NG_j^2/8$. The parent windows are disjoint dyadic windows; their complete scatters are bounded by the summable actual angular energy under failure. Therefore

$$\boxed{\neg RH\ \Longrightarrow\ \sum_j2^jG_j^2<\infty,
\qquad G_j=o(2^{-j/2}).}$$

This is stronger by two powers of the logarithmic scale than the earlier source-floor consequence. It controls the same actual screened $G_j$. Prime density supplies its weight, not a lower bound on its sign or size.

A sufficient arithmetic contradiction is now

$$\sum_j2^jG_j^2=\infty.$$

One stronger concrete provider would be fixed $\varepsilon>0$ and a set $E$ with divergent $\sum_{j\in E}(j+1)^{-1}$ such that

$$|G_j|\ge\frac{\varepsilon}{\sqrt{2^j(j+1)}}\quad(j\in E).$$

No such provider is proved or inserted as an axiom. The finite split identity is formalized; this stronger eventual rate assembly is ordinary mathematics.

### 7. A sharper discrete obstruction from the same zero

Write $R=|\rho|$, $\alpha=2\beta-1\in(0,1)$, and

$$a_\rho(n)=\frac{n^{-\rho}-(n+1)^{-\rho}}\rho
=\int_n^{n+1}x^{-\rho-1}\,dx,\qquad
K_\rho=\sum_{n\ge1}n(n+1)|a_\rho(n)|^2.$$

Abel summation, initially in $\Re s>1$ and then analytic continuation to $\Re s>0$, yields

$$L_\rho(g_d)=\sum_na_\rho(n)g_d(n)
=\frac{(d^{-1}-d^{-\rho})\zeta(\rho)}\rho=0,
\qquad L_\rho(1)=\rho^{-1}.$$

The witness is continuous on $H$. Consequently, for the actual constant residual,

$$\boxed{D\ge\frac1{R^2K_\rho}.}$$

This uses the discrete functional norm rather than replacing it by a larger continuous norm. To bound it, observe

$$|a_\rho(n)|\le\min\{n^{-\beta-1},2n^{-\beta}/R\}.$$

For any $T>0$, the full head obeys

$$\sum_{n\le T}n(n+1)|a_\rho(n)|^2
\le\frac{8T^{2-\alpha}}{R^2}.$$

For every remaining interval, weighted Cauchy-Schwarz gives

$$n(n+1)|a_\rho(n)|^2\le\int_n^{n+1}x^{-2\beta}\,dx.$$

Keeping the whole tail therefore gives

$$\sum_{n>T}n(n+1)|a_\rho(n)|^2\le T^{-\alpha}/\alpha.$$

Take $T=R/2$ to obtain

$$K_\rho\le\frac{2^\alpha(1+2\alpha)}\alpha R^{-\alpha}
\le\frac6\alpha R^{-\alpha},$$

and hence

$$\boxed{D\ge\frac\alpha{2^\alpha(1+2\alpha)}R^{\alpha-2}
\ge\frac\alpha6R^{\alpha-2}.}$$

This proof is ordinary mathematics and was independently reviewed. Wolfram checked the finite algebra; it is supplementary evidence, not a proof of the infinite-series statements. The existing repository already contains the annihilator in `LateralScreeningContinuation20260924.md`; this height-sensitive norm estimate is an additional quantitative assembly.

The same discrete functional also bounds the actual first-point error:

$$\Delta\ge\frac{|1-2^{-\rho}|^2}{R^2K_\rho},\qquad
C_\infty+2\le\frac{R^2K_\rho}{|1-2^{-\rho}|^2}.$$

#### Multiple zeros: retain their Gram correlations

For a finite family of off-line zeros, include multiplicity rows

$$a_{\rho,k}(n)=\int_n^{n+1}(-\log x)^kx^{-\rho-1}\,dx,
\qquad b_{\rho,k}=(-1)^kk!/\rho^{k+1}.$$

Let $K$ be their full discrete Gram matrix. The exact finite dual optimization gives

$$D\ge b^*K^\dagger b.$$

The actual residual supplies feasibility; use the inverse when the rows are independent. For the conjugate pair put $B_\rho=\sum_nn(n+1)a_\rho(n)^2$. Then

$$D\ge\frac{2\bigl(K_\rho/R^2-
\Re(B_\rho/\bar\rho^2)\bigr)}{K_\rho^2-|B_\rho|^2}.$$

This retains the cross term. Separate one-zero floors cannot simply be added. The finite-family optimization is a prose-level Hilbert-space derivation, not a new Lean theorem in this checkpoint.

### 8. What external results add, and what they do not

Burnol's continuous projection formula and the Balazard-Saias-Yor identity give

$$\Omega_\zeta=\frac1{2\pi}\int_{-\infty}^{\infty}
\frac{\log|\zeta(1/2+it)|}{1/4+t^2}\,dt
=\sum_{\Re\rho>1/2}\log\left|\frac\rho{1-\rho}\right|>0$$

under failure, counting multiplicities. If $W$ is the continuous Nyman-Beurling space, then

$$D=1-e^{-2\Omega_\zeta}+\|P_W1-P_V1\|^2.$$

The arithmetic projection remainder is essential. Kunik's discussion of the integer-step subspace explicitly separates it from the continuous projection formula. The repository's formal Burnol consequences preserve an explicit `hBurnol` hypothesis.

Guth-Maynard's 2026 version gives the unconditional density estimate

$$N(\sigma,T)\le T^{30(1-\sigma)/13+o(1)}.$$

It permits a sparse off-line set. Its large-value theorem requires bounded Dirichlet coefficients and supplies an upper estimate; it does not automatically give a lower bound for adaptively screened signed CRT contrasts.

Platt-Trudgian rigorously exclude off-line zeros through at least height $3\cdot10^{12}$. Bellotti excludes

$$\beta\ge1-\frac1{54.004(\log|\gamma|)^{2/3}(\log\log|\gamma|)^{1/3}}$$

for $|\gamma|\ge3$. Neither excludes a high zero arbitrarily close to $1/2$.

Maier-Rassias analyze smoothed Mobius trial energy under exactly one off-line quadruplet and an additional reciprocal-derivative moment bound. Their conditional polynomial growth is compatible with this repository's failure anatomy. It is not a contradiction or an unconditional provider.

Suzuki's positive Li-norm identities are themselves RH-equivalent. Their unconditionally defined square norms cannot be equated to Li coefficients when assuming failure.

A separate callable Deep Research tool was unavailable. The investigation used primary papers through web search, GitHub, read-only parallel audits and Wolfram symbolic evaluation. The earlier context request failed; subsequent context requests succeeded without supplying research-level theorems. The evaluator supplied finite symbolic checks.

### 9. Why the stringent conditions still do not contradict one another

The Mellin annihilator has coordinates $n(n+1)\overline{a_\rho(n)}\sim n^{1-\bar\rho}$. Its tail energy behaves like $N^{1-2\beta}$, so its normalized tail grows like $N^{2-2\beta}$. Thus a nonzero square-integrable obstruction can have a vanishing tail and an unbounded normalized tail. This illustrates compatibility; it does not identify that witness with the actual canonical residual.

Likewise, at the level of scalar source/survivor identities one may take prime source energy comparable to $\log p$, survivors $s_p=2^{-p}$, errors $s_p-1$, and zero nonprime gains. These satisfy divergent source, finite surviving energy, alignment saturation and all finite tree identities. They are not the repository's arithmetic rows and are not a counterexample to RH. They show why positive source estimates plus square identities alone cannot force the desired contradiction.

A very high hypothetical zero with $\beta$ close to $1/2$ has an arbitrarily small positive spectral defect and obeys the cited density and zero-free bounds. Numerical verification over a finite height range cannot exclude that remaining scenario.

### 10. Precise remaining contradiction targets

Any one of these established sufficient providers would refute the simultaneous failure conditions:

1. Prove nonsummability of the actual log-weighted prime survivor energy, with a quantitative transfer to the true Schur rows.
2. Prove $\sum_j2^jG_j^2=\infty$ for the actual screened pooled gaps; the weaker threshold in Section 6 is sufficient.
3. Obtain a nonsummable actual moving CRT contrast certificate after retaining or controlling the complete inverse-Gram screening remainder.
4. Prove a cofinal subpower upper bound on the actual signed raw off-diagonal sum, contradicting the same-zero polynomial lower bound.
5. Prove cofinal boundedness of the actual inverse source energy or of $Nt_N$, contradicting their failure growth.
6. Derive an arithmetic upper bound on $D$ smaller than the simultaneous discrete zero-Gram floor for every possible off-line zero set.

The strongest next arithmetic task is a lower estimate for actual signed survivor or contrast energy, possibly obtained from a useful explicit model with a proved weighted square-summable screening error. Fixed-column removal and upper large-sieve inequalities alone do not supply it. This is the remaining substantive gap, rather than an unstated RH-strength provider.

### 12. Coverage audit: cofinality, inverse Gram growth, DPP, Mellin and Bagchi

This audit answers the follow-up about these five families. The first edition integrated the principal cofinal barriers and integer-DPP/Mellin hole consequences, but did not separately develop operator-norm growth, the Mellin-frequency DPP, spatial coupling or Bagchi's named equivalence. This section makes their roles explicit. It adds ordinary deductions and an assumption audit; it adds no Lean declarations or external axioms.

#### Cofinal conditions: keep the quantifiers

Under failure, the checked normalized residual-tail result gives $Nt_N\to\infty$. Hence for every $K$ there is a threshold after which $Nt_N>K$ at every index. Thus there is no cofinal bounded subsequence.

Similarly, the exact signed capacity budget has $U_N\to\infty$ and $A_N/U_N\to-1$. For every fixed $\theta<1$ and $K\in\mathbb R$ this implies, eventually,

$$A_N<-\theta U_N-K.$$

Indeed choose $\theta<c<1$; eventually $A_N/U_N<-c$, and $(c-\theta)U_N>K$. This rules out the strict-fraction cofinal provider, with every signed prime cross term and nonprime gain still inside $A_N$.

The inverse-column cofinal criteria in ProjectedDualColumnConcentration.lean remain separate, explicit arithmetic obligations. With the unconditionally supplied $a>0$ and $\ell(n)=\operatorname{logProductPower}(1/11)(6+\log n)$, put $M_n(d)=\operatorname{projectedDualCoefficientMass}(n,d)$. For present conductors this is the full $\ell^1$ norm of the signed inverse-Gram column. The checked endpoint criterion and contraposition imply, under failure,

$$\exists d>1,\ \exists\varepsilon>0,\quad
e^{-a\ell(n)}M_n(d)^2\ge\varepsilon\quad\text{eventually}.$$

The stronger repository barrier applies whenever the fixed limiting correction for $d$ is nonzero: for each $b<a$, $e^{-b\ell(n)}M_n(d)^2\to\infty$. The unconditional stretched-energy provider and the existence of a nonzero fixed correction under failure permit that barrier to be used. Neither conclusion establishes divergence of the fixed column's Euclidean norm without retaining its dimension or support cost.

Separate cofinal sets need not intersect. The concentration criterion requires support, leakage and column-energy bounds at the same indices. This joint-index obligation cannot be replaced by separately cofinal estimates.

#### Matrix norm growth is unconditional

Use the Euclidean operator norm on conductor coefficients and the full Pareto Gram matrix $G_N$ for $g_2,\ldots,g_N$. For $N\ge2$,

$$G_N(N,N)=\|g_N\|_H^2
\le\frac{N-1}{N^2}+\frac1N<\frac2N.$$

The first term bounds the entire physical head $1\le n<N$, using $g_N(n)=n/N$. The second bounds the entire tail using $0\le g_N(n)<1$ and $\sum_{n\ge N}1/[n(n+1)]=1/N$. Positive definiteness and the Rayleigh principle give

$$\boxed{\|G_N^{-1}\|_{2\to2}\ge \frac1{G_N(N,N)}>\frac N2.}$$

Thus inverse-matrix unboundedness holds with either truth value of RH. It does not itself obstruct RH. Fixed inverse entries nevertheless have finite limits, as proved in ParetoInverseGramDual.lean:

$$(G_N^{-1})_{de}\longrightarrow
\langle P_Vu_d,P_Vu_e\rangle,\qquad
\|u_d\|^2-\lim_N(G_N^{-1})_{dd}
=\|(I-P_V)u_d\|^2.$$

Under failure at least one fixed dual has a positive saturation deficit. All fixed inverse diagonals attain their full dual norms exactly when $1\in V$. This identity, the actual inverse-column concentration criteria, and the growing inverse-source quadratic form are the relevant directional constraints; an operator-norm upper or lower bound alone does not replace them.

#### Integer DPP and its Mellin obstruction

For normalized integer projection kernel $K_N$, the vacancy at site $k$ is $1-K_N(k,k)$. The existing RHFalseJointObstruction theorem already retains the same-zero all-site Mellin floors, weighted-hole divergence and determinant defect. IntegerDPPMellinObstruction.lean also explicitly proves

$$v_N\ge v_\rho
=2(2\beta-1)\frac{|1-2^{-\rho}|^2}{|\rho|^2}>0,\qquad
C_N+2\le\frac2{v_\rho},\qquad
\sum_n h_n\le-\log v_\rho.$$

Here $v_N$ is the first-site vacancy, $C_N$ the complete tail capacity and $h_n$ the actual hazard. These are compatible with the summable screened gains in Sections 3-6; they do not force filling.

The Mellin-frequency DPP is an additional representation of the same finite-dimensional projection under the Mellin isometry. Its actual kernel is

$$\mathcal K_N(t,u)=E(t)\overline{E(u)}\,
v_N(t)^TG_N^{-1}\overline{v_N(u)},\qquad
E(t)=\frac{\zeta(1/2+it)}{1/2+it},\quad
v_{N,d}(t)=d^{-1}-d^{-1/2-it}.$$

MellinProjectionDPP.lean constructs the finite-rank probability law unconditionally. MellinDPPIntensity.lean proves, for positive rank, $\mathcal K_N(t,t)=0$ exactly at critical-line zeta zeros and a rank-independent positive lower bound away from them. These intensity-zero statements hold under either truth value of RH. The process is not a process of sampled zeta zeros and is not the samplewise Mellin transform of an integer configuration. An infinite locally finite frequency process requires additional local trace control; the finite-rank construction does not supply it.

#### Coupling: ordinary theorem and formal boundary

[Lyons, Determinantal probability measures, Theorem 7.1](https://arxiv.org/pdf/math/0204325) gives stochastic domination for nested closed projection subspaces. Together with monotone coupling and gluing, it supplies the ordinary mathematical route to increasing arithmetic DPPs $Z_N$. The repository proves the first-site scalar threshold coupling unconditionally. Its full spatial construction still requires SpatialWindowFeasible; IntegerDPPSpatialCoupling.lean reduces that obligation exactly to finite transport and does not supply the provider.

For every supplied monotone spatial coupling, the existing union law gives

$$\mathbb P(k\text{ never enters})=1-K_\infty(k,k).$$

Thus failure forces a positive never-entry probability at every site, and the weighted series $\sum_k(k+1)\mathbb P(k\text{ never enters})$ diverges. Coupling cannot change these fixed marginals. Even an unconditional formalization of full coupling would not establish zero vacancy. An additional arithmetic filling or weighted-hole estimate is needed.

#### Bagchi's implications

The prior handoffs identify the intended author as Bhaskar Bagchi. [Bagchi, Theorem 1](https://arxiv.org/pdf/math/0607733) states the exact ordinary equivalence in this weighted sequence space:

$$RH\iff 1\in V\iff V=H.$$

Hence under failure $V\ne H$, its projection is not the identity, and the limiting integer DPP has a nonzero defect. The constant-to-full-density direction and approximation-to-RH implications are established project components. Some formal reverse equivalences still explicitly take PositiveResidueDensityFromRH or another classical density/Baez-Duarte provider. Bagchi establishes the mathematical input; citing him does not supply its missing Lean proof. That classical formalization obligation is distinct from the open RH-strength arithmetic estimate.

These additions reinforce a consistent failure scenario: nonzero Mellin defect, persistent coupled holes, finite capacity and summable hazards, exceptionally accurate prime screening, and badly conditioned inverse matrices with the specified directional failures. No contradiction between them has been proved.

#### Earlier primary references

- Jean-Francois Burnol, *A note on Nyman's equivalent formulation of the Riemann Hypothesis*, Theorem 1.2 and Lemma 2.4: <https://arxiv.org/pdf/math/9910055>.
- Matthias Kunik, *Charakterisierung der Riemannschen Hypothese mit Hilfe eines Hilbertschen Folgenraumes*, integer-step discussion pp. 3-4: <https://math.ovgu.de/math_media/Medien/Institute/IAN/Kunik/Publikationen/rh.pdf>.
- H. M. Bui, S. J. Lester and M. B. Milinovich, *On Balazard, Saias, and Yor's equivalence to the Riemann Hypothesis*, equation (1.1), Theorem 1.2: <https://arxiv.org/pdf/1306.0856>.
- Pierre Dusart, *Estimates of Some Functions Over Primes without R.H.*, Theorem 6.9: <https://arxiv.org/pdf/1002.0442>.
- Larry Guth and James Maynard, *New large value estimates for Dirichlet polynomials*, April 7, 2026 version, Theorems 1.1-1.2: <https://arxiv.org/html/2405.20552v2>.
- Dave Platt and Tim Trudgian, *The Riemann hypothesis is true up to $3\cdot10^{12}$*: <https://arxiv.org/pdf/2004.09765>.
- Chiara Bellotti, *Explicit bounds for the Riemann zeta function and a new zero free region*, Theorem 1.2: <https://arxiv.org/pdf/2306.10680>.
- Helmut Maier and Michael Th. Rassias, *A criterion related to the Riemann Hypothesis*, Theorem 1.1: <https://arxiv.org/pdf/1705.09918>.
- Masatoshi Suzuki, *Li coefficients as norms of functions in a model space*, Theorem 1.1: <https://arxiv.org/pdf/2301.05779>.


# Primary sources for the new agenda

1. Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of Number Theory 65 (1997), 325-333. DOI 10.1006/jnth.1997.2137. <https://www.sciencedirect.com/science/article/pii/S0022314X97921375>.
2. Enrico Bombieri and Jeffrey Lagarias, *Complements to Li's Criterion* (1999), author manuscript. <https://websites.umich.edu/~lagarias/doc/bombieri.pdf>. See also Lagarias's retrospective: <https://arxiv.org/pdf/math/0404394>.
3. Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, Journal of the London Mathematical Society 108 (2023), 1448-1487. DOI 10.1112/jlms.12785. <https://arxiv.org/pdf/2206.03682>.
4. Masatoshi Suzuki, *Li coefficients as norms of functions in a model space*, Journal of Number Theory 252 (2023), 177-194. <https://arxiv.org/pdf/2301.05779>. Its norm identities are RH-equivalent.
5. Masatoshi Suzuki, *Chains of reproducing kernel Hilbert spaces generated by unimodular functions*, Annales de l'Institut Fourier 75 (2025), 1463-1508. <https://aif.centre-mersenne.org/item/10.5802/aif.3705.pdf>. Generator and operator hypotheses remain essential.
6. Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v3, revised September 23, 2026. <https://arxiv.org/html/2606.09096v3>. This is a primary preprint; its conditional spectral limits are not a proof of RH.
7. Alain Connes and Caterina Consani, *Weil positivity and Trace formula: the archimedean place*, Selecta Mathematica 27 (2021). DOI 10.1007/s00029-021-00689-4. <https://alainconnes.org/wp-content/uploads/Selecta.pdf>.
8. Alain Connes, Caterina Consani and Henri Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, November 27, 2025. <https://arxiv.org/html/2511.22755v1>. The simple-even and true-eigenvector approximation steps are explicit open hypotheses.
9. Alain Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*. <https://arxiv.org/pdf/math/9811068>. Local and semilocal results do not discharge the number-field global trace limit.
10. Russell Lyons, *Determinantal probability measures*, Publications Mathématiques de l'IHÉS 98 (2003), 167-212. DOI 10.1007/s10240-003-0016-0. <https://arxiv.org/pdf/math/0204325>.
11. Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*. <https://arxiv.org/pdf/math/0607733>. Theorem 1 gives the weighted-sequence density equivalence used here.

The user's "Lee criterion" is interpreted as Li's criterion, and "Bachdi" as Bagchi, consistently with the repository handoffs. The report uses logically distinct representations of the same obstruction; it does not multiply equivalent criteria into independent probability estimates.
