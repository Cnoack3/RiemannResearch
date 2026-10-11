# Infinite Gaussian analytic bridge toward RH

**Research continuation, 11 October 2026.** This note separates exact infinite identities, finite algebra, quantitative tail decay, and the arithmetic assertion still needed for RH. No novelty or completed RH proof is claimed.

**Verification:** all five standalone modules compiled, and nine important declaration-foundation reports passed the exact-module import check. The introducing server checkpoint validates the exported modules before publication. The named full actual Gaussian Hankel criterion is a **conditional research reduction**: its numerical tail and moment providers remain Open.

## 1. Actual zeros and an unconditional signed Laplace identity

Sum over **distinct actual nontrivial zeros** with their analytic multiplicities:
\[
\rho=\tfrac12+\delta_\rho+i\gamma_\rho,
\qquad m_\rho\in\mathbb N_{>0},\qquad
w_\rho=\rho-\tfrac12,\quad z_\rho=-iw_\rho.
\]
Both ordinate signs and every horizontal partner occur. Equivalently one may sum over the multiset, without an additional multiplicity factor. The actual strip gives \(|\delta_\rho|<1/2\). The existing reciprocal-square summability input is
\[
\sum_\rho\frac{m_\rho}{1+\gamma_\rho^2+\delta_\rho^2}<\infty.
\tag{1}
\]
For \(a>0\), define
\[
H(a)=\sum_\rho m_\rho e^{-a\gamma_\rho^2},
\qquad R(a)=\sum_\rho m_\rho e^{a w_\rho^2}.
\]
Both series converge absolutely. For every real \(x>1/2\), the exact complex identity is
\[
\boxed{\int_0^\infty e^{-x^2a}\bigl(H(a)-R(a)\bigr)\,da
=\sum_\rho m_\rho\left[
\frac1{x^2+\gamma_\rho^2}-\frac1{x^2-w_\rho^2}\right].}
\tag{2}
\]
The integral is an absolutely integrable signed complex integral. It does not replace \(R\) by an absolute-value trace and asserts no pointwise sign for \(H-R\).

Here is the complete domination argument. Put \(c=x^2-1/4>0\). The two complex rates have real parts
\[
x^2+\gamma_\rho^2,\qquad
\Re(x^2-w_\rho^2)=x^2+\gamma_\rho^2-\delta_\rho^2
>c+\gamma_\rho^2.
\]
The actual Lean majorant retains the horizontal square explicitly:
\[
\frac{m_\rho}{x^2+\gamma_\rho^2-\delta_\rho^2}
\le \left(1+\frac{5}{4c}\right)
\frac{m_\rho}{1+\gamma_\rho^2+\delta_\rho^2}.
\]
The ordinate-only rate has a smaller mass. Thus (1) controls both sums of absolute integral masses. For \(\Re q>0\),
\[
\int_0^\infty m e^{-qa}\,da=\frac m q,
\qquad \int_0^\infty|m e^{-qa}|\,da=\frac m{\Re q}.
\]
Countable integral/sum interchange proves (2). Also \(e^{-ua}\le1/(au)\) for \(a,u>0\), giving pointwise summability from the same mass majorant. Thus this actual-zero assembly requires no additional zero-height bound, counting estimate, or RH assumption.

The main declaration is `ActualZeroGaussianLaplace.infinite_signed_gaussian_laplace`. Explicit `damped_heatDefect_integrable`, `signed_resolvent_summable`, and both pointwise heat-trace summability theorems rule out any use of default values for a divergent integral or sum.

## 2. Finite real interpolation and exact contamination

Fix \(a>0\), a nonreal target \(z_0=x_0+iy_0\), and its conjugate. Gaussian weights are \(v_z=m_z e^{-az^2}\), so the pair has nonzero conjugate weights. Choose \(\xi\in\mathbb C\) with
\[
2\Re(v_{z_0}\xi^2)=-\eta<0.
\]
For any finite set \(F\) of unwanted distinct nodes, excluding the target pair, take
\[
q_u(X)=(X-\Re u)^2+(\Im u)^2,\qquad
P_F(X)=\prod_{u\in F}q_u(X)\in\mathbb R[X].
\]
At complex arguments, \(q_u(z)=(z-u)(z-\bar u)\). Write \(\xi/P_F(z_0)=b+ic\) and set
\[
p_F(X)=\left(\frac c{y_0}X+b-\frac{cx_0}{y_0}\right)P_F(X).
\]
Then \(p_F(z_0)=\xi\), \(p_F(\bar z_0)=\bar\xi\), and \(p_F\) vanishes at every unwanted node. The finite core energy is exactly \(-\eta\). No conjugation-stable cutoff is required: the real quadratic factors provide the conjugation automatically. A vanished node kills all its multiplicity; no Hermite conditions are imposed.

**Degree convention:** if \(M=|F|\), put \(d=2M\). Then \(\deg P_F=d\) and \(\deg p_F\le d+1\). Redundant factors from including conjugate unwanted nodes are permitted and counted in \(M\).

Define the real full energy \(Q_a(p)=\sum_z\Re(v_zp(z)^2)\). Whenever this series is summable, the implemented cutoff theorem gives exactly
\[
Q_a(p_T)=-\eta+
\sum_{z\notin K_T}\Re(v_zp_T(z)^2).
\tag{3}
\]
Hence a signed tail smaller than \(\eta\) proves full negativity. The stronger sufficient condition is
\[
\sum_{z\notin K_T}|v_z|\,|p_T(z)|^2<\eta.
\]
The implemented transfer also proves eventual full negativity when the core is bounded above by \(-\eta\) and the **changing-polynomial** tails tend to zero. Summability for each fixed polynomial alone supplies no such limit.

## 3. A complete paper shell estimate, with \(B=1/2\)

Use all signed nodes, weighted count \(N(s)=\sum_{|\Re z|\le s}m_z\), and the unconditional paper bound \(N(s)\le C s\log(s+2)\) for sufficiently large \(s\). For actual cutoff sets, \(M(T)\le N(T)\), hence \(d(T)=2M(T)=O(T\log T)\).

There is a fixed \(r_*>0\) such that \(|P_{F_T}(z_0)|\ge r_*\): every factor from \(|u|\ge|z_0|+1\) has modulus at least one, and the finitely many remaining nonzero factors have a fixed positive product after taking their minima with one. No uniform separation of high zeros is needed. This yields a fixed \(K\) such that, outside a sufficiently large cutoff,
\[
|p_T(z)|\le K\,3^{d(T)}|z|^{d(T)+1}.
\tag{4}
\]
Put \(b_T=T^2+1/4\) and \(D=d(T)+1\). If \(D\le aT^2/2\), then for \(t\ge T\), the inequality \(\log(1+u)\le u\) gives
\[
(t^2+1/4)^D e^{-at^2}
\le b_T^D e^{-aT^2}e^{-a(t^2-T^2)/2}.
\]
On the shell \(T+k<|\Re z|\le T+k+1\), the **global** count gives mass at most \(C(T+1)(k+1)^2\log(T+3)\), while the last Gaussian ratio is at most \(e^{-2ak}\) for \(T\ge2\). Consequently
\[
\boxed{\sum_{|\Re z|>T}|v_z|\,|p_T(z)|^2
\le C_aK^2\,9^{d(T)}b_T^{d(T)+1}e^{-aT^2}
(T+1)\log(T+3),}
\tag{5}
\]
where
\[
C_a=C e^{a/4}\frac{1+e^{-2a}}{(1-e^{-2a})^3}.
\]
This uses \(\sum_{k\ge0}(k+1)^2q^k=(1+q)/(1-q)^3\). Every omitted node, both signs, and all multiplicities remain in (5); no local unit-window count is assumed.

## 4. Growing-degree decay implemented in Lean

The stronger implemented limit assumes only
\[
\frac{d(T)\log T}{T^2}\longrightarrow0.
\tag{6}
\]
For large \(T\), \((T+1)\log(T+3)\le b_T^2\), \(9\le T^2\), and \(b_T\le T^3\). Thus the envelope in (5), apart from its fixed constant, is at most
\[
\exp\bigl(-aT^2+(5d(T)+9)\log T\bigr)\longrightarrow0.
\]
The general Lean lemma proves \(e^{-aT^2+b(T)}\to0\) whenever \(b(T)/T^2\to0\) and \(a>0\). Condition (6) also makes \((d(T)+1)/T^2\to0\), supplying the preceding shell threshold eventually. The concrete \(O(T\log(T+2))\) envelope theorem remains available. These are analytic decay statements, not assumptions that the desired horizontal energy vanishes.

## 5. Formal boundaries and the unresolved arithmetic assertion

| Formal theorem or analytic component | Open actual provider or identification |
|---|---|
| Actual infinite \(H/R\) Laplace identity and absolute convergence | Centered spectral sum equals the normalized \(\xi'/\xi\) |
| Real quadratic interpolation and exact finite negative core | Actual finite cutoffs and distinct-node reindexing |
| Exact conditional infinite-tail transfer | Uniform \(r_*\), (4), degree bound, and actual shell estimate (5) |
| Full envelope limit under (6) and its exact infinite-negative-witness assembly | Actual absolute-complex tail bound by the numerical envelope |
| Polynomial-square negativity framework | Gaussian polynomial summability and finite moment/Hankel identification |

`GaussianHankelTailBridge.not_polynomialSquareNonneg_of_nonreal_pair_and_growing_degree_tail` connects the finite pair core directly to (6) and the numerical envelope. Target membership, absolute summability, and the tail bound may hold only eventually; its constant may depend on the selected negative assigned value. It assumes no separate vanishing-tail conclusion. The concrete actual estimate (5) remains an explicit provider obligation.

The remaining normalization for the resolvent interpretation is
\[
\frac{\xi'}{\xi}(\tfrac12+x)
=x\sum_\rho\frac{m_\rho}{x^2-w_\rho^2}.
\]
Only after proving that identification does multiplying (2) by \(x\) give the actual ordinate-resolvent comparison. The Laplace identity itself supplies no missing arithmetic positivity or reverse inequality.

On paper, (3)--(6) produce a finite negative full Gaussian polynomial witness from any off-line zero. After the moment identification, positivity of every ordinary Gaussian Hankel matrix at one fixed width would therefore imply RH. The actual assertion of positivity remains unproved; counting, convergence, and finite checks do not supply it.

## 6. Sources, computational checks, and foundations

- Mathlib [improper integrals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.html) and [dominated convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/DominatedConvergence.html) provide the complex exponential integral and summable-integral interchange APIs.
- Bickel--Pascoe--Sargent, [*Zero-free regions near a line*](https://arxiv.org/abs/2108.04807), study Hankel positivity relaxations with spacing hypotheses. Their criteria are context, not an actual positivity provider here.
- Suzuki, [*Aspects of the screw function corresponding to the Riemann zeta-function*](https://arxiv.org/pdf/2206.03682), supplies related RH criteria. Theorem 1.8 uses different screw-function moments and cannot be substituted for these Gaussian moments.
- Schmüdgen, [*Ten Lectures on the Moment Problem*](https://arxiv.org/pdf/2008.12698), gives Hamburger representation from the full PSD Hankel tower; this is an alternative analytic tool, not a proof of actual PSD.

Wolfram independently returned the exact per-zero integral in (2) for \(x>1/2\), \(|\delta|<1/2\), arbitrary real \(\gamma\), the geometric identity used in (5), and the Gaussian limit with a fixed \(T(\log T)^2\) penalty. These are small cross-checks, not kernel proofs. The exact-module import job and its foundation reports are recorded below; final project acceptance and publication are the introducing server checkpoint. Standard foundation reports do not discharge any listed Open hypothesis.

Exact-module import job `job_js_Ll8edCU-zOCwibn5RDWIAC-r9NpPi` completed with exit code 0 and `verified=true`. The five modules contain 77 public supporting theorems. The nine important reports printed only `propext`, `Classical.choice`, and `Quot.sound`; no project-local axioms or unfinished proofs are used. Final aggregate-project and changed-module validation is the introducing checkpoint.
