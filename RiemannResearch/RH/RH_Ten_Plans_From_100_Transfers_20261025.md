# Ten ranked RH plans synthesized from Transfers 1–100

Date: 25 October 2026.
Source snapshot: RiemannResearch main at bbfdc8fa28da9f1aa7fe375a8a7c798bf40cea3e.

## Status and ranking

This is a research synthesis, not a proof of RH. The ranking measures the tractability of the next useful mathematical step, availability of exact certificates, and dependence on genuinely new analytic input. It is not a numerical probability of proving RH.

The six development memoranda covering Transfers 1–100 were read, together with selected actual declaration types and the post-100 Q conditioning/trace-bound audits. Twelve representative declarations were freshly checked on the Lean server; the exact audit scope appears below. This does not mean that all 100 theorems were independently re-proved in this session.

The common goal is
\[
1\in V,\qquad V=\overline{\operatorname{span}\{g_d:d\ge2\}}^{L^2(Q)},
\quad Q(n)=\frac1{\zeta(2)n^2},\quad g_d(n)=\frac{n\bmod d}{d}.
\]
For the finite legal projection \(p_D=P_{V_D}1\), set
\[
\kappa_D=\|p_D\|_Q^2,\qquad e_D=\|1-p_D\|_Q^2=1-\kappa_D.
\]
Every plan must eventually eliminate \(e_\infty\), not merely prove convergence to it.

The verified forward implications from closure/saturation to RH do not require the open converse provider. Full RH iff statements in the repository explicitly retain
\[
hBaezDuarte:\mathrm{RH}\longrightarrow\mathrm{NaturalApproximation}.
\]
This is an open formalization dependency, distinct from the established classical theorem of Báez-Duarte.

Use the actual Q source vector \(b_D(q)=\langle1,R_q\rangle_Q\) for Q inverse-Gram calculations. The Pareto packet source is \(\Lambda(q)\); these finite source vectors must not be identified. Here \(R_q=\sum_{d\mid q}\mu(q/d)d\,g_d\).

## 1. Certified complete-error constructions

**Transfers:** 2–6, 12, 14, 24–25, 36, 47, 52, 91.

**Goal.** Produce a specified sequence of rational legal packets with certified complete errors tending to zero. Finite computations should reveal a family and a bound that can be proved for all stages.

For a finite residue combination \(F=\sum_dc_dg_d\), the exact identity is
\[
\|1-F\|_Q^2=
\frac1{\zeta(2)}\sum_{n\le H}\frac{|1-F(n)|^2}{n^2}
+\frac1{\zeta(2)}\sum_{n>H}\frac{|1-F(n)|^2}{n^2}.
\]
Writing \(L=\sum_d|c_d|\), the second term is at most
\[
\frac{(1+L)^2}{\zeta(2)H}.
\]
This is an ordinary mathematical certificate derived from \(0\le g_d<1\) and \(\sum_{n>H}n^{-2}\le H^{-1}\); this specific displayed bound was not newly formalized here.

**First work.** Compute rational candidates, certify their head errors and full tails, and compare smoothed Möbius coefficients with actual Gram optimizers. The full-Gram backward-error identities can certify approximate solves. Replace the crude absolute coefficient tail bound by signed periodic-block calculations when it loses too much cancellation.

**RH-closing obligation — Open.** Prove that one explicit family has certificates tending to zero. Finding many small numerical errors, or enumerating possible certificates without proving eventual success for every tolerance, is not enough.

**Why first.** Every finite result is checkable, and failed constructions reveal exactly whether coefficient growth, solver accuracy, or tail energy is the obstacle.

## 2. Uniformly bounded physical-head interpolation

**Transfers:** 19, 29, 34–35, 47–49; general observation geometry in 61–67.

**Goal.** Construct legal \(F_j\) with \(F_j(n)\to1\) for every fixed positive \(n\), and a fixed finite bound on \(\|F_j\|_Q\). The bound need not be close to one.

A useful new synthesis target is
\[
J_j=\|F_j\|_Q^2+
\lambda_j^2\sum_{n\le H_j}Q(n)|F_j(n)-1|^2\le C,
\quad H_j\to\infty,\quad\lambda_j\to\infty.
\]
Then every fixed \(n\) eventually satisfies
\[
|F_j(n)-1|^2\le C/(\lambda_j^2Q(n)),
\]
and \(\|F_j\|_Q^2\le C\). Bounded pointwise convergence yields weak convergence to one; weak closedness of \(V\) gives \(1\in V\). Transfers 48–49 then supply strongly convergent finite convex combinations. Transfer 35 already proves the forward RH criterion under the still weaker frequently bounded full-error hypothesis.

**First work.** Instantiate the general finite observation machinery with physical evaluations, then bound the minimum of \(J_j\). Also test convex combinations of exact-head packets, retaining their signed cross terms; individual packet energies may grow while a suitably chosen average stays bounded.

**RH-closing obligation — Open.** An arithmetic uniform bound on these actual interpolation costs.

Physical-head evaluations are different from conductor-coefficient requests. Their identification is not supplied by the existing coefficient-constraint modules. The displayed soft-head implication is an ordinary mathematical deduction here, not a newly saved Lean theorem.

## 3. Arithmetic blocks with cumulative Schur gain

**Transfers:** 5, 7, 13, 17, 24, 36, 52, 85–92.

For a disjoint new block \(B\), residualize its packets against the old legal space. Let \(S_D\) be their Gram matrix and \(s_D\) their correlations with \(1-p_D\). The exact geometry gives
\[
e_{D\cup B}=e_D-G_D,\qquad G_D=s_D^TS_D^{-1}s_D.
\]

**Goal.** Specify arithmetic blocks—dyadic conductor bands, prime-power bands, or prime blocks together with their composite corrections—and prove
\[
G_j\ge\eta_j e_j-\varepsilon_j,\quad \eta_j,\varepsilon_j\ge0.
\]
A useful error-tolerant finite consequence is
\[
e_m\sum_{j<m}\eta_j
 \le e_0-e_m+\sum_{j<m}\varepsilon_j
 \le e_0+\sum_{j<m}\varepsilon_j.
\]
Indeed, \(e_m\le e_j\), sum the lower gain bounds, and telescope the exact gains. Thus divergent cumulative \(\eta_j\) and
\[
\sum_{j<m}\varepsilon_j=o\!\left(\sum_{j<m}\eta_j\right)
\]
force \(e_m\to0\).

**First work.** Certify actual block efficiencies \(G_j/e_j\), identify a plausible lower envelope, and prove it from arithmetic correlations. Computation errors may be included in \(\varepsilon_j\).

**RH-closing obligation — Open.** The arithmetic gain estimate, rather than the already-proved product/summability equivalence. Greedy convergence to the full legal projection does not by itself show that the projection is one.

The cumulative inequality above is an ordinary mathematical synthesis in this note; Wolfram independently checked the scalar Schur formula.

## 4. Bounded growing Möbius pinning

**Transfers:** 15–16, 21–23, 26, 31–33, 41–46, 61–68, 71, 75.

**Goal.** Impose the continuous original coefficient targets \(-\mu(m)\) for \(2\le m\le J\), enlarge the legal stage to keep the physical energy uniformly bounded, and let \(J\to\infty\).

These continuous coefficient functionals separate the full Hilbert space. On a bounded physical family, convergence of all these coordinates to those of one forces weak convergence to one. Hence bounded legal pinned vectors would imply closure, and convexification would produce strong approximants.

**First work.** Use the exact coupled inverse-Gram costs to choose stage sizes and penalties jointly. Compare hard pins, soft pins, and block pinning, preserving the off-diagonal costs. For approximate pins, require each fixed requested coordinate's actual error to vanish.

**RH-closing obligation — Open.** A uniform complete energy bound for growing successful pins. Feasibility of each finite system is already available; it is not a uniform estimate.

Transfer 68's vanishing regularization budget only controls displacement from the canonical optimizer. It does not remove the canonical residual floor. This plan seeks bounded pinned families with the correct coordinates, which is a different analytic target.

## 5. Arithmetic decay of the weighted Möbius defect

**Transfers:** 4, 16–17, 50–51, 69–76.

For canonical Q coefficients \(C_N(m)\), use the positive admissible weighted defect
\[
W_N=\sum_{m\ge2}w_m|C_N(m)+\mu(m)|^2.
\]
The repository proves convergence of \(W_N\), a uniform geometric tail for its canonical weights, and that its limiting value vanishes exactly when \(e_\infty=0\).

**Goal.** Prove arithmetic decay of finite heads of this series, then use the already-controlled tails. For the canonical indexing \(m=j+2\), the tail from index \(J\) is at most \(2(1/2)^J\).

**First work.** Analyze the actual finite signed transforms
\[
C_N(m)=m\sum_{\substack{q\le N+1\\m\mid q}}\mu(q/m)a_N(q).
\]
Seek cancellation estimates for fixed \(m\), allowing a very slow diagonal in \(N\). Transfer 76 identifies the exact signed inverse-tail condition when passing between raw packet coefficients and continuous coordinates.

**RH-closing obligation — Open.** The limits \(C_N(m)\to-\mu(m)\), or an equivalent bound making the finite weighted heads vanish.

The raw packet coefficients are not the same coordinates. Neither convergence of individual raw coefficients nor a formal interchange with an infinite signed sum supplies these target limits. Compact injectivity also supplies no uniform inverse norm bound on arbitrary families.

## 6. Prevent escape of the canonical residual into physical tails

**Transfers:** 18–19, 29, 34–35, 47.

This route uses the canonical **Pareto** residual \(r_P=1-P_V^P1\), not an identification of the P and Q projection vectors. Set
\[
T_N=\sum_{n>N}\frac{|r_P(n)|^2}{n(n+1)}.
\]
The verified dichotomy is
\[
r_P=0\quad\hbox{or}\quad NT_N\to\infty,
\]
even though \(T_N\to0\) always.

**Goal.** Prove \(N_jT_{N_j}\le C\) along an unbounded subsequence. This already forces \(r_P=0\), hence RH; no full rate at every \(N\) is necessary.

**First work.** Derive dyadic or arithmetic-block tail bounds from packet orthogonality and the exact approximate-head pairing identities. A residual-specific estimate
\[
\sum_{n>N_j}|r_P(n)|^2/[n(n+1)]\le C/N_j
\]
would close the route.

**RH-closing obligation — Open.** This normalized-tail bound. Square summability alone cannot provide it. Pointwise boundedness of the residual must not be silently assumed.

## 7. Upgrade annihilator identities to Noor tail regularity

**Transfers:** 9, 18–20, 34.

For the Pareto canonical residual define
\[
A_n=(n+1)\sum_{k\ge0}\frac{r_P(k+n+1)}{(k+n+1)(k+n+2)}.
\]
The repository identifies the sufficient tail-regularity condition with existence of \(L\) such that
\[
\sum_n|A_n-L|^2<\infty.
\]
It already has the exact difference-energy identity
\[
\sum_n|A_n-A_{n+1}|^2=e_\infty^P-(e_\infty^P)^2.
\]

**Goal.** Use all arithmetic annihilator identities to obtain the missing control of \(A_n-L\), beyond control of its differences.

**First work.** Seek a Hardy-type inequality on the subspace satisfying the packet annihilation relations. Test the needed boundary/low-frequency condition explicitly. Difference-square summability by itself is insufficient.

**RH-closing obligation — Open.** TailRegular for the canonical residual. The implication TailRegular implies RH is already a checked declaration.

For a Q annihilator the relevant Pareto object is its correctly weighted inverse-adjoint image, as specified by Transfer 18. The primal sequence-preserving metric map cannot replace that dual map.

Noor's paper motivates this route; it does not provide the missing residual-specific regularity automatically.

## 8. Complete Mellin probes and control their actual source signatures

**Transfers:** 10, 20, 27–30, 37–40, 53–60, 77–84.

The exact complete-Q identity is
\[
\zeta(2)e_\infty
 =\operatorname{Captured}_P(r_Q)
  +\operatorname{Unobserved}_P(r_Q)
  +\operatorname{MetricCorrection}(r_Q),
\]
where the first two terms use the specified P image of the Q residual. Transfer 84 proves that \(e_\infty=0\) is equivalent to vanishing of both Mellin captured and unobserved energies; norm comparison then handles the Q correction.

**Goal.** Choose a test family for which completeness can be proved, then show the actual residual signatures vanish.

**First work.** Investigate distinct half-plane probes with an interior accumulation point, such as \(z_j=1+1/(j+1)\), using analyticity and Mellin injectivity to establish completeness. Separately estimate the explicit packet arithmetic signatures on those probes, with all source corrections present.

**RH-closing obligation — Open.** Vanishing of those signatures together with the needed completeness theorem. Completeness alone does not annihilate a residual with nonzero observations.

Actual zeta-zero probes have special signatures but cannot simply be assumed complete. Their positive zero-product slack and the full unobserved remainder must remain. Unconditionally summable Mellin innovations identify captured energy; they do not prove it exhausts the residual.

## 9. Bound the actual Q target vacancy

**Transfers:** 8, 93–100; post-100 trace and angle bounds.

Transfers 98–99 express the target defect through the full signed complementary-kernel energy and the vacancy of the normalized target. Transfer 100 gives
\[
v_N^{\mathrm{cond}}=e_N+\operatorname{conditioningCost}_N\ge e_N.
\]

**Goal.** Obtain an independent arithmetic upper bound \(v_{N_j}\le\epsilon_j\to0\) for target vacancy, or for the corresponding complete signed hole energy.

**First work.** Exploit the actual physical Q kernel and its signed cross terms to derive a target-specific estimate. Trace, gap determinants, volume formulas, and variance formulas are tools for this estimate, not substitutes for it.

**RH-closing obligation — Open.** Decay of target vacancy. Conditioning on fixed legal heads has limit \(e_\infty\), and heads already in the stage reproduce the canonical defect exactly. Good head mass or a spectral gap only controls amplification by conditioning.

Do not identify this physical-site projection DPP with a newly invented conductor-indexed ridge L-ensemble; their kernels and events differ.

## 10. Target spectral mass near zero

**Transfers motivating the construction:** 2, 9, 13–14, 61–68, 69–75. This is a proposed extension, not an existing completed spectral theorem in the transfer ledger.

Choose positive weights \(\alpha_d\) with
\(\sum_d\alpha_d\|R_d\|_Q^2<\infty\), and form the positive compact operator
\[
Af=\sum_d\alpha_d\langle f,R_d\rangle_Q R_d.
\]
Then \(\ker A=V^\perp\). Let \(\nu_1\) be the spectral measure of the constant target. Its atom at zero is precisely \(e_\infty\).

For the regularized target
\[
F_\lambda=A(A+\lambda I)^{-1}1,
\]
the spectral identity is
\[
\|1-F_\lambda\|_Q^2
=\int\left(\frac{\lambda}{t+\lambda}\right)^2\,d\nu_1(t).
\]

**Goal.** Prove a target-specific small-spectrum estimate, for example
\[
\nu_1([0,t])\le Ct^\theta\quad(0<t<t_0,\ \theta>0).
\]
It removes the atom at zero and yields norm convergence. Operator truncation then produces finite legal approximants.

**First work.** Establish the operator/spectral interfaces and relate finite resolvent quadratic forms to the exact arithmetic Gram and Schur data. Seek control only in the constant-target direction, not a uniform lower spectral bound.

**RH-closing obligation — Open.** The small-spectrum estimate. Compactness, positivity, or trace-class structure alone permits a nonzero kernel.

The compact injective coefficient-observation map from Transfer 75 is not this legal-packet synthesis operator. Substituting that already-injective map would lose the legal-range requirement and would not prove RH.

## Recommended work order

Use Plan 1 as the certificate engine for Plans 2–5. Give the principal analytic effort to Plan 2 (bounded interpolation) and Plan 3 (arithmetic block gain). Plans 6–7 offer residual-based alternatives. Plans 8–10 require more new analytic structure.

An estimate making zero-sampled source data accurate for each fixed dictionary can assist Plan 1 or 3. It does not establish capacity saturation of growing dictionaries. Selecting very large heights removes data error, while \(1-\kappa_D\) remains an independent term.

## Verification in this session

The serialized signature/axiom audit succeeded:
- job_1nHTDlUc0-PC3ajqcMcCY3aTcIIsZ3eD: exit code 0, verified true, server execution 21.849 seconds.
- job_qzbTOABvIErLn9uzwTsSi7oxaoHoSaS-: exit code 0, verified true, server execution 28.767 seconds. This second audit recovered the axiom evidence omitted by truncation in the first result.

These durations are server-reported execution times, not workspace-opening or client polling times. Workspace-opening and transport delays were not separately instrumented. Some source-outline requests timed out; focused source reads and the successful verification jobs supplied the needed evidence.

All twelve printed axiom lists contained only propext, Classical.choice, and Quot.sound. This does not discharge any local theorem hypothesis.

Freshly inspected declarations (namespace prefix RiemannResearch.RH):
1. RamanujanPointwiseCriterion.q_riemannHypothesis_of_pointwise_frequently_bounded
2. QRamanujanCanonicalOptimizer.packet_energy_limit_identity
3. QRamanujanCanonicalOptimizer.packet_relativeGain_not_summable_iff
4. RamanujanWeightedDefect.q_defect_uniform_tail
5. RamanujanWeightedDefect.qLimitDefect_zero_iff
6. RamanujanCanonicalOptimizer.riemannHypothesis_of_packet_tailRegular
7. RamanujanRegularizationCriteria.q_minimum_decomposition
8. RamanujanRegularizationCriteria.q_bias_quarter_bound
9. RamanujanMellinExhaustion.q_energy_zero_iff_mellin_energies_zero
10. QRamanujanDPP.conditionedVacancy_eq
11. QRamanujanDPP.fixed_conditioned_vacancy_tendsto
12. RamanujanRawInversionTails.q_raw_tendsto_iff_tail

Wolfram Language independently returned {0,0} for the scalar Schur-capacity difference and the two-dimensional ridge objective completion. These are symbolic cross-checks, not arithmetic RH estimates or Lean proofs.

This publication changes documentation only. It adds no Lean theorem and no provider for any Open obligation. The isolated checks above are not a fresh verification of the entire repository. The publication checkpoint receipt is reported separately.

## External sources and their roles

- Luis Báez-Duarte, A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis: https://arxiv.org/abs/math/0202141. Supports the classical natural-dilation criterion, not an automatically filled Lean provider.
- S. Waleed Noor, A Hardy space analysis of the Báez-Duarte criterion for the RH: https://arxiv.org/abs/1809.09577. Supports the tail-regularity research direction.
- François Alouges, Sébastien Darses, Erwan Hillion, Polynomial approximations in a generalized Nyman–Beurling criterion: https://arxiv.org/abs/2006.02953. Distinguishes unconditional approximation in an enlarged family from the additional coefficient control needed for an RH criterion.
- Sandro Bettin, J. Brian Conrey, David W. Farmer, An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion: https://arxiv.org/abs/1211.5191. Its optimal asymptotic is conditional on RH and an inverse-zeta-derivative moment hypothesis; it must not be imported as an unconditional upper bound.
