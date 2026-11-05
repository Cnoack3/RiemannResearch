# Mertens estimates and squarefree displacement criteria (2026-11-05)

Write $M(x)=\sum_{n\le x}\mu(n)$ and $\Phi(x)=(\log x)^{3/5}(\log\log x)^{-1/5}$. Let $V$ be the closed legal squarefree span in $L^2(Q)$, $r=1-f_Q$ its projection residual and $d=f_Q-f_P$ the displacement between the two projections. $T_N$ keeps all physical coordinates beyond $N$.

| Module | Declarations and scope |
|---|---|
| [MertensExponentialEntropy](Analysis/MertensExponentialEntropy.lean) | `exponential_entropy_eq`, `exponential_entropy_le`, `exponential_entropy_small`. For $\eta(\varepsilon)=\varepsilon(1+\log(1/\varepsilon))$, one has $\eta(e^{-u})=(1+u)e^{-u}$, at most $1/2$ for $u\ge6$. Every $0\le c<b$ gives $\eta(e^{-bu})\le[b/(b-c)]e^{-cu}$ by the elementary exponential inequality. |
| [MertensPowerPairing](Analysis/MertensPowerPairing.lean) | `min_cutoff_power_le`, `power_defect_pairing_tendsto_zero`, `summable_power_pairing_of_growth`. For $a>0$, defects bounded by $C\min(N,(n+1)N^{-a})$ that eventually vanish at each fixed coordinate pair to zero against a weight $v$ if $\sum(n+1)^{1/(1+a)}\lvert v_n\rvert<\infty$. For $v_n=w_n/(n+1)^2$, growth $w_n=O((n+1)^\beta)$ suffices when $\beta<a/(1+a)$. The defect bound is an input to this scalar result. |
| [VinogradovKorobovProfile](Analysis/VinogradovKorobovProfile.lean) | `vkProfile_tendsto_atTop`, `vkProfile_eventually_mono`, `vkProfile_eventual_log_increment`, `vkProfile_dominates_logLog_sq`. The profile diverges and is eventually increasing. For every $\delta>0$, $\Phi(y)-\Phi(x)\le\delta\log(y/x)$ for all sufficiently large $x$ and all $y\ge x$. `vk_second_order_of_variable_coefficient` extracts a correction $k\Phi/\log\log x$ for $k<Ar/5$ from its stated variable-coefficient bound on an arbitrary $F$. |
| [QProfileTailEnergy](RH/QProfileTailEnergy.lean) | `profile_tail_energy_le` bounds $\lVert T_Nu\rVert_Q^2$ by $2C^2H(N)^2/(\zeta(2)N)$ from $\lvert u(n)\rvert\le CH(n)$ and $H(n)^2/\sqrt n\le H(N)^2/\sqrt N$ beyond $N\ge1$. `profile_weighted_tail_tendsto_zero` and its `of_little_o` variant give a vanishing weighted tail with $\eta_jH(q_j)^2\to0$, or with this product bounded and $u=o(H)$ in the stated envelope sense. |
| [QSquarefreeMertensProfileCriterion](RH/QSquarefreeMertensProfileCriterion.lean) | `defect_energy_of_uniform_mertens_log` combines the repository's uniform Mertens energy estimate with the complete exact-head defect. `annihilator_mean_zero_of_mertens_profile` and `profile_B_tail_tendsto_zero` supply the two estimates used by `residual_zero_iff_mertens_profile_tail`. The tail and physical-envelope RH corollaries apply the repository's squarefree capacity criterion. |
| [QSquarefreeVKDisplacement](RH/QSquarefreeVKDisplacement.lean) | `riemannHypothesis_of_vk_exponential_displacement`, `riemannHypothesis_of_vk_log_displacement`, `mertens_vk_absorb_constant`, `riemannHypothesis_of_walfisz_displacement`. Under an eventual Mertens bound $\lvert M(x)\rvert\le Cx e^{-a\Phi(x)}$, the eventual bound $\lvert d(n)\rvert\le D e^{b\Phi(n)}$ suffices for RH for every $0<2b<a$. In particular $\log(2+\lvert d(n)\rvert)=o(\Phi(n))$ suffices. Euclid's theorem supplies cofinal legal heads. |
| [MertensFirstMomentEnvelope](RH/MertensFirstMomentEnvelope.lean) | An explicit finite defect bound and dominated convergence for the signed Schur witness imply RH from a summable first-moment majorant along cofinal legal heads. |
| [MertensVKFirstMoment](RH/MertensVKFirstMoment.lean) | Under the VK Mertens estimate at rate $a$, for each fixed $0<c<a$, finiteness of the pure weighted absolute moment is equivalent to zero projection residual and implies RH. The pointwise corollary admits every $0<b<a$, with arbitrary fixed prefactors. The full infinite-range Mertens estimate and the actual displacement bound are explicit premises. |

The residual equivalence has explicit quantifiers. Take $q_j\to\infty$ with $q_j+1$ eventually squarefree, $0<\varepsilon_j\le1$, $\eta_j=\eta(\varepsilon_j)\le1/2$ eventually, and $\eta_j\to0$. Assume $\lvert M(y)\rvert\le\varepsilon_j y$ for **every** real $y\ge q_j$ for all sufficiently large $j$. Then

$$r=0\quad\Longleftrightarrow\quad q_j\eta_j\lVert T_{q_j}d\rVert_Q^2\longrightarrow0.$$

Residual vanishing implies `RiemannHypothesis` through the existing closure theorem. The outstanding displacement problem is to prove one of these upper bounds for the actual $d$ with no RH assumption.

Walfisz proved the full VK bound for the ordinary Mertens function. Its proof remains external to this Lean development. [Gerhold, *Acta Arithmetica* 142 (2010), equation (2)](https://doi.org/10.4064/aa142-2-8).

## Displacement criteria at the two Mertens scales

Write $Z=\zeta(2)$, $Q(n)=1/(Zn^2)$ for $n\ge1$, and $\Psi(x)=((6+\log x)\log(6+\log x))^{1/11}$. Define the two nonnegative series

$$J_c=\frac1Z\sum_{n\ge1}\frac{|d(n)|e^{-c\Phi(n)}}n,
\qquad K_a=\frac1Z\sum_{n\ge1}\frac{|d(n)|^2e^{-a\Psi(n)}}n.$$

The Lean sums run over the naturals. Their terms at zero vanish.

**Vinogradov–Korobov scale.** Assume $|M(x)|\le Cxe^{-a\Phi(x)}$ for all sufficiently large real $x$. For every fixed $0<c<a$, `residual_zero_iff_vk_displacement_absolute_moment` proves $r=0\iff J_c<\infty$ and `riemannHypothesis_of_vk_displacement_absolute_moment` gives $J_c<\infty\Rightarrow\mathrm{RH}$. In particular, for every $0<b<a$ and every constant $D$, an eventual bound $|d(n)|\le D e^{b\Phi(n)}$ implies RH. The pointwise argument chooses an intermediate moment exponent $b<c<a$. An eventual power saving $|M(x)|\le Cx^s$ with $C\ge 0$ and $s<1$ supplies the VK bound, with prefactor one, at every fixed $a>0$. See [MertensVKFirstMoment](RH/MertensVKFirstMoment.lean) and [MertensPowerToVK](RH/MertensPowerToVK.lean).

**Repository Mertens scale.** The project's unconditional `M_stretched_loglog_bound` supplies a fixed $b>0$ such that $r=0$ if and only if there exists $D\in\mathbb R$ with $|d(n)|\le D e^{b\Psi(n)}$ for all sufficiently large $n$. The theorem `riemannHypothesis_of_stretched_log_displacement` gives $\log(2+|d(n)|)=o(\Psi(n))\Rightarrow\mathrm{RH}$. Establishing this bound for the actual displacement remains open. A separate theorem supplies a fixed $a>0$ such that $K_a<\infty\Rightarrow\mathrm{RH}$. Both coefficients are existential and precede the respective displacement test. The profile comparison used in these implications holds for $\Psi_\beta(x)=((6+\log x)\log(6+\log x))^\beta$: for each $0\le\beta<1/2$ and $A\ge0$, eventually in $x$ one has $A(\Psi_\beta(y)-\Psi_\beta(x))\le\log y-\log x$ for every $y\ge x$. See [MertensUnconditionalStretched](RH/MertensUnconditionalStretched.lean), [MertensStretchedWeightedMoment](RH/MertensStretchedWeightedMoment.lean), and [StretchedLogProductIncrement](Analysis/StretchedLogProductIncrement.lean).

**Explicit Lee–Leong scale.** Put $W=53.99$ and $A=(5/(3W^3))^{1/5}$. `LeeLeongMertensEstimate` is the following external premise for every real $x\ge\exp(\exp(10.01))$:

$$|M(x)|<25.85\,x\log x\,\exp\!\left[-A\left(1-\frac{\log W}{\log\log x}\right)^{-1/5}\Phi(x)\right].$$

From this input, `mertens_vk_of_leeLeong` retains the full leading coefficient in $|M(x)|\le x e^{-A\Phi(x)}$ eventually. Thus for every $0<c<A$, $r=0\iff J_c<\infty$ and $J_c<\infty\Rightarrow\mathrm{RH}$. For every $0<b<A$ and constant $D$, an eventual bound $|d(n)|\le D e^{b\Phi(n)}$ also implies RH. The first-moment statement here uses strict interior rates. See [MertensLeeLeongCriterion](RH/MertensLeeLeongCriterion.lean) and Lee–Leong, Theorem 1.1, [v5 PDF, (11)](https://arxiv.org/pdf/2208.06141v5) or [v5 HTML, (12)](https://arxiv.org/html/2208.06141v5).

**Pointwise endpoint.** [MertensEndpointEnvelope](RH/MertensEndpointEnvelope.lean) and [MertensEndpointPairing](RH/MertensEndpointPairing.lean) prove `riemannHypothesis_of_leeLeong_endpoint`. Under the same explicit arithmetic premise, an eventual bound $|d(n)|\le D\exp(A\Phi(n))$ suffices at the leading coefficient $A$ itself. The second-order term in the published estimate gives enough decay to retain a factor $\exp(-\sqrt{\Phi(n)}/8)$ in a common majorant for the finite-head errors. With the Lee–Leong input the residual vanishes if and only if the following endpoint series converges:
$$J_* = \sum_{n\ge3}\frac{|d(n)|}{n}\exp\left(-A\Phi(n)-\tfrac18\sqrt{\Phi(n)}\right).$$
Convergence implies RH. In particular $|d(n)|=O(\exp(A\Phi(n)+t\sqrt{\Phi(n)}))$ suffices for each fixed $t<1/8$. The proofs absorb the remaining factor $\exp(-(1/8-t)\sqrt{\Phi(n)})$ into $1/(\log n)^2$.

## Converse from the explicit squarefree approximants

[MertensBaezDuarteConverse](RH/MertensBaezDuarteConverse.lean) takes Báez-Duarte’s squared-error convergence under RH as an explicit input. Its finite coefficients are $-\mu(m)\exp(-c\log m/\log\log N)$. The Lean proof checks squarefree support, transfers the continuous approximation to the discrete Pareto norm and to the $Q$-norm, and deduces $r=d=0$ under RH. Together with the Lee–Leong estimate this proves the literal equivalences
$$\mathrm{RH}\iff J_c<\infty\quad(0<c<A),\qquad
\mathrm{RH}\iff\log(2+|d(n)|)=o(\Phi(n)).$$
The same two inputs yield $\mathrm{RH}\iff J_*<\infty$ in `riemannHypothesis_iff_leeLeong_endpoint_displacement_moment`. At the smaller scale $\Psi$ the reverse direction uses the same Báez-Duarte input, and the forward-to-RH proof uses only the repository’s arithmetic estimates. See [Báez-Duarte, Rend. Lincei 14 (2003), Theorem 2, formula (3.1)](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0) and [Bagchi, Remark 8](https://arxiv.org/pdf/math/0607733).

## Shifted tests

[MertensShiftedPairing](RH/MertensShiftedPairing.lean) proves the analytic continuation and boundary passage for the actual Schur witness. A family of holomorphic tests must have a locally summable majorant in the open domain, an absolutely summable squarefree expansion near one interior point, and a separate summable majorant along a sequence where the weighted tests converge coordinatewise to the witness charge. These hypotheses imply RH. [MertensShiftedMobiusSeed](RH/MertensShiftedMobiusSeed.lean) proves absolute summability of the Möbius atom coefficients and exact witness cancellation for their series throughout $\Re(s)>1$.

[MertensShiftedTest](NumberTheory/MertensShiftedTest.lean) defines the finite divisor test with the pole at one removed using Mathlib’s completed zeta factor. Each physical test is holomorphic for $\Re(s)>0$ and tends to one at $s=0$ for $n\ge1$.

[MertensShiftedFloorSum](NumberTheory/MertensShiftedFloorSum.lean) counts each divisor through its positive multiples. [MertensShiftedTestIdentity](RH/MertensShiftedTestIdentity.lean) identifies the finite test with its squarefree residue series throughout $\Re(s)>0$, using the absolutely convergent Dirichlet series for $1/\zeta(1+s)$. On $\Re(s)>1$ the actual witness pairs to zero with this finite test.

[MertensShiftedLocalMajorant](RH/MertensShiftedLocalMajorant.lean) gives $|H_s(n)|\le n^{1-\eta}\sum_{k\ge2}k^{-1-\eta}$ for $0<\eta<1$ and $\Re(s)\ge2\eta$. [MertensActualShiftedCriterion](RH/MertensActualShiftedCriterion.lean) supplies the concrete continuation step. The remaining hypotheses for `riemannHypothesis_of_actual_shifted_boundary` are the interior moments of the actual witness charge and one summable boundary dominator. A proof of the sharper uniform shifted Perron estimate and a proof of the required displacement growth would give further progress.
