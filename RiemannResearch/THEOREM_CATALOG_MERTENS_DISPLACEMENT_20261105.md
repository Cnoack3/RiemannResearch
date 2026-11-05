# Mertens estimates and squarefree displacement criteria (2026-11-05)

Write $M(x)=\sum_{n\le x}\mu(n)$ and $\Phi(x)=(\log x)^{3/5}(\log\log x)^{-1/5}$. Let $V$ be the closed legal squarefree span in $L^2(Q)$, $r=1-f_Q$ its projection residual and $d=f_Q-f_P$ the displacement between the two projections. $T_N$ keeps all physical coordinates beyond $N$.

## Square-sampled Mertens estimates and the boxed displacement criterion

`NumberTheory.PrimeNumberTheorem.mertens_vk_of_square_samples` retains the exponent $a>0$ from an eventual bound $|M(k^2)|\le Ck^2e^{-a\Phi(k^2)}$ with $C\ge0$. Filling the gaps between squares gives $|M(x)|\le(C+3)xe^{-a\Phi(x)}$ on the full real half-line beyond a threshold. `riemannHypothesis_of_square_sample_vk_log_displacement` specializes this to the logarithmic displacement criterion. Walfisz supplies the arithmetic estimate in the literature (Gerhold, Acta Arith. 142 (2010), equation (2), DOI 10.4064/aa142-2-8). The square-sampled estimate has **Open** formal-provider status.

`QMertensFirstMoment.residual_zero_iff_vk_log_displacement` identifies zero squarefree projection residual with $\log(2+|d(n)|)=o(\Phi(n))$ under the ordinary VK Mertens bound. The upper-growth condition on the actual displacement is **Open**. Every interior rate $0<b<a$ already forces zero residual under $|d(n)|\le D e^{b\Phi(n)}$ eventually. The equivalence with zero residual uses the signed pairing and needs no reverse implication from RH.

`QDisplacementVKSignCount` gives a separate conditional test. Under the same VK arithmetic input, at arbitrarily large $X$ it suffices that one strict sign of $d$ occurs on at most $D e^{b\Phi(X)}$ sites through $X$, with $0\le b<2^{2/5}a$. The choice of sign may depend on $X$. The sign-count premise for the actual displacement is **Open**.

## Previously catalogued transfers

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

## Critical secondary Lee–Leong coefficient

Put $L(x)=\log\log x$, $S(x)=\Phi(x)/L(x)$, $A=(5/(3\cdot53.99^3))^{1/5}$,
$\kappa=A\log(53.99)/5$, and $U_t(x)=A\Phi(x)+\kappa S(x)+t\sqrt{\Phi(x)}$.
The term $\kappa S(x)$ comes from the linear term of the variable coefficient
in Lee–Leong, Theorem 1.1. Its positive quadratic remainder absorbs the
factor $25.85\log x$ and every fixed multiple of $\sqrt{\Phi(x)}$.

| Conditional research reduction | Hypotheses and conclusion |
|---|---|
| [Critical Mertens estimate](RH/MertensCriticalEstimate.lean) | `mertens_critical_sqrt_of_leeLeong` derives $\lvert M(x)\rvert\le x\exp(-U_t(x))$ eventually, for every fixed real $t$, from the explicit Lee–Leong estimate. |
| [Critical displacement moment](RH/MertensCriticalDisplacement.lean) | For each $s\ge0$, convergence of $\sum_{n\ge3}\lvert d(n)\rvert e^{-U_s(n)}/n$ implies RH. Under Báez-Duarte's explicit approximation theorem, RH also implies convergence. |
| Pointwise and exceptional-set forms | For every fixed real $t$, $\lvert d(n)\rvert=O(e^{U_t(n)})$ implies RH. For fixed $s\ge0$ with $s>t$, the same bound may be restricted to $n\notin E$ if $\sum_{n\in E}e^{-2U_s(n)}<\infty$. The proof uses the complete $Q$-energy of $d$ on the exceptional sites. |

The [finite envelope](RH/MertensCriticalEnvelope.lean) controls the variation
between the cutoff and the physical site. The [pairing theorem](RH/MertensExponentialCutoffPairing.lean)
uses the existing signed identity along legal squarefree heads.
**Open in Lean** — providing the Lee–Leong estimate from its published proof,
and Báez-Duarte's approximation for the reverse implication.
**Open displacement obligation** — prove one of these bounds for the actual
projection displacement independently of RH. The generic convergence lemmas
assume neither of the two external analytic inputs.

## Full variable-coefficient exponent

Write $r_0=\log(53.99)$ and $F(x)=A(1-r_0/L(x))^{-1/5}\Phi(x)$ for sufficiently large $x$. This is the full exponent in Lee–Leong's estimate. Their prefactor is $25.85x\log x$. For each fixed $\delta>0$, put $H_\delta(x)=F(x)-\delta\sqrt{\Phi(x)}$.

| Conditional research reduction | Hypotheses and conclusion |
|---|---|
| [Uniform arithmetic bound](RH/MertensFullProfile.lean) | $F-\delta\sqrt{\Phi}$ is eventually increasing. The printed estimate implies $\lvert M(x)\rvert\le x e^{-H_\delta(x)}$ eventually. |
| [Finite Möbius envelope](RH/MertensFullEnvelope.lean) | In a window close to the cutoff, variation in $F$ costs $O(\Phi^2/\log x)$ in the exponent, and the harmonic factor costs $O(\log\log x)$. Each is $o(\sqrt\Phi)$. The physical bound is uniform over all sufficiently large cutoffs and all sites. |
| [Full-profile first moment and pointwise criterion](RH/MertensFullDisplacement.lean) | `riemannHypothesis_iff_leeLeong_full_moment` gives $\mathrm{RH}\iff\sum_{n\ge3}\lvert d(n)\rvert e^{-H_\delta(n)}/n<\infty$ under the two stated literature inputs. `riemannHypothesis_of_leeLeong_full_displacement` needs only the Lee–Leong input and $\lvert d(n)\rvert=O(e^{H_\delta(n)})$. |
| Exceptional sites | Fix $0<\eta<\delta$. The growth bound with margin $\delta$ need only hold outside $E$ if $\sum_{n\in E}e^{-2H_\eta(n)}<\infty$. |

**Open displacement obligation** — establish a convergent moment, or a sufficient bound, for the actual $d$ without assuming RH. This theorem uses the printed Theorem 1.1 as its arithmetic input. The implicit truncation result below uses the stronger intermediate estimate in Proposition 5.2.

## A sign-count criterion using the repository's arithmetic estimates

For $\varepsilon\in\{-1,1\}$, let $N_\varepsilon(X)$ count the positive integers $n\le X$ with $\varepsilon d(n)>0$. The zero coordinate contributes nothing. [QDisplacementSignCounts](RH/QDisplacementSignCounts.lean) proves
$$
\left(\sum_{1\le n\le X}\frac{(\varepsilon d(n))_+}{n}\right)^2
\le N_\varepsilon(X)\sum_{n\ge1}\frac{|d(n)|^2}{n^2}.
$$
The complete sum on the right is finite. For fixed $B,C\ge0$, if arbitrarily large $X$ have $\min(N_+(X),N_-(X))\le C(\log X)^B$, then RH follows by the cofinal harmonic-prefix theorem. The sign may vary with $X$. **Open** — proving that count bound for the actual displacement. This implication requires neither external analytic premise.


## Finite Gram tests and the implicit truncation

**Conditional research reduction with internal arithmetic.** Set the stage to $2k^4$, so that all squarefree conductors through $2k^4+1$ enter the two Gram systems. At their exact displacement take the smaller of the two signed positive harmonic masses over $n\le k^8$. A bound of $C(\log k)^E$ on arbitrarily large $k$, for fixed nonnegative $C,E$, implies RH. **Open:** prove that bound. The exact finite prime and Möbius tests avoid a convergence-rate assumption. [Proof and scope](RH/FiniteGramDisplacementResearch20261105.md) · [Lean declaration](RH/QFiniteHarmonicProbe.lean) · [Finite computations](RH/FiniteGramDisplacementExperiment20261105.md)

| Result | Declaration or file |
|---|---|
| The limiting residual vanishes exactly when arbitrarily large heads admit one matched finite stage beyond the head passing a fixed unit harmonic budget. Grid and iterated polylog tests are also sufficient. | [QFiniteHarmonicPrefix](RH/QFiniteHarmonicPrefix.lean) |
| Signed harmonic mass identity, prefix stability, and the uniform allowance $\sqrt{61\zeta(2)/7200}$ for the centered iteration when $X\le 9^j$. | [QResolventHarmonicPrefix](RH/QResolventHarmonicPrefix.lean) |
| On the squarefree closure the quadratic residual polynomial $(18R^2-I)/17$ gives an exact signed remainder and norm factor $1/17$ per two-step cycle. | [QDisplacementChebyshevResolvent](RH/QDisplacementChebyshevResolvent.lean) |
| A projected finite head of the Pareto residual has vanishing harmonic error on windows $(N+2)^2$. The infinite projector and actual source enter this construction. | [QDisplacementProjectedHead](RH/QDisplacementProjectedHead.lean) |
| Four legal atoms give opposite plateaux and $h(s_p;5p)\ge1/5$, with $\zeta(2)\|s_p\|_Q^2\le1/(p-1)$. Exact block equalities apply to the actual residual and witness. | [SquarefreeHarmonicPulse](RH/SquarefreeHarmonicPulse.lean) · [SquarefreePulseEquations](RH/SquarefreePulseEquations.lean) |
| For bounded legal tests supported above physical cutoff $N$, the pairing with $d$ is $o(N^{-3/2})$. The finite-horizon inequality retains the norm of the actual Pareto residual tail. | [QDisplacementTailTests](RH/QDisplacementTailTests.lean) |
| **Paper counterexample.** Within the closed squarefree span, $h(v;X)\asymp\sqrt X/(\log X)^\beta$ for all large $X$ is attainable for every $\beta>1/2$ and impossible for $\beta=1/2$. | [Construction and sharpness proof](RH/SquarefreeHarmonicObstruction20261105.md) |

**Conditional research reduction with a literature input.** Lee–Leong Proposition 5.2 with its implicit optimized truncation supplies a reserve beyond the printed exponent $F$. The formal transfer accepts every fixed real $s$ in $|d(n)|=O(\exp(F(n)+s\sqrt{\Phi(n)}))$. It also accepts an eventual polynomial bound on the weighted dyadic masses at any fixed signed square-root margin. A finite signed-kernel maximum recovers each block mass exactly. **Open in Lean:** a provider of the specialized published input. **Open for the RH argument:** a growth or moment bound on the actual displacement. The complete asymptotic expansion and stronger logarithmic-scale consequence in the associated note are paper deductions. [Implicit cutoff](RH/MertensImplicitTruncation.lean) · [Reserve transfer](RH/MertensTruncationReserve.lean) · [Signed dyadic blocks](RH/MertensDyadicDisplacement.lean) · [Literature derivation](RH/MertensImplicitTruncationResearch20261105.md)


**Single-probe reduction and sign obstruction.** With $a_p=\langle g_p,1-f_{P,p}\rangle_Q$ and squarefree conductors through $p+1$, the scaled entry $\zeta(2)p a_p$ tends along primes to the squared limiting Pareto residual norm. **Open:** show $p a_p\to0$ along a cofinal subsequence. The finite norm comparison transfers Burnol’s positive logarithmic lower bound into eventual positivity of the individual entries. The transfer of Burnol from his continuous family to this dictionary is a paper proof. [Finite identity, limit, and positivity comparison](RH/QFiniteSingleResidueTest.lean) · [Paper proof with the matched cutoff](RH/SingleResidueBurnolResearch20261105.md)

## The first projected correction and harmonic resolvent errors

In the notation of the [research note](HarmonicResolventAndFullMoment20261105.md), let $b=\Pi Br_Q$, $b_M=\Pi_M B r_M$, $u_1=4b/3$, and $h$ be the smaller signed harmonic prefix.

| Declaration | Conclusion |
|---|---|
| `QSquarefreeDisplacementResolvent.resolvent_error_weighted_energy` | $4\sum_{k<N}9^k\|d-u_k\|^2\le\|r_Q\|^2$ for every $N$. |
| `QSquarefreeDisplacementRigidity.harmonic_resolvent_sqrt_depth` | The prefix error at depth $j$ is at most $\sqrt{\zeta(2)X}\,3^{-j}\|r_Q\|/(2\sqrt{j+1})$. |
| `QSquarefreeDisplacementRigidity.harmonic_resolvent_adaptive_div_sqrt_tendsto_zero` | $h(u_{j(X)};X)=o(\sqrt X)$ if $X\le9^{j(X)}$. |
| `QFixedHarmonic.residual_zero_iff_fixed_firstStep_cofinal_polylog` | For fixed $C,B_1\ge0$, residual zero iff $h(u_1;X)\le C(\log X)^{B_1}$ at cofinal cutoffs. |
| `QFixedHarmonic.residual_zero_iff_cofinal_moving_harmonic_one` | Residual zero iff arbitrarily large physical cutoffs admit arbitrarily large finite stages with $h(b_M;X)\le1$. |
| `QMertensFirstMoment.residual_zero_iff_cofinal_full_moving_moment` | Under the Lee–Leong input, residual zero iff a single constant bounds the full-weight finite moments of $b_M$ at arbitrarily large stages for each fixed physical head. |
| `QMertensFirstMoment.riemannHypothesis_of_first_resolvent_full_moment` | Under the Lee–Leong input the weighted absolute moment of $u_1$ implies RH. |
| `QMertensFirstMoment.leeLeong_full_moment_iff_resolvent_shells` | Full displacement moment summability equals summability of the moments of $u_j$ on the dyadic shells, independent of the arithmetic premise. |

**Conditional research reductions.** Open — supply a cofinal one-sided estimate for the actual first correction, or the uniform finite weighted moment. Open in Lean — supply `LeeLeongMertensEstimate` for the full-weight forward implication. The harmonic forward implication uses the repository's established arithmetic. The RH-to-residual-zero converse in the equivalence with RH uses `BaezDuarteMobiusApproximation`. The accompanying numerical certificates give finite values and an upper bound for the residual norm.

## A translated full Lee–Leong moment

Let $F$ be the full printed exponent and $G(x)=(\log x)^2\exp[-F(\exp(\log x-F(x)))]$. The full logarithmic prefactor in Lee–Leong's estimate is retained.

| Declaration in `QMertensFirstMoment` | Conclusion |
|---|---|
| `errorEnvelope_eventually_le_leeLeongDelayed` | Uniform Möbius defect envelope at relative error $25.85\log N\,e^{-F(N)}$ is at most $2+400nG(n)$ for all sufficiently large cutoffs and every site. |
| `summable_leeLeongDelayedDamping_Q` | The scalar moment of $G$ is finite. |
| `leeLeongDelayedDamping_eventually_le_explicit` and `leeLeongDelayedDamping_le_full_margin` | A loss bounded by $(2A)^2\Phi(x)^2/\log x+2\log\log x$ suffices. Each earlier fixed positive square-root margin dominates the translated damping. |
| `residual_zero_iff_cofinal_delayed_heads` | With the Lee–Leong premise, a uniform constant for finite translated first-correction moments on cofinal conductor stages for each physical cutoff is equivalent to $r_Q=0$. |
| `riemannHypothesis_of_delayed_displacement_moment` | The translated absolute moment of the actual displacement suffices for RH under the same arithmetic input. |

**Conditional research reductions.** Open — bound the translated moment of the actual correction or displacement. Open in Lean — supply the published arithmetic input as a checked provider. The exact coefficient $3/5$ in the upper bound is proved by `leeLeongDelayedDamping_eventually_sharp_log_reserve`. Optimality for the raw uniform envelope is a paper deduction in the [research note](HarmonicResolventAndFullMoment20261105.md).

The new first-correction result `residual_zero_iff_cofinal_implicit_correction_heads` uses the stronger Proposition 5.2 specialization from the preceding section. At any fixed real $s$, its test uses the mass $|b(n)|e^{-F(n)-s\sqrt{\Phi(n)}}/n$, including the exact printed exponent when $s=0$. Open — prove the uniform finite-moment budget or provide a checked analytic input where required.
