# Mixed-conductor screening and the full integer CRT

The Hilbert results use the complete Pareto law \(P(n)=1/[n(n+1)]\).
Write \(C_M\) for the span of the mixed Ramanujan packets through \(M\),
\(C\) for their closed span, \(S=I-P_C\), and \(V\) for the full legal
residue closure. A mixed conductor has at least two distinct prime factors.

## Categorical form of the legal mean

In `TopModuleCat ℝ`, `legalMeanSplitting` exhibits the mixed inclusion and the legal mean as a split short exact sequence.
For the screened section \(s(a)=au\), the retraction sends \(v\) to \(v-s(m(v))\).
The inclusion is a categorical kernel (`legalMixedIsKernel`) and the mean is a categorical cokernel (`legalMeanIsCokernel`).
The splitting identifies the legal space with the biproduct of the mixed closure and the scalar line.
Under `legalMixedQuotientIso` the quotient projection becomes the actual mean.
For every continuous linear map \(f:X\to\mathbb R\), `legalMean_unique_mixed_lift` writes each lift \(v:X\to V\) of \(f\) uniquely as \(i\circ k+s\circ f\) with \(k:X\to M\), where \(i\) includes the mixed closure \(M\) into \(V\). [Lean declarations](RH/MixedConductorSplitExact.lean)

## Contractive sections of the legal mean

Write \(m(v)=\langle v,\mathbf1\rangle_P\), \(u=(I-P_C)J_2/\log 2\), and \(E=\operatorname{dist}_P(\mathbf1,V)^2\).
For every bounded linear right inverse \(s\) of \(m\), `legalMeanSection_norm_sq` gives
\[
\|s\|^2=\|u\|_P^2+\|s(1)-u\|_P^2.
\]
The canonical section \(t\mapsto tu\) attains the minimum. Integer dilation produces right inverses with squared norms \(d\|u\|_P^2\) for every positive integer \(d\).

The adjoint satisfies \(m^*(t)=(1-E)tu\) and \(mm^*=(1-E)I\). The conditional research reduction `screenedPrimeClosure_eq_constantLine_iff_coisometry` identifies \(V\cap C^\perp=\mathbb R\mathbf1\) with \(mm^*=I\). Equivalently, the legal mean admits a section of norm at most one. **Open** is existence of such a contractive section. [Lean declarations](RH/MixedConductorContractiveSection.lean)

The closed unit ball reaches exactly the means \(|a|\le 1/\|u\|_P\). The scaled map \(\|u\|_P m\) has an isometric section. The physical mean has a section of squared norm strictly below \(1000/961\). For every finite set of distinct right-half-strip zeros \(Z\), each physical mean section satisfies \(1\le\|s\|^2\prod_{z\in Z}|(1-z)/z|^2\). A contractive physical section implies RH. Lean states the published RH-to-natural-approximation implication explicitly for the converse. [Metric lifting and finite zero bounds](RH/MixedConductorMetricLifting.lean)

The minimum operator norm of a physical section is `‖normalizedScreenedTwo‖`. A contractive physical section exists exactly when `limitEnergy = 0`, equivalently when the screened and constant lines agree. `limitEnergy_finite_zero_product_remainder` keeps the full squared Mellin remainder. A single right-hand zero bounds the excess squared section norm below by $(2\Re z-1)/|1-z|^2$. All finite zero-product tests at budget one hold exactly under RH. [Physical sections and zero families](RH/MixedConductorMetricLifting.lean)

The raw cumulative GCD parity formula at any fixed positive modulus grows at least as $n/(4P^2-1)$ and has infinite Pareto energy. For a signed finite legal fit, its energy on one full period bounds its complete squared norm within a factor of two. `exists_contractive_legalMeanSection_iff_bounded_parity_periods` reduces the physical section to finite normalized-residue coefficients. **Open** is a uniform bound on the one-period energies of fits matching $k/(2k+1)$ on increasing heads. A cofinal bound for the explicit Möbius parity lifts would suffice. [Finite-period criterion](RH/ParetoParityPeriodSection.lean)

### Resetting the GCD profile at each period

The following argument is a paper proof. For \(P>1\), write \(a(k)=1/(4\gcd(k,P)^2-1)\), \(G(r)=\sum_{k=1}^r a(k)\), and \(F(n)=G(n\bmod P)\). At a compatible modulus, \(F\) matches the parity head through \(N<P\). Divisor inversion gives \(a(k)=\sum_{d\mid P,\,d\mid k}b_d\). Thus \(G(n)=\sum_{d\mid P} b_d\lfloor n/d\rfloor\) and \(G(P)=P\sum_{d\mid P}b_d/d\). In \(F(n)=G(n)-G(P)\lfloor n/P\rfloor\) the linear terms cancel, giving a finite legal sum of normalized residues.

For \(0\le r<P\), symmetry gives \(G(r)+G(P-1-r)=G(P-1)\). The \(\varphi(P)\) coprime sites each contribute \(1/3\), so \(G(P-1)\ge\varphi(P)/3\). Cauchy–Schwarz and the smallest first-period weight give
\[
\sum_{r=1}^P\frac{F(r)^2}{r(r+1)}
\ \ge\ \frac{1}{P(P+1)}\sum_{r=0}^{P-1}G(r)^2
\ \ge\ \frac{G(P-1)^2}{4(P+1)}
\ \ge\ \frac{\varphi(P)^2}{36(P+1)}.
\]
Ordering the distinct prime divisors as \(p_1<\cdots<p_t\) gives \(p_j\ge j+1\) and \(2^t\le P\). Euler's product then gives \(\varphi(P)/P\ge\prod_{j=1}^{t}j/(j+1)=1/(t+1)\). The lower bound diverges as \(P\to\infty\). The periodic reset therefore fails the uniform energy test. Existence of other signed coefficient arrays meeting the test remains open.

## Sharp first-site interpolation and complete costs

Let $e=2\mathbf{1}_{\{1\}}-\mathbf{1}$. For every mixed vector $v$ with first value one, `mixed_unit_firstSite_cost` proves $\|v\|^2=1+\|v-e\|^2$. The conditional research reduction `rh_of_sharp_mixed_firstSite_cost` shows that arbitrarily small squared-cost excess at this single site implies RH. Attaining infimum one is open. The Mellin symbol of $e$ is $(1-2^{1-s})/s$.

`mixed_parity_agenda_cost_barrier` gives the power growth forced by a right-half-strip zero. `rh_of_mixed_agenda_cofinal_subpower` excludes every such zero if the complete squared residual of cofinal exact mixed fits is subpolynomial. The required subpolynomial estimate remains open.

`dyadicMomentProfile_mean` and `dyadicMomentProfile_second` evaluate the first two Pareto moments of the profile $1/(2n+1)$ as $3-4\log 2$ and $5-\pi^2/2$.

`freshDilation_exact_head_cost` bounds the complete cost of a single dilation difference below by $(\sqrt p-1)^2$ times the fitted head energy for every $p>h$.

The conductor-768 transfer `limitEnergy_le_of_roundedHead` gives the exact budget $1987639569969424585050133/293203310455500000000000000$ under the finite integer inequality `roundedHead (2^22) ≤ 674763337657`. The module proves the CRT arithmetic, the full tail transfer, the sieve partition and the first 256 physical sites. The complete rounded-head inequality was independently replayed in integers and is an explicit Lean premise.

## A single adjoint parity vector for endpoint attainment

Let \(r=\mathbf 1-P_V\mathbf 1\), \(E=\|r\|_P^2\), and \(g=D_2^*J_2\) for the ambient adjoint of the scaled dilation. Its physical profile is \(g(n)=n/(2n+1)\). For \(L_d f(n)=f(\lfloor n/d\rfloor)\) with zero anchor, the complete symbolic identities give
\[
g=\tfrac13\mathbf 1+\sum_{d=2}^{\infty}\frac{L_d\mathbf 1}{(2d-1)(2d+1)},\qquad
\langle r,g\rangle_P=\tfrac13 E+\sum_{d=2}^{\infty}\frac{\langle r,L_dr\rangle_P}{(2d-1)(2d+1)}.
\]
The complete signed pairing lies between \(E/6\) and \(E/2\). Consequently the projection attains its upper endpoint exactly when \(g\in V\), or equivalently when \(\langle D_2r,J_2\rangle_P\le0\). Equivalently, the dyadic adjoint commutes with \(P_V\) on \(J_2\). Invariance of \(V\) under that one ambient adjoint is also equivalent to attainment.

For a period \(P\) divisible by every integer through \(N\), the cumulative GCD classes with weights \(a_d=1/[(2d-1)(2d+1)]\) reconstruct \(g\) on every site through \(N\). Möbius interpolation also gives a finite legal fit to each head. For any such fit \(v_N\), the exact tail pairing gives \((E/6)^2\le\|r\mathbf 1_{n>N}\|_P^2\|g-v_N\|_P^2\). **Open** is a bound on these complete errors along arbitrarily long heads for some choice of legal fits, or a proof that \(\langle D_2r,J_2\rangle_P\le0\). Every finite packet combination vanishes at a common multiple of its conductors. The resulting one-site obstruction and the endpoint equivalences are kernel-checked. [Adjoint criterion](RH/ParetoParityAdjointCriterion.lean) · [GCD and finite-head theorems](RH/ParetoParityAdjointHeads.lean)

### Complete errors of finite exact heads

Write \(a_d=1/((2d-1)(2d+1))\) and \(A_N=\sum_{d=1}^N a_d L_d\). The constant head transfers to the parity head through \(A_N\), with \(\|A_N\|\le 1/2\). Applying \(A_N\) to the canonical constant-head Möbius vector gives a legal vector \(v_N\in\mathrm{finiteSpace}(N(N+1))\) with \(v_N(k)=g(k)\) for every \(k\le N\). Its full error \(e_N=\|g-v_N\|_P^2\) satisfies \(e_N/N\to0\). For each \(0<c<c_{\rm contour}\), some \(B\ge0\) gives \(e_N\le 13/2+B N\exp(-c\sqrt{\log N})\) for every \(N\ge1\). [Transfer and signed error identity](RH/ParetoParityFiniteHeadTransfer.lean) · [Möbius lifts and global estimates](RH/ParetoParityMobiusLifts.lean)

The finite inverse uses only proper dilations. Starting from a finite parity head fit \(v\), the recursion \(x_0=0,\ x_{j+1}=3v-3\sum_{d=2}^{N+1}a_d L_d x_j\) produces finite legal constant-head fits as soon as \(N<2^j\), with \(\|x_j\|\le6\|v\|\). The separate consecutive-conductor Möbius interpolant has full squared error at most \(N+1/[4(N+1)]\). [Finite inverse](RH/ParetoParityHeadInverse.lean) · [Consecutive conductors](RH/ParetoParityConsecutiveHeads.lean)

At each zeta zero \(s\ne1\) with \(\sigma=\Re s>1/2\), every legal fit through \(N\ge1\) has full squared error at least \((2\sigma-1)N^{2\sigma-1}/(36|s|^2)\). Consequently a cofinal family with error energy \(o(N^p)\) excludes these zeros whenever \(2\sigma-1\ge p\). Subpower complete errors for all \(p>0\) would imply RH. Báez-Duarte natural approximation gives finite parity heads below every positive prescribed complete error budget. An unconditional uniformly bounded complete error remains open. [Mellin obstruction](RH/ParetoParityHeadMellin.lean) · [Zero-free regions and natural approximation](RH/ParetoParityHeadZeroFree.lean)

For the centered vector \(g_0=J_2/\log 2-\mathbf1\) of the parity manuscript, a constant-head fit \(u\) gives a mixed-closure fit with full error at most \((1+\|J_2/\log 2\|)\|u-\mathbf1\|\). Delaying the mean correction to dilation \(N+1\) balances its norm against the physical tail mass. Finite mixed packets can realize the same head with arbitrarily small additional error. In particular, finite mixed fits with squared error \(o(N)\) exist for \(g_0\). [Finite mixed centered heads](RH/ParetoMixedCenteredParityHeads.lean)

### The periodic GCD lift

One explicit choice extends the matched heads by \(F_P(n)=\sum_{j=1}^{n\bmod P}a_{\gcd(j,P)}\), with \(a_d=1/[(2d-1)(2d+1)]\). This choice permits an exact tail calculation. With \(b_d=\sum_{e\mid d}\mu(d/e)a_e\) and \(r_d(n)=n\bmod d\), divisor inversion gives
\[
 F_P(n)=\sum_{d\mid P}\frac{b_d}{d}\bigl(r_P(n)-r_d(n)\bigr).
\]
Thus \(F_P\) is a finite legal vector. For \(P=N!\) and \(N\ge3\), it agrees with \(g\) through site \(N\). Pairing the coprime residues \(j\) and \(P-j\) gives exactly \(\varphi(P)/2\) coprime sites below \(P/2\). Each contributes \(a_1=1/3\) and all other increments are positive. For \(P/2\le n<P\), \(F_P(n)\ge\varphi(P)/6\) and \(g(n)<1/2\). The Pareto weights on this half-period sum to \(1/P\). Writing \(x_+=\max(x,0)\) gives
\[
 \|F_P-g\|_P^2\ \ge\ \frac{(\varphi(P)/6-1/2)_+^2}{P}.
\]
The Euler product satisfies \(\varphi(N!)/N!=\prod_{p\le N}(1-1/p)\ge\prod_{j=2}^N(1-1/j)=1/N\). The lower bound therefore tends to infinity. This symbolic derivation applies to the displayed periodic lifts. Uniform control for other choices of signed finite lifts remains open.

## Conductor-8192 enclosure of the normalized projection

Write \(\rho=\|P_M(J_2/\log 2)\|_P\) and \(E=\operatorname{dist}_P(\mathbf1,V)^2\). The kernel-checked identity is
\[
(1/\log 2-1)-\rho^2=E/(1-E).
\]
The upper endpoint is attained exactly when \(E=0\). Attainment implies RH. The reverse direction in Lean takes `RiemannHypothesis → BaezDuarte.NaturalApproximation`. [Norm and endpoint theorems](RH/ParetoParityNormBounds.lean)

The conductor-8192 integer trial has scale \(10^9\). For \(T=2^{30}\), its rounded integer head is \(H=5067697348817286\). The twice-centered mean, discrepancy amplitude, and signed CRT covariance are \(b=112901299\), \(A=5074605440756600\), and \(B=161141128064221680975\). With \(C=10^9\), the complete energy budget is
\[
D=\frac{H}{C^2}+\frac{3b^2+B}{12C^2(T+1)}
  +\frac{A^2+2|b|A}{8C^2(T+1)(T+2)}
=\frac{5845890643391160621199204193718469}{1152921507828072450000000000000000000}.
\]
Using \(E\le D\) in the identity gives \(0.66151243224796<\rho\le\sqrt{1/\log2-1}\), improving the supplied conductor-768 bound \(0.66020430387572<\rho\).

| Evidence | Scope |
| --- | --- |
| [CRT tail theorem](RH/ParetoRawTrialPeriodicTail.lean) and [integer reductions](RH/ParetoParity8192Arithmetic.lean) | Lean bounds every omitted site and evaluates \(b,A,B\) from the [signed coefficients](RH/ParetoParity8192Data.lean). |
| [Head identities](RH/ParetoParity8192Head.lean), [segmented sieve](RH/ParetoParity8192Sieve.lean), and [enclosure](RH/ParetoParity8192Certificate.lean) | The kernel proves the divisor-jump recurrence, the exact block and stripe formulas, and the first 128 rounded terms. The enclosure theorem takes the finite inequality `roundedHead (2^30) ≤ 5067697348817286`. |
| [Full integer replay](RH/ParetoParity8192Replay.md) | An independent C++ executable reads the signed coefficient rows used by Lean and evaluates every rounded term through \(2^{30}\). It verifies the eight stripe subtotals and their exact sum. The complete head equality is an arithmetic replay result. |

## Saturation of the mixed projection of parity, 18 November 2026

Put \(\ell=\log 2\), \(z=J_2-\ell\mathbf 1\), \(C_B=\|P_{C_B^{\rm mix}}J_2\|_P^2\) and \(D_B=\ell-\ell^2-C_B\). Here \(C_B^{\rm mix}\) is the span of mixed packets through \(B\), and \(C_\infty\) denotes the corresponding squared capture by their closed span.

| Lean module | Established result |
| --- | --- |
| [MixedConductorCaptureGains](RH/MixedConductorCaptureGains.lean) | `deficit_add_capture` identifies the centered error. Every finite deficit is positive. The exact product and `fixed_capture_saturation_iff_relativeGain_not_summable` reduce saturation to divergence of the actual relative gains. `riemannHypothesis_of_mixed_correlation_shares` accepts lower bounds from individual candidate directions. |
| [MixedCaptureLegalTrials](RH/MixedCaptureLegalTrials.lean) | If \(d=\operatorname{dist}_P(\mathbf1,V)^2\), then \(C_\infty=\ell-\ell^2/(1-d)\). The complete period-5040 legal trial proves \(C_B>\ell-(1000/961)\ell^2\) for every sufficiently large mixed cutoff. |
| [MixedCaptureZeroPair](RH/MixedCaptureZeroPair.lean) | A nonreal zeta zero with real part greater than one half forces a strictly positive deficit. The upper bound retains the contribution of its conjugate. |
| [MixedParityCaptureFifteen](RH/MixedParityCaptureFifteen.lean) | `fixedTwo_centered_trial_balance` keeps the complete excess square for any mixed trial. Five explicit mixed packets prove \(C_B>1/15\) for every \(B\ge15\). |
| [MixedConductorResonanceProduct](RH/MixedConductorResonanceProduct.lean) | Every common prime contributes a full lattice of Mellin resonances. Their Euler product gives an explicit squared error floor. For even mixed packets the Mellin argument yields capture at most \(\ell-1/2\). |
| [OddPeriodBlock](RH/OddPeriodBlock.lean), [OddPeriodEvenPackets](RH/OddPeriodEvenPackets.lean), [FixedOddPeriodProjection](RH/FixedOddPeriodProjection.lean) | A discrete signed test of squared dual norm \(Q(49Q^2-1)/21\) annihilates the even mixed packets and the positive-index \(Q\)-periodic corrections for odd \(Q\). The complete gap is at least \(21Q/[16(49Q^2-1)]\), in particular \(7/256\) with only even mixed packets. Any saturating sequence requires unbounded odd conductor periods. |

**External exact-arithmetic certificate.** A trial of 35,704 rational mixed packets through 40,000 proves \(C_{40000}>0.21001598\). The computation evaluates 320,000,000 physical coordinates and bounds the entire infinite tail. The variational identity has a Lean proof. The larger witness has a separate integer verifier. [Proof, exact fractions and reproduction files](RH/MixedParityCaptureFiniteCertificate.md)

**Open arithmetic obligation.** Prove nonsummability of \(g_B=(C_{B+1}-C_B)/D_B\), or of certified nonnegative lower bounds for those gains. The finite certificate and the necessary growth of the odd conductors do not establish divergence. [Dyadic argument](RH/MixedConductorOddPeriodFloor.md)

## Norm of the normalized screened packet

For \(u=SJ_2/\log 2\) and \(E=\|\mathbf 1-P_V\mathbf 1\|_P^2\),
`normalizedScreenedTwo_norm_sq` gives \(\|u\|_P^2=1/(1-E)\).
The norm is at least one, equals one exactly when \(E=0\), and exceeds one exactly when \(E>0\).
The period-5040 trial gives \(\|u\|_P^2<1000/961\).
The legal projection is \((\|u\|_P^2)^{-1}u\). Screening this projection recovers the constant exactly when \(E=0\).
[Norm and RH declarations](RH/MixedCaptureLegalTrials.lean) · [Projection identities](RH/MixedConductorRankOne.lean)

Unit norm is equivalent to natural approximation and implies RH. Failure of RH forces strict norm excess.
The converse from RH to unit norm takes `RiemannHypothesis → BaezDuarte.NaturalApproximation` as an explicit hypothesis.
This implication remains open in Lean. Báez-Duarte proves it in Theorem 1 of the published paper, numbered 1.1 in the preprint.
[Lean bridge](RH/BaezDuarteNaturalApproximation.lean) · [Published theorem](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0) · [Preprint](https://arxiv.org/abs/math/0202141)

## Lean declarations

| Module | Result |
| --- | --- |
| [PrimePowerRamanujanClosure](RH/PrimePowerRamanujanClosure.lean) | `finite_screened_error_eq_mean_covariance_projection_tail` gives the exact three-term split for a moving input and independent mixed cutoff. |
| [RamanujanPacketDilation](RH/RamanujanPacketDilation.lean) | `dilation_ramanujanPacket_fiber` selects precisely the output conductors \(t\) with \(t/\gcd(t,m)=q\). `dilation_ramanujanPacket_divisors` and `hilbertDilation_ramanujanPacket_divisors` give the equivalent divisor expansion, with repeated prime factors retained. |
| [MixedConductorDilation](RH/MixedConductorDilation.lean) | `hilbertDilation_mem_mixedClosure` proves invariance. `fullScreening_dilation_primePow` shifts the exponent by \(v_p(m)\). `coprimeDilationSpan_closure_eq_mixedClosure` and `mem_mixedClosure_orthogonal_iff_coprime_dilation` identify the generators and their annihilator. |
| [MixedConductorCovariance](RH/MixedConductorCovariance.lean) | `offDiagonalCovarianceMass_gain` and `offDiagonalCovarianceMass_split` retain the complete squared projection differences. `exists_finiteScreening_cutoffs` selects finite cutoffs for arbitrary moving inputs and positive tolerances. `fullScreening_tendsto_iff_exists_cutoffs` gives the resulting convergence equivalence. `exists_centered_mixed_dual_maximizer` attains the unit-ball dual bound for centered inputs. `exists_monotone_finiteScreening_cutoffs` makes the schedule increasing while preserving the lower bounds and tolerances. |
| [MixedConductorHead](RH/MixedConductorHead.lean) | `exists_mixed_exact_head_at` fits any head through \(H\) in the mixed window through \(s(H+1)\) for a prime \(s>H+1\). `mixed_exact_head_error_sq_ge` proves the complete squared error lower bound \(H+1\) for a mixed constant head. `centeredInput_exact_head_tail_product_lower` gives the complete dual tail bound for a mixed correction of the canonical centered input. `mixed_exactHead_one_error` retains the remainder above the sharp head cost. `riemannHypothesis_of_bounded_fixedTwo_exact_heads` reduces the fixed-input problem to uniformly bounded errors. |
| [ResidueConductorVariation](RH/ResidueConductorVariation.lean) | `norm_sq_le_of_residueConductorVariation` bounds a signed dyadic average by \(13\) in complete squared norm. `residuePairing_dyadic_variation_tendsto` proves vanishing dyadic mean absolute differences for every fixed Hilbert vector. |
| [DyadicAdditiveRigidity](NumberTheory/DyadicAdditiveRigidity.lean) | `eq_log_of_coprime_additive_of_dyadic_variation` identifies a coprime-additive function with vanishing dyadic variation as a multiple of \(\log\). |
| [MixedConductorRankOne](RH/MixedConductorRankOne.lean) | `fullScreening_packet_eq_mangoldt_smul` identifies each screened packet with \(\Lambda(q)u\). `mem_mixedClosure_iff_mem_closedSpace_and_mean_zero` identifies \(C\) with the mean-zero subspace of \(V\). `fixed_capture_tendsto_saturation_iff` gives the fixed-input criterion, and `covarianceMass_eq_fixed_error_add_diagonal_tail` retains the additional diagonal projection tail. `hilbertDilation_sub_self_mem_mixedClosure` gives trivial dilation action on the full legal quotient. |
| [ParetoRamanujanGramCRT](RH/ParetoRamanujanGramCRT.lean) | `ramanujanPacketHilbert_inner_eq_lcm_digamma` evaluates each complete Gram entry at its pairwise lcm. `ramanujan_meanOne_optimal_error` gives the inverse-Gram minimum and the exact error remainder for every alternative mean-one trial. |
| [PsiNormalizedRamanujanUnscreened](RH/PsiNormalizedRamanujanUnscreened.lean) | `unnormalizedInput_sequence_primeTowers`, `unscreened_pointwise_tendsto_zero`, and `unscreenedApproximant_norm_sq_eventually_bounds` give the unscreened tower identity and complete asymptotics. `offDiagonalCovarianceMass_div_psi_sq_eq_removed_energy` gives the exact normalized energy removed by mixed screening. |
| [MixedConductorSeedObstruction](RH/MixedConductorSeedObstruction.lean) | `restricted_mixed_seed_error_floor` gives a positive Mellin bound when all correction conductors are multiples of the input prime. |
| [FiniteGeneralizedCRT](NumberTheory/FiniteGeneralizedCRT.lean) | `exists_int_modEq_iff_pairwise` gives existence for arbitrary finite congruences under pairwise gcd compatibility. `int_solution_class` gives the exact lcm solution class. `existsUnique_int_modEq_of_pairwise` gives the normalized representative for positive moduli. |
| [ProfiniteGeneralizedCRT](NumberTheory/ProfiniteGeneralizedCRT.lean) | `exists_profiniteInt_iff_pairwise` lifts any indexed family of compatible positive-modulus congruences to a profinite integer. `profiniteInt_ext_of_lcm_cofinal` gives uniqueness when every positive modulus divides a finite lcm of the given moduli. |
| [ProfiniteCRT](NumberTheory/ProfiniteCRT.lean) | `profinitePadicEquiv` identifies the all-modulus inverse limit with the product of the \(p\)-adic integer rings. `padicProjection_toZModPow` identifies the reductions, and `isTopologicalRingCRT_profinitePadicEquiv` proves continuity in both directions. |

The weighted Gram entries use the complete progression weights in
[ParetoFullTailCRT](RH/ParetoFullTailCRT.lean). The CRT specifies the
compatible cells and their reductions. For a finite packet window with a
prime power, put \(b=G^{-1}\lambda\) and \(T=\lambda^\mathsf{T}b\). The
checked mean-one optimum has coefficients \(b/T\) and squared error
\(1/T-1\). Every alternative mean-one vector adds the squared norm of its
difference from that optimizer.

## Rank-one full screening

Let \(u=S R_2/\log 2\). If \(h\in C^\perp\), the residue pairing
\(F_h(q)=\langle r_q,h\rangle_P\) is additive on coprime moduli.
For \(n<M\) every adjacent residue difference in the block \([M,2M)\)
vanishes. At any physical coordinate \(n\), the sum of its absolute
differences is at most \(\min(3n,2M^2)\). Splitting the complete weighted
norm at \(M^2\) gives
\[
\left(\frac1M\sum_{q=M}^{2M-1}|F_h(q+1)-F_h(q)|\right)^2
 \le 13\,\|h\mathbf1_{\{n\ge M\}}\|_P^2 .
\]
The right side tends to zero. The additive rigidity theorem then gives
\(F_h(q)=c_h\log q\). Möbius inversion and
\(\sum_{d\mid q}\Lambda(d)=\log q\) give \(S R_q=\Lambda(q)u\).
In particular \(Sx=\langle x,\mathbf1\rangle_P u\) for every \(x\in V\).
The logarithmic step is checked in Lean using Cesàro means along
arithmetic progressions. The classical additive rigidity result and its
short-interval version are discussed in I. Kátai,
[On additive functions](https://doi.org/10.5486/PMD.1978.25.3-4.10), equations
(1.1) and (1.2).

Put \(\delta=\|\mathbf1-P_V\mathbf1\|_P^2\), the repository's
`limitEnergy`. The checked identities are
\[
\|u-\mathbf1\|_P^2=\frac{\delta}{1-\delta},
\qquad
A_N(\infty)=\psi(N)^2\frac{\delta}{1-\delta}.
\]
Consequently \(A_N(\infty)/N^2\to0\) if and only if
\(\mathbf1\in V\). The diagonal value \(A_N(N)\) adds the entire
squared finite-to-full projection difference on the centered input.

## The constant as a logarithmic test vector

[ParetoLogResidueTest](RH/ParetoLogResidueTest.lean) verifies
\(F_{\mathbf1}(d)=\log d\) for positive \(d\).
The vectors sharing these moments are exactly \(\mathbf1+V^\perp\).
Their unique representative in \(V\) is \(P_V\mathbf1\).
Uniqueness in the whole Hilbert space is equivalent to \(\mathbf1\in V\).

Let \(r=\mathbf1-P_V\mathbf1\), \(\delta=\|r\|_P^2\), and
\(T_k f(n)=f(\lfloor n/k\rfloor)\) with the zero anchor.
For every \(m\ge1\), Lean checks
\[
 \langle r,\mathbf1_{\{1\le n\le m\}}\rangle_P
 =\delta-\langle r,T_{m+1}r\rangle_P,
 \qquad
 |\langle r,T_{m+1}r\rangle_P|\le\frac{\delta}{\sqrt{m+1}}.
\]
The conditional reduction `riemannHypothesis_of_nonpositive_compactHead_residual`
uses nonpositive signed residual mass on a single nonempty initial interval.

**Open.** Establish that nonpositive signed mass for some \(m\ge1\).
The logarithmic moments determine the projected constant and leave this endpoint open.

## Prime-power telescopes at a mixed cutoff

[ScreenedPrimePowerTelescope](RH/ScreenedPrimePowerTelescope.lean) connects the
finite telescope to the rank-one theorem. [PrimePowerPacketSummation](RH/PrimePowerPacketSummation.lean)
also proves summation by parts for arbitrary tower coefficients, including the endpoint term. With \(D_d(n)=n\bmod d\),
\(\sum_{a=1}^A J_{p^a}=D_{p^A}\) in the complete Hilbert space.
Every single fully screened prime power spans \(W_*\). For every \(d>1\) put
\(x_d=D_d/\log d\). Then \(Sx_d=u\), and
\[
 \|\mathbf1-S_B x_d\|_P^2
 =\frac{\delta}{1-\delta}+\|(P_C-P_{C_B})x_d\|_P^2 .
\]
The centered residue \(D_d-(\log d)\mathbf1\) belongs to \(C\) exactly when the
target belongs to \(V\). In particular the fixed conductor 2 tests centered parity.
For any two legal inputs of means \(m_x,m_y\), the centered Gram entry at cutoff
\(B\) equals \(m_xm_y\delta/(1-\delta)+\langle(P_C-P_{C_B})x,(P_C-P_{C_B})y\rangle_P\).
The declaration `finiteScreening_centered_gram` proves this identity. For any prescribed sequence
of moduli, convergence to the target along some mixed cutoffs is equivalent
to target membership. The cutoffs may exceed any prescribed lower bounds.

For finite mixed conductors and any correction in their span, all common
multiples are compulsory physical observations. On a set \(T\) of such
multiples with \(2\log d\le n<d\), the squared error is at least
\(|T|/(8\log^2 d)\). The declaration `logNormalizedResidue_error_partition`
retains the exact sum over the complementary sites. For a fixed period \(L\),
the number of eligible multiples is asymptotic to \(d/L\), so a fixed mixed
window gives divergent error as the input conductor grows. The arithmetic
saturation of the fixed conductor 2 remains open.

The first mixed conductor is 6. With \(b=\log 2-\pi/(2\sqrt3)\) and
\(h=\pi/\sqrt3\), the optimal mixed coefficient for the raw packet
\(J_2-tJ_6\) is \(t=b/h\). Its captured energy is \(b^2/h\).
The theorem `fixedTwo_mixed_capture_at_six` identifies the energy of the actual
mixed-window projection with this value. The theorem `conductor_six_mixed_fit_error`
gives the unit-mean target error for every real coefficient, including the whole
square above the minimum.

## Fixed-conductor criterion

For \(y_M=(I-P_{C_M})R_2/\log 2\), the exact finite error is
\[
\|\mathbf1-y_M\|_P^2=
 \frac{\log 2-(\log 2)^2-\|P_{C_M}R_2\|_P^2}{(\log 2)^2}.
\]
The numerator tends to zero if and only if \(\mathbf1\in V\), which
implies Mathlib's `RiemannHypothesis`. The kernel-checked equivalence
with `BaezDuarte.NaturalApproximation` uses the existing complete
normalization transfer. The converse from RH follows on paper from
Báez-Duarte's [strong Nyman–Beurling theorem](https://arxiv.org/abs/math/0202141),
Theorem 1.1. The repository still treats that analytic direction as an
external provider.

**Open arithmetic estimate.** Prove that \(\|P_{C_M}R_2\|_P^2\) increases
to \(\log 2-(\log 2)^2\). This criterion has a fixed prime input. The
specific diagonal canonical family additionally needs decay of its
moving-input projection tail. Finite mixed exact heads alone are compatible
with growing complete error.

For the centered input \(Z_N\) and \(e=u-\mathbf1\), an exact-head mixed
correction \(c\in C\) through \(H\) satisfies
\[
\psi(N)^2\|e\|_P^4
\le \|e\mathbf1_{\{n>H\}}\|_P^2\,\|Z_N-c\|_P^2 .
\]
Thus exact heads with \(H_N\to\infty\) would imply RH if their complete
squared errors were merely \(O(\psi(N)^2)\). The checked theorem
`riemannHypothesis_of_bounded_centeredInput_exact_head` retains that
bound as an explicit hypothesis. A specific mixed correction family
with this bound remains Open.

For the fixed target \(z=R_2-(\log 2)\mathbf1\), it also suffices to find
mixed corrections \(c_H\) that match \(z\) through cofinal heads and satisfy
\(\sup_H\|z-c_H\|_P^2<\infty\). The proof tests the signed tail against
\(Sz\). The squared tail norm of this fixed dual vector tends to zero.
The required uniform bound for a finite mixed correction family remains Open.

The universal constant-head bound has an exact remainder. If \(c\in C\)
agrees with \(\mathbf1\) through \(H\), then
\[
\|\mathbf1-c\|_P^2 =
H+1+\|\mathbf1-c-(H+1)\mathbf1_{\{n>H\}}\|_P^2 .
\]
For a general exact-head trial, `exactHead_tail_eq_covariance_add`
separates the full signed tail into the optimal finite covariance and the
square of the distance from the chosen correction to its mixed projection.

A restriction on possible corrections comes from the single-seed Mellin
separation. For input \(R_p/\log p\), corrections using only conductors
divisible by \(p\) leave squared error at least
\[
\frac{1}{1+(2\pi/\log p)^2}.
\]
The resonance is \(1+2\pi i/\log p\). For \(p=2\) the lower bound is
approximately \(0.01202368852\), so the fixed-conductor route requires
odd mixed conductors. The one-dilation correction \(x-D_mx\) also has exact
centered error \(m\|x\|_P^2-\langle x,\mathbf1\rangle_P^2\).

## Finite Wolfram validation

The folded Gram computations use complete Pareto progression weights
evaluated through the digamma formula. For the fixed input \(R_2/\log 2\),
the rounded squared errors at \(M=6,12,16,24,32\) were respectively
\(0.39026475,\ 0.34962883,\ 0.29572248,\ 0.23328243,\ 0.21336861\).
Exact symbolic residue reductions also gave zero divisor-formula defect on
complete periods for the tested overlapping cases. The finite values
supply benchmarks for the fixed-input criterion. Wolfram symbolically
simplified the first mixed Gram entries to
\(\langle R_2,R_6\rangle_P=\log 2-\pi/(2\sqrt3)\) and
\(\|R_6\|_P^2=\pi/\sqrt3\), reproducing the first squared error.


A separate exact-integer sweep checked 238 conductor–dilation pairs at
17,850 period points, with zero defects. In a 60-digit two-cutoff sweep,
the following are the centered input energy, its removed projection energy,
and the remaining variance. The displayed values are rounded.

| \(N\) | \(M\) | \(\|Z_N\|_P^2\) | \(\|P_{C_M}Z_N\|_P^2\) | \(A_N(M)\) |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 8 | 10.22034218 | 5.30013589 | 4.92020630 |
| 8 | 16 | 10.22034218 | 6.63897044 | 3.58137174 |
| 8 | 24 | 10.22034218 | 7.43156952 | 2.78877267 |
| 12 | 8 | 39.29932290 | 20.03422230 | 19.26510059 |
| 12 | 16 | 39.29932290 | 31.02541408 | 8.27390882 |
| 12 | 24 | 39.29932290 | 32.43376536 | 6.86555753 |
| 16 | 8 | 87.99537120 | 40.27636435 | 47.71900685 |
| 16 | 16 | 87.99537120 | 77.65514950 | 10.34022170 |
| 16 | 24 | 87.99537120 | 78.67103434 | 9.32433686 |

The gain from \(M=8\) to \(M=24\) agreed with the separately evaluated
squared projection difference to more than 55 digits of absolute working
precision for all three prime cutoffs.

## Unscreened size

For \(x_N=\psi(N)^{-1}\sum_{p^k\le N}R_{p^k}\), the prime-power
sum telescopes for each prime to \(r_{p^{k_p}}\), where \(p^{k_p}\) is its
largest power at most \(N\). Thus
\(0\le x_N(n)\le\pi(N)\min(n,N)/\psi(N)\).
On \(n\le N/2\), primes in \((N/2,N]\) give the lower bound
\(n(\pi(N)-\pi(N/2))/\psi(N)\). The checked complete norm bounds give
\(\|x_N\|_P^2\asymp N/(\log N)^2\), with eventual comparison constants
\(1/2048\) and \(32\). The checked pointwise limit is \(x_N(n)\to0\) for
every fixed \(n\). For the prime number theorem
forms, see Leonard Tomczak's
[Analytic Number Theory lecture notes](https://math.berkeley.edu/~ltomczak/notes/Mich2022/AnaNT_Notes.pdf),
Section 5.
