# CRT carry Schur blocks, Dirichlet Grams and the RH implications

This catalog follows Christian Noack's *Q CRT Carry Gram and Schur Matrices with Zeta Trace Identities* (13 October 2026). Write $Z=\zeta(2)$, $c_0=\log(2\pi)-\gamma$, $Q(n)=1/(Zn^2)$, and $g_d(n)=(n\bmod d)/d$. All approximation statements use the original $Q$. The separate parameter $s$ changes the weights of a fixed finite feature family.

## Actual finite geometry

| Mathematical statement | Lean source and declarations |
|---|---|
| Distinct conductors greater than one give linearly independent $Q$ atoms and a positive definite Gram | [QCovarianceInvertibility](RH/QCovarianceInvertibility.lean), `qResidue_linearIndependent`, `qGram_posDef`, `qError_eq_determinant_ratio` |
| The least CRT inverses give a legal carry. Removing the span of its previously available atom terms gives the negative of the screened incoming atom. The full block spans the new stage | [QCRTPrimorialCarry](RH/QCRTPrimorialCarry.lean), `primeBase_screen_carry`, `full_prime_block_span_eq`, and [QCRTCarryGain](RH/QCRTCarryGain.lean) |
| The matrix $T=\left(\begin{smallmatrix}I&U\\0&-I\end{smallmatrix}\right)$ is involutive. The Gram determinant, inverse congruence, and target energy are exactly preserved | [CarryGramCongruence](LinearAlgebra/CarryGramCongruence.lean), `change_mul_self`, `det_congr`, `inv_congr`, `target_energy_invariant` |
| Screened Gram entries equal the Schur complement. Independence survives screening. The inverse Gram measures the exact additional target energy | [FiniteGramScreenedCapacity](Analysis/FiniteGramScreenedCapacity.lean), `screened_gram_entry`, `screened_linearIndependent`, `screened_gram_positive`, `capacity_screened_add`. See also [FiniteHilbertGram](Analysis/FiniteHilbertGram.lean), `residual_schur_value`, `residual_completion`, `residual_minimizes`, and [FiniteGramDeterminantCertificates](Analysis/FiniteGramDeterminantCertificates.lean), `bordered_det_ratio` |
| Every finite optimizer has a strictly positive residual on the common-period multiples | [QCommonPeriodError](RH/QCommonPeriodError.lean), `primorialError_exact`, `primorialError_lower` |

The carry identity requires its CRT coefficients. The involution calculation permits arbitrary $U$ because it describes only a coordinate change. In particular, taking a floor of an arbitrary combination would require a separate legality proof.

## Residue norms and traces

Let $D(d)=d c_0-Zd^2\|g_d\|^2$. For $d\ge1$, the missing zero mesh point contributes exactly one to the scaled error. The remaining cell errors are nonnegative and sum to at most $Z-1$. Hence
$$
1\le D(d)\le Z,\qquad
\frac{c_0}{Zd}-\frac1{d^2}\le\|g_d\|^2\le
\frac{c_0}{Zd}-\frac1{Zd^2}.
$$
For a squarefree dictionary excluding conductor one, the complete defect is at most $\zeta(2)/\zeta(4)-1$. The proof embeds the disjoint square multiples of its squarefree conductors into the positive integers. [QSquarefreeTraceRemainder](RH/QSquarefreeTraceRemainder.lean), `squarefree_trace_defect_upper`

The sum over any finite positive divisor set preserves every mesh defect. Its error is between $\sum_d 1/(Zd^2)$ and $\sum_d 1/d^2$. [QResidueMeshNorm](RH/QResidueMeshNorm.lean), `defect_bounds`, `norm_bounds`, `residue_trace_exact`, `total_defect_bounds`, `total_defect_le_zetaTwo`, `residue_trace_asymptotic_of_mass`

Fix an old squarefree primorial $L$ and incoming prime $p$. Form $V=W_L+\mathbb Rg_p$, let $r=(I-P_V)1$, $e=\|r\|^2$, and $h_d=-(I-P_V)g_{pd}$. For a selected subset $A$ of old nontrivial divisors, write $B_A=\sum_{d\in A}1/d$, $T_A=\sum_{d\in A}\|h_d\|^2$, and $S_A=\sum_{d\in A}\langle r,h_d\rangle^2$. Then
$$
T_A+\sum_{d\in A}\|P_Vg_{pd}\|^2
 +\sum_{d\in A}\frac{D(pd)}{Z(pd)^2}=\frac{c_0 B_A}{Zp}.
$$
This exact identity records both sources of slack and applies to the full physical Schur trace. [QCRTCarrySourceBudget](RH/QCRTCarrySourceBudget.lean), `blockTrace_exact`, `blockTrace_upper`

A direct Euler-product argument proves trace decay without a prime asymptotic. At most one of two consecutive cutoffs $n+4,n+5$ is prime. For $M_n=\sum_{d\mid L_n}1/d$, this gives $M_n^2\le M_0^2(n+3)$ and $M_n/(n+4)\to0$. Thus $T_A\to0$ for every varying choice of subblock. The sharper classical leading constant in the note follows from $\prod_{q\le y}(1+q^{-1})=\prod_{q\le y}(1-q^{-2})/\prod_{q\le y}(1-q^{-1})$ and Mertens's product theorem. The Lean proof of decay uses the elementary bound. [QPrimorialCarryTrace](RH/QPrimorialCarryTrace.lean), `mass_prime_step`, `mass_sq_bound`, `actual_trace_tendsto_zero`. [Mertens, 1874](https://doi.org/10.1515/crll.1874.78.46)

## Conditional arithmetic reduction to RH

At prime cutoffs set $b_n=S_A/(T_A e^2)$, with zero for an empty block. Nonprime cutoffs contribute zero. For the actual total capacity $\kappa=1/\delta-4$,
$$
\left(\frac1e-\frac1{\delta_L}\right)+ b_n
\ \le\ \kappa_{pL}-\kappa_L.
$$
Thus divergence of $\sum b_n$ implies $\delta_{L_n}\to0$ and RH. The paper's smaller budget $Zp S_A/(c_0B_Ae^2)$ also suffices. Lean uses $1/\delta-1$ for the absolute capacity, an additive shift of three that cancels in every increment. Its cutoff $n=0$ includes 2 and 3, so the separately treated $2\to6$ block precedes the cofinal sequence. [QCRTCarrySourceBudget](RH/QCRTCarrySourceBudget.lean), `capacity_split`, `prime_gain_add_selectedBudget_le`, `arithmeticBudget_sum_le_capacity`, `riemannHypothesis_of_arithmeticBudget_diverges`

The best subset for this particular trace certificate is always a singleton or the empty set. For $h_d\ne0$ put $b_{n,d}=\langle r,h_d\rangle^2/(e^2\|h_d\|^2)$. With positive total variance, $b_n(A)$ is an average of these scores with weights $\|h_d\|^2/T_A$. Lean proves the upper bound by the largest singleton, attainment, and equivalence of divergence of the best-singleton series with existence of a divergent selected-subblock series. This optimizes the trace certificate. The full inverse-Gram gain can be larger. [QCRTCarrySourceBudget](RH/QCRTCarrySourceBudget.lean), `selectedBudget_weighted_singletons`, `selectedBudget_le_best`, `bestBudget_attained`, `divergent_selection_iff_best_singletons`, `riemannHypothesis_of_best_singletons`

Two sufficient estimates for these actual scores are available.

- An eventual bound $S_A\ge c e^2B_A/p^2$ with $c>0$ and $B_A>0$ on prime stages gives a divergent multiple of $\sum_p1/p$.
- A bound $b_n+u_n\ge c/p$ at the prime stages suffices when $u_n\ge0$ and $\sum_nu_n<\infty$. The chosen divisors can change with the prime. Conversely, failure of RH forces the budget of every such selection to be summable.

A further criterion permits a complementary set of primes of arbitrary size. It is enough to prove the singleton lower bound on any set $\mathcal P$ with $\sum_{p\in\mathcal P}1/p=\infty$. Under failure of RH every set on which the best budget exceeds $c/p$ must have finite reciprocal sum. [QCRTCarrySourceBudget](RH/QCRTCarrySourceBudget.lean), `riemannHypothesis_of_singletons_on_good_stages`

The implication uses the published squarefree form of the Nyman–Beurling criterion and the project's cofinality and projection theorems. A source lower estimate for the actual residual over a cofinal family remains open. The bound on $T_A$ alone supplies no lower bound on $S_A$. [QCRTCarrySourceBudget](RH/QCRTCarrySourceBudget.lean), `riemannHypothesis_of_eventual_source_floor`, `riemannHypothesis_of_prime_scores_with_defect`, `summable_selectedBudget_of_not_RH`. [Bagchi, Remark 8](https://arxiv.org/pdf/math/0607733), [published article](https://doi.org/10.1007/BF02829783), [Báez-Duarte's strong criterion](https://arxiv.org/abs/math/0202141)

## Zeta, leverage and the determinant agenda

1. For a family on $\mathbb Z/D\mathbb Z$, each entry of the unnormalized Gram is a finite Hurwitz combination and a Dirichlet series for $\Re s>1$. The normalized Gram has a punctured complex limit at $s=1$ equal to the uniform counting Gram. Whenever the base uniform Gram is nonsingular, the Schur determinant converges to its uniform-period determinant ratio. [PeriodicDirichletGram](Analysis/PeriodicDirichletGram.lean), `gram_hurwitz`, `gram_dirichlet`, `gram_entry_meromorphic`, `dirichlet_ratio_meromorphic`, `normalized_tendsto_periodGram`, `schur_det_tendsto_uniform_period`. [DLMF §25.11](https://dlmf.nist.gov/25.11)
2. The Schur determinant is the joined-over-base determinant ratio. Normalizing its Dirichlet Grams contributes $\zeta(s)^{-k}$. Jacobi's formula yields $k(-\zeta'/\zeta)$ minus the difference between the joined and base log-moment traces. The entrywise Schur derivative itself is $\mu\Omega$ minus the log-weighted form on the screened columns. The single screened trace consequently agrees with the joined-minus-base formulation. This form differentiates the actual Schur determinant in the half-plane where the base and joined normalized determinants are nonzero. [GramLogarithmicDerivative](Analysis/GramLogarithmicDerivative.lean), `det_logDeriv`, and [PeriodicDirichletGram](Analysis/PeriodicDirichletGram.lean), `det_ratio`, `schur_det_eq_ratio`, `schur_entry_hasDerivAt`, `schur_logDeriv_screened`, `schur_det_logDeriv`. The inverse normal-equation differential is proved in [SchurMatrixDerivative](Analysis/SchurMatrixDerivative.lean)
3. The deformation is the literal $Q$ tilt and specializes to the original Hilbert pairing at $s=2$ by `gram_eq_Q_tilt` and `normalized_two_eq_Q`. The scalar term has an actual von Mangoldt series. The real part also has an absolutely convergent sum over the actual nontrivial zeros, counted with multiplicity, with summands $m_\rho(\Re s-\Re\rho)/|s-\rho|^2$ and the gamma and rational terms. This supplies the zero-resolvent version for the logarithmic trace in the note's real parameter, using the project's unconditional contour theorem. Each zero retains its real part. [CRTCarryZetaResolvent](RH/CRTCarryZetaResolvent.lean), `schur_prime_series`, `schur_actual_zero_trace_re`
4. The conditional mean of $\log(a+Dk)$ with weights $(a+Dk)^{-\sigma}$ increases with $a$ for $\sigma>1$. The proof compares weighted double sums and justifies the infinite limit. Its endpoint equals $\log D+\mu_\sigma$. The quadratic-form and leverage bounds may use the largest class supporting the feature. Genuine residue atoms and carries vanish on the zero class. Hence for those features one can use $m_\sigma(D-1)$ when $D\ge2$. For a positive definite finite Gram the leverage weights are nonnegative and sum to its rank. [PeriodicLogCompression](Analysis/PeriodicLogCompression.lean), `ordered_weighted_sums`, `mean_mono`, `mean_last`, `compression_upper`, `weighted_trace`, `leverage_sum`, `log_trace_upper`
5. For every positive semidefinite matrix $A$ and $|z|\le R$,
   $|\det(I-z^2A)-1|\le\exp(R^2\operatorname{tr}A)-1$. The actual physical blocks have vanishing trace, so their unscaled spectral polynomials converge uniformly to $1$ on every complex disk. An actual zero of $\xi$ rules out a pointwise identification with any constant multiple of $\xi(1/2+iz)$. Every bounded nonnegative scalar rescaling of these physical blocks also converges to the constant determinant. The disk estimate further applies to any proposed positive normalization whose trace still tends to zero. [VanishingTraceDeterminant](Analysis/VanishingTraceDeterminant.lean), `det_disk_bound`, `det_tendstoUniformlyOn_disk`, and [QPrimorialCarryTrace](RH/QPrimorialCarryTrace.lean), `unscaled_det_tendsto_one`, `bounded_rescaling_det_tendsto_one`. [CRTCarryZetaResolvent](RH/CRTCarryZetaResolvent.lean), `no_unscaled_xi_limit`

A modified positive family with a genuine completed-zeta determinant limit on the strip would imply RH by `HilbertPolya.riemannHypothesis_of_strip_positive_matrix_limit`. Constructing such a family from arithmetic data, proving the normalization and proving the limit with the necessary zero data remain open. The meromorphic identity for the normalized Dirichlet Gram permits cancellations at zeros of zeta.

The original note also presents the complex genus-one Hadamard formula with $B_\xi$ and the Chebyshev $\psi$ integral as alternative expressions for the scalar term. The checked trace here uses the actual von Mangoldt series and the absolutely convergent real-part zero sum throughout $\Re s>1$. The latter directly covers the original real parameter. [Riemann’s original manuscript](https://www.claymath.org/collections/riemanns-1859-manuscript/), [DLMF §25.2](https://dlmf.nist.gov/25.2)

## First block and numerical continuation

For $L=2$, $p=3$, the genuine carry $\lfloor g_2+2g_3\rfloor$ is the indicator of residues $1,2,5\pmod6$. The module derives all six probability masses by dilation and residue-class partition, certifies $0.47497491154\le h\le0.47497491155$ using trigamma tails, evaluates the Gram and target, and simplifies their Schur complement. [QFirstCarrySchur](RH/QFirstCarrySchur.lean), `true_weights`, `h_trigamma`, `gram_eq`, `target_eq`, `omega_eq`, `eta_eq`, `gain_bounds`, `final_error_bounds`

The exact rational first-block certificates imply $0.038057105\le\Omega\le0.038057108$, $0.01391833\le\eta^2/\Omega\le0.01391835$, and $0.05476693\le\delta_6\le0.05476696$. These intervals include every repeated period under $Q$.

The following exploratory calculations use full progression weights $\zeta(2,a/(pL))/(Z(pL)^2)$ for every class and Cholesky solves. $S,T,B$ below use all incoming composite conductors. Wolfram independently evaluated the first block and the differentiated first-block Hurwitz matrix. It gave $-0.9606278978556629815\ldots$ for the logarithmic derivative at $\sigma=2$ on both sides of the trace identity. The table contains rounded floating-point diagnostics.

| Old $L$ | $p$ | $\delta_{pL}$ | $T$ | $p^2S/(B e^2)$ | $S/(T e^2)$ | Best singleton budget |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 3 | .054766943370 | .03805711 | 2.021009 | 2.950258 | 2.950258 |
| 6 | 5 | .025400225436 | .05191586 | 2.260241 | 1.741464 | 1.971749 |
| 30 | 7 | .016870436061 | .03092194 | .044580 | .041191 | .099151 |
| 210 | 11 | .013549481065 | .01476851 | .101355 | .098852 | .296435 |
| 2310 | 13 | .011752997896 | .01014318 | .109006 | .126685 | .280279 |
| 30030 | 17 | .008402443600 | .00586044 | .557222 | .731169 | 2.364431 |

The sharp drop at $p=7$ illustrates the unresolved uniformity issue. A research target is to estimate the positive part of $c/p-\max_d\{\langle r,h_d\rangle^2/(e^2\|h_d\|^2)\}$ by a summable sequence. This is a statement about observable residual pairings. Its inputs can be estimated from individual divisor innovations at each finite stage.
