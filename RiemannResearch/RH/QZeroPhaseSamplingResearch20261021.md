# Zero-phase sampling of the complete Q geometry

Prepared for Christian Noack on 21 October 2026.

**Verification evidence.** The coherent seven-module candidate passed Lean-server job `job_lyysB2iYhMA3_sUq34irskqbeTPwhti2` (`verified=true`, exit 0; server elapsed 51.670 seconds). The arithmetic/closure candidate passed `job_xR-gOGP0D4dh3vKjAFu3pVeXUJGenHEY` (109.866 seconds). The final saved-module import and axiom check passed `job_JnLIITc1oOKShH3ulH5N7q-vDsXqqug7`: all nine new modules imported successfully, exit 0, `verified=true`, server elapsed 185.662 seconds. The eleven inspected decisive declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Their theorem types still contain the explicitly stated domain-specific hypotheses; an axiom report does not discharge those hypotheses.

The earlier combined import job `job_u4CfcLL2-dlJkhA8Bsrtmj1rw-vJe63F` reached its 180-second wall limit after building six new modules; it is not counted as a successful check. The longer-limit job above completed the saved-source check. Server durations include dependency preparation and compilation, not just kernel time; queue/observation delays are separate. The initial workspace-opening request yielded after its first 30-second observation window; no independent precise opening or kernel-only duration was captured. Publication is gated by the final source audit and aggregate/changed-module checkpoint. The final response and containing Git history identify that checkpoint and published commit. Actual zero-bin equidistribution and vanishing sampled errors remain explicit domain-specific inputs.

## 1. Purpose and precise scope

The aim is to use phase information from zeta-zero ordinates as a deterministic sampling mechanism for the **existing complete Q inner product**. The construction does not replace the squarefree legal dictionary, discard an infinite physical tail, or assume RH.

The verified saved-module results include:

1. Exact regrouping of a sample by its cells.
2. Importance weighting that recovers a prescribed finite weighted mean from asymptotically uniform cell frequencies.
3. A bridge from periodic physical representatives to complete Q inner products.
4. Uniform relative comparison of all energies and signed cross terms when every cell frequency is relatively accurate.
5. A quadratic bound for the displacement between true and sampled least-squares optimizers.
6. Existence of a sufficiently slow growing-stage diagonal, conditional on fixed-stage cell convergence.

The actual analytic assertion that the zeta-zero phase bins have the required joint frequencies is established in classical mathematics, but **is not supplied by this finite formalization**. The older actual FMZ interface still requires the open-in-Lean input `UniformSelbergDensity (1/4)`; that input must not be reported as proved merely because it is a classical theorem or appears as a hypothesis of a verified consumer.

Even after the sampling interface is complete, an independent arithmetic estimate forcing the legal approximation error to zero remains necessary. Sampling the same minima does not make their limiting vanishing easier by itself.

## 2. Complete Q space and finite periodic coordinates

Put
\[
Z=\zeta(2),\qquad Q(n)=\frac1{Zn^2}\quad(n\ge1),
\qquad g_d(n)=\frac{n\bmod d}{d}.
\]
For a finite set of distinct primes \(\mathcal P\), let
\[
L=\prod_{p\in\mathcal P}p,
\qquad
V_L=\operatorname{span}_{\mathbb R}
  \{g_d: d\mid L,\ d>1\}.
\]
All squarefree divisors are retained, including composite divisors.

Use physical representatives \(a=1,\ldots,L\), with the zero residue represented by **L**, not the auxiliary index zero. Define the complete weights
\[
w_L(a)=\sum_{j\ge0}Q(a+jL)
       =\frac1Z\sum_{j\ge0}\frac1{(a+jL)^2}.
\]
They satisfy \(w_L(a)>0\) and \(\sum_{a=1}^Lw_L(a)=1\).

For bounded L-periodic physical functions F and G, the exact regrouping of the full absolutely convergent series is
\[
\boxed{
\langle F,G\rangle_Q
 =\sum_{a=1}^Lw_L(a)F(a)G(a).
}
\tag{2.1}
\]
The full infinite progression is already inside each weight. Formula (2.1) is not a finite-head approximation.

The Lean Hilbert encoding assigns an auxiliary value at zero. A physical periodic representative need only agree with that encoded sequence at **positive** integers. This qualification is essential for the constant function and residuals such as \(1-F\): their natural periodic representatives may have a nonzero value at zero, while the auxiliary Hilbert sequence has value zero there. The `qInner_eq_periodic_weights` bridge handles this explicitly.

## 3. From zero ordinates to CRT cells

Let \(\rho=\beta+i\gamma\) range over nontrivial zeta zeros with \(0<\gamma\le T\), **counted with multiplicity**, and write \(N(T)\) for the count. No restriction to the critical line is made.

For each \(p\in\mathcal P\), set
\[
\theta_p(\gamma)
 =\left\{\frac{\gamma\log p}{2\pi}\right\}\in[0,1),
\qquad
b_p(\gamma)=\lfloor p\theta_p(\gamma)\rfloor\in\{0,\ldots,p-1\}.
\]
The CRT determines a unique \(a_L(\gamma)\in\{1,\ldots,L\}\) such that
\[
a_L(\gamma)\equiv b_p(\gamma)\pmod p
\qquad(p\in\mathcal P).
\]
In particular, an all-zero tuple maps to L.

For \(a\in\{1,\ldots,L\}\), write \(a_p=a\bmod p\). Its torus cell is the half-open box
\[
B_a=\prod_{p\in\mathcal P}
 \left[\frac{a_p}{p},\frac{a_p+1}{p}\right).
\]
These L boxes partition the torus, have Haar volume \(1/L\), and have boundaries of Haar measure zero. The equivalence
\[
a_L(\gamma)=a
\quad\Longleftrightarrow\quad
(\theta_p(\gamma))_{p\in\mathcal P}\in B_a
\tag{3.1}
\]
is the ordinary half-open-box interpretation of the checked floor-bin/CRT equivalence. The floor-defined code, its uniqueness and its positive physical residues are formalized; the measure-theoretic null-boundary argument remains part of the analytic provider.

When \(N(T)>0\), define
\[
\nu_{L,T}(a)=
 \frac{\#\{\rho:0<\gamma\le T,\ a_L(\gamma)=a\}}{N(T)},
\qquad
q_{L,T}(a)=L\nu_{L,T}(a).
\]
A finite set of distinct ordinate values would lose multiplicities. A formal finite sample must instead use zero indices, a multiset, or another representation preserving multiplicity.

The classical fixed-stage input is
\[
\boxed{
\forall a\in\{1,\ldots,L\},\qquad
\nu_{L,T}(a)\longrightarrow\frac1L
\quad(T\to\infty).
}
\tag{3.2}
\]
It says nothing yet about a prescribed L growing with T.

## 4. Exact importance-weighted sampling

For any periodic physical test \(\Phi\), set
\[
\mathcal S_{L,T}(\Phi)
 =\frac1{N(T)}\sum_{0<\gamma\le T}
     Lw_L(a_L(\gamma))\,\Phi(a_L(\gamma)).
\]
Every zero is counted with its multiplicity. Finite regrouping gives
\[
\boxed{
\mathcal S_{L,T}(\Phi)
 =\sum_{a=1}^Lw_L(a)q_{L,T}(a)\Phi(a).
}
\tag{4.1}
\]
The weight is **L times the complete Q cell mass**. An unweighted sample approaches the uniform residue average, which is generally a different inner product.

If (3.2) holds at this fixed L, then finite summation implies
\[
\mathcal S_{L,T}(\Phi)
 \longrightarrow\sum_{a=1}^Lw_L(a)\Phi(a).
\]
With \(\Phi=FG\), this limit is exactly \(\langle F,G\rangle_Q\) by (2.1). In particular,
\[
\mathcal S_{L,T}(|1-F|^2)
 \longrightarrow\|1-F\|_Q^2
\qquad(F\in V_L).
\]

At finite T, \(\mathcal S_{L,T}(1)\) need not equal one. The construction uses a positive quadratic form, not an exactly normalized empirical probability law. Renormalizing by its total sampled weight is a different finite formula and requires its own comparison.

Generic version: for c cells, target masses w(a), finite sample s, and cell map A, the correct weight is c w(a). Uniform frequencies \(\operatorname{freq}_s(a)\to1/c\) recover \(\sum_a w(a)\Phi(a)\).

## 5. Relative cell control is uniform over the whole stage

Suppose
\[
0\le\delta<1,
\qquad
\max_{1\le a\le L}|q_{L,T}(a)-1|\le\delta.
\tag{5.1}
\]
For vectors on these cells define
\[
B(f,g)=\sum_a w_L(a)f(a)g(a),\qquad E(f)=B(f,f),
\]
\[
\widehat B(f,g)=\sum_a w_L(a)q_{L,T}(a)f(a)g(a),
\qquad\widehat E(f)=\widehat B(f,f).
\]
Then, simultaneously for every f,
\[
\boxed{
(1-\delta)E(f)\le\widehat E(f)\le(1+\delta)E(f).
}
\tag{5.2}
\]
The exact signed perturbation is
\[
\widehat B(f,g)-B(f,g)
 =\sum_a w_L(a)(q_{L,T}(a)-1)f(a)g(a).
\]
Weighted Cauchy--Schwarz gives
\[
\boxed{
|\widehat B(f,g)-B(f,g)|^2
 \le\delta^2 E(f)E(g).
}
\tag{5.3}
\]
The estimates have no coefficient-size hypothesis and hold uniformly over all cell vectors. Consequently they cover an optimizer selected after the sample is observed. This is stronger than pointwise convergence for a preselected finite list of test functions.

The relevant discrepancy is **relative**:
\[
\delta=L\max_a|\nu_{L,T}(a)-1/L|.
\]
An absolute cell-frequency error must therefore be multiplied by L. Also, \(\delta<1\) forces every cell to occur; hence \(N(T)\ge L\). These facts matter for effective computation even though they do not obstruct qualitative fixed-stage convergence.

## 6. Quadratic optimizer-displacement estimate

Work in one fixed common finite linear trial space V of periodic vectors, with target y. Let
\[
p=\operatorname*{argmin}_{v\in V}E(y-v),\qquad
\widehat p=\operatorname*{argmin}_{v\in V}\widehat E(y-v).
\]
Under (5.1), both forms are positive definite on physical cell vectors, so these minimizers exist and are unique. More generally the following calculation needs only the two indicated normal equations.

Put
\[
r=y-p,\quad z=\widehat p-p,\quad
D=E(r),\quad X=E(z).
\]
The true and sampled normal equations yield
\[
B(r,z)=0,\qquad \widehat B(r-z,z)=0.
\]
Thus
\[
E(r-z)=D+X,
\qquad
X=\widehat B(r-z,z)-B(r-z,z).
\tag{6.1}
\]
Apply (5.3) to \(r-z\) and z:
\[
X^2\le\delta^2(D+X)X.
\]
If X=0 the conclusion is immediate; otherwise divide by X. Therefore
\[
\boxed{
(1-\delta^2)X\le\delta^2D,
\qquad
X\le\frac{\delta^2}{1-\delta^2}D.
}
\tag{6.2}
\]
In particular,
\[
\boxed{
E(y-\widehat p)=D+X
 \le\frac{D}{1-\delta^2}.
}
\tag{6.3}
\]
The squared displacement is quadratic in the relative metric error. This improves the estimate obtained from competitor inequalities alone.

The sampled minimum \(\widehat D=\widehat E(y-\widehat p)\) also obeys
\[
\boxed{
(1-\delta)D\le\widehat D\le(1+\delta)D.
}
\tag{6.4}
\]
This last comparison uses only two-way minimization and (5.2), and therefore applies to a common affine feasible family as well.

For y=1 and V=V_L, E is the actual complete Q norm and \(D=D_L=\|1-P_{V_L}1\|_Q^2\). Since the zero trial is available, \(0\le D_L\le1\).

## 7. Slow diagonals: existence does not provide heights

Let \(L_M\) be an exhaustive squarefree primorial sequence and assume (3.2) for each fixed M. Choose any prescribed positive tolerances \(\delta_M\to0\) with \(\delta_M<1\).

At each M there are finitely many cells. Thus pointwise convergence over those cells supplies a threshold \(T_M\) beyond which
\[
\max_a|L_M\nu_{L_M,T}(a)-1|\le\delta_M.
\]
The thresholds can be enlarged so that \(T_M\to\infty\) and are strictly increasing. This is a diagonal choice; no uniform theorem in M is being silently used.

One may instead keep stage M fixed until the required threshold is reached and obtain a stage function \(M(T)\to\infty\) that grows as slowly as needed. This proves existence of a sufficiently slow schedule. It does **not** establish an explicit useful rate, nor authorize an arbitrary previously chosen fast schedule such as \(M(T)=\lfloor\log T\rfloor\).

With \(p_M=P_{V_{L_M}}1\) and sampled optimizer \(\widehat p_M\),
\[
\|\widehat p_M-p_M\|_Q^2
 \le\frac{\delta_M^2}{1-\delta_M^2}D_{L_M}\longrightarrow0.
\]
Consequently, if \(p_M\to h=P_H1\), then \(\widehat p_M\to h\), and both sampled minima and true errors approach
\[
D_\infty=\|1-h\|_Q^2.
\]
This limit need not have been proved zero. The diagonal faithfully approximates the same unknown limiting projection.

## 8. Analytic provenance and what is still missing in Lean

Ford--Zaharescu [1, Introduction] records unconditional one-dimensional equidistribution of \(\{\alpha\gamma\}\) for fixed nonzero \(\alpha\). For distinct primes, unique factorization makes every nontrivial integer combination of their logarithms nonzero. Applying the one-dimensional statement to each torus character, then Weyl's criterion and the null-boundary box criterion, gives (3.2). This is a mathematical deduction from the classical result.

Ford--Meng--Zaharescu [2, Theorem 1 and Corollary 1.1] supplies a stronger smooth-test simultaneous discrepancy result; prime-log frequencies fit its full-rank case. Its smooth-test hypothesis is not the discontinuous bin-indicator statement. A separate approximation or boundary argument is needed before invoking it for bins. The leading \(N(T)^{-1}\)-normalized equidistribution needed here should not be confused with the finer \(T^{-1}\)-normalized secondary bias.

The new finite-cell algebra does not supply either analytic route. A complete unconditional Lean chain still needs an actual zero-ordinate provider and the torus-to-box convergence step. The exact floor-bin/CRT identification and positive-residue reindexing are formalized in `Analysis/PrimePhaseCRTCells.lean`. The existing declaration `ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson_of_selberg` is in `Analysis/ActualPrimeTorusFMZContinuous.lean`; the density interface is in `Analysis/ActualZeroSelbergDensity.lean`. The older `UniformSelbergDensity (1/4)` dependency is open **in the repository's formal chain**, not a claim that the classical density theorem is mathematically unknown. This centered second-order consumer has a smooth Fourier-decay requirement; it should not be applied directly to bin indicators.

No assumption about GUE, pair correlation, simplicity, or statistical independence of consecutive zeros is required for this fixed-stage sampling interface.

## 9. Independence caution

Uniform limiting phase cells are an artificial coding used to sample finite residue representatives. They do not assert that the physical residues of an integer N drawn from Q are independent across primes.

Likewise, independence of the arithmetic valuations \(v_p(N)\) under the Zipf-2 law is a different product-law statement. The phase bins \(b_p(\gamma)\), residue coordinates \(N\bmod p\), and valuations \(v_p(N)\) must not be identified. The complete weights \(w_L\) are what restore the actual Q geometry after phase sampling.

## 10. Coordinated research agenda toward RH

### A. Finish the actual analytic provider

The cleanest initial target is normalized fixed-character decay for the actual zero family, with multiplicities, followed by finite-dimensional Weyl equidistribution. It may avoid formalizing the strongest secondary-bias version of FMZ. If the older FMZ path is used, discharge its exact density and exponential-sum hypotheses instead of hiding them in an abstract parameter.

Success criterion: a theorem about the actual zeta zeros yielding the actual phase-bin frequencies, with all substantial assumptions visible.

### B. Connect boxes, bins, CRT, and physical representatives

The finite floor-bin CRT construction and positive-residue convention are now formalized. Complete the measure-theoretic passage from continuous torus tests to these bins, preserving boundary conventions and zero multiplicities. The complete-Q assembly is `weighted_primePhase_inner_tendsto`; discharge its explicit `hcell` input for the actual zero family.

Success criterion: the limit of the actual weighted zero sample is exactly the full Q Gram form, including constants and residuals.

### C. Separate qualitative selection from effective computation

The finite simultaneous bound and strictly increasing diagonal selection from fixed-stage convergence are formalized in `Analysis/FiniteSamplingDiagonal.lean`. Quantitative heights require a separate discrepancy estimate uniform over the chosen growing prime set and its bins. Record dependence on L, number of primes, test complexity, and the requested relative tolerance.

Success criterion: first a valid existence theorem; only then an explicit height schedule if supported.

### D. Use sampling to certify signed gains, not merely to restate minima

Let r be an actual Q residual and z a nonzero legal innovation screened against the old trial space. The gain is
\[
G=\frac{|\langle r,z\rangle_Q|^2}{\|z\|_Q^2}.
\]
For a common periodic realization, (5.3) controls the error in its sampled signed source. A sample can certify a gain only when that source exceeds the rigorous perturbation allowance. If a sampled optimizer replaces the true residual, its displacement must also be included using (6.2).

The essential open estimate remains a quantitative cofinal accumulation of **actual complete legal gains**, or another independent estimate forcing \(D_\infty=0\). New prime, composite-divisor, and CRT carry directions should be treated in their full signed block Gram geometry.

### E. Combine with the rational-minimizer and metric-refinement route

The same finite sampling theorem applies to the rational weights
\[
u_L(a)=a^{-2}+\frac{2}{L(2a+L)}
\]
by using the sample multiplier `L u_L(a)`. This is an objective with its stated complete finite weights; it is not a probability normalization. Preserve the exact signed objective and all cross terms.

When the period changes, use the existing metric-refinement identities to distinguish a refund caused by weight refinement from improvement caused by genuinely new legal directions. A lower bound on actual new-space gain remains the arithmetic task. The zero-sampling framework can certify the same signed forms if relative sampling errors are controlled.

### F. Preserve the RH boundary

By (6.4), accurately sampled minima tend to zero exactly when the original minima do. That is useful stability, not a new unconditional proof of their vanishing. Any proposed breakthrough must identify the independent arithmetic inequality that changes this status.

## 11. Module and declaration map

The saved-module check covers the following declarations. The final checkpoint additionally validates the aggregate project and changed modules before publication.

| Component | Intended owner / declarations | Present status |
|---|---|---|
| Finite sample regrouping and weighted limits | `Analysis/FiniteCellSampling.lean`; `weighted_sampleMean_eq`, `weighted_sampleMean_tendsto` | Saved-module checked |
| Relative forms and optimizer perturbations | `Analysis/FiniteWeightedSampling.lean`; `sampled_energy_comparison`, `sampled_form_sub_sq_le`, `optimizer_displacement_le`, `sampled_optimizer_true_error_le`, `sampled_minimum_comparison` | Saved-module checked |
| Complete periodic Q bridge | `RH/QZeroPhaseSampling.lean`; `qInner_eq_periodic_weights`, `weighted_inner_sample_exact`, `weighted_inner_sample_tendsto` | Saved-module checked |
| Fixed-stage-to-diagonal selection | `Analysis/FiniteSamplingDiagonal.lean` | Saved-module checked |
| Actual floor/CRT coding and Q assembly | `Analysis/PrimePhaseCRTCells.lean`, `RH/QPrimePhaseSampling.lean` | Saved-module checked; frequency hypothesis explicit |
| Conditional sampled-error-to-RH consumer | `RH/QZeroPhaseSamplingRH.lean`; `riemannHypothesis_of_weighted_sampled_error` | Saved-module checked; legality, discrepancy and vanishing-error inputs explicit |
| Actual zeta joint bin frequency convergence | Actual zero analytic layer plus box/bin/CRT bridge | Not supplied by this continuation |
| Independent cofinal legal gain or strict-budget estimate | Existing RH arithmetic program | Open |

A successful generic theorem verifies its conditional implication. It does not verify the actual zero-family hypothesis until that hypothesis is separately supplied. Final reporting must list the exact module checks, axiom audit if performed, checkpoint result, and commit without treating a queued job as a success.

## References

[1] Kevin Ford and Alexandru Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, J. reine angew. Math. **579** (2005), 145--158. Introduction for unconditional normalized equidistribution; Theorem 1 for the finer smooth-test bias. <https://arxiv.org/abs/math/0405459>.

[2] Kevin Ford, Xianchang Meng, and Alexandru Zaharescu, *Simultaneous distribution of fractional parts of Riemann zeta zeros*, Bull. London Math. Soc. **49** (2017), no. 1, 1--9. Theorem 1 and Corollary 1.1. <https://arxiv.org/abs/1511.06814>.

These references support the analytic background. The finite importance-weighted metric identities and optimizer estimates are elementary derivations spelled out in this memorandum; no novelty claim is made.


## 12. Link to the floor-logarithm / valuation question

See `PrimeLogValuationResearch20261021.md` for the exact divisor/Möbius bridge between `Nat.log p n` and `n.factorization p`. It suggests using independent valuation coordinates to calculate signed transforms, while retaining the separate complete-Q norm and squarefree-legality obligations. Neither sampling nor finite inversion supplies those obligations automatically.
