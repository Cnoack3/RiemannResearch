# Comparison of d66e444 and 1235e6b, with verified connecting theorems

Date: 24 September 2026. Baseline: 1235e6b319068f361f315257fb84ade8873652a7.

## Conclusion

Both commits give unconditional progress, but at different levels. The new mathematics in d66e444 is a scalar mean-point refinement. The new mathematics in 1235e6b is a quantitative complete-energy estimate and an actual uniform moving-Hardy theorem. Neither establishes RH, coefficient convergence to Möbius coefficients, or vanishing critical approximation error.

The useful connection is full signed energy comparison and constrained optimization. A uniform absolute bound on the growing Gram inverse is unnecessary for this comparison. It remains necessary to obtain a substantive arithmetic improvement in the optimized tail energy, or to exploit the exact weight defect, before the current limiting Hardy boundary can move from 1 to 1/2.

The new modules in this continuation establish:
- A residue-independent fourth-power mean-point bound.
- Actual untruncated midpoint-residual energy comparison and Hardy transfer.
- Quantitative signed-covariance capacity, an exact weighted-energy identity for the attained optimizer, and its unconditional moving-Hardy bound.

These are independently derived formal consequences of the cited repository results; no mathematical novelty claim is made.

## 1. What d66e444 actually adds

Write K=trigamma(1), a positive real number, and
\[
e(r,L)=L\alpha_{r,L}-\sqrt{r(r+1)}.
\]
For every real r,L>0, the new scalar theorems prove
\[
0\le (L\alpha_{r,L})^2-r(r+1)
 \le \frac{K r(r+1)^3}{L^3},
\qquad
0\le e(r,L)\le
 \frac{K r(r+1)^3}{2\sqrt{r(r+1)}L^3}.
\]
The extra inverse power of L comes from cancellation of the common shifted reciprocal-series tails. The previous quadratic bound and fixed-r convergence were already present.

The changes to ProgressionMidpointInverse.lean in this commit are formatting, not new inverse theorems. Inherited results already prove, for arbitrary finite dimensions and arbitrary signed rows,
\[
(1-\delta_Q)G\preceq M\preceq G,\qquad
(1-\delta_Q)b^\top M^{-1}b
 \le b^\top G^{-1}b\le b^\top M^{-1}b,
\quad \delta_Q=(2Q+3)^{-2},
\]
when the exact Gram is positive definite. The occupation-probability error is at most delta_Q, even for arbitrarily growing dictionary dimensions.

Thus the missing ingredient is not relative inverse stability. Absolute inverse size, saturation, and the actual Möbius correction coefficients are different questions.

Sources:
- [Commit d66e444](https://github.com/Cnoack3/RiemannResearch/commit/d66e444)
- [Mean points](CRTTrigammaMeanValue.lean)
- [Existing inverse comparison](ProgressionMidpointInverse.lean)
- [Existing complete-energy and minimum comparisons](ParetoProgressionMidpoint.lean)

## 2. What 1235e6b actually adds

Let F_N be canonicalMobiusHilbert N, b=N+1, and r_N=1-F_N. Define
\[
E_u(f)=\int_1^\infty |f(\lfloor x\rfloor)|^2 x^{-u-1}\,dx.
\]
Then E_1(f) is the complete squared Pareto norm.

One unconditional constant C>=0 controls the simultaneous finite-cutoff bound
\[
\frac{\|F_N\|_P^2}{N}
 \le\frac3N+2K D_{N,K,J}^2+\frac4K,
\quad
D_{N,K,J}=\frac1J+\frac1{NJ}
+\frac{C(H_K+H_J+2)}{\log N},
\]
eventually in N, for every K>=2 and J>=1. All tails remain included.

Put
\[
x_N=\frac{1+\log(\log N+3)}{\log N},\quad A=2+4C,
\quad
B_C(N)=\frac3N+(4+2A^2)x_N+4A^2x_N^2.
\]
The optimized theorem proves ||F_N||_P^2/N<=B_C(N) eventually and B_C(N)->0.

With
\[
q_C(N)=2B_C(N)+\frac3N,\qquad
\beta_N=1+\frac{\log q_C(N)}{4\log(N+1)},
\]
it proves, eventually,
\[
\beta_N<1,\quad \beta_N\longrightarrow1,\qquad
\forall\sigma>\beta_N,\quad
\int_{\mathbb R}|\mathcal M r_N(\sigma+2\pi it)|^2dt
\le\sqrt{q_C(N)}\longrightarrow0.
\]
This is genuine uniform convergence on moving half-planes. A fixed line sigma<1 eventually lies outside these half-planes; the theorem therefore establishes no fixed new zero-free half-plane inside the critical strip.

The exact identity retained in the commit is
\[
E_u(F_N)=\frac{1-b^{-u}}u
+b^{1-u}\left(E_1(F_N)-1+\frac1b\right)
-\Delta_{b,u}(F_N),\quad u\ge1,
\]
where
\[
\Delta_{b,u}(f)=
\int_b^\infty |f(\lfloor x\rfloor)|^2x^{-2}
\left(b^{1-u}-x^{1-u}\right)dx\ge0.
\]

Sources:
- [Commit 1235e6b](https://github.com/Cnoack3/RiemannResearch/commit/1235e6b)
- [Original quantitative handoff](QuantitativeMobiusMovingBoundary20260924.md)
- [Arithmetic source](CanonicalMobiusQuantitativeEnergy.lean)
- [Moving-Hardy source](CanonicalMobiusMovingBoundary.lean)

## 3. New uniform scalar theorem

The new module UniformTrigammaMeanPoint.lean proves
\[
\boxed{\quad e(r,L)^4\le\frac{\operatorname{trigamma}(1)}{512L^3}
\quad(r\ge1,\ L>0).\quad}
\]
The right side is independent of r, so the estimate remains valid for arbitrary growing residues.

Proof mechanism: the arithmetic/geometric mean sandwich gives
\[
e\ge0,\qquad 8\sqrt{r(r+1)}e\le1.
\]
Multiply the cube of the latter estimate by the cubic mean-point estimate:
\[
e^4\le\frac{K(r+1)}{1024rL^3}\le\frac{K}{512L^3}.
\]
This is uniform scalar progress. It does not imply small critical energy or coefficient convergence.

Declaration: progressionAlpha_scaled_error_fourth_uniform.

## 4. New actual midpoint-energy certificate

For a Hilbert vector f, define the complete midpoint energy
\[
E_{\rm mid}(f)=\sum_{n\ge0}
\frac{f(n)^2}{(n+1/2)^2},
\]
where f(n) denotes its anchored physical sequence, so f(0)=0.

The definition and summability are formalized. The exact atom relation is
\[
\frac1{n(n+1)}-\frac1{(n+1/2)^2}
=\frac{1}{n(n+1)(2n+1)^2}\quad(n>0).
\]
If f vanishes at physical coordinates 1,...,N, then
\[
a_N\|f\|_P^2\le E_{\rm mid}(f)\le\|f\|_P^2,
\qquad a_N=1-\frac1{(2N+3)^2},
\]
and
\[
0\le\|f\|_P^2-E_{\rm mid}(f)
\le\frac{\|f\|_P^2}{(2N+3)^2}.
\]

Consequently any candidate residual f with the same zero head and the certificate
E_mid(f)<=E_mid(r_N) satisfies
\[
\|f\|_P^2\le \frac{\|r_N\|_P^2}{a_N}.
\]
For u>=1 and sigma>u/2, this gives
\[
\int_{\mathbb R}|\mathcal M f(\sigma+2\pi it)|^2dt
\le\frac{b^{1-u}\|r_N\|_P^2}{a_N}.
\]
The complete logarithmic theta schedule and convergence along arbitrary admissible moving lines are also formalized.

This is a certificate theorem: it does not assume that a midpoint minimizer has been constructed. Any actual minimizer over a family containing r_N would satisfy its energy-comparison premise. The next section instead uses an optimizer whose existence is already proved in the repository.

This physical midpoint norm approximates every positive atom. The older progression midpoint formula retains each residue's first atom exactly. They are related quadratures, not identical definitions. Both control residual squares before expansion, retaining every signed cross term.

Module: MidpointTailEnergy.lean.
Principal declarations: midpointEnergy_eq_physical, midpointEnergy_zeroHead_error,
midpointEnergy_competitor_scheduled_line_bound,
midpointEnergy_competitor_moving_lines_tendsto.

## 5. Main connecting theorem: actual signed-covariance optimization

Take any finite nonempty family of positive indices k_i>=N containing N. Allow signed coefficients c_i with sum c_i=1. Let A_N be the repository's attained optimizer of the complete tail energy of sum c_i F_{k_i}.

Write K_N for its actual tail covariance and kappa_N for capacity. In Lean, kappa_N=sum z_i where K_N z=1, and independence of the chosen normal solution is proved. This supports the usual interpretation 1^T K_N^dagger 1 without requiring an invertible matrix or a particular pseudoinverse convention.

The existing attainment theorem gives
\[
\|A_N\|_P^2=\frac{N}{N+1}+\kappa_N^{-1}.
\]
The new comparison proves that every retained family member is a valid competitor. Combining with the arithmetic ceiling yields
\[
\boxed{\quad
\frac{N}{N+1}+\kappa_N^{-1}
=\|A_N\|_P^2
\le\|F_N\|_P^2\le N B_C(N).\quad}
\]
In particular,
\[
\boxed{\quad
1\le\left(NB_C(N)-\frac{N}{N+1}\right)\kappa_N.\quad}
\]
The same constant and eventual cutoff work for every such finite family, with no restrictions on the number of indices, their horizon, or covariance condition number.

The new exact identity is
\[
\boxed{\quad
E_u(A_N)=\frac{1-b^{-u}}u+b^{1-u}\kappa_N^{-1}
-\Delta_{b,u}(A_N),\qquad u\ge1.\quad}
\]
The existing formal PNT provider, actual finite optimizer, complete tail, and exact weight defect are now linked in one statement.

For arbitrary growing dictionaries with these finite admissibility conditions, the new theorem also proves
\[
\forall\sigma>\beta_N,\quad
\int_{\mathbb R}|\mathcal M(1-A_N)(\sigma+2\pi it)|^2dt
\le\sqrt{q_C(N)},
\]
eventually, with the same beta_N<1 tending to 1. The optimizer is constructed, not postulated; only ordinary finite-family conditions occur.

Module: CanonicalMobiusCapacityHardy.lean.
Principal declarations:
optimizedAverage_norm_sq_le_member;
capacity_eventual_quantitative_bound;
optimizedAverage_weighted_energy_exact;
optimizedAverage_explicit_moving_hardy.

## 6. Literature check and a constraint on the target

Manzur, Noor and Quintero, "A Hardy space approximation supporting zero-free half-planes for the zeta-function", arXiv:2606.16097v1, Theorem 3.1, proves the raw legal Möbius expansion converges in H^2(C_alpha) for alpha>1. Proposition 3.1 connects closure at alpha>=1/2 to zero-freeness to its right. The repository's already formalized endpoint and moving-bound results should be compared against these precise exponents.

Primary source: https://arxiv.org/html/2606.16097v1

Báez-Duarte, "Arithmetical aspects of Beurling's real variable reformulation of the Riemann hypothesis", arXiv:math/0011254, Propositions 4.4 and 4.6, proves nonconvergence in critical L^2 for the raw legal Möbius sums and the classical corrected family B_m. With
\[
B_m(t)=\sum_{d\le m}\mu(d)\{1/(dt)\}
-m\,m_m\{1/(mt)\},\quad m_m=\sum_{d\le m}\mu(d)/d,
\]
the repository's physical canonical family satisfies
\[
F_N(y)=-B_{N+1}(1/y).
\]
Indeed the added mu(N+1) term cancels using
m_{N+1}=m_N+mu(N+1)/(N+1). Legal balance makes the physical profile a step function.

Thus full-sequence critical convergence of this particular canonical family is not a viable target. This observation does not exclude subsequences, further optimized cutoff-dependent coefficients, uniform boundedness, or the repository's weaker moving-Hardy criterion. The classical nonconvergence theorem and its transfer are literature/mathematical analysis here, not newly formalized in Lean.

Primary source: https://arxiv.org/pdf/math/0011254

Lee and Leong's stronger unconditional Mertens estimates illustrate a possible future arithmetic improvement beyond the repository's inverse-log provider. Improving a logarithmic/subpower saving can enlarge the leftward moving shift, but by the displayed scheduling formula it does not automatically change the limiting boundary to 1/2. No stronger external estimate was silently assumed in these Lean results.

Primary source: https://arxiv.org/html/2208.06141v4

## 7. Exact remaining research obligation

For the actual optimized family, the crude positive tail ceiling at u=1+2alpha is
\[
(N+1)^{-2\alpha}\kappa_N^{-1}.
\]
A common bound with alpha_N->0, or a sufficient quantitative improvement using the retained defect, would bear directly on the RH-strength moving-bound target. The new lower bound on kappa_N does not supply this: its certified reciprocal tail ceiling is still NB_C(N)-N/(N+1).

Relative midpoint stability only transports an energy rate already proved. It cannot turn the present arithmetic rate into the missing one. Compactness alone cannot supply the rate either.

The next substantive arithmetic target is therefore a gain in the actual optimized signed covariance capacity, or a lower estimate for the retained weight defect, with explicit uniformity as the shift tends to the critical value. Any claim that a fixed positive capacity is obtained must be checked against the existing RH implication in CanonicalMobiusCovarianceMinimum.lean.

A narrower implementation target is to identify finite CRT tail charts for these actual optimized families, subtracting the head atoms exactly and handling singular covariance. For Q>N and residues 1<=r<=Q, the relevant tail weight is
\[
V_{Q,N}(r)=W_Q(r)-\mathbf1_{r\le N}/[r(r+1)].
\]
The existing remainder estimate also controls the corresponding midpoint weight after the same head subtraction. This is the appropriate finite adapter; merely inserting the full Gram inverse bound into the tail problem would overlook the head subtraction.

## 8. Verification scope

The baseline moving-Hardy and relative inverse theorems were checked in Lean. The new source checks and principal-declaration axiom audits use only propext, Classical.choice and Quot.sound; no admissions or project-local axioms are introduced. Wolfram Language independently simplified the midpoint atom identity, quartic cancellation factor, logarithmic scheduling identity, and cutoff correction algebra exactly. These symbolic checks support algebra; they do not replace Lean verification.

Final publication uses the repository's affected-module checkpoint, including the root export. This is not a claim that every unrelated repository theorem or all external literature was reverified. The published checkpoint result is reported separately with the final commit.
