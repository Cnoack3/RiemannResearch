# Legal tail capacity under dilation

Write \(S_K=V\cap\ker H_K\), \(t_K=\mathbf 1_{\{j>K\}}\), \(v_K=P_{S_K}t_K\), \(q_K=\|v_K\|^2\), and \(C_K=(K+1)q_K\). Here \(H_K\) records the first \(K\) positive physical sites. Let \(C_*=\sup_K C_K\).

## Lean declarations

| Result | Owning declaration |
| --- | --- |
| Inclusion of the dilated legal space | `legalHeadKernel_dilation` |
| Orthogonality of the new component to every vector in the old dilated space | `legalTailMean_dilation_orthogonal` |
| Exact capacity increment, legal-test lower bound, and exact common-multiple comparison | `normalizedLegalTailMeanCapacity_gain`, `legalTailMean_gain_test`, `normalizedLegalTailMeanCapacity_two_lift_gain` |
| Divisibility monotonicity and factorial convergence to the full supremum | `normalizedLegalTailMeanCapacity_mono_of_dvd`, `normalizedLegalTailMeanCapacity_factorial_mono`, `normalizedLegalTailMeanCapacity_factorial_tendsto` |
| Antitonicity of the raw capacity, the rounding estimate, and ordinary convergence | `legalTailMeanCapacity_antitone`, `normalizedLegalTailMeanCapacity_rounding`, `normalizedLegalTailMeanCapacity_tendsto` |
| Base capacity and its exact relation to the screened bilinear defect | `normalizedLegalTailMeanCapacity_zero`, `normalizedLegalTailMeanCapacity_zero_mul_defect` |
| RH at any fixed stage or at the supremum, and a conditional contraction criterion | `normalizedLegalTailMeanCapacity_eq_one_iff_RH`, `normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH`, `riemannHypothesis_of_tailCapacity_relative_gain` |
| Complete squared norm under the scaled reciprocal-cell map, anchored rational generators, and the converse for finite legal fits | `scaled_reciprocalFloor_norm_sq`, `realGenerator_eq_neg_divisorAnchor`, `rational_residue_pair_mem_legalHeadKernel`, `rational_residue_pair_scaled_mean`, `legal_zero_head_exists_nyman_mesh` |
| Uniform conjugate-zero obstruction for a nonreal right zero | `legalTailMeanCapacity_conjugate_zero_gap` |
| Finite distinct-zero product obstruction at every stage and at the stage supremum | `legalTailMeanCapacity_finite_zero_product_gap`, `normalizedLegalTailMeanCapacity_iSup_le_finite_zero_product` |

[Capacity and dilation](RH/LegalTailMeanCapacityDilation.lean) · [Nyman mesh](RH/LegalTailNymanMesh.lean) · [Conjugate-zero bound](RH/LegalTailMeanCapacityConjugate.lean) · [Finite zero-product bound](RH/LegalTailMeanCapacityZeroProduct.lean)

## What coprime directions measure

If \(L+1=m(K+1)\), put \(b=m^{-1}D_m v_K\). Pairing \(b\) against \(D_m x\) for \(x\in S_K\) gives the mean of \(D_m x\). Thus \(v_L-b\) belongs to \(S_L\) and is orthogonal to the full image \(D_m S_K\). The exact gain is
\[
 C_L-C_K=(L+1)\|v_L-b\|^2.
\]
For any legal test \(y\in S_L\), its squared mean discrepancy satisfies
\[
 (L+1)|\langle\mathbf 1,y\rangle-\langle b,y\rangle|^2
       \le (C_L-C_K)\|y\|^2 .
\]
If \(J+1\) also divides \(L+1\), let \(b'\) be the lift from \(J\). The parallelogram identity gives
\[
 C_L-\frac{C_K+C_J}{2}
  =(L+1)\left(\left\|v_L-\frac{b+b'}2\right\|^2+
                      \frac14\|b-b'\|^2\right).
\]
For coprime \(K+1,J+1\) the product is their least common multiple. An actual discrepancy gives a strict gain above equal parent capacities. Two orders of dilation from the same ancestor transport the same vector. The project already proves the composition law for the Hilbert dilation.

For the sharp two-dimensional comparison, scale \(b,b',t_L\) by \(\sqrt{L+1}\) to obtain \(A,B,T\). Set \(a=C_K\), \(b_0=C_J\), and \(h=\langle A,B\rangle\). Then \(\langle T,A\rangle=a=\|A\|^2\) and \(\langle T,B\rangle=b_0=\|B\|^2\). With \(a b_0>h^2\), orthogonalizing \(B\) against \(A\) gives this exact gain **on the two-dimensional span**, and therefore a lower bound for \(C_L-C_K\):
\[
 \frac{(b_0-h)^2}{b_0-h^2/a}.
\]
Wolfram Language gives the same expression from the inverse of the symbolic \(2\times 2\) Gram matrix. At determinant zero, \(B=cA\) implies \(ca=c^2a=b_0>0\), hence \(c=1\). The scalar inverse-Gram evaluation is supplementary symbolic work.

To prove ordinary convergence, round \(N+1\) up to a multiple \(b\) of \(K+1\). Since \(b\le N+K+1\), antitonicity of \(q\) gives \(C_K\le bq_N\le C_N+K/(N+1)\). Let \(N\) tend to infinity with \(K\) fixed. The bound applies at every index.

## Endpoint and the screened bilinear form

At stage zero, \(S_0=V\) and \(C_0=1-E\). For the screened mean-one section \(u\), the new base identity reads
\[
 C_0\bigl(1+\operatorname{defectForm}(u,u)\bigr)=1.
\]
The rank-one factorization gives \(\operatorname{defectForm}(u,u)=\|u-\mathbf1\|^2\). The categorical converse implies \(E=0\) under RH. The lower bound \(1-E\le C_K\) then forces \(C_K=1\) for every \(K\). The existing Mellin obstruction gives the implication back to RH even if just one stage attains one. In particular an unconditional proof of strict gain at a prescribed pair of stages would imply the negation of RH.

**Open.** Produce explicit arithmetic legal directions whose discrepancies give a uniform positive fraction of the **remaining** deficit whenever it is positive, or prove another estimate forcing that deficit to vanish. The contraction criterion has a domain-specific gain hypothesis. A positive sequence of gains may have a sum smaller than the initial deficit. The rank-one form evaluates the missing coefficient and the centered snake identifies its vanishing. Neither identity sets its value to zero. [Bilinear form](RH/MixedConductorBilinear.lean) · [Centered unit](RH/CenteredMeanSquarefreeConverse.lean)

A model explains why the projection and dilation laws cannot by themselves furnish the missing estimate. In \(L^2(0,1)\), fix \(1/2<\sigma<1\) and impose the single legal constraint \(V=(x^{\sigma-1})^\perp\). Use \(D_m f(x)=m\mathbf 1_{\{x\le1/m\}} f(mx)\), the usual mean, and the tail \(\mathbf1_{(0,1/N]}\) at denominator \(N\). This closed space is invariant under every \(D_m\). The optimal tail vector is
\[
 \mathbf1_{(0,1/N]}(x)\left[1-\frac{2\sigma-1}{\sigma}(Nx)^{\sigma-1}\right].
\]
Indeed it pairs to zero with the restricted constraint and differs from the tail by a multiple of that constraint on its support. Substitution \(y=Nx\) gives \(C_{N-1}=(1-\sigma)^2/\sigma^2<1\) at every scale. All transported optimizers agree, including along coprime directions. The legal mean has a one-dimensional complement to its kernel. This is an exact Hilbert-space counterexample to a purely geometric relative-gain argument. The project's arithmetic legal space must supply the additional input.

## Finite distinct-zero product obstruction in Lean

For a finite type \\(ι\\) and an injective family \\(z:ι\\to\\mathbb C\\) with \\(\\Re z_i>1/2\\), \\(z_i\\ne1\\), and \\(\\zeta(z_i)=0\\), the new theorem proves at every stage
\\[
 C_K\\le\\prod_{i\\inι}\\left|\\frac{z_i-1}{z_i}\\right|^2.
\\]
The proof rescales the complete inverse-Cauchy Mellin kernel to the physical tail. Pointwise cancellation preserves its optimized charge, change of variables multiplies its energy by \\(K+1\\), and the zero physical head localizes Cauchy--Schwarz. No diagonal approximation or numerical Gram solve is used.

This is stronger than the single-zero and conjugate-pair bounds, but it is not Burnol's projection equality. Injectivity records each distinct zero once. Burnol's scalar product counts analytic multiplicity, so repeated-zero factors require confluent Cauchy kernels carrying Mellin derivative jets. The continuous endpoint also still requires a formal proof that the factorial union of the transported legal spans closes to the real Nyman space.

## Continuous endpoint derived using published analysis

The following proof relates this particular discrete limit to Burnol's continuous projection formula. The scaled norm, the finite dictionary and the uniform two-zero inequality are addressed by the Lean modules above. The identification of the closed spans below and the application of Burnol's continuous projection theorem are paper-level steps.

For \(m=K+1\), define \(J_m f(t)=f(\lfloor m/t\rfloor)\) on \(0<t\le1\) using the physical sequence. The cell indexed by \(j\ge m\) has length \(m/[j(j+1)]\). Thus \(J_m\) multiplies squares of norms on zero-head vectors by \(m\), and \(J_m t_{m-1}=1\). The image \(W_m=J_m S_{m-1}\) is closed and \(C_{m-1}=\|P_{W_m}1\|^2\). For \(m\mid n\), composing the physical dilation by \(n/m\) and dividing by the same factor yields \(W_m\subset W_n\).

Put \(r_d(j)=(j\bmod d)/d\) and \(g_\alpha(t)=\{\alpha/t\}-\alpha\{1/t\}\). For \(d\ge m\) the finite legal trial \(r_d-(m/d)r_m\) has head zero. Its image is exactly \(g_{m/d}\), and its scaled mean is \((m/d)\log(d/m)\). Thus the legal-test inequality has an explicit logarithmic term for this family. Its inner product with the transported projection is the remaining unknown in the score. Conversely the repo's anchored divisor reconstruction expresses every finite legal zero-head combination at \(m>1\) as a sum of these trials. At \(m=1\), \(r_1=0\) and the same conclusion follows directly from the residue dictionary. Finite legal approximants with the prescribed head are dense in \(S_{m-1}\) by finite head repair. Equivalently, the head map has finite-dimensional range and a bounded section with values in the finite legal span, which corrects convergent approximants with a correction tending to zero. We get the real closed-span identity
\[
 W_m=\overline{\operatorname{span}_{\mathbb R}}\{g_{m/d}:d>m\}.
\]
[Exact head repair](RH/ParetoFiniteHeadRepair.lean) · [Finite reconstruction](RH/MultiRangeCompleteness.lean)

For any rational \(a/b\in(0,1)\), choose a factorial \(m\) divisible by \(a\), then \(d=mb/a\) is an integer larger than \(m\). For \(\alpha_j\to\alpha\) in \((0,1)\), \(g_{\alpha_j}(t)\to g_\alpha(t)\) off the countable discontinuity set \(\{\alpha/k:k\ge1\}\). The functions are uniformly bounded, so convergence holds in \(L^2\). The closure of the factorial union is therefore the continuous real Nyman space. Approximation of a real target by complex combinations has the same infimum of squared errors, by taking real parts. The nested-space distance formula and Burnol's Theorem 1.2 give
\[
 C_*=\prod_{\zeta(\rho)=0,\ \Re\rho>1/2}
       \left|\frac{1-\rho}{\rho}\right|^{2m_\rho},
\]
where the product runs over distinct zeros and \(m_\rho\) is the multiplicity. The repo proves convergence and positivity for the scalar product. Burnol's projection theorem supplies the identification with the continuous squared norm. [Burnol, Theorem 1.2](https://arxiv.org/abs/math/9910055) · [Scalar product in Lean](RH/BurnolZeroProductConvergence.lean) · [Continuous projection obligations](RH/BurnolProjectionConsequences.lean)

A noncircular quantitative consequence follows from the published verification height \(T=3\cdot10^{12}\). Write \(d_\rho=(2\Re\rho-1)/|\rho|^2\), so each individual squared factor is \(1-d_\rho\). The off-line zeros have \(|\Im\rho|>T\), and \(d_\rho\le|\Im\rho|^{-2}\). The finite-product bound \(1-\prod(1-d_\rho)\le\sum d_\rho\) passes to the limit. Counting multiplicities, \(N(t)\le t\log t\) for \(t\ge T\) follows directly from Corollary 1.2 of Hasanalizade, Shen and Wong. Counting positive and negative ordinates and integrating by parts gives
\[
 0\le 1-C_*
 \le 2\int_{(T,\infty)} t^{-2}\,dN(t)
 \le 4\int_T^\infty \frac{\log t}{t^2}\,dt
 =\frac{4(1+\log T)}{T}.
\]
This fixed positive error bound uses external theorems and the paper-level transfer. Proving saturation still requires excluding all right zeros beyond the certified height, or a separate arithmetic approximation theorem. [Platt and Trudgian](https://arxiv.org/abs/2004.09765) · [Hasanalizade, Shen and Wong, Corollary 1.2](https://arxiv.org/abs/2107.06506)
## Factorial rational-mesh closure (2026-11-28)

The continuous Nyman module now contains the exact cofinal parameter theorem.
The set of ratios `(n + 1)! / d` with `d > (n + 1)!`, over all `n`, is
exactly the rational subset of `(0,1)`. Consequently its generator closed
span equals Burnol's full continuous Nyman space.

| Result | Owning declaration |
| --- | --- |
| Factorial mesh parameters equal all rational parameters in `(0,1)` | `factorialMeshParameters_eq_rationalParameters` |
| Factorial rational-mesh closed span equals the continuous Nyman space | `factorialMeshClosedSpace_eq_closedSpace` |

[Continuous Nyman space](RH/NymanContinuousSpace.lean)

The completed-stage identification and scalar comparison are now proved.

## Physical and rescaled limits, 2026-11-28

| Result | Owning declaration |
| --- | --- |
| Compact weak-* ball, exact test-error bound, boundary atom, and vanishing criterion | `physicalTailEnergy_weakStar_compact`, `physicalTailEnergy_test_error`, `physicalTailEnergy_weakStar_tendsto`, `physicalTailEnergy_weakStar_zero_iff_RH` |
| Coefficients on the physical triangular hat mesh | `physicalTailEnergy_hat_vanish`, `physicalTailEnergy_first_hat_pair`, `physicalTailEnergy_first_interior_hat_bound` |
| Finite triangular rational rows with simultaneous legal realizations | `triangularMeshRow_subset_factorial`, `triangularMeshRow_legal_witness`, `iUnion_triangularMeshRow_eq_rational` |
| Ambient reciprocal-cell isometry, completed legal range, stage projection norm | `reciprocalCellIsometry`, `legalCellIsometry_range`, `normalizedLegalTailMeanCapacity_eq_realMeshProjection` |
| Exact strong error and common-coordinate residual density estimate | `commonTailOptimizer_gain`, `commonTailOptimizer_strong_limit`, `commonTailResidual_energy_variation` |
| Capacity supremum as the projection energy of one in the full complex Nyman space | `normalizedLegalTailMeanCapacity_iSup_eq_nymanProjection` |
| Actual block averages, residue cancellations, and signed dyadic correlation | `tailBlockResidual_coordinate`, `tailBlockResidual_residue_cancellation`, `tailBlockResidual_first_identity` |
| Linear and quadratic overshoot floors, effective finite witness, and the fixed-window criterion | `tailBlockOvershoot_linear_lower`, `tailBlockOvershoot_quadratic_lower`, `tailBlockOvershoot_exists_block`, `fixedBlock_liminf_zero_iff_RH` |
| Exact two-generator trial energy available at every scale | `twoGeneratorMesh_energy`, `twoGeneratorMesh_le_normalizedCapacity` |

The weak-* atom has mass \(1-C_*\). Proving its vanishing still requires
arithmetic input. Burnol's zero-product evaluation of the continuous
projection norm remains a separate analytic obligation in Lean.

## Gaussian repulsion and fixed windows

| Result | Owning declaration |
| --- | --- |
| Exact split of the horizontal diagonal and multiplicity-sensitive reflection bound | `actualCollision_eq_rootDiagonal_add`, `reflected_pair_le_distinctRootCollision` |
| Full Gaussian mass on distinct complex roots and the quarter-pair reconstruction error | `distinctRootGaussianMass_eq_sum`, `reconstructedDistinctRoot_quarter_error` |
| Prescribed bandwidth, signed Landau integral, and exact integer recovery | `distinctRootGaussianPrecision_bounds`, `calibratedSineRootExcess_eq_landau_integral`, `calibratedSineRootExcess_round` |
| Equivalence to every fixed legal window and the paired obstruction from one right zero | `fixedBlock_liminf_zero_iff_calibrated_sine_excess`, `right_zero_forces_fixed_block_and_sine_excess` |

The remaining comparison is \(S_T<1\) at cofinal heights in absolute ordered
pairs. The finite tests permit arbitrary analytic multiplicity on the line.
