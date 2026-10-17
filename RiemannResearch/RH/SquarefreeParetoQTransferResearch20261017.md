# Squarefree restriction of the Pareto program and transfer to Q

Research date: 17 October 2026. Base source inspected: [b7e8a604ad5ea71c958b45755f06332b6c4672bf](https://github.com/Cnoack3/RiemannResearch/commit/b7e8a604ad5ea71c958b45755f06332b6c4672bf).

**Status.** Three new Lean modules compile on the user's server. All 29 public theorem axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`; the five private helpers are covered through those public theorem dependencies. The native module/import and axiom-check jobs are recorded in Section 9. The final checkpoint must still validate the exact aggregate project before publication. The record distinguishes the checked geometric theorems from the open arithmetic providers and the external analytic RH-to-squarefree-closure direction.

The existing project already contains a general P/Q transfer layer. This work reuses that layer and supplies the missing restricted-coefficient assembly and squarefree relative-gain statements. The reverse implication from RH to squarefree closure is a classical analytic theorem; it is not newly formalized here.

## 1. The spaces, stages, and main conversion

Put
\[
 Z=\zeta(2),\qquad P(n)=\frac1{n(n+1)},\qquad
 Q(n)=\frac1{Zn^2},\qquad g_d(n)=\frac{n\bmod d}{d},\quad n\ge1.
\]
Let \(\mathcal H_P=L^2(P)\), \(\mathcal H_Q=L^2(Q)\), and, for \(M=P,Q\),
\[
 W_M=\overline{\operatorname{span}\{g_d:d\ge2,\ d\text{ squarefree}\}}^{\,M}.
\]
The algebraic span always consists of finite linear combinations. Its closure uses the entire infinite weighted norm.

For consistency with the existing Lean optimizer, stage n contains the distinct squarefree conductors from 2 through n+1:
\[
 D_n=\{d:2\le d\le n+1,\ d\text{ squarefree}\},\qquad
 V_n^M=\operatorname{span}\{g_d:d\in D_n\}.
\]
Write
\[
 F_n^M=P_{V_n^M}^{M}1,\quad E_n^M=\|1-F_n^M\|_M^2,
 \quad F_\infty^M=P_{W_M}^{M}1,\quad r_M=1-F_\infty^M.
\]
The superscript matters: equivalent norms give the same legal closure as physical functions, while the two orthogonal projections can differ.

The central converted chain is
\[
\begin{aligned}
1\in W_P
&\iff 1\in W_Q
\iff E_n^P\to0
\iff E_n^Q\to0\\
&\iff \forall d\ge2\text{ squarefree},\quad c_{n,d}^P\to-\mu(d)\\
&\iff \forall d\ge2\text{ squarefree},\quad c_{n,d}^Q\to-\mu(d)\\
&\iff K_n^Q\to\infty
\iff \sum_{n\ge0}\alpha_n^Q=\infty.
\end{aligned}                                                     \tag{1}
\]
Here \(c_{n,d}^M\) are actual finite projection coefficients, with zero assigned when an atom is absent, \(K_n^Q\) is the genuine centered inverse-covariance capacity, and \(\alpha_n^Q\) is the actual relative projection gain defined in Section 6.

Classically each condition in (1) is equivalent to RH. The external analytic input for RH implying squarefree membership is Bagchi's Remarks 4 and 8, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733). Those remarks explicitly restrict the approximation to squarefree conductors; the norm comparison then transfers it to Q. In the present formalization, squarefree membership implies Mathlib's RH through the existing Mellin theorem. The external RH-to-membership implication remains a separate formalization obligation.

## 2. Conversion map for the earlier Pareto results

| Earlier result family | Squarefree statement | Transfer to Q and status |
|---|---|---|
| Finite Möbius sums and damped Möbius trials | Terms at nonsquarefree conductors already vanish because \(\mu(d)=0\). Such trials are already squarefree legal. | Keep the identical physical sequence and coefficients; use the Q norm. Extra repair terms must themselves be checked for legality. |
| Exhaustive finite projections | Replace \(\{2,\dots,n+1\}\) by \(D_n\), or use the existing masked dictionary. | Each measure has its own optimizer; both converge strongly to their own closed-span projection. Existing generic projection theorem. |
| Fixed coefficient stabilization | Every squarefree coefficient has an unconditional limit; simultaneous identification with \(-\mu(d)\) is equivalent to \(1\in W_P\). | The same criterion holds for the actual Q coefficients. New checked Lean modules. |
| Normal equations and completed squares | Restrict the finite Gram system to distinct squarefree conductors. | Compute actual Q means, Gram matrices, and covariance. Existing Q inverse-capacity development. |
| Möbius correction formula | \(c=-\mu_D+G^{-1}(b+G\mu_D)\). | Same exact algebra with \(G_Q,b_Q\). The means \(b_P\) and \(b_Q\) are generally different. |
| Schur innovations and additive gains | A nonredundant squarefree enumeration gives positive innovation norms and the usual exact Schur identity. | Native Q projection increments give exact additive and multiplicative criteria. New checked Lean module. |
| Inverse-Gram source forms | All same-source variational comparisons survive on a squarefree finite family. | Existing two-sided Q/P inverse-Gram comparison. Do not replace its common source by different measure-specific means. |
| Exact-head bounded families | Squarefree legal trials with growing exact heads and bounded full norm force constant membership. | Existing Q exact-head and bounded-coordinate closure theorems; the full energy bound remains an arithmetic obligation. |
| Dual/Riesz and inverse-Gram identities | Retain the orthogonal-complement remainder; the squarefree closed span is proper. | Native Q Riesz vectors are changed by the weights. Section 7 gives the corrected limiting targets. |
| Mellin zero obstructions | Every squarefree trial is a legal trial, so the original separating functionals still apply. | Existing QMellinTransfer retains the exact positive metric correction. |
| Orthonormal coordinates and DPP identities | Orthonormalize within the squarefree closed span and retain the ambient residual term. | Rebuild native Q orthogonality and kernels. Existing Q squarefree-coordinate and legal-DPP modules supply this geometry. |
| Dilation and full-space density | General dilation invariance and \(1\in W\iff W=\mathcal H\) do not survive the restriction. | This is an algebraic obstruction, present in both metrics; see Section 7. |
| Full-residual arithmetic tail or spectral estimates | A proof using orthogonality to every conductor requires a new restricted-family argument. | Norm equivalence alone does not identify the P and Q residuals or transfer native self-adjointness. |

Primorial divisor stages may replace \(D_n\) because they exhaust all finite squarefree conductors. Increases in a target conductor alone do not imply exhaustive stages.

## 3. Exact P/Q metric identity

The physical identity
\[
 ZQ(n)=P(n)+\frac{P(n)}n
\]
gives, for the same physical f in the two realizations,
\[
 \boxed{Z\|f\|_Q^2=\|f\|_P^2+R(f)},\qquad
 R(f)=\sum_{n\ge1}\frac{|f(n)|^2}{n^2(n+1)}.                 \tag{2}
\]
No tail has been truncated. In particular,
\[
 \frac1Z\|f\|_P^2\le\|f\|_Q^2\le\frac2Z\|f\|_P^2.       \tag{3}
\]
If f vanishes through H, then
\[
 0\le R(f)\le\frac{\|f\|_P^2}{H+1},\qquad
 \|f\|_P^2\le Z\|f\|_Q^2
 \le\left(1+\frac1{H+1}\right)\|f\|_P^2.                 \tag{4}
\]
The identity map on physical sequences is therefore a continuous linear equivalence. It preserves any prescribed conductor family, arbitrary norm-closure membership, strong convergence, and uniform boundedness. The actual implementation is `QParetoEquivalence.paretoEquiv`, with `toQ` and `toPareto` preserving physical coordinates.

For each finite squarefree stage, minimizing separately in the two metrics gives
\[
 \boxed{E_n^P\le ZE_n^Q\le2E_n^P}.                         \tag{5}
\]
To prove the first inequality, insert the Q optimizer into the P variational problem and apply (3). For the second, insert the P optimizer into the Q problem. The optimizers need not coincide. Existing provider: `QParetoGramComparison.optimizer_error_bounds`.

If \(K_n^M=(1-E_n^M)/E_n^M\), with positive finite errors, (5) also yields the comparison of the actual target capacities
\[
 \boxed{\frac Z2(1+K_n^P)\le1+K_n^Q\le Z(1+K_n^P)}.       \tag{6}
\]
This follows by taking reciprocals in (5), using \(1+K=1/E\). The added ones are essential because the actual target mean vectors differ. Formula (6) is a mathematical consequence recorded here; no separate Lean declaration for it is claimed.

For a finite common family v, polarization of (2) retains the exact signed matrix identity
\[
 ZG_Q=G_P+C,\qquad
 C_{de}=\sum_{n\ge1}\frac{v_d(n)v_e(n)}{n^2(n+1)}.
\]
Thus \(G_P\preceq ZG_Q\preceq2G_P\). For every common source b and genuine invertible Gram matrix,
\[
 \frac Z2 b^T G_P^{-1}b\le b^T G_Q^{-1}b\le Zb^T G_P^{-1}b.
\]

## 4. The squarefree coefficient proof

Anchor f(0)=0 and define, for d>=2,
\[
 \lambda_d(f)=-\sum_{k\mid d}\mu(d/k)\,[f(k)-f(k-1)].        \tag{7}
\]
This is a finite-coordinate continuous functional under either measure. The existing Möbius inversion theory gives
\[
 \lambda_d(g_e)=\mathbf1_{d=e},\qquad
 \lambda_d(1)=-\mu(d).                                    \tag{8}
\]
The full family of functionals separates the ambient Hilbert space: if every \(\lambda_d(f)=0\), divisor inversion makes f(n)=n f(1), and weighted square summability forces f(1)=0.

If d is nonsquarefree, \(\lambda_d\) vanishes on every squarefree atom. Continuity therefore gives
\[
 \lambda_d(f)=0\quad(f\in W_M,\ d\text{ nonsquarefree}).     \tag{9}
\]
This is also the target value because \(\mu(d)=0\).

Define the actual coefficients by
\[
 c_{n,d}^M=\lambda_d(F_n^M),\qquad
 c_{\infty,d}^M=\lambda_d(F_\infty^M).
\]
Biorthogonality makes these the coefficients of the finite synthesis; the Q module explicitly identifies them with the existing genuine inverse-covariance coefficients.

Strong projection convergence and continuity give
\[
 c_{n,d}^M\longrightarrow c_{\infty,d}^M
\]
unconditionally. Their exact limiting correction is
\[
 \boxed{c_{\infty,d}^M=-\mu(d)
   +\sum_{k\mid d}\mu(d/k)\,[r_M(k)-r_M(k-1)]}.             \tag{10}
\]
The residual and correction depend on M.

Suppose every squarefree limiting coefficient is -mu(d). By (10), all squarefree coordinates of r_M vanish. For nonsquarefree d, both the constant and its projected part have zero coordinate by (9), so those coordinates of r_M vanish as well. Separation now gives r_M=0. Conversely r_M=0 immediately identifies every coefficient. This proves the coefficient equivalences in (1).

It also explains why discarded coordinates do not create a hidden extra assumption: their target values and their values throughout the restricted closed span are already zero.

The quantitative stabilization estimate retains the full limiting defect:
\[
 |c_{\infty,d}^M-c_{n,d}^M|^2
 \le\|\lambda_d\|_M^2\,(E_n^M-\|r_M\|_M^2).              \tag{11}
\]
The exact energy identity behind it is
\[
 E_n^M=\|r_M\|_M^2+\|F_\infty^M-F_n^M\|_M^2.
\]

Checked providers are `CoordinateProjectionCriterion.target_mem_iff_coordinate_limits`, `SquarefreeMobiusProjection.p_coefficient_limits_iff_closure`, `q_coefficient_limits_iff_closure`, `p_q_coefficient_limits_iff`, and `qCoefficient_error_bound`. The general theorem applies to any restricted dictionary whose omitted coordinates vanish and whose retained-plus-omitted coordinates separate the ambient space. All those hypotheses are discharged by the concrete Möbius coordinate arguments in the application module.

## 5. Finite Gram and centered-capacity formulas

Index only distinct squarefree conductors. In either metric let
\[
 G_{de}=\langle g_d,g_e\rangle_M,\quad b_d=\langle1,g_d\rangle_M,
 \quad \Sigma=G-bb^T.
\]
Biorthogonality gives independence of the atoms. A finite residue sum vanishes at every multiple of their common period, so it cannot equal a nonzero constant. Consequently the centered family is independent as well, and G and Sigma are positive definite.

For the actual target one has
\[
 c^*=G^{-1}b=\frac{\Sigma^{-1}b}{1+b^T\Sigma^{-1}b},\qquad
 K=b^T\Sigma^{-1}b,\qquad E=\frac1{1+K},                    \tag{12}
\]
and the full completed square is
\[
 \boxed{\|1-\sum_d c_dg_d\|_M^2
 =\frac1{1+K}+\|\sum_d(c_d-c_d^*)g_d\|_M^2}.              \tag{13}
\]
The exact Möbius correction is
\[
 c^*=-\mu_D+G^{-1}(b+G\mu_D).                              \tag{14}
\]
Restricting to squarefree conductors does not remove the signed source in (14).

The Q implementation already exists in `QSquarefreeInverseCapacity.lean`: `candidate_eq_optimizer`, `error_eq_reciprocal`, `exact_minimum`, `candidate_parseval_error`, and `inverseCapacity_tendsto_iff_squarefree_closure`. Its complete divisor-wavelet Parseval identity includes the constant r=1 term. This work does not replace it with a sum over squarefree wavelet indices: legal squarefree residue atoms can have nonsquarefree wavelet coordinates.

## 6. Exact squarefree gain criteria

Use the existing masked enumeration, so stage n+1 adjoins conductor n+2 when it is squarefree and adjoins zero otherwise. Set
\[
 a_n=\|F_{n+1}^Q-F_n^Q\|_Q^2,\qquad
 \alpha_n=\frac{a_n}{E_n^Q}.
\]
Every finite error is positive. Nested projection gives the exact identities
\[
 \boxed{E_n^Q=E_{n+1}^Q+a_n},\qquad
 E_N^Q=1-\sum_{n<N}a_n
 =\prod_{n<N}(1-\alpha_n),\quad0\le\alpha_n<1.             \tag{15}
\]
If n+2 is nonsquarefree, its atom is zero, the stage does not change, and a_n=alpha_n=0. Thus the formulas do not divide by a zero Schur innovation.

The existing residual-product theorem now gives
\[
 \boxed{1\in W_Q\iff E_n^Q\to0\iff
         \sum_{n\ge0}\alpha_n=\infty}.                     \tag{16}
\]
For a nonredundant increasing squarefree enumeration, the usual Schur quantities satisfy a_n=eta_n^2/sigma_n with sigma_n>0. The P version has the same form with its own projections and gains. Divergence is an arithmetic target, not a consequence of the exact product identity.

Checked provider: `QSquarefreeRelativeGain.closure_iff_relativeGain_not_summable`, with the finite equalities and zero-gain stages proved explicitly in the accompanying draft.

## 7. Corrections required for density, dilation, and dual targets

These are restrictions on particular old implications, not obstructions to approximating the constant.

**Ambient totality does not transfer.** Equation (9), together with lambda_d(g_d)=1, proves g_d is outside W_M whenever d is nonsquarefree. Hence W_M is a proper ambient subspace even if it contains one. The old full-dictionary implication that constant membership forces ambient totality cannot be reused. The Q module includes `q_nonsquarefree_atom_not_mem`.

**General dilation invariance fails.** For the unscaled physical dilation S_m f(n)=f(floor(n/m)),
\[
 S_mg_d=g_{md}-\frac1d g_m.
\]
Taking m=d=p prime introduces g_(p^2). Its lambda_(p^2) coordinate is one, so S_p g_p is outside the squarefree closure in either metric. Norm equivalence cannot repair a conductor that is absent from the dictionary.

**Inverse-Gram diagonals need restricted targets.** Write
\[
 \lambda_d(f)=\sum_{n=1}^d A_d(n)f(n),\qquad
 A_d(n)=\mathbf1_{n+1\mid d}\mu(d/(n+1))
       -\mathbf1_{n\mid d}\mu(d/n).
\]
The native Riesz vectors are
\[
 h_d^P(n)=n(n+1)A_d(n),\qquad h_d^Q(n)=Zn^2 A_d(n).          \tag{17}
\]
Thus the Q Riesz vector is not obtained merely by keeping the P vector's physical values.

For a finite squarefree stage containing d,e, biorthogonality gives the complete identity
\[
 \boxed{(G_n^M)^{-1}_{de}
 =\langle h_d^M,h_e^M\rangle_M
 -\langle(I-P_{V_n^M})h_d^M,(I-P_{V_n^M})h_e^M\rangle_M}.   \tag{18}
\]
Therefore the correct limiting diagonal is
\[
 \lim_n(G_n^M)^{-1}_{dd}=\|P_{W_M}h_d^M\|_M^2,             \tag{19}
\]
with the omitted norm-square retained. It need not equal the full ambient norm of h_d, even when RH holds.

For a concrete test,
\[
 h_2^P=(4,-6,0,\ldots),\quad\|h_2^P\|_P^2=14,
 \quad\lambda_4(h_2^P)=-10,\quad\|h_4^P\|_P^2=40;
\]
\[
 h_2^Q=Z(2,-4,0,\ldots),\quad\|h_2^Q\|_Q^2=8Z,
 \quad\lambda_4(h_2^Q)=-6Z,\quad\|h_4^Q\|_Q^2=30Z.
\]
Because h_4 annihilates W_M, orthogonal decomposition and Cauchy-Schwarz give
\[
 \lim_n(G_n^P)^{-1}_{22}\le14-\frac{100}{40}=\frac{23}{2},
 \qquad
 \lim_n(G_n^Q)^{-1}_{22}\le8Z-\frac{36Z^2}{30Z}=\frac{34Z}{5}. \tag{20}
\]
In particular copying the old target 14 into the squarefree P inverse-Gram criterion would be false. The correct coefficient criterion in Section 4 avoids that problem. Formulas (17)-(20) are mathematical derivations and exact algebraic checks in this record; no new Lean verification of them is asserted.

Native self-adjointness, orthogonality, spectra with metric-dependent normalizations, and DPP probabilities likewise need their own Q inner product. Existing operator similarity preserves algebraic identities and eigenvector equations, but is not an isometry.

## 8. An explicit legal conversion of exact-head repairs

Pure Möbius sums are already squarefree supported. Let
\[
 B_H=-\sum_{2\le d\le H}\mu(d)g_d,\qquad
 s_H=\sum_{d\le H}\frac{\mu(d)}d.
\]
Divisor inversion gives B_H(n)=1-n s_H for 1<=n<=H. If an earlier construction repaired this using a nonsquarefree conductor, replace that repair conductor by any squarefree R>H. Then
\[
 \boxed{F_{H,R}=B_H+R s_H g_R},\qquad F_{H,R}(n)=1\ (1\le n\le H). \tag{21}
\]
This is a finite squarefree legal trial. Its common period is the LCM of its squarefree conductors and is itself squarefree. Primes or sufficiently large primorials supply R.

Writing u_H=1-B_H, the complete error is
\[
 \boxed{\|1-F_{H,R}\|_M^2
 =\|u_H\|_M^2-2R s_H\langle u_H,g_R\rangle_M
 +(R s_H)^2\|g_R\|_M^2}.                                  \tag{22}
\]
Every signed and squared term remains. The construction supplies exact legal heads; it does not prove a uniform full-energy bound. Existing squarefree affine-head and constrained-minimum modules should be used for optimizing this family rather than assuming the one-atom repair is energetically effective.

## 9. Lean verification record and publication workflow

The following modules have passed server verification against the inspected base:

1. `RiemannResearch/Analysis/CoordinateProjectionCriterion.lean`: coordinate annihilation through closure, retained-coordinate target characterization, and the finite projection coefficient limit criterion.
2. `RiemannResearch/RH/SquarefreeMobiusProjection.lean`: separate P/Q projections, unconditional stabilization, squarefree target equivalences, omitted-coordinate obstructions, genuine inverse-capacity coefficient recovery, exact residual correction, and quantitative stabilization.
3. `RiemannResearch/RH/QSquarefreeRelativeGain.lean`: complete additive/product identities, strict relative gains, the closure/nonsummability equivalence, and zero innovation at nonsquarefree stages.

| Server job | Scope | Terminal result |
|---|---|---|
| `job_Gi6TxCFckdoc8JbloKGwukWxpa3MAcVH` | Combined proof bodies and ten main axiom reports | succeeded; exit 0; 6.875 seconds |
| `job_SHNSHui49yJ_uBZyGjHb1T7-Vm8Jspuu` | Native coefficient module and its generic coordinate-criterion dependency | succeeded; exit 0; 12.732 seconds |
| `job_4xQVOP2K4DgaSJjSRzInsxzl-eI6kDrq` | Native Q relative-gain module | succeeded; exit 0; 6.444 seconds |
| `job_PuSOPKtXfQV9oRT1WfNU9CeqLWtDd9QV` | Native imports of all three final modules and all 29 public theorem axiom reports | succeeded; exit 0; 15.346 seconds |

The first compiler diagnostics were repaired by qualifying the exhaustive-walk closure namespace, using a direct rewrite for the omitted-atom contradiction, explicitly identifying the transported P span, and making the zero-stage projection proof explicit. Copyright-header warnings were also fixed before the final native import/axiom check.

Every one of the 29 public axiom reports was inspected and contained exactly the ordinary foundations `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs or project-local axiom declarations in the new sources. These reports do not discharge hypotheses in theorem types: the two RH consumers still explicitly assume simultaneous squarefree Möbius limits or nonsummability of the actual relative gains.

This scope is three new Lean modules. The report explicitly labels additional mathematical derivations such as (6) and (17)-(22); it does not present them all as new Lean declarations. The classical RH-to-squarefree-density theorem is cited and remains outside the new formalization.

The exact exported project delta must pass the final `agent_workspace_checkpoint` before publication. Its terminal result supplies the final validation scope and published commit, which the final chat report records. GitHub-hosted CI is not the verification path.

## 10. Remaining research targets

1. **Open arithmetic target:** show that the actual squarefree optimizer's fixed coefficients identify with -mu(d), or equivalently that its inverse capacity diverges. Convergence to some coefficient limit is already geometric and does not identify it.
2. **Equivalent open target:** prove nonsummability of the native squarefree relative gains. Finite nonzero gains and monotonicity of capacity do not suffice.
3. **Exact-head alternative:** optimize the complete signed energy in (22), or use the existing constrained minima, and prove the bounded or subpolynomial complete-energy provider required by the corresponding RH consumer.
4. **Formalization target:** with this conversion layer checked, formalize the classical RH-to-squarefree approximation argument without introducing an unproved analytic axiom. Existing damping/Hardy modules expose the remaining analytic estimates.

The conversion makes the earlier Pareto toolkit available in the correct squarefree Q space. It does not establish one of these open arithmetic providers or prove RH.
