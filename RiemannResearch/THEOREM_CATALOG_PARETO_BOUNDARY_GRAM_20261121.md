# The centered Pareto boundary and finite Gram determinants

Write `G_n` for the Pareto Gram matrix of the packets with conductors from 2 through
$n+1$, $\mu_i=\Lambda(i+2)$ for their means, $S_n=G_n-\mu\mu^\top$, and
$I_n=\mu^\top S_n^{-1}\mu$. The stage counts conductors. A cutoff on the number of
distinct prime factors is a different filtration. Let $u$ be the screened mean-one
vector, $r=1-P_V1$, and $d=\|\partial\|^2=\|u\|^2-1$ for the centered mean snake
boundary. All norms and projections are in the original Pareto geometry.

## Exact calculations

| Lean declaration | Result |
|---|---|
| `centeredInverseGramMass_eq_div` | $I_n=m_n/(1-m_n)$ with $m_n=\mu^\top G_n^{-1}\mu$. |
| `boundary_eq_zero_iff_centeredInverseGramMass_tendsto` | $\partial=0$ exactly when $I_n\to+\infty$. For $d>0$ the limit equals $1/d$. |
| `normalizedScreenedTwo_not_mem_finiteSpace` | The canonical mean-one vector is outside every finite packet span. A finite-span vector is physically bounded, and the screened one-sided rigidity theorem would identify it with the constant. Every finite span vanishes at a common multiple. |
| `single_zero_outside_gram_disk` | Any zeta zero $z=\sigma+it$, $\sigma>1/2$, $z\ne1$, satisfies $(\sigma-1-I_n)^2+t^2>I_n(I_n+1)$. |
| `mixed_det_ratio` | For $H_n=\operatorname{Gram}(P_MJ_2,\ldots,P_MJ_{n+1})$, $\det H_n/\det S_n=1-dI_n$. The ratio is positive at each finite stage and decreases with $n$. |
| `mixed_det_eq_centered_iff` | At any nonempty stage, equality $\det H_n=\det S_n$ is equivalent to $\partial=0$. The entries of $H_n$ use the full mixed projection. |
| `centeredInverseGramMass_one`, `centeredInverseGramMass_two` | For $a=\log 2$, $b=\log 3$, $c=\pi/(3\sqrt3)$, $D=a(2b-c)-(a+b/2-c)^2$ and $F=ca(2b-a)$, the first two information values are $a/(1-a)$ and $F/(D-F)$. |
| `det_siteGram` | Set $j_k=(J_{i+2}(k))_i$ and $A_n(k)=G_n+\mu j_k^\top$. Then $\det A_n(k)/\det G_n=1+(P_n1)(k)$. At site one, $j_1$ is the negative Möbius vector. |
| `projection_two_first_site_gap` | $(P_11)(1)=1$ and $D((P_21)(1)-1)=(c-b/2)(b/2-a+c)>0$. The limiting first-site projection is at most one. Hence the first-site projections cannot be monotone increasing. |
| `first_two_sites_det_positive` | The determinant sign at physical sites 1 and 2 is strict at **every** stage from 2 onward. The exact error of the trial $(J_2+J_3)/2$ is $1-(a+b+3c)/4<1/6$. |
| `abs_screened_residual_pairing` | $\langle |u|,r\rangle=2\mathbb E_P[u_-]+(1-\|r\|^2)\,\||u|-u\|^2/2$. Orthogonality of $r$ to $V$ and one-sided rigidity give $|u|\in V\iff\partial=0$. |

The infinite conductor-two projection itself satisfies
$\|P_M(J_2/a)\|^2=a^{-1}-1-d$. The scalar $d$ is the exact amount missing
from the proposed endpoint. It is independent of the finite stage information
$I_1=a/(1-a)$. The polarized identity also gives
$a+b/2-c-ab-\langle P_MJ_2,P_MJ_3\rangle=ab\,d$. A reverse bound on this
mixed pairing would suffice. The arithmetic determinants avoid computing a mixed
projection in each trial.

## A projection-free arithmetic obligation

For every $\varepsilon>0$ and cutoff $N$, it suffices to find $n\ge N$ satisfying

$$
 (2-\varepsilon)\det G_n\ \le\ \det A_n(1)+(2-\sqrt2)\det S_n .
$$

`boundary_eq_zero_iff_first_site_det_budget` proves that this quantifier statement is
equivalent to the vanishing of the actual boundary. Here $A_n(1)=G_n-\mu\,\mu_{\rm Mob}^{\top}$, where $\mu_{\rm Mob}$ is the vector of Möbius values. No full mixed projection occurs in this test. The coefficient comes from the dyadic residual estimate. The sharper sufficient condition takes $\varepsilon=0$
along arbitrarily late stages. The theorem `first_two_det_certificates` proves strict slack at stages one and two.
An estimate relating arbitrarily late determinants remains open.

For an exact implementation, one solve $G_n c_n=\mu$ supplies both scalars.
The zero-slack comparison is
$-\mu_{\rm Mob}^{\top}c_n+(2-\sqrt2)(1-\mu^\top c_n)\ge1$.
Other site values use $j_k^\top c_n$ from the same solve. The declaration `riemannHypothesis_of_cofinal_first_site_solve` accepts this single-solve test directly.

There is a different sign test at physical sites. For every fixed $k\ge1$, require
$\det A_n(k)\ge\det G_n$ at arbitrarily late $n$. The witness $n$ may depend on $k$
and on the requested cutoff. If the boundary is nonzero, then for every $B$ there
is a fixed site where eventually $\det A_n(k)<-B\det G_n$.
`boundary_eq_zero_iff_cofinal_site_det_sign` and
`eventually_negative_site_det_of_boundary_ne` give these two statements.

A finite lattice shortcut also fails already for conductors two and three. The vector $J_2-J_3$ is legal at that stage. Its absolute value takes the values $0,2,1$ at sites one through three and violates the stage relation $2f(1)=f(2)+2f(3)$. This is `exists_two_stage_abs_outside`. The separate question about $|u|$ concerns the full closed space.

## The categorical and analytic steps

The split legal mean identifies its quotient with the screened line and leaves
the weight $\|u\|$ on the scalar coordinate. For $v\in V$, $m=P_Mv$, the existing
`legal_support_parseval` and `legalSupportEquiv` give
$\|v\|^2=|C(v)|^2\|u\|^2+\sum_k\|P_{L_k}m\|^2$ and the linear isometry onto
the screened line together with the Hilbert $\ell^2$ sum of the layers.
The natural comparison of successive
support rows has connecting map equal to the identity on the relevant layer.
The comparison through the stage retraction kills the layer and has zero boundary.
These are `successiveLayerBoundary_eq_id` and `truncatedLayerBoundary_eq_zero`.
In the ambient diagram the missing assertion is the vanishing of the class
of $u-1$ in $1^\perp/M$. The general snake map depends on all three vertical maps.
[Weibel, *An Introduction to Homological Algebra*, Lemma 1.3.2](https://assets.cambridge.org/97805214/35000/sample/9780521435000ws.pdf)
and [Stacks Project, Tag 07JV](https://stacks.math.columbia.edu/tag/07JV).

Bagchi gives the discrete Hilbert-space formulation and the Gram determinant
description of the finite distance. The logarithmic rate discussed on page 146
is conjectural. The calculations above require no asymptotic rate.
[Bagchi, *Proc. Indian Acad. Sci. (Math. Sci.)* 116 (2006), 137–146](https://doi.org/10.1007/BF02829783).

In the abstract Hilbert model $H=\mathbb R^2\oplus\ell^2$, take $1=e_1$,
$u=e_1+s e_2$, $M=\ell^2$, and $V=\mathbb Ru\oplus M$. The mean is inner
product with $e_1$. Every coordinate stage of $M$ splits orthogonally and Parseval
holds with scalar weight $\sqrt{1+s^2}$. Yet $e_1\in V$ exactly when $s=0$.
The arithmetic site and covariance tests supply the additional content needed in
the Pareto problem.

## Declaration index

Every public declaration in the five new modules appears below. The [full categorical and companion index](CATEGORY_THEORY_DECLARATIONS.md) also covers the underlying quotient diagrams, CRT functors, and global Parseval equivalence.

| Module | Declarations |
|---|---|
| [MixedConductorGramBoundary](RH/MixedConductorGramBoundary.lean) | `meanVector`, `meanPencil`, `det_meanPencil`, `centered_det_pos`, `centeredInverseGramMass`, `centeredInverseGramMass_eq`, `centered_det_ratio_tendsto`, `centeredInverseGramMass_monotone`, `centeredInverseGramMass_tendsto_of_ne`, `boundary_eq_zero_iff_centeredInverseGramMass_tendsto`, `riemannHypothesis_of_centeredInverseGramMass_tendsto` |
| [MixedConductorGramZeroFree](RH/MixedConductorGramZeroFree.lean) | `normalizedScreenedTwo_not_mem_finiteSpace`, `packetUnitMeanLimit_eq_screened`, `packetMass_lt_limitMass`, `centeredInverseGramMass_eq_div`, `centeredInverseGramMass_nonneg`, `centeredInverseGramMass_mul_boundary_lt_one`, `single_zero_strict_gram_bound`, `single_zero_outside_gram_disk`, `zeta_ne_zero_on_gram_rectangle` |
| [MixedConductorProjectedGram](RH/MixedConductorProjectedGram.lean) | `mixedPacketGram`, `centeredPacketGram_apply`, `mixedPacketGram_eq_pencil`, `mixed_det_ratio`, `mixedPacketGram_det_pos`, `mixed_det_ratio_antitone`, `mixed_det_eq_centered_iff`, `mixed_det_ratio_tendsto_zero_of_boundary_ne`, `boundary_eq_zero_iff_cofinal_mixed_det_lower`, `centeredInverseGramMass_one`, `det_two_meanPencil`, `centeredInverseGramMass_two` |
| [MixedConductorGramSites](RH/MixedConductorGramSites.lean) | `siteVector`, `siteGram`, `siteVector_one`, `det_siteGram`, `boundary_eq_zero_iff_cofinal_site_det_sign`, `eventually_negative_site_det_of_boundary_ne`, `boundary_eq_zero_iff_first_site_det_budget`, `riemannHypothesis_of_cofinal_first_site_det`, `first_site_det_as_one_solve`, `riemannHypothesis_of_cofinal_first_site_solve`, `projection_one_first_site`, `projection_two_first_site_gap`, `projection_two_first_site_gt_one`, `first_two_det_certificates`, `site_positive_of_residual_lt_weight`, `half_two_three_trial_error`, `two_stage_residual_lt_sixth`, `first_two_sites_det_positive`, `projection_first_site_not_monotone` |
| [MixedConductorAbsoluteBoundary](RH/MixedConductorAbsoluteBoundary.lean) | `exists_two_stage_abs_outside`, `abs_screened_residual_pairing`, `negative_mass_le_abs_legal_distance`, `screened_eq_one_iff_abs_pairing_nonpos`, `abs_screened_mem_iff_boundary_zero`, `boundary_zero_iff_projected_one_nonnegative`, `riemannHypothesis_of_abs_screened_mem` |
