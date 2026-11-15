# Conrey–Baluyot normalized Littlewood continuation — 15 November 2026

Base: [ee6afa898e3c93e10d6db3568ac2b30245df13e7](https://github.com/Cnoack3/RiemannResearch/commit/ee6afa898e3c93e10d6db3568ac2b30245df13e7).
This continuation resolves the recovery note's branch-compatibility target and constructs outward rectangles. It also sharpens the conditional conversion of an actual second moment to a vertical logarithmic integral.

**Subsequent continuation:** [Signed right boundary and revised agenda](THEOREM_CATALOG_CONREY_BALUYOT_RIGHT_BOUNDARY_20261115.md) discharges the signed right integral, permits any prescribed left interval, and adds the conditional moment count. The theorem below is the specialization a=1/2, c=alpha of that stronger current declaration.

## Established declarations

All Conrey–Baluyot declarations below are in namespace
`RiemannResearch.Analysis.ConreyBaluyot`.

| Declaration | Owning module | Content |
| --- | --- | --- |
| `Complex.logLifts_eqOn_of_exp_eq` | `Analysis/ComplexLogLiftUniqueness.lean` | Continuous exponential lifts on a preconnected set agree if they agree at one point. |
| `Complex.logLift_eq_principal_on_Icc` | same | A normalized lift equals the principal logarithm when the entire image interval lies in the slit plane. |
| `Complex.logLift_im_eq_phase_on_Icc` | same | A normalized continuous polar phase equals the lift's imaginary part throughout the interval. |
| `Complex.exists_logRectangleBoundary_eq_contour` | `Analysis/ComplexLittlewoodBoundary.lean` | Strengthened existing theorem: bottom-right principal normalization and top-right normalization under an explicit whole-side slit-plane condition. |
| `Complex.exists_logRectangleBoundary_eq_weighted_zeros` | `Analysis/ComplexLittlewoodZeros.lean` | Propagates the normalization through the exact weighted-zero identity. |
| `exists_mollifiedZeta_littlewood_identity_with_remainder` | `Analysis/ConreyBaluyotLittlewood.lean` | Propagates normalization while retaining the exact nonnegative mollifier-zero remainder. |
| `exists_uniform_dyadic_mollifiedZeta_outward_anchor_rectangle` | `Analysis/ConreyBaluyotDyadicRectangle.lean` | Builds a zero-free border with fixed right anchor and horizontal edges strictly outside the closed dyadic window. |
| `GoodHorizontalPhase.integral_logLift_bound` | `Analysis/ConreyBaluyotDyadicLittlewood.lean` | Transfers the phase integral bound to the actual normalized logarithm lift. |
| `exists_uniform_dyadic_littlewood_normalized_boundary_bound` | same | Supplies the exact identity, both normalized horizontal bounds, outward coverage, and the corrected closed-window multiplicity estimate for the same lifts. |
| `Complex.scaledLogSecondMomentDefect_nonneg` | `Analysis/ComplexLogSecondMoment.lean` | Nonnegative tangent defect for positive mean-square scale and nonzero argument. |
| `Complex.integral_log_norm_scaled_second_moment_exact` | same | Exact scaled second-moment/logarithm identity with the entire integrated defect. |
| `Complex.integral_log_norm_le_of_mean_square_bound` | same | Converts an explicit mean-square bound into a logarithmic bound. |
| `integral_log_mollifiedZeta_le_log_of_moment` | `Analysis/ConreyBaluyotMollifiedBoundary.lean` | Actual-mollifier specialization; the second-moment estimate is still an explicit hypothesis. |

The horizontal-real-zero, phase, normalized-phase, good-height, and dyadic-good-height providers now retain their common right-half-plane lower bound. The dyadic nominal-height window is enlarged from \([T,2T]\) to \([T-\tfrac14,2T+\tfrac14]\). A direct estimate at scale \(T\) removes the earlier extra factor of two in the constructed horizontal constant, with the threshold enlarged by one before the power-length condition is imposed.

## Exact uniform theorem and domain conditions

Fix \(\varepsilon\ge0\) and \(\theta>0\). The main theorem constructs
\(\eta,b,D,H\) with
\[
0<\eta<\tfrac14,\qquad b\ge2,\qquad D>0,\qquad H\ge b+2.
\]
For every \(T\ge H\), every
\[
\tfrac12+\frac1{\log(T^\theta)}\le\sigma\le\tfrac12+\eta,
\]
every \(0<\delta\le\tfrac14\), and every \(\tfrac12<\alpha<b\), it constructs
\(t_1,t_2,\ell,Z,B,U\) satisfying
\[
T-\delta<t_1<T<2T<t_2<2T+\delta,\qquad
\tfrac12<\ell<\alpha.
\]
The function remains the one fixed
\(F(s)=\zeta(s)M_{\sigma,T^\theta,\varepsilon}(s)\) throughout.

The border of \([\ell,b]+i[t_1,t_2]\) is zero-free, and \(Z\) is exactly its finite product-zero set. The continuous lifts satisfy
\[
e^{B(x)}=F(x+it_1),\qquad e^{U(x)}=F(x+it_2),\qquad
B(b)=\log F(b+it_1),\quad U(b)=\log F(b+it_2),
\]
where the corner logarithms are principal. Write
\[
I_x=\int_{t_1}^{t_2}\log|F(x+it)|\,dt,\quad
A_B=\int_\ell^b\operatorname{Im}B(x)\,dx,\quad
A_U=\int_\ell^b\operatorname{Im}U(x)\,dx,
\]
\[
Z_\zeta=\sum_{\rho\in Z}\operatorname{ord}_\rho(\zeta)(\Re\rho-\ell),
\qquad
Z_M=\sum_{\rho\in Z}\operatorname{ord}_\rho(M)(\Re\rho-\ell).
\]
The same lifts satisfy
\[
I_\ell-I_b+A_U-A_B=2\pi(Z_\zeta+Z_M),\qquad Z_M\ge0,
\]
\[
|A_B|\le D\log T,\qquad |A_U|\le D\log T,\qquad
|A_U-A_B|\le2D\log T.
\]
The theorem also proves
\[
\sum_{\substack{\rho\in Z\\ \Re\rho\ge\alpha\\ T\le\Im\rho\le2T}}
\operatorname{ord}_\rho(\zeta)
\le
\frac{(I_\ell-I_b+2D\log T)/(2\pi)-Z_M}{\alpha-\ell}.
\]
Every zeta zero in \([\alpha,b]+i[T,2T]\) is explicitly proved to belong to \(Z\).
The sum uses zeta analytic multiplicity, so a mollifier-only zero has zero contribution. This is a finite multiplicity estimate, not an evaluation of the repository's global density function.

No branch-compatibility premise, horizontal budget, or supplied zero-free border remains in this uniform theorem. The right-half-plane provider gives \(\Re F\ge1/2\) everywhere on and to the right of \(b\), at these same parameters. Covering-map uniqueness identifies the vertical lift with the principal logarithm. A common additive logarithm shift cancels exactly from the boundary functional; no independent winding correction is dropped.

The outward construction covers the closed window directly. It removes the need for a limiting-height argument for this particular count; it does not assert a general boundary-limit theorem.

## Sharper vertical conversion, still conditional on a moment

For \(A>0\), define
\[
d_A(z)=\frac{|z|^2/A-1}{2}+\frac{\log A}{2}-\log|z|.
\]
For \(z\ne0\), Lean proves \(d_A(z)\ge0\). With \(L=T-H\), the exact identity is
\[
\int_H^T\log|f(t)|\,dt
=
\frac L2\log A+
\frac{A^{-1}\int_H^T|f(t)|^2\,dt-L}{2}
-\int_H^T d_A(f(t))\,dt.
\]
Interval integrability is explicit in the general theorem. For the actual mollified zeta, positive height and a zero-free vertical segment provide it.

If \(0<H<T\), \(E\ge0\), the segment is zero-free, and the actual uncentered second moment satisfies
\[
\int_H^T |F(\alpha+it)|^2\,dt\le L+E,
\]
the specialized theorem proves both inequalities
\[
\int_H^T\log|F(\alpha+it)|\,dt
\le \frac L2\log(1+E/L)\le\frac E2.
\]
This improves the earlier linear conversion and preserves the exact defect in its supporting identity. It does **not** prove the actual moment estimate.

## Remaining obligations and next target

| Obligation | Current status |
| --- | --- |
| Same normalized branches in the exact identity and horizontal bounds | Discharged on the stated uniform strip |
| Outward coverage of the closed dyadic window | Discharged for the finite count above |
| Sharp conversion from an actual second moment to the left log integral | Discharged as a conditional analytic conversion |
| Actual uniform mollified second moment in the required range, at admissible left boundaries | Open |
| Uniform signed right vertical integral for this nonstandard mollifier | Discharged; see the signed right-boundary continuation |
| Complete and multilinear Kloosterman inputs | Open |
| Unconditional numerical density provider and remaining Ingham input | Open |
| RH | Not established |

The selected left edge is \(\ell<\alpha\); applying a moment theorem only on a prescribed different line requires an additional uniformity or limiting argument. The outward construction resolves height coverage, not that separate alignment issue.

The signed right-boundary target is now discharged by a holomorphic rectangle shift and the established exponential decay. No logarithmic Dirichlet-series interchange is needed. The optional sharper dilogarithm estimate remains a quantitative refinement, not a missing hypothesis of the current bound.

The next target is the actual uncentered second moment for the same mollifier, on a left interval selected before applying the strengthened rectangle theorem. See the [current agenda](THEOREM_CATALOG_CONREY_BALUYOT_RIGHT_BOUNDARY_20261115.md) for exact quantifiers, retained signs, and remaining obligations.

## Verification of the earlier normalized snapshot

The final focused Bazel check imported the dyadic module and all its transitive
imports and passed nine standard-axiom guards:
`job_qDiwPYKgguPwV5cyuB9Ufw-HicMwt4y0`, 55.470 seconds of server verification,
[BuildBuddy evidence](https://app.buildbuddy.io/invocation/e4832212-bb9d-4999-8d43-a1a5228fba2b).
Each guard accepted exactly `propext`, `Classical.choice`, and `Quot.sound`.

Retained workspace: `ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2/RiemannResearch`.

Publication is through the managed full-project Bazel/BuildBuddy checkpoint
`//:RiemannResearch`; the commit containing this catalog identifies the
published source. The final publication job and invocation are reported in
the completion message and can be recovered from this workspace's job ledger.
Axiom checks do not discharge hypotheses written in theorem types.
