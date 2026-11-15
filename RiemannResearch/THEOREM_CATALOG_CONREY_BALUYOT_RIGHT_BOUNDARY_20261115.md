# Conrey–Baluyot signed right boundary — 15 November 2026

Base: [e737f81aa004b72f4ecf767fe94d432bb6946855](https://github.com/Cnoack3/RiemannResearch/commit/e737f81aa004b72f4ecf767fe94d432bb6946855).

This continuation discharges the handoff's signed right-boundary obligation for the actual nonstandard mollifier. It strengthens the normalized dyadic theorem, makes its left-edge interval selectable, and assembles the sharper conditional second-moment count. The actual moment and the arithmetic density inputs remain open. RH is not established.

## Established declarations

Unless prefixed by `Complex`, declarations are in `RiemannResearch.Analysis.ConreyBaluyot`. Paths are relative to `RiemannResearch/`.

| Declaration | Module | Content |
| --- | --- | --- |
| `Complex.integral_vertical_rectangle_identity` | `Analysis/ComplexRightBoundary.lean` | Exact finite rectangle identity with both horizontal integrals and the remote vertical remainder. |
| `Complex.norm_integral_vertical_le_of_exp_decay` | same | Holomorphy and horizontal exponential decay give cancellation on every finite vertical interval, uniformly in both endpoints. |
| `Complex.norm_log_le_two_mul_norm_sub_one` | same | Principal logarithm bound throughout Re z ≥ 1/2. |
| `Complex.norm_integral_log_vertical_le_of_exp_decay` | same | Full complex logarithm integral bound. |
| `Complex.abs_integral_log_norm_vertical_le_of_exp_decay` | same | Signed real logarithm integral bound. |
| `mollifiedZeta_right_integral_bounds` | `Analysis/ConreyBaluyotRightBoundary.lean` | Actual-product application with explicit decay constant and anchor. |
| `exists_uniform_mollifiedZeta_right_integral_bound` | same | Unconditional uniform provider on the coupled parameter strip; constants precede length, sigma, right line and both endpoints. |
| `exists_uniform_dyadic_mollifiedZeta_outward_anchor_rectangle` | `Analysis/ConreyBaluyotDyadicRectangle.lean` | Strengthened: the left edge can lie inside any prescribed nonempty interval above 1/2. |
| `exists_uniform_dyadic_littlewood_normalized_boundary_bound` | `Analysis/ConreyBaluyotDyadicLittlewood.lean` | Replaces `exists_uniform_dyadic_littlewood_normalized_horizontal_bound`; retains exact signs and multiplicities, adds the right bound, selectable left interval, full rightward zeta-zero coverage, and conditional logarithmic moment count. |

## Exact identity before estimation

For g holomorphic at every point of Re z ≥ b, Cauchy–Goursat gives, for R ≥ b and arbitrary real u,v,
\[
i\int_u^v g(b+it)\,dt
=
\int_b^R g(x+iu)\,dx-\int_b^R g(x+iv)\,dx
+i\int_u^v g(R+it)\,dt.
\]
No signed contribution or remote edge is omitted. If a>0, C≥0 and
\[
|g(z)|\le C e^{-a\Re z}\qquad(\Re z\ge b),
\]
the horizontal integrals have norm at most C e^{-ab}/a, and the remote vertical integral has norm at most C e^{-aR}|v-u|. Taking R to infinity proves
\[
\left|\int_u^v g(b+it)\,dt\right|\le \frac{2C}{a}e^{-ab}.
\]
This bounds the norm of the signed integral, not the integral of the pointwise norm.

For Re z≥1/2 the convex-set derivative estimate gives |log z|≤2|z−1| for the principal logarithm. Thus holomorphy, Re F≥1/2, and |F(z)−1|≤C e^{-a Re z} imply
\[
\left|\int_u^v\log F(b+it)\,dt\right|\le\frac{4C}{a}e^{-ab}.
\]
The real part is the required signed integral of log|F|.

## Actual mollifier and uniformity

The function remains F(s)=ζ(s)M_{σ,y,ε}(s). The existing actual coefficient and decay providers establish |F(s)−1|≤D 2^{2−Re s}. Together with the positive-real anchor, the application gives
\[
\boxed{
\left|\int_u^v\log F(b+it)\,dt\right|,
\quad
\left|\int_u^v\log|F(b+it)|\,dt\right|
\le \frac{4D}{\log2}\,2^{2-b}.}
\]
The complex integral uses the principal logarithm, already normalized at the Littlewood right corners.

For every ε≥0 the uniform theorem constructs η,Y,b,C with 0<η<1/4, Y>1, b≥2, C>0. For every y≥Y, every 1/2+1/log y≤σ≤1/2+η, every c≥b, and all real u,v, both integrals are bounded by C 2^{2−c}. Neither interval length nor mollifier length appears in the bound.

No second moment, coefficient convolution, logarithmic Dirichlet-series expansion, or interchange with an infinite series is assumed. Wolfram independently simplified the horizontal majorant to 2^{4−b}D/log 2, agreeing with the formal constant. That calculation is supporting evidence, not Lean acceptance. The earlier dilogarithm-series bound remains an optional quantitative refinement, not a required step in the current proof.

## Strengthened dyadic theorem

Fix ε≥0 and θ>0. The theorem chooses uniform η,b,D,C,H, with positive D,C and H≥b+2. For T≥H and the coupled sigma strip, choose
\[
0<\delta\le1/4,\qquad \tfrac12\le a<c\le\alpha<b.
\]
It supplies outward heights and a zero-free left edge:
\[
T-\delta<t_1<T<2T<t_2<2T+\delta,\qquad a<\ell<c,\qquad \ell<\alpha.
\]
The proof intersects parameter strips and enlarges the threshold before selecting the rectangle. It uses the same right anchor and fixed mollifier y=T^θ for every term.

Let L=t₂−t₁ and let Z be the exact finite product-zero set in the rectangle. With the normalized catalog's notation,
\[
Z_M=\sum_{\rho\in Z}\operatorname{ord}_{\rho}(M)(\Re\rho-\ell)\ge0,
\qquad I_\ell-I_b+A_U-A_B=2\pi(Z_\zeta+Z_M).
\]
Both horizontal bounds persist. The same rectangle now has |I_b|≤C and a complex-log integral bound C.

Every zeta zero with Re ρ≥α and T≤Im ρ≤2T belongs to Z. No upper bound on Re ρ is required: zeta nonvanishing for Re s≥2 supplies it. Mollifier-only zeros contribute zero zeta multiplicity.

The original signed finite multiplicity estimate remains:
\[
N_Z(\alpha;T,2T)\le
\frac{(I_\ell-I_b+2D\log T)/(2\pi)-Z_M}{\alpha-\ell}.
\]

### Conditional research reduction: moment to count

For every E≥0, the theorem additionally proves
\[
\int_{t_1}^{t_2}|F(\ell+it)|^2\,dt\le L+E
\quad\Longrightarrow\quad
\boxed{
N_Z(\alpha;T,2T)\le
\frac{\bigl[\frac L2\log(1+E/L)+C+2D\log T\bigr]/(2\pi)-Z_M}
{\alpha-\ell}.}
\]
The moment is on the selected line ℓ, with the same mollifier parameters and outward endpoints. It remains an explicit premise. Required integrability and boundary nonvanishing are discharged by the construction. The full mollifier-zero remainder is subtracted.

## Revised research agenda

| Obligation | Status and acceptance criterion |
| --- | --- |
| Compatible branches and outward closed-window coverage | Proved and retained |
| Signed right integral for the same nonstandard mollifier | Discharged by the uniform provider |
| Left edge inside a prescribed interval | Proved for any 1/2≤a<c≤α<b |
| Actual uniform mollified second moment | **Open.** Prove the uncentered moment for the same σ,y,ε family, uniformly on a selected left interval and the outward height windows. |
| A moment available only on a different prescribed line | **Open if needed.** Prove a neighborhood estimate or a justified limiting passage; selectable intervals alone do not permit changing the line. |
| Full arithmetic error | **Open.** Retain diagonal, off-diagonal, cutoff and endpoint terms, then prove the required decay. |
| Complete and multilinear Kloosterman estimates | **Open.** Supply their exact uniform arithmetic hypotheses in the actual moment argument. |
| Global density function and Ingham assembly | **Open.** Identify the finite multiplicity sum with the repository counting conventions and provide the remaining estimates. |
| RH-level zero exclusion or residual vanishing | **Open.** The finite boundary estimates do not force the count to vanish. |

Priority 1 is the actual uncentered moment on a selectable left interval. Choose the interval from the intended analytic theorem before invoking the new dyadic result. Coefficient normalization and right decay do not control the critical-strip off-diagonal moment.

Priority 2 is quantitative arithmetic error control. Use `exists_strict_error_budget` only after proving the corresponding analytic bounds, and keep the cutoff exponent and error-loss parameters distinct.

Priority 3 is density assembly and a separate RH-level forcing step. Even E=0 leaves the horizontal O(log T) budget and positive right-bound constant in the displayed upper bound unless further signed cancellation or remainder information is supplied. A small moment alone does not force all zero counts to vanish.

## Verification and resumption

The focused check of the combined right-boundary, selectable-rectangle, and conditional-count modules passed with Bazel/BuildBuddy: `job_S3tnOR-1IiT5jQ0m7mKakmtSK7bKA7nN`, 45.731 seconds of server verification, [BuildBuddy](https://app.buildbuddy.io/invocation/8bdcca11-d382-4c38-a920-a6f8e6b585ad). The final guard check also includes the subsequent removal of the redundant rightmost zero-coverage hypothesis.

Eight final standard-axiom guards passed: `job_9nc_Q5inRIPHiLixoLKz7YgNzAUuK6VR`, 29.971 seconds of server verification, [BuildBuddy](https://app.buildbuddy.io/invocation/d64439ca-441b-45c2-aeed-154fc2d0cab8). Every guarded result depends only on `propext`, `Classical.choice`, and `Quot.sound`. This check imports the final dyadic module and its transitive dependencies, including full rightward zero coverage.

Publication requires the managed full-project Bazel/BuildBuddy checkpoint `//:RiemannResearch`. Its terminal job and published commit are reported at completion. Axiom guards inspect dependencies; they do not discharge moment premises.

Retained workspace: `ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2`.
Project root: `/home/cri_2025/lean-agent-workspaces/ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2/RiemannResearch`.

Resume from the commit containing this catalog, compare with current main, and keep one queued or running verification per workspace. The next analytic target is the actual uncentered mollified second moment at admissible left boundaries.
