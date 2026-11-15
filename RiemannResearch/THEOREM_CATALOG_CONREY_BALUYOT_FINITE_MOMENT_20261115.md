# Conrey–Baluyot finite moments and prescribed-line transfer — 15 November 2026

Starting published checkpoint: [0ae685c9dfc5ab72a9791d16b915a17e42d8ef7a](https://github.com/Cnoack3/RiemannResearch/commit/0ae685c9dfc5ab72a9791d16b915a17e42d8ef7a).
Current main matched that checkpoint when this continuation began.

The exact finite twisted moment is now formalized for the actual nonstandard mollifier.
Two technical obstacles in the right-boundary handoff are removed: outward endpoint
strips can be made arbitrarily inexpensive, and a moment bound on one prescribed
evaluation line transfers to a selectable interval with arbitrary positive slack.
The combined count is a **conditional research reduction**: the central moment
itself and the substantive arithmetic estimates remain open in Lean. RH is not proved.

## Established identities and transfer lemmas

Unless prefixed by `Complex`, declarations are in
`RiemannResearch.Analysis.ConreyBaluyot`.

| Declaration | File in Analysis/ | Content |
| --- | --- | --- |
| `Complex.integral_finite_sum_norm_sq` | `FiniteTwistedMoment.lean` | Exact complex-valued finite twisted Gram identity for a continuous weight on a finite interval. |
| `Complex.integral_finite_sum_norm_sq_diagonal` | same | Exact diagonal plus complete signed off-diagonal. |
| `mollifiedZeta_secondMoment_eq_twisted_coefficients` | `ConreyBaluyotTwistedMoment.lean` | The handoff's precise finite expansion for the actual coefficients and exact floor cutoff. |
| `mollifiedZeta_secondMoment_eq_diagonal_add` | same | Explicit diagonal and signed off-diagonal, with positive heights. |
| `mollifiedZeta_secondMoment_le_iff_offDiagonal` | same | Exact equivalence identifying the required signed aggregate estimate. It supplies no arithmetic bound. |
| `mollifiedSecondMoment_outward_identity` | `ConreyBaluyotMomentEndpoints.lean` | Exact central interval plus both outward strips. |
| `exists_uniform_mollifiedSecondMoment_endpoint_transfer` | same | Any positive endpoint budget is achievable by choosing a sufficiently small positive outward width, uniformly over the admitted sigma and evaluation lines. |
| `continuous_mollifiedSecondMoment_line` | `ConreyBaluyotMomentContinuity.lean` | Continuity in the evaluation line with all mollifier parameters and positive endpoints fixed. |
| `exists_mollifiedSecondMoment_admissible_interval` | same | Prescribed-line moment transfers with arbitrary slack to an open interval and preserves half the counting gap. |

## Exact finite expansion

Write
\[
N=\lfloor y^{1+\varepsilon}\rfloor,\quad
a_n=\mathrm{mollifierCoefficient}(\sigma,y,n),\quad
F(s)=\zeta(s)M_{\sigma,y,\varepsilon}(s),
\]
and
\[
J_{\ell;u,v}(q)=\int_u^v|\zeta(\ell+it)|^2e^{itq}\,dt.
\]
For every real evaluation line \(\ell\) and \(0<u\le v\), the formal theorem gives
\[
\left(\int_u^v|F(\ell+it)|^2\,dt:\mathbb C\right)
=
\sum_{m=1}^{N}\sum_{n=1}^{N}
a_m\overline{a_n}(mn)^{-\ell}
J_{\ell;u,v}(\log n-\log m).
\]
This is stronger than taking only the real part: the entire double sum is exactly real.
There is no infinite series interchange, moment asymptotic, RH hypothesis or
coefficient normalization assumption. The Lean totalized coefficient definitions
are used literally, even outside the useful normalized parameter strip.

With
\[
\mathcal D=
\left(\sum_{n=1}^{N}|a_n|^2n^{-2\ell}\right)
\int_u^v|\zeta(\ell+it)|^2\,dt,
\]
and \(\mathcal O\) the full sum over \(m\ne n\), the second moment is
\(\mathcal D+\Re\mathcal O\). Thus the exact remaining target is
\[
\int_u^v|F(\ell+it)|^2dt\le(v-u)+E
\quad\Longleftrightarrow\quad
\Re\mathcal O\le(v-u)+E-\mathcal D.
\]
The off-diagonal can contain main-order cancellation; a small absolute bound
for each summand is not interchangeable with this signed aggregate target.

## Outward endpoints with any positive budget

The primary identity retains the two strips:
\[
\mathcal M(u,v)=\mathcal M(u,T)+\mathcal M(T,2T)+\mathcal M(2T,v).
\]
The already proved growth provider yields a constant \(K>0\) and the usual
coupled sigma strip. For \(T\ge2\), \(y\ge Y\), \(\ell\ge1/4\), put
\[
B=K(2T+1)y^{1+\varepsilon},\qquad
\delta=\min\left\{\frac14,\frac{\kappa}{2(B^2+1)}\right\}>0.
\]
For every \(u\in[T-\delta,T]\) and
\(v\in[2T,2T+\delta]\), both endpoint strips together cost at most
\(2\delta B^2\le\kappa\). Consequently
\[
\mathcal M(T,2T)\le T+E
\quad\Longrightarrow\quad
\mathcal M(u,v)\le(v-u)+E+\kappa.
\]
The width is selected after \(T,y,\kappa\), before sigma, the evaluation
line, endpoints or central moment error. No claim is made for a width fixed
independently of the growing mollifier.

## Moving the evaluation line

For fixed \(\sigma,y,\varepsilon,u,v\), with \(0<u\le v\), the actual
moment is continuous in \(\ell\). One proof extends the integrand to all
real t by replacing t by \(\max(u,t)\), which keeps the zeta argument away
from its pole and agrees with the original integrand on the integration interval.

Given \(1/2<\ell_0<\alpha\), a moment bound on \(\ell_0\) and any
\(\kappa>0\), there exist
\[
\frac12<a<\ell_0<c<\alpha,\qquad
\alpha-c\ge\frac{\alpha-\ell_0}{2},
\]
on which the moment bound holds with added error \(\kappa\).
The neighborhood may depend on all fixed parameters. This is not a uniform
modulus of continuity as T or y grows. It suffices because the rectangle
selection theorem allows its left interval to be chosen after those parameters.

## Conditional research reduction: a moment on one prescribed line

`exists_uniform_dyadic_count_of_prescribed_line_moment` in
`Analysis/ConreyBaluyotMomentCount.lean` combines the two transfers with
the existing normalized dyadic Littlewood theorem.

For each \(\varepsilon\ge0\) and \(\theta>0\), constants
\(\eta,b,D,C,H\) are chosen before T and sigma. For \(T\ge H\),
the coupled sigma strip, \(1/2<\ell_0<\alpha<b\), \(E\ge0\) and
\(\kappa>0\), its sole substantive moment premise is
\[
\int_T^{2T}|\zeta(\ell_0+it)M_{\sigma,T^\theta,\varepsilon}(\ell_0+it)|^2dt
\le T+E.
\]
In particular \(\ell_0=\sigma\) is permitted whenever the displayed inequalities hold.

The conclusion constructs outward endpoints, a zero-free left line, the exact
product-zero set, normalized compatible logarithm lifts, and
\[
\alpha-\ell\ge\frac{\alpha-\ell_0}{2}.
\]
It retains
\[
I_\ell-I_b+A_U-A_B=2\pi(Z_\zeta+Z_M),\qquad Z_M\ge0,
\]
the signed horizontal difference bound, signed right bound, and coverage of
every zeta zero in the full closed rightward dyadic window.
Writing \(L=t_2-t_1\), it proves
\[
\mathcal M(\ell;t_1,t_2)\le L+E+\kappa
\]
and
\[
N_Z(\alpha;T,2T)\le
\frac{\bigl[\frac L2\log(1+(E+\kappa)/L)+C+2D\log T\bigr]/(2\pi)-Z_M}
{\alpha-\ell}.
\]
Half the slack is used for the line neighborhood and half for the outward strips.
No moment provider is asserted by this conditional theorem.

## Revised research agenda

| Priority | Obligation | Status and acceptance |
| --- | --- | --- |
| Completed | Exact finite twisted expansion | Proved for actual coefficients, exact cutoff and distinct mollifier/evaluation parameters. |
| Completed | Outward endpoint moment transfer | Proved with any positive tolerance and an adaptive width. |
| Completed | Prescribed line to selectable interval | Proved with arbitrary slack and a protected denominator; no uniform modulus claimed. |
| 1 | Actual central mollified second moment | **Open in Lean.** Prove \(\mathcal M_{\sigma,y,\varepsilon}(\sigma;T,2T)\le T+E\), uniformly on the coupled strip, with the actual cutoff and a quantified E. A separate neighborhood or outward moment provider is no longer required. |
| 2 | Signed aggregate twisted estimate | **Open.** Prove the exact off-diagonal inequality above, or derive the actual smoothed moment retaining all main terms and remainders. |
| 3 | Complete and multilinear Kloosterman inputs | **Open.** Connect the exact arithmetic hypotheses to this family and prove their uniform bounds. A finite completion identity alone is not the needed bound. |
| 4 | Parameter/error assembly | **Open.** Only after proving analytic errors, apply \(\theta<4/7\) parameter algebra with cutoff and independent loss parameters kept distinct. |
| 5 | Global density and Ingham counting interface | **Open.** Match closed-window boundaries, analytic multiplicities and dyadic conventions to the global repository counters. |
| 6 | RH-level forcing | **Open.** A fixed density exponent or a finite boundary budget does not eliminate every zero. Even zero central excess leaves the right/horizontal budgets unless stronger signed information is proved. |

The source's next analytic route is Baluyot's thesis, Section 3.3:
Gaussian smoothing (3.3.1)-(3.3.5), followed by the complete decomposition
\(g=M_1+M_2+D_1+D_2+E\) in (3.3.8)-(3.3.16).
Section 3.4 estimates the arithmetic errors. This is primary-source guidance,
not a Lean provider. In particular its gcd main terms involve off-diagonal
mollifier pairs and must not be confused with only m=n in the elementary expansion.

Source: [Baluyot (2017), On the Zeros of Riemann's Zeta-function](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320).
The reference supports the conventions and analytic strategy, not a novelty claim.
Wolfram independently simplified the difference between the two phase-product
forms to zero. That computation supports the sign check and is not a proof certificate.

## Verification and continuation

The first focused continuity/endpoint candidate passed Bazel/BuildBuddy in
62.500 seconds of server verification:
`job_BVLa1_w1YWUE4LuiH5s4dh-RPRpcR2v2`,
[invocation](https://app.buildbuddy.io/invocation/3636cc39-2bef-4f8a-b780-d148bb44a069).
The final focused guard check imported all five final modules and passed nine
standard-axiom guards in 22.633 seconds of server verification:
`job_SK_6YsAYTXA7qsJe5Va5dIa-IKR5TYmV`,
[invocation](https://app.buildbuddy.io/invocation/0b28c350-72be-4736-b29d-2fcd0dd5dcec).
Every guarded declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`. These checks do not discharge the central moment premise.

The managed full-project checkpoint targets `//:RiemannResearch`; its terminal
job, integrated validation and published commit are reported in the completion record.
A separate coupling-variance update reached main during this continuation and must
be preserved by the managed integration gate.

Workspace token: `ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2/RiemannResearch`.

Resume from the commit containing this catalog, compare with newer main and
retain one verification per workspace. Do not reopen the right-boundary,
line-neighborhood or adaptive-endpoint transfers as assumptions. The next
substantive target is the central moment, with its full signed arithmetic error.
