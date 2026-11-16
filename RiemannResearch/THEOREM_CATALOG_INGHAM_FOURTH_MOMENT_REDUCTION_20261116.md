# Ingham I1: divisor energy, actual residual, and fourth-moment transfer

Prepared 16 November 2026 (America/Los_Angeles).

Investigation base: `8db47ed43c4ffd5fffff3b69319f21c3a1bc0e28`.
Mathlib dependency: `51e6992efd06126df61a496bebf8f49482a4e129`
(`v4.33.0-rc2`). The user approved publication of this verified continuation
on 16 November 2026. The managed checkpoint records validation, integration,
and publication.

## Status

**Current status:** [the completed uniform remainder proof](THEOREM_CATALOG_ZETA_REMAINDER_BOUND_20261116.md) supplies I1 unconditionally and
proves the actual mixed mollifier four-thirds moment with a squared logarithm.
The paragraphs and research route below describe this earlier reduction's
original scope; its conditional consumers now have actual providers.

**The classical actual-zeta fourth-moment bound I1 is not proved by this
continuation.** The arithmetic logarithmic-energy input is proved, as are
the finite-polynomial mean values and the exact transfer to the existing
Ingham critical-error consumer. The uniform bound on the actual analytic
residual remains an explicit hypothesis.

The formal results do not assume RH, a zero-density estimate, or I1 in order
to prove the divisor bounds. A conditional theorem taking a residual or
fourth-moment estimate as input is not an unconditional provider of that input.

The subsequent [dyadic and L2 continuation](THEOREM_CATALOG_INGHAM_DYADIC_L2_20261116.md)
closes the dyadic-to-global assembly and the actual critical-line phase
conditions, proves finite smoothing and damped-shell estimates, and replaces
the factor-three residual transfer by its sharper L2 form. The later canonical
criterion needs only a uniform actual residual bound on `[U,2U]`. The infinite
tail limit and complete Mellin/contour estimates have now been supplied in
the completed remainder continuation. The detailed agenda below records
the initial state before those later providers.

## Proposed changes

| File | Responsibility |
| --- | --- |
| [Analysis/DivisorCoefficientEnergy.lean](Analysis/DivisorCoefficientEnergy.lean) | Reciprocal convolution, `d(n)^2 <= d_4(n)`, and harmonic fourth-power energy |
| [Analysis/DivisorPolynomialMoment.lean](Analysis/DivisorPolynomialMoment.lean) | Actual divisor coefficients, signed identity, bounded weights, finite exponential smoothing |
| [Analysis/ActualZetaFourthMomentReduction.lean](Analysis/ActualZetaFourthMomentReduction.lean) | Exact actual-zeta residual, conditional uniform fourth moment, and Ingham consumer |
| `../RiemannResearch.lean` | Three new module exports beside the existing Ingham imports |
| This catalog | Evidence, exact hypotheses, and continuation route |

No existing theorem statement is weakened or replaced. Existing I2 remains
the actual unconditional finite Mobius-mollifier result.

## Audit and reuse

Bounded declaration/filename searches and focused source reads found no
complete actual-zeta fourth-moment provider in the inspected repository
snapshot. This is not an exhaustive claim about every Lean repository.

The development reuses:

- Mathlib's arithmetic convolution, multiplicativity, prime-power divisor
  formulas, `sum_Ioc_mul_eq_sum_prod_filter`, and harmonic upper bound.
- `dirichlet_polynomial_second_moment_window_le` and
  `Complex.integral_finite_sum_norm_sq_diagonal`.
- `InghamMollifier.continuous_critical_zeta` and
  `InghamMollifier.critical_error_moment_le_fourth_moment`.

The pinned Mathlib `LSeries/RiemannZeta.lean` provides the ordinary functional
equation and the Dirichlet series in `Re(s)>1`;
`LSeries/Convolution.lean` provides multiplication of absolutely convergent
L-series. These should be reused for the zeta-square series rather than
reproved. They do not supply the required critical-line approximation.

The repository's recent Estermann work was also inspected. In particular,
`rectangleIntegral_estermannMellinKernel_diagonal` proves a finite contour
identity at the diagonal parameters `alpha=beta=0`.
`finite_estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound`
still takes tail bounds as input. The moving collision at `1-s`, and constants
uniform in the outer height, are not discharged by citing those declarations.

## Unconditional arithmetic and polynomial results

Write `d(n) = ArithmeticFunction.sigma 0 n`, and
`H_N = sum_{1 <= n <= N} 1/n`. The new arithmetic namespace is
`ArithmeticFunction`.

| Declaration | Exact result |
| --- | --- |
| `reciprocalWeight_mul` | Dividing coefficients by `n` commutes with Dirichlet convolution |
| `sum_reciprocal_mul_eq` | Exact finite product sum with the constraint `ab <= N` retained |
| `sum_reciprocal_mul_le` | The hyperbolic sum is bounded by the product of the two finite reciprocal sums |
| `sigma_zero_sq_le_convolution` | `d(n)^2 <= (d*d)(n)` for all natural `n` |
| `sum_sigma_zero_sq_div_le_harmonic_four` | `sum d(n)^2/n <= H_N^4` |
| `sum_sigma_zero_sq_div_le_log_four` | `sum d(n)^2/n <= (1+log N)^4` |

The prime-power proof uses
`(j+1)(k-j+1) >= k+1` for `0 <= j <= k`, then multiplicativity.
Two applications of the reciprocal convolution bound give the fourth
power of the harmonic sum. No asymptotic divisor summatory formula is used.

Set

\[
 K=12\sqrt{2\pi}\,e^{1/2},\qquad
 P_{N,w}(t)=\sum_{n=1}^{N}w_n d(n)n^{-1/2-it}.
\]

In namespace `RiemannResearch.Analysis`, the exact coefficient identity is
`criticalDivisorCoefficient_norm_sq`, and
`divisorPolynomial_second_moment_identity` retains the full signed
off-diagonal interval expression. The upper bound is

\[
 \int_H^T |P_{N,w}(t)|^2\,dt
 \le K(T-H+N)(1+\log N)^4
 \quad(H\le T,\ N\ge1,\ |w_n|\le1).
\]

`divisorPolynomial_second_moment_le` proves this with the same constant for
every interval, cutoff, and admissible coefficient sequence. Weights may
depend on the outer parameters but are fixed while integrating in `t`.
`damped_divisorPolynomial_second_moment_le` specializes to
`w_n=exp(-n/Y)` for every `Y>0`, independently of `N`.
The statement is finite: it does not justify sending `N` to infinity with
the same right-hand side.

## Exact actual residual and conditional I1

For continuous functions `P,Q : real -> complex`, define the actual residual

\[
 R(t)=\zeta(1/2+it)^2-P(t)-Q(t).
\]

`zeta_fourth_power_residual_identity` proves the complete equality

\[
 |\zeta|^4=|P|^2+|Q|^2+|R|^2+
 2\Re(P\overline Q)+2\Re(P\overline R)+2\Re(Q\overline R).
\]

`zeta_fourth_moment_le_residual` consequently bounds the integral by three
times the sum of the three square moments. The residual is defined from
the actual `riemannZeta`, not supplied as an unrelated arbitrary error.
This definition alone provides no smallness estimate.

For `P=P_{N,u}` and `Q=phi*conj(P_{N,v})`, the checked polynomial bound
applies when `phi` is continuous and `|phi(t)|<=1` on the interval.
`zeta_fourth_moment_le_two_divisor_polynomials` gives

\[
 \int_H^T|\zeta|^4\le
 3\left(2K(T-H+N)(1+\log N)^4+\int_H^T|R|^2\right).
\]

For `2<=T` and `1<=N<=T`, `cutoff_log_four_cost_le` proves
`K(T+N)(1+log N)^4 <= 162 K T (log T)^4`. Thus
`zeta_fourth_moment_le_of_residual_bound` proves that the explicit premise

\[
 \int_0^T|R(t)|^2\,dt\le C_R T(\log T)^4
\]

implies I1 at that height with constant

\[
 C=3(324K+C_R).
\]

`exists_fourth_moment_bound_of_uniform_residual` handles the quantifiers:
fix `H_0>=2`, `C_R>=0`, a continuous bounded phase, and bounded weights
`u(T,n),v(T,n)`. If every `T>=H_0` admits `1<=N<=T` with the displayed
actual-residual estimate using that same `C_R`, then there is one `C>0`
valid for all `T>=H_0`. These phase, weight, and residual hypotheses are
visible in the theorem type. In particular the uniform residual provider
is still **Open**.

## Historical analytic route to the provider (now completed)

The classical target and Mellin strategy are supported by
[Chourasiya--Simonic, Section 5.1](https://arxiv.org/html/2507.15184v2).
The following formulas are the proposed next analytic work, not newly
checked Lean declarations. Fix `s=1/2+it`, `Y>0`, `N=floor(Y)`,
`c_-=-3/4`, `c_+=1/4`. With upward vertical contours, put

\[
 D_{\le N}(w)=\sum_{n\le N}d(n)n^{-w},\quad
 D_{>N}(w)=\sum_{n>N}d(n)n^{-w},\quad
 S_Y(s)=\sum_{n\ge1}d(n)n^{-s}e^{-n/Y}.
\]

Mellin inversion and the first shift should establish

\[
 S_Y(s)=\frac1{2\pi i}\int_{(2)}\zeta(s+z)^2\Gamma(z)Y^z\,dz
 =\zeta(s)^2+\mathcal P_Y(s)+
 \frac1{2\pi i}\int_{(c_-)}\zeta(s+z)^2\Gamma(z)Y^z\,dz,
\]

\[
 \mathcal P_Y(s)=Y^{1-s}\bigl(\Gamma'(1-s)+
                 (\log Y+2\gamma)\Gamma(1-s)\bigr).
\]

Here the crossed poles are `z=0` and the double pole `z=1-s`.
Use the functional equation, then shift only the finite head to `c_+`:

\[
 I_-(s)=\frac1{2\pi i}\int_{(c_-)}
 \chi(s+z)^2\Gamma(z)Y^zD_{>N}(1-s-z)\,dz,
\]
\[
 I_+(s)=\frac1{2\pi i}\int_{(c_+)}
 \chi(s+z)^2\Gamma(z)Y^zD_{\le N}(1-s-z)\,dz.
\]

The required exact identity is

\[
 \zeta(s)^2=D_{\le N}(s)+\chi(s)^2D_{\le N}(1-s)+R_Y(s),
\]
\[
 R_Y(s)=\sum_{n>N}d(n)n^{-s}e^{-n/Y}
       +\sum_{n\le N}d(n)n^{-s}(e^{-n/Y}-1)
       -\mathcal P_Y(s)-I_-(s)-I_+(s).
\]

The head shift crosses only the Gamma pole at zero; its orientation gives
the positive reflected polynomial above. Every horizontal side, vertical
tail, interchange, residue, and integrability condition still needs proof.

### Parameter and logarithm bookkeeping for the next proof

The following is our proposed upper-bound strategy, using the newly proved
energy estimate. It seeks only the correct logarithmic degree, not the
classical asymptotic main term or a log-cubed error.

Work first on `[U,2U]`, with `Y=U`, `N=floor(U)`, and `U>=2`. Both main
polynomials have length at most the interval length. The actual phase is
`phi(t)=chi(1/2+it)^2`; its modulus-one and continuity facts must be connected
to the existing functional-equation API.

Two existing Gamma ingredients should be reused:
`Complex.exists_gamma_mul_cpow_neg_strip_pow_bound` in
`DampedGammaStripBounds.lean` provides arbitrary inverse-power decay on
fixed strips, and `GammaRatioVertical.norm_Gamma_ratio_le` supplies a
quotient bound for `0<a<=b<=1`, `|v|>=1/2`.
For uniformity in `Y`, apply the former with damping `lam=1` and retain
`Y^c` separately; its constants otherwise may depend on the damping.
The quotient theorem still needs recurrence, conjugation, and compact-range
assembly to give the exact bounds on `chi` required here.

For the arithmetic tails, split into shells `2^j U < n <= 2^(j+1) U`.
The finite-polynomial theorem and the new energy bound supply an L2 norm
cost at most a constant times

\[
 U^{1/2}\,2^{j/2}(1+j)^2(\log U)^2
\]

before damping. Exponential damping supplies `exp(-2^j)` and makes the
sum of these shell costs finite. All triangle inequalities must be used
in L2 before squaring. Prove the finite-shell bounds first, then the
summability and limit passage; pointwise convergence alone is insufficient.

On the central contour region `|Im z|<=U/2`, write `z=c+iv` and note that
`|t+v|` lies between `U/2` and `5U/2`. Uniform estimates for `chi` give
`|Y^z chi(s+z)^2| <= A_c U^(-c)` for fixed `c`.
For the tail on `c_-=-3/4`, the coefficient `n^c` adds a shell factor
`2^(cj) U^c`. The remaining exponent is `c+1/2=-1/4`, so its L2 shell sum
converges. For the finite head on `c_+=1/4`, `n^c<=U^c`, canceling the
factor `U^(-c)`. An L1 bound for `Gamma(c+iv)` then supplies a height-independent
constant via Minkowski. The oscillatory factors `n^(iv)` have modulus one
and therefore fit the coefficient-weight theorem.

Outside `|v|<=U/2`, the above comparison for `|t+v|` is unavailable.
This region includes `v` close to `-t`. It must be estimated separately
with sufficiently high inverse-power Gamma decay and uniform bounds on `chi`,
retaining the full integrals.
The moving double-pole term likewise requires Gamma and Gamma-derivative
bounds at `1/2-it`. The existing Gamma ingredients have not yet been
assembled into these complete uniform remainder estimates.

Give each of the five displayed pieces of `R_Y` an L2 bound
`B_j sqrt(U) (log U)^2`. Then
`integral_[U,2U] |R_Y|^2 <= (sum B_j)^2 U (log U)^4`, with a constant
independent of `U`. This is enough for the upper-bound problem.
Finally sum dyadic windows and absorb the finite initial interval using
continuity. That assembly is a separate step: the checked uniform residual
criterion above currently asks for a bound on `[0,T]`, not merely one dyadic
window. No extra factor of `log T` may be introduced by replacing the
geometrically decreasing window lengths with a uniform length bound.

## What the Ingham connection discharges

`InghamMollifier.critical_error_moment_le_of_fourth_moment_bound` proves,
for `X>=1` and `0<=H<=T`, that any supplied bound
`integral_[0,T] |zeta|^4 <= C T(log T)^4` gives

\[
 \int_H^T|\zeta(1/2+it)M_X(1/2+it)-1|^{4/3}\,dt
 \le 2^{1/3}\left[
 (CT(\log T)^4)^{1/3}
 \bigl(K(T-H+X)(1+\log X)\bigr)^{2/3}+T-H\right].
\]

The proof derives the needed subinterval fourth-moment bound from `[0,T]`
using nonnegativity and the proved continuity of actual zeta.

| Obligation | Current status, including the completed remainder continuation |
| --- | --- |
| Divisor coefficient energy with fourth logarithmic power | Proved |
| Finite weighted divisor-polynomial mean value | Proved |
| Actual zeta-square smoothed representation with uniform remainder | Proved in the completed remainder continuation |
| I1 actual fourth-moment provider | Proved by `exists_actual_zeta_fourth_moment_bound` |
| I2 actual mollifier second moment | Already proved; reused |
| Substitution of I1 into the actual critical-error inequality | Unconditional `exists_actual_critical_error_moment_log_bound` now supplied |
| Moving right-line error moment, Gabriel interpolation, and boundary/counting assembly | Unchanged |
| Independent near-line Selberg estimate and Z03 | Unchanged; not closed |

## Verification and publication

Focused Bazel/BuildBuddy acceptance passed for
`//RiemannResearch/Analysis:ActualZetaFourthMomentReduction` and its imports:
job `job_In5927jSrABMldzyDZKRMTXnXuL9kwV8`, reported server time 21.945 seconds,
[log](https://app.buildbuddy.io/invocation/49c72d83-45f1-4fbf-b76a-f07a13ae580c).
The subsequent source change only makes direct imports explicit.

Six explicit axiom guards passed on the final Lean sources, including the
direct-import cleanup: `job_FVgTUytj2zUtVYIoCz413Nij_Ia9rmPj`, reported
server time 45.430 seconds,
[log](https://app.buildbuddy.io/invocation/1545c1ae-d0bd-4d41-9a0a-b9a2bec45a09).
They require exactly `propext`, `Classical.choice`, and `Quot.sound` for
the divisor-square majorant, logarithmic energy bound, polynomial moment,
exact residual identity, uniform conditional fourth moment, and Ingham
consumer. No placeholders or project-specific axioms were added.
Axiom guards do not discharge assumptions appearing in theorem types.

Full-project Bazel/BuildBuddy validation passed for `//:RiemannResearch`,
including the three exports and all project source modules:
`job_WaA9YMzav0GBND9EmI3_mXshYi2g3ZAo`, reported server time 213.268 seconds,
[log](https://app.buildbuddy.io/invocation/bfae0d1d-165d-448d-a376-cd1bedc62e18).
The validated source is the uncommitted delta based on `8db47ed4`, not a
new published Git commit. Only this documentation was updated afterward.
These durations are server verification times, not end-to-end task times.

Final Lean source SHA-256 digests:

| Module | SHA-256 |
| --- | --- |
| `DivisorCoefficientEnergy.lean` | `a1d1cf54311c073e571f64bf4f418a0e4bca0192ad2c6eedaf3d3f5965ddc4e8` |
| `DivisorPolynomialMoment.lean` | `5af184b325779798060069deac6494a3e1af2041bc32b7d8ee07a2df55195013` |
| `ActualZetaFourthMomentReduction.lean` | `91885ed6bd188a751953e2caa27dcedf75715a06ec62b98bc882a5f6d2502969` |

The user approved committing and publishing these changes on 16 November 2026.
Use the managed checkpoint record for the publication commit and validation
of any integration with newer main.
