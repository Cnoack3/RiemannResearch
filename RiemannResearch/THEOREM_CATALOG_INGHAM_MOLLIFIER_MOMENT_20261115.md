# Ingham continuation: the actual mollifier second moment

Date: 2026-11-15 (Pacific). Investigation base:
`0b6554aad967f5135202b8b65d0a98f33e64a57c`.

Consumer: obligation I2 in the attached Ingham/Z03 continuation, and
`InghamMollifier.critical_error_moment_le`.

## Result

The actual finite Mobius mollifier now has an unconditional bound with one
explicit constant independent of both parameters. For every integer X >= 1
and every real T >= 0,
\[
\int_0^T |M_X(1/2+it)|^2\,dt
\le 36\sqrt{2\pi}\,e^{1/2}(T+X)\log(2X).
\]
Thus the proposed I2 target for X >= 2 and T >= 2 is discharged, with no
analytic-provider premise, density assumption, or arithmetic conjecture.

The sharper bound, valid on every real interval [H,T] with H <= T, is
\[
\int_H^T |M_X(1/2+it)|^2\,dt
\le 12\sqrt{2\pi}\,e^{1/2}(T-H+X)(1+\log X).
\]

Namespace prefix, except for the generic Complex and Real lemmas:
`RiemannResearch.Analysis.`.

| Declaration | File | Meaning |
| --- | --- | --- |
| `Complex.integral_exp_sum_gaussian_identity` | `Analysis/ComplexGaussianMeanValue.lean` | Exact full coefficient-weighted Gaussian double sum |
| `Complex.integral_exp_sum_gaussian_le` | same | General Schur estimate with an explicit row premise |
| `Real.abs_sub_le_mul_abs_log_sub_of_le` | `Analysis/DirichletPolynomialMeanValue.lean` | Log-frequency separation on a bounded positive interval |
| `gaussian_log_row_le` | same | Actual log-frequency Gaussian rows bounded by 6 |
| `dirichlet_polynomial_second_moment_window_le` | same | Translation-uniform finite Dirichlet-polynomial mean value for arbitrary complex coefficients |
| `InghamMollifier.mollifier_second_moment_identity` | `Analysis/ActualInghamMollifierMoment.lean` | Exact interval diagonal plus signed off-diagonal identity |
| `InghamMollifier.mollifier_second_moment_log_two_mul_le` | same | Explicit actual-mollifier bound above |
| `InghamMollifier.exists_mollifier_second_moment_bound` | same | The existential I2 acceptance target |
| `InghamMollifier.mollifier_second_moment_window_le` | same | Every real H <= T, with cost (T-H+X)(1+log X) |
| `InghamMollifier.critical_error_moment_le_fourth_moment` | same | Existing mixed-moment step with the mollifier input discharged |

## Proof and exact identities

Write a_n = mu(n) exp(-log(n)/2). The ordinary interval identity retains
the diagonal T sum |a_n|^2 and every signed term in
`Complex.finiteTwistedOffDiagonal`. The estimates do not replace that identity.

For the estimate use the centered Gaussian with variance L^2, L = T + 2X.
Its density is at least exp(-1/2)/(sqrt(2 pi) L) on [0,T].
The exact Gaussian mean has kernel
exp(-L^2(log m-log n)^2/2). The elementary inequality
|m-n| <= X |log m-log n| bounds this kernel by the existing summable
integer-cell envelope, whose row mass is at most 6. The full weighted
Schur estimate gives a bound by 6 sum |a_n|^2. Finally,
sum |a_n|^2 <= harmonic(X) <= 1 + log X <= 3 log(2X).

The generic Schur theorem has a row hypothesis; the Dirichlet application
proves that hypothesis. No such premise remains in the actual I2 provider.
All Gaussian integrability and interval comparisons are proved.

The critical error theorem now bounds the 4/3 moment using only the actual
zeta fourth-moment integral and the displayed explicit expression, together
with the original interval-length term T-H. It does not assume or prove the
asymptotic zeta fourth moment.

## Updated obligations

| ID | Status after this continuation |
| --- | --- |
| I1 | Open: actual zeta fourth moment, uniformly O(T (log T)^4) |
| I2 | Proved: actual Mobius mollifier, uniformly O((T+X) log(2X)) |
| I3 | Open: moving right-line error moment with the required parameter dependence |
| I4 | Open: applicable Gabriel interpolation theorem |
| I5 | Open integration task: matching actual boundaries and counting |
| I6 | Open: unconditional provider for the existing InghamDensityBound |
| Z1 | Open: the separate truncated near-line Selberg excess estimate |
| Z2 / Z03 | Not closed; blocked by I6 and Z1 |

The focused declaration and filename audit found no reusable actual-zeta
fourth-moment theorem or approximate-functional-equation module at the base
commit. This is an audit finding, not a claim about mathematical possibility.
For I1, the new finite-polynomial theorem provides a mean-value input; an
actual zeta-squared representation and quantitatively controlled remainder
are still required. The source's Section 5.1 describes the smoothed divisor
series, Mellin identity, and contour shift used in Ramachandra's approach.
Prove those analytic steps and the needed divisor-sum estimates before
claiming I1. Keep all contour and tail terms explicit.

Neither global Ingham density, UniformSelbergDensity (1/4), nor RH is proved
by this continuation.

## Provenance and verification

The requested target and continuation order come from the uploaded
`Ingham_Z03_Remaining_Obligations_2026-11-16(1).md`.
Chourasiya and Simonic,
\[An explicit form of Ingham's zero density estimate](https://arxiv.org/html/2507.15184v2),
supports the analytic target and subsequent agenda. The Gaussian proof here
uses Mathlib's actual Gaussian characteristic function and the repository's
checked integer-cell envelope. It is not presented as a new mathematical
mean-value theorem.

Wolfram independently reproduced the Gaussian Fourier normalization during
exploration; that computation is not a Lean premise. Kernel proofs provide
acceptance. All new modules are exported and use the existing Analysis
Bazel package. The managed checkpoint validates the full project before
publication. Only ordinary foundational axioms are allowed in the principal
declaration audit; theorem hypotheses must also be read separately.

Focused module acceptance passed in job
`job_ycv0akFMaNCaJ1cP4pskvHTVud47HzyI`, with a reported server verification
duration of 93.874 seconds, including the new modules and their transitive
imports. [BuildBuddy log](https://app.buildbuddy.io/invocation/c37d6bff-5b66-4fc1-9f5e-5eb63787dbe4).
This is distinct from the final full-project checkpoint and from workspace
setup, network, or polling time.

Five explicit axiom guards passed in
`job_M9CHuLaEl50IOmp0mZVT5eGCdgwDTzXd` (43.684 server seconds):
the Gaussian identity, translated general mean value, actual signed interval
identity, existential I2 provider, and mixed-moment consumer.
The guards require exactly `propext`, `Classical.choice`, and `Quot.sound`.
[Guard log](https://app.buildbuddy.io/invocation/0a1dab58-e14f-47a8-b11a-59f588ef19de).
