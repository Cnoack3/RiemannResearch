# Ingham continuation: mixed moments, a sharp fixed strip, and an actual thin strip

Date: 2026-11-15. Investigation base: `f1df51cb44c3b28bd0087864c316c8915271cef4`.
Integration base: `ac85bee98c61d52bb7865e010acab73ee988360a`.
Consumer: the Ingham input to the actual Selberg/Z03 density assembly.

## Status

Ingham's density estimate is a classical unconditional theorem. The project's
`ActualZeroOrdinate.InghamDensityBound` is still a proposition awaiting an
unconditional Lean proof. This checkpoint does not supply that proof, does not
close Z03, and does not prove RH. No domain-specific axiom is introduced.

The reference is Chourasiya and Simonič, *An explicit form of Ingham's zero
density estimate*, [arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2).
Equation (41) supplies the mixed-moment step; Corollary 1 motivates the profile
`T^(3(1-sigma)/(2-sigma)) (log T)^((7-5 sigma)/(2-sigma))`.
Numerical constants and finite-height RH computations in that paper are not
imported as Lean facts.

## Checked mathematical additions

### Actual critical-line moment

Files:
- `Analysis/ComplexMixedMomentBounds.lean`
- `Analysis/ActualInghamCriticalMoment.lean`

For continuous complex functions f,g on the real line and H <= T,
`Complex.integral_mul_four_thirds_le` proves
$$
\int_H^T |fg|^{4/3}
\le \left(\int_H^T|f|^4\right)^{1/3}
     \left(\int_H^T|g|^2\right)^{2/3}.
$$
`Complex.integral_mul_sub_one_four_thirds_le` then proves
$$
\int_H^T |fg-1|^{4/3}
\le 2^{1/3}\left[
 \left(\int_H^T|f|^4\right)^{1/3}
 \left(\int_H^T|g|^2\right)^{2/3}+T-H\right].
$$
Both input moments retain the same interval. No enlargement to [0,T] is needed.

`InghamMollifier.critical_error_moment_le` applies this to the actual
`riemannZeta` and `InghamMollifier.mollifier X` on Re(s)=1/2, proving the
required continuity and integrability. The result holds for every natural X
and all H <= T. It has no asymptotic moment hypothesis. It also does not assert
an asymptotic bound for either moment on its right-hand side.

### Sharp fixed-strip transfer and the endpoint a=4/3

File: `Analysis/ActualSelbergIngham.lean`.

For 0 < eta <= 1/2, `ingham_exponent_comparison_on_strip_iff` proves
$$
\left[\forall\sigma\in[1/2+\eta,1],\quad
 \frac{3(1-\sigma)}{2-\sigma}\le1-a(\sigma-1/2)\right]
\iff a\le\frac4{3-2\eta}.
$$
The necessity is already detected at sigma=1/2+eta. The accompanying
`ingham_exponent_add_sharp_gap_le` retains the uniform additive gap
$$
d=\left(\frac4{3-2\eta}-a\right)\eta.
$$
For a < 4/(3-2eta), the gap is positive.
`exists_selberg_far_windows_of_ingham_sharp` absorbs the four extra
logarithms using this d. Given a classical count constant C, its proof
takes the far-window constant F=C(4/d)^4.

The existing `exists_selberg_far_windows_of_ingham` now accepts a <= 4/3.
The same endpoint extension is propagated to
`uniformSelbergDensity_of_near_excess_and_ingham` and
`uniformSelbergDensity_of_truncated_near_excess_and_ingham` in
`Analysis/ActualSelbergTruncatedNearLine.lean`.

These density transfers remain conditional on `InghamDensityBound` and,
where applicable, their displayed near-line estimate. This improves the
previous Lean reduction; it is not a new unconditional global density theorem.
The fixed-strip upper slope is an optimal scalar comparison for this argument,
not a claimed optimal density bound for zeta.

### Unconditional actual-zero bound on a shrinking strip

File: `Analysis/ActualInghamThinStrip.lean`.

`height_log_le_ingham_profile_iff` proves an exact equivalence, for T>1 and
sigma<2:
$$
T\log T\le T^{3(1-\sigma)/(2-\sigma)}
 (\log T)^{(7-5\sigma)/(2-\sigma)}
\iff
(\sigma-1/2)(2\log T+4\log\log T)\le3\log\log T.
$$
Combining it with the existing proved total-zero count,
`exists_ingham_profile_on_thin_strip` establishes an actual inclusive,
multiplicity-weighted zero-count bound with one C>0 for every T>=9,
sigma in [1/2,1], and the displayed strip condition. It does not assume
`InghamDensityBound`, RH, a zero table, or a mollifier-moment estimate.

The theorem's condition is kept in product form so no extra denominator
positivity premise is hidden. Where 2 log T + 4 log log T is positive, its
width is 3 log log T/(2 log T + 4 log log T). This is exactly the range in
which the total-count comparison proves the stated profile with the same C.

## Remaining analytic work

The next substantial moment input is an actual critical-line fourth-moment
estimate, with all thresholds and constants quantified, of the form
$$
\exists C>0,\ \exists H\ge2,\ \forall T\ge H,\quad
\int_0^T|\zeta(1/2+it)|^4\,dt\le C T(\log T)^4.
$$
The new mixed-moment theorem consumes this together with an appropriate
uniform second-moment estimate for the actual finite Mobius mollifier.

The literature route also requires the moving right-line error moment,
Gabriel interpolation, and the matching horizontal/boundary budget.
Existing detector and signed-rectangle modules supply identities and conditional
assembly; a fixed Re(s)=3/2 pointwise tail bound alone does not supply the
moving right-line moment used by the density proof. The near-line Selberg
provider required by Z03 remains a separate obligation.

## Verification

All new modules are exported by `RiemannResearch.lean` and use the existing
Analysis Bazel package. Focused acceptance includes the actual moment module,
the thin-strip module, the updated truncated-near-line consumer, and explicit
axiom guards for the six principal declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by those guards.
Local hypotheses such as `InghamDensityBound` are part of theorem types and
are not discharged by an axiom audit.

Focused Bazel acceptance succeeded in job
`job_p6gRcpkQbK33MJ3Rl_gLcpPkKXU2REjm`, with a reported verification
duration of 28.572 seconds. This duration is the server's check duration,
not workspace setup or polling time.
[BuildBuddy log](https://app.buildbuddy.io/invocation/65b60e4a-7d7e-4b32-967c-abaf68a86bbf).

Final publication is gated by the managed Bazel/BuildBuddy full-project
checkpoint, with a second validation if newer main changes are integrated.
Wolfram was used for exploratory exponent algebra only; Lean proofs supply
the verification evidence.
