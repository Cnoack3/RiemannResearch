# Montgomery continuation: analytic providers

Starting revision: `ba2477cb077f116e4fa6b9f45272368448bcbfe0`.
Task: follow `Montgomery_Parseval_Lean_Continuation_2026-11-10.md`.

This continuation supplies analytic estimates and smoothing kernels for the
actual zeta-zero multiset. It does not prove the pair-correlation conjecture,
RH, a gamma-operator asymptotic, or decay of the actual horizontal defect.
The exact homogeneous Parseval results from the starting revision are reused.

## Actual-zero local mass and Bessel estimates

Let `Copies T` retain every analytic multiplicity at heights `0 < gamma <= T`,
and put `w(d)=4/(4+d^2)`. The already-checked unconditional unit-window bound
is instantiated with the actual zeta function. Sorting copies by
`floor(-gamma)` handles the half-open interval endpoints exactly.

`MontgomeryLocalMass.exists_actual_cauchy_row_bound` proves

\[
\sum_{i\in\mathrm{Copies}(T)}w(y-\gamma_i)\le C\log(T+3)
\qquad(T\ge0,\ y\in\mathbb R).
\]

The generic cell estimate has constant 32 times the largest unit-cell
occupancy. Its summable envelope is `8/(1+|a-b|)^2`.
Schur's inequality gives the corresponding coefficient-sensitive estimate

\[
\int e^{-2|s|}\left|\sum_i c_i e^{is\gamma_i}\right|^2ds
\le C\log(T+3)\sum_i|c_i|^2.
\]

Using the existing unconditional total zero-count bound and the exact
Montgomery normalization, `exists_formFactor_le_log` proves

\[
0\le F_T(\alpha)\le C\log T\qquad(T\ge9,\ \alpha\in\mathbb R).
\]

No RH, Selberg-density assumption, coefficient estimate, or form-factor
asymptotic is an input. The bound still grows with T; it does not establish
uniformly bounded limiting masses or the conjectured value one.

`MontgomeryComplexSchur` proves the entry comparison

\[
\left|\frac4{4-(z+\overline w)^2}\right|
\le\frac43\,w(\Im z-\Im w),
\qquad |\Re z|,|\Re w|\le\tfrac12.
\]

Consequently the same coefficient Bessel bound holds for arbitrary
copy-dependent horizontal displacements of the actual ordinates in the
closed half-strip. Specialization to `z_i=rho_i-1/2` discharges these inputs
from the actual critical strip. This provides useful control for future
horizontal Taylor integrals without replacing squared coefficient sums by
the square of their absolute sum.

## Positive sech smoothing and its complete transform

`ShiftedSechKernel` proves that

\[
\kappa_\delta(v)=\Re\frac1{\cosh(\pi(v+i\delta))}
=\frac{\cosh(\pi v)\cos(\pi\delta)}
 {\sinh^2(\pi v)+\cos^2(\pi\delta)}
\]

is strictly positive for `|delta|<1/2`, integrable, and has exact mass one.
It proves complete interval and half-line integrals from the primitive
`arctan(sinh(pi*v)/cos(pi*delta))/pi`, with both infinite endpoints retained.
The explicit bound is

\[
0<\kappa_\delta(v)\le
\frac2{\cos(\pi\delta)}e^{-\pi|v|}.
\]

`SechLaplaceTransform` proves the sharp-strip bilateral transform

\[
\int_{\mathbb R}\frac{e^{zx}}{\cosh x}\,dx
=\frac\pi{\cos(\pi z/2)},\qquad |\Re z|<1,
\]

including integrability. The proof uses the logistic substitution into
Euler's beta integral and the gamma reflection formula, all checked in Lean.
`ShiftedSechSpectrum` proves positivity, boundedness by one, and integrability
of `cosh(delta*u)/cosh(u/2)` in the corresponding open strip.

`ShiftedSechTransform.integral_kernel_phase` completes handoff A.2:

\[
\int_{\mathbb R}\kappa_\delta(v)e^{iuv}\,dv
=\frac{\cosh(\delta u)}{\cosh(u/2)},\qquad |\delta|<\tfrac12.
\]

It evaluates the transform of the frequency profile with the proved Laplace
identity, then applies Fourier inversion. The necessary integrability of
both functions is proved, not included as a sampling assumption.

`ActualZeroSechSmoothing` specializes this to the actual density

\[
m_T(v)=\sum_{i\in\mathrm{Copies}(T)}
  \kappa_{\delta_i}(v-\gamma_i).
\]

It proves nonnegativity, integrability, exact mass `Ncount(0,T)`, and

\[
\int m_T(v)e^{iuv}\,dv
=\operatorname{sech}(u/2) S_T^\sharp(u).
\]

Every zero and analytic multiplicity is retained. The actual critical strip
discharges all shift bounds, and actual reflection identifies the cosh sum
with the Landau sum. No RH or zero-density input is introduced.

These providers preserve the attenuation from fixed-width smoothing. A
positive density or an exact transform is not a zero-sampling asymptotic.
Narrowing a complex-shifted sech kernel also narrows its pole-free strip;
the raw Gaussian damping estimate below does not authorize that operation.

## Gaussian Fourier damping removal

For a real frequency test `f` with `f` and `a^2 |f(a)|` integrable,
`MontgomeryGaussianSmoothing` proves all integrability statements and the
complete signed remainder identity before taking an absolute value. Its
unconditional actual-zero estimate is

\[
\left|\int f(a)F_T(a)\,da-
\int f(a)e^{-(b\log T\,a)^2}F_T(a)\,da\right|
\le Cb^2(\log T)^3\int a^2|f(a)|\,da,
\quad T\ge9.
\]

The constant is uniform in the test, width, and height. The inputs are the
proved `F_T <= C log T` estimate and `0 <= 1-exp(-x^2) <= x^2`.
Thus damping disappears whenever `b(T)^2 (log T)^3 -> 0`. The real test need
not be continuous, positive, or supported below one.

The concrete choice `b(T)=1/(log T)^2` is also proved. The multiplier becomes
`exp(-(a/log T)^2)`, its error is at most
`C/(log T) * integral a^2 |f(a)|`, and the difference tends to zero. This
corollary has only the test-integrability assumptions; no unproved spectral
or width hypothesis remains.

Scope: this is removal of Gaussian damping in the Fourier pairing for the
actual raw form factor. A physical-space convolution identity is not asserted
by this module, and it is not a theorem about undoing fixed-width sech
attenuation. The undamped pairing is connected to actual zero pairs by the
previous exact Fourier-pairing theorem whenever its inversion hypotheses hold.
The removal estimate supplies no limiting value for either pairing.

## Exact scalar horizontal energies

`MontgomeryCoshLaplace` proves, with integrability and `|d|<1`,

\[
q(u,d):=\int e^{-2|s|}\bigl(\cosh((u+s)d)-1\bigr)^2ds
=\frac{\cosh(2ud)}{2(1-d^2)}
-\frac{8\cosh(ud)}{4-d^2}+\frac32.
\]

The negative middle term is part of the exact equality. It is not discarded
in the definition. Positivity follows from the integral representation.

`MontgomeryHorizontalBound` applies finite L2 Minkowski to the actual signed
correction, giving

\[
\sqrt{\mathcal N_T\mathcal H_T(\alpha)}
\le\sum_{i\in\mathrm{Copies}(T)}\sqrt{q(\alpha\log T,\delta_i)},
\qquad T>1.
\]

Critical-line copies contribute zero. A separate uniform-strip bound uses
`E(T)=sum_i delta_i^2` and proves

\[
\mathcal N_T\mathcal H_T(\alpha)
\le J(\alpha\log T)E(T)^2,
\quad
J(u)=\frac{32}{3}\cosh u-\frac{512}{15}\cosh(u/2)+24.
\]

The proof integrates the existing sharp pointwise strip inequality; it
retains the exponential frequency dependence. These are unconditional
upper bounds, with no hypothesis that the right-hand sides vanish.

Mathematical limitation, not a newly formalized asymptotic: since
`J(u) ~ (16/3) exp(|u|)`, using this last majorant uniformly up to a fixed
`A>1` would require a bound as strong as
`E(T)=o(T^((1-A)/2)*sqrt(log T))`. The cumulative nonnegative energy would
then tend to zero, excluding every off-line zero. This is not a weaker
substitute for RH. The coefficient Bessel estimate above is intended to
avoid this loss in later signed or horizontal-derivative arguments.

## Analytic obligations that remain open

- The complete gamma remainder for the actual homogeneous Weil identity,
  including pole terms and a precisely normalized diagonal.
- Uniform sampling transfer for growing homogeneous polynomial families.
  The existing length restriction still requires `D^k+1<T`.
- Decay of the actual horizontal defect, with its exponential horizontal
  factors retained, or another justified transfer to raw ordinate pairs.
- The signed close-shift prime correlation estimate or an averaged raw
  probe asymptotic in the fixed-support range above one.
- Control of concentration at the transition frequencies before deducing
  the full weak pair-correlation limit.

Gamma audit question: the proposed bound for a complete error matrix must
specify whether its exact diagonal has been subtracted or renormalized.
The logarithmic main term of the digamma factor can leave a diagonal term
of order `1/log T` after `T log T` normalization, independent of `D/T`.
No counterexample to a precisely defined error matrix is asserted here;
its definition and complete diagonal should be derived first.

## External checks and sources

- Montgomery (1973), [original pair-correlation paper](https://websites.umich.edu/~hlm/paircor1.pdf):
  form-factor and Cauchy-kernel framework.
- Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh,
  [2026 correction, Section 3](https://arxiv.org/html/2501.14545v3#S3):
  the corrected low-support complex-zero asymptotic remains external
  literature; it is not used as an unchecked Lean input.
- [DLMF 4.35](https://dlmf.nist.gov/4.35): hyperbolic identities supporting
  the sech computations; [DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16):
  digamma integral relevant to the remaining gamma calculation.
- [Simonic, arXiv:1910.08274](https://arxiv.org/abs/1910.08274):
  the Selberg density estimate is weaker than the decay needed by the
  positive horizontal-energy majorant. It is not imported as an axiom.

Wolfram independently checked the scalar q integral and the factorization
`J(u)=(8/15)(1+16x+40x^2)`, with `x=cosh(u/2)-1`. The finite symbolic
checks also verified the sech real form and arctangent primitive derivative.
These checks are supporting evidence; the Lean proofs use no Wolfram oracle.

## Verification scope

Each substantive module is developed using focused Bazel/BuildBuddy checks.
The publication checkpoint audits all sources and validates the full
`//:RiemannResearch` target, including downstream consumers and any
integration revision, before publishing. The final checkpoint job and commit
are reported in the accompanying chat.
