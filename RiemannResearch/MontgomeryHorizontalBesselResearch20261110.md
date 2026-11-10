# Montgomery continuation: coefficient-sensitive horizontal transfer

Date: November 10, 2026.
Starting main: `29fa256722998cc6fa8b9b0f6682fd7788ffae85`.
The supplied Parseval handoff started at `ba2477cb...`; the newer
`ac28c2fb...` already completed the sech transform, actual local Cauchy row
bound, and Gaussian damping removal. This continuation reuses those providers.

## Established analytic estimate

All sums below run over `ActualZeroOrdinate.Copies T`: actual nontrivial zeros
of Mathlib's Riemann zeta function, with every analytic multiplicity and
$0<\gamma_i\le T$. Put $\delta_i=\Re\rho_i-1/2$ and
$\mathcal N_T=T\log T/(2\pi)$. The existing horizontal defect is

\[
\mathcal H_T(\alpha)=\mathcal N_T^{-1}
\int_{\mathbb R} e^{-2|s|}
\left|\sum_i e^{i(\alpha\log T+s)\gamma_i}
 (\cosh((\alpha\log T+s)\delta_i)-1)\right|^2\,ds .
\]

Define the explicit one-point budget

\[
B_T(u)=\sum_i\left[(e^{u\delta_i}-1)^2+\delta_i^2\right].
\]

There is an absolute constant $C>0$, independent of height and frequency,
such that for $T\ge9$,

\[
\boxed{\mathcal H_T(\alpha)\le C\,B_T(\alpha\log T)/T.}
\]

This is an unconditional upper bound for the actual horizontal defect.
There is no RH, Selberg density assumption, sampling hypothesis, or presumed
pair-correlation asymptotic in its declaration. It does not assert that its
right-hand side tends to zero.

For $M_T(v)=\sum_i\delta_i^2e^{2v|\delta_i|}$, the second bound is uniform in
$|\alpha|\le A$:

\[
\boxed{\mathcal H_T(\alpha)\le
\frac{C}{T}\bigl(1+(A\log T)^2\bigr)M_T(A\log T).}
\]

The precise Lean declarations are
`exists_horizontalDefect_le_budget` and
`exists_horizontalDefect_le_exponentialMoment` in
`Analysis/MontgomeryHorizontalBessel.lean`.

## Why the zero-count loss is reduced

The preceding positive estimate had the form
$J(u)(\sum_i\delta_i^2)^2/\mathcal N_T$.
The new argument uses a Schur bound for the signed perturbation kernel before
summing coefficients. It keeps a sum of squared coefficients instead of
squaring their absolute sum. The two bounds are complementary: neither is
asserted to dominate the other in every finite configuration.

For $w(d)=4/(4+d^2)$, set
$K(z)=(2-z)^{-1}+(2+z)^{-1}=4/(4-z^2)$.
The exact mixed difference is

\[
\Delta_{a,b}K(id)=K(a+b+id)-K(a+id)-K(b+id)+K(id).
\]

The new resolvent theorem proves

\[
|\Delta_{a,b}K(id)|\le4|ab|w(d),
\qquad |a|,|b|\le\tfrac12.
\]

The full signed equality is retained. Each half-plane resolvent is factored by

\[
\frac1{q-a-b}-\frac1{q-a}-\frac1{q-b}+\frac1q
=\frac{ab}{q(q-a-b)}
 \left(\frac1{q-a}+\frac1{q-b}\right).
\]

Consequently, for arbitrary repeated real ordinates (t_i), displacements
$|a_i|\le1/2$, complex coefficients (c_i), and a row bound
$\sum_j w(t_i-t_j)\le D$,

\[
\int e^{-2|s|}
 \left|\sum_i c_i e^{ist_i}(e^{sa_i}-1)\right|^2ds
\le4D\sum_i|c_i|^2a_i^2.
\]

Integrability and the exact Gram identity are proved before the estimate.
For actual zeros, the already-proved unconditional local zero-count theorem
supplies $D\le C_0\log(T+3)$.

At general frequency $u$, the exact decomposition

\[
e^{(u+s)a}-1=(e^{ua}-1)e^{sa}+(e^{sa}-1)
\]

combines the complex-strip Bessel estimate with the new mixed-difference
estimate. Reflection identifies the resulting actual exponential difference
with the original cosh correction. Division by the exact Montgomery
normalization cancels the logarithmic row-bound loss, giving (C B_T(u)/T).

## Conditional limit transfers

`MontgomeryHorizontalLimit.lean` proves the following for any real frequency
function $\alpha(T)$, including moving frequencies:

* If $B_T(\alpha(T)\log T)/T\to0$, then
  $\mathcal H_T(\alpha(T))\to0$.
* Under that same explicit hypothesis, the difference between the square roots
  of the raw and complex form factors tends to zero.
* If additionally $F_T^\sharp(\alpha(T))\to\ell\ge0$, then
  $F_T(\alpha(T))\to\ell$.

These are conditional research reductions. Neither budget decay nor the
complex high-support asymptotic is supplied by the upper-bound theorem.

## Positive-budget limitation and noncircularity

The exponential weight is essential. An unweighted assertion such as
$\sum\delta_i^2=o(T)$ is not enough at $u\asymp\log T$.

For a fixed window $A$, the budget criterion is less restrictive than the
previous worst-strip energy criterion. For example, an abstract finite
reflection-symmetric exceptional set with maximum displacement $b$ has
$B_T(A\log T)=O(T^{2Ab}+1)$. Thus $2Ab<1$ allows that fixed exceptional
set to pass the budget condition. This observation is a paper consequence
of the explicit formula, not a claim that the actual zeros have only finitely
many exceptions.

In contrast, demanding this positive-budget criterion for every arbitrarily
large $A$ would exclude every off-line zero: a fixed reflected copy with
positive displacement $d$ contributes
$(T^{Ad}-1)^2/T$, which does not tend to zero when $Ad\ge1/2$.
Therefore the family of all-window positive-budget criteria must not be
advertised as a globally weaker substitute for RH. The actual signed defect
can retain cancellations that its positive majorant discards.

The new bound also does not by itself supply the corrected BGSTB asymptotic
in Lean or an asymptotic above support one. It controls the transfer error
between two existing actual-zero statistics.

## Remaining analytic obligations and next work

1. **Open:** decay of the actual budget on a chosen fixed frequency window,
   or a stronger estimate that preserves more of the signed horizontal
   cancellation. A fourth-order mixed kernel could retain
   $\delta_i^2\delta_j^2$ rather than the current first-difference
   $\delta_i\delta_j$ majorant.
2. **Open:** the complex or raw high-support form-factor asymptotic.
   The signed close-shift prime correlation and averaged raw-probe routes
   from the handoff remain available; no estimate for them is claimed here.
3. **Open:** the complete gamma remainder and growing homogeneous sampling
   transfer. The exact diagonal normalization must be specified first.
   Existing homogeneous Parseval does not extend the length condition
   $D^k+1<T$ into fixed support greater than one.
4. **Open:** transition-frequency concentration and the full weak
   pair-correlation limit.
5. **Not proved:** Montgomery's pair-correlation conjecture or RH.

## Provenance and verification

The Poisson/Gram framework is from Montgomery (1973),
https://websites.umich.edu/~hlm/paircor1.pdf, and the complex-zero formulation
of Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, Acta Arithmetica 214
(2024), https://doi.org/10.4064/aa230612-20-3. The corrected 2026
low-support error statement is in Section 3 of
https://arxiv.org/html/2501.14545v3; it remains external literature here.
The resolvent factorization and coefficient estimates are elementary
deductions formalized in this continuation; mathematical novelty is not claimed.

Wolfram independently returned zero for the exact mixed inverse difference
and factored the hyperbolic Gram kernels. A finite grid test of the proved
mixed-kernel majorant had maximum ratio 0.2; this does not replace the
uniform Lean proof. It was used for symbolic validation only. No Wolfram result
or literature theorem was introduced as an unchecked axiom.

Focused Bazel/BuildBuddy checks establish the new modules. The final
publication checkpoint must additionally validate the entire
`//:RiemannResearch` target and any integrated main revision before pushing.
The final job and published commit are reported in the accompanying chat.

### Completed focused verification and axiom audit

- Focused Bazel acceptance: `job_ge4mJL0iDs0fQHcSCVcSy1XDjc9PqRgZ`,
  target `//RiemannResearch/Analysis:MontgomeryHorizontalLimit` and its
  transitive imports, succeeded with `verified=true`.
  [BuildBuddy record](https://app.buildbuddy.io/invocation/31fff5c9-d963-409f-a30f-400fdd19cd05).
- A guarded axiom audit for the general difference-energy bound, both main
  actual horizontal bounds, and the exponential-moment transfer theorem
  succeeded in `job_oFqAmI8UXpearMWq5hIRje8np44QGTCy`.
  It accepts exactly `propext`, `Classical.choice`,
  and `Quot.sound`.
  [Audit record](https://app.buildbuddy.io/invocation/b24eafe0-9b6f-4c5c-8c5b-f59dc4c3fee5).
- This axiom audit does not erase hypotheses from theorem types. The
  convergence assumptions listed above remain open.
- The publication checkpoint is the separate full-project acceptance gate.
