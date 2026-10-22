# Finite Weil normalization and corrected Schur certificates — 2026-10-13

## Scope and source

Continuation of the user-provided **Early RH operator-algebra program: critical audit and consolidated research record**, dated 2026-10-12, especially sections 3–4, 10, and 20. This continuation addresses normalization and certificate mathematics. It does not formalize the whole audit, replay the old interval programs, certify a corrected endpoint, or prove RH.

Profiles are real valued. The common pole, prime, diagonal, and endpoint terms remain an arbitrary shared scalar. Identifying these integral formulas with an actual Fourier matrix or zero-side explicit formula remains separate.

## Established integral correction

Module: RH/FiniteWeilNormalization.lean (13 theorems).

Reuse the existing gamma kernel, regulator, continuous correction and primitive:
\[
 K(t)=\frac{e^{t/2}}{e^t-e^{-t}},\quad r(t)=e^{-t/2},\quad
 c(t)=\frac{2e^{-t/2}}{(1+e^{-t/2})(1+e^{-t})}.
\]
The standard numerator is proved explicitly:
\[
 K(t)(\phi(t)-r(t)\phi(0))
 =\frac{e^{t/2}\phi(t)-\phi(0)}{e^t-e^{-t}}.
\]
The wrong integrand is \(K(t)(\phi(t)-\phi(0))\).

Define the shift by its actual integral,
\[
 \Delta(L)=\int_0^L c(t)\,dt.
\]
The fundamental theorem of calculus yields
\[
 \Delta(L)=\log2+\frac\pi2
 -2\log(1+e^{-L/2})+\log(1+e^{-L})-2\arctan(e^{-L/2}).
\]

- finiteNormalizationShift_pos: \(\Delta(L)>0\) for \(L>0\).
- half_length_le_finiteNormalizationShift: \(\Delta(L)\ge L/2\) for \(0\le L\le2\log2\), hence through \(\log4\).
- finite_gamma_integral_difference: with both finite integrals explicitly integrable, their difference is exactly \(\phi(0)\Delta(L)/2\).
- finite_weil_value_shift: when \(\phi(0)=2w\), \(Q_{\rm zip}=Q+\Delta(L)w\).
- finite_weil_lower_bound_iff: a whole-form lower bound \(m\) for the shifted form is equivalent to the bound \(m-\Delta(L)\) for the corrected form.

There is no sign assumption on \(w\). The value-shift theorem therefore applies to real bilinear entries with their actual Gram entry as \(w\). It becomes a scalar identity-matrix shift only in an orthonormal basis. No Fourier orthonormality or matrix-entry identification is asserted here.

## Established certificate algebra

Module: LinearAlgebra/ShiftedSchurCertificate.lean (8 theorems).

The exact sum-of-squares identity is
\[
\begin{aligned}
 &(c-\delta-\ell)
 [(a-\delta)x^2-2hxy+(c-\delta)y^2-\ell(x^2+y^2)]\\
 &\quad=((c-\delta-\ell)y-hx)^2+
 ((a-\delta-\ell)(c-\delta-\ell)-h^2)x^2.
\end{aligned}
\]
A valid polynomial certificate for the whole form is consequently
\[
 c-\delta-\ell>0,\qquad
 h^2\le(a-\delta-\ell)(c-\delta-\ell).
\]
This can use rational or interval bounds without a floating-point square root. The theorem finite_weil_lower_bound_of_block_envelope applies it directly to the finite integral formulas with \(\delta=\Delta(L)\). Its core/tail envelope and numerical inequalities remain explicit hypotheses.

Reusing an old Schur margin has an additional loss:
\[
 (a-\delta)-\frac{b^2}{c-\delta}
 =\left(a-\frac{b^2}{c}\right)-\delta
   -\frac{\delta b^2}{c(c-\delta)}.
\]
The exact scalar identity scalarSchurMargin_sub_scalar requires both denominators nonzero. It does not assert an operator resolvent bound.

Two rational counterexamples are proved:
1. The matrix [[2,1],[1,1]] has Schur margin 1, but its value at \((1,-1)\) is 1 while the squared norm is 2. A Schur margin need not be a whole-form lower bound.
2. Subtracting \(I/2\) leaves the naively corrected Schur margin \(1/2>0\), but the actual corrected Schur margin is \(-1/2\), and the corrected quadratic value at \((1,-2)\) is \(-1/2\).

Thus the tail inverse must be corrected along with the diagonal.

## Verification evidence and assumptions

The combined 21-theorem candidate passed server Lean:
- Job: job_G-wuRTjuZwvujV04eoMhs47z_4lra1K4.
- Result: classification success; verified true; exit code 0.
- Seven inspected principal declarations (integral shift, quantitative lower bound, concrete certificate consumer, scalar certificate, changed Schur margin and counterexample) reported only propext, Classical.choice, and Quot.sound.
- The ephemeral check had an end-of-input whitespace warning on its last diagnostic command; no admitted proof was reported.
- Publication is separately gated by server checkpoint validation of the actual saved modules and affected local reverse dependents. The checkpoint receipt records final integration and publication status.

No local axiom, unsafe declaration, admitted proof, or RH hypothesis is introduced. Integrability and the certificate envelope remain visible in theorem types; an axiom listing does not discharge them.

## RH research obligations

**Stage A, partial completion:** the finite normalization shift is proved from integrals. Still Open: identify each corrected Fourier coefficient with the standard formula, including off-diagonal entries and basis normalization; independently compare arithmetic and spectral sides with justified truncation errors.

**Stage B, conditional certificate architecture:** the corrected core/tail algebra is proved and connected to finite integral formulas. Still Open: validated coefficient enclosures, a strictly positive corrected infinite-tail bound, rigorous coupling bounds, and numerical parameters passing the polynomial certificate at \(L=\log3\). The old shifted margins do not provide them.

**Stages C–D, Open:** a corrected fixed-endpoint certificate, then arithmetic control of corrected cores along unbounded support lengths. No cofinal positivity or RH-strength arithmetic estimate is obtained here.

Next concrete target: coefficient-level integral identities for the constant and first nonzero Fourier modes of the correctly normalized form, followed by a fresh interval certificate whose failure gates cannot be bypassed by preselected constants. Preserve every signed remainder and the actual Gram normalization.
