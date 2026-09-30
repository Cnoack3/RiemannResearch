# A single signed Möbius aggregate of the derivative corrections

Continuation on 2026-09-29 from the requested baseline 41b7faf6, using its
current descendant 093d8ec2. The existing Abel, CRT, zeta-moment, and Weil
bridges are reused. This is a new repository assembly, not a literature
priority claim.

## What is established

The new module RH/DerivativeMobiusAggregate.lean proves a uniform
reconstruction of the reciprocal correction by signed derivative rows.
It then turns the family of fixed-coordinate cancellation conditions into
one one-sided cofinal scalar estimate. The estimate itself is still open.

Use repository stage n, with conductors 2,...,n+1. Write

- \(e_{n,d}=c_{n,d}+\mu(d)\) for the actual inverse-Gram correction;
- \(h_d=\Delta g_d\), \(H_n=\Delta C_n=\sum_{d=2}^{n+1}e_{n,d}h_d\);
- \(B_n(d)=\langle h_d,H_n\rangle\);
- \(q_n=\sum_{d=2}^{n+1}e_{n,d}/d\);
- \(R_{m+1}=\Delta(1-F^{\rm raw}_{m+1})\);
- \(r=1-P_V1\), \(E=\|r\|^2\).

The anchored point vector \(\delta_1\) has value one at physical site one
and zero elsewhere; \(\|\delta_1\|^2=1/2\). Existing results give, without RH,

\[
R_{m+1}=\delta_1+\sum_{d=2}^{m+1}\mu(d)h_d\longrightarrow0,\qquad
H_n\longrightarrow-\Delta r.
\]

In particular, \(\sup_n\|H_n\|<\infty\).

## Exact finite reconstruction and complete square

Define the two independently indexed finite quantities

\[
T_{m,n}=-\sum_{d=2}^{m+1}\mu(d)B_n(d),\qquad
U_{m,n}=\langle R_{m+1},H_n\rangle.
\]

Rows \(B_n(d)\) are defined even when d is larger than n+1. Finite linearity
and the exact first-site evaluation yield

\[
\boxed{\frac{q_n}{2}=T_{m,n}+U_{m,n}.}
\]

The factor 1/2 is the physical Pareto weight at site one. It is not omitted.
The complete square is

\[
\boxed{\left(\frac{q_n}{2}\right)^2
=T_{m,n}^2+2T_{m,n}U_{m,n}+U_{m,n}^2.}
\]

The error estimate applies only after retaining the full signed remainder:

\[
|U_{m,n}|\le\|R_{m+1}\|\,\|H_n\|,\qquad
\boxed{\exists C>0\ \forall m,n,\quad
\left|\frac{q_n}{2}-T_{m,n}\right|\le C\|R_{m+1}\|.}
\]

Consequently, for each epsilon>0 there is an M such that the error is
less than epsilon for EVERY m>=M and EVERY optimization stage n.
No inverse-Gram operator norm or absolute coefficient mass occurs.
C is unconditional and finite; an effective numerical value is not asserted.

Verified declarations: mobiusRowAggregate_exact, mobiusRowAggregate_square,
mobiusRowRemainder_bound, mobiusRowAggregate_uniform_bound, and
mobiusRowAggregate_uniform_approximation.

## Exact Abel and CRT forms

Let \(P_n(k)=\sum_{j<k}\texttt{correctionCoefficient}(n,j)\) and
\(K_i(j)=\langle h_{i+2},h_{j+2}\rangle\). Then

\[
T_{m,n}
=-\sum_{i=0}^{m-1}\mu(i+2)
\left[P_n(n)K_i(n)
-\sum_{k<n}P_n(k+1)\{K_i(k+1)-K_i(k)\}\right].
\]

Both the endpoint at conductor n+2 and every signed difference summand
remain present. The CRT version substitutes the already checked exact row

\[
B_n(d)=\left(\frac1d-M(d)\right)q_n
-\frac1d\sum_e e_{n,e}M(e)
+\sum_e e_{n,e}M(\operatorname{lcm}(d,e)),
\]
\[
M(a)=\sum_{\substack{k\ge1\\a\mid k}}\frac1{k(k+1)}.
\]

Thus the scalar aggregation retains all lcm intersections and complete
physical tails. Verified declarations: mobiusRowAggregate_eq_abel and
mobiusRowAggregate_eq_crt. No new Weil positivity claim is used.

## Joint limit and the surviving dyadic square

For ANY function m(n) tending to infinity, with no relative rate condition,

\[
\boxed{
T_{m(n),n}\longrightarrow L
=-\frac{r(1)}2
=-\frac12\left[
(2-\sqrt2)E+\frac{\sqrt2}{2}
\left\|r-\frac{\sqrt2}{2}D_2r\right\|^2
\right].
}
\]

Here \(D_2\) is the repository's doubleDilation operator.
The last equality is the existing exact dyadic identity, with its entire
nonnegative square retained. Hence L<=0, and L=0 exactly when r=0.
If r is nonzero, L is strictly negative.

This joint limit is justified by strong convergence and uniform norm control,
not by interchanging a growing sum with fixed-row limits.

Verified declarations: mobiusRowRemainder_tendsto_zero,
mobiusRowAggregate_tendsto, and mobiusRowAggregate_tendsto_full_remainder.

The same scalar obstruction controls every limiting derivative test:

\[
\boxed{
|\langle f,\Delta r\rangle|^2
\le(4+2\sqrt2)\|f\|^2r(1)
\quad\text{for every }f\in H.
}
\]

This is limiting_derivative_test_sq_le_firstCoordinate. In particular it
applies to every fixed derivative atom. It is control by the identified
obstruction, not a proof that the obstruction is zero.

## The remaining concrete arithmetic estimate

Taking m(n)=n gives the completely finite signed Gram expression

\[
T_n=-\sum_{d=2}^{n+1}\mu(d)
       \sum_{e=2}^{n+1}e_{n,e}\langle h_d,h_e\rangle.
\]

The new kernel-checked criterion is

\[
\boxed{
\left[\forall\varepsilon>0\ \forall N\
 \exists n\ge N:\ T_n>-\varepsilon\right]
\ \Longleftrightarrow\
\left[\forall i,\ \texttt{fixedMismatch}(n,i)\longrightarrow0\right]
\ \Longleftrightarrow\ r=0.
}
\]

Therefore the boxed one-sided cofinal lower bound is sufficient for RH.
It requires no prescribed convergence rate, no upper bound on T_n, and
no requirement that T_n be nonnegative at every stage.

The equivalence is formalized as cofinal_mobius_gram_iff_fixedMismatch;
mobiusRowAggregate_cofinal_iff_residual_zero proves the general moving-cutoff
version; riemannHypothesis_of_cofinal_mobiusRowAggregate is the conditional
RH endpoint.

**Open:** produce the one-sided cofinal lower-bound provider for the actual
inverse-Gram coefficients. Its equivalence to residual vanishing makes its
RH strength explicit. We have reduced the form and number of required
arithmetic estimates, not discharged their substance.

PNT alone proves \(R_{m+1}\to0\) and removes U from the reconstruction.
It does not show \(q_n\to0\): the existing exact limit is \(-r(1)\).
Similarly, the CRT, tail-pairing, adjoint-row and Weil identities identify
or approximate signed corrections but do not supply the required lower bound.

## Verification and integration

The complete Lean candidate, including all declarations above, passed a
serialized Lean check (exit code 0). Seven key declarations were checked
with #print axioms; all depend only on propext, Classical.choice, and
Quot.sound. These ordinary foundations do not discharge the explicit
cofinal arithmetic hypothesis in the conditional endpoint.

No sorry, admit, project-local axiom, or unsafe declaration is introduced.
The new module is exported in RiemannResearch.lean and listed in the theorem
catalog. The publication checkpoint performs affected-module integration
validation; the final research response reports its actual outcome.
