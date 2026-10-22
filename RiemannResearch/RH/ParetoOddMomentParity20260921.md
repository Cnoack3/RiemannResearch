# Pareto odd-moment continuation: parity elimination and sign obstruction

Date: 21 September 2026. Starting published commit:
`71c3c9fc7e016da474889dc25e14a87167997500`.

This continuation follows the handoff's actual odd-moment variational
problem. It does not prove the vanishing-energy premise or RH.

## Exact elimination of all even coefficients

At stage n, partition the moduli 2,...,n+1 into E (even) and O (odd).
Write the actual full tail Gram matrix in this order as

\[
G=\begin{pmatrix}G_{EE}&G_{EO}\\G_{OE}&G_{OO}\end{pmatrix}.
\]

For fixed signed odd coefficients b, the unique optimal even coefficients
are

\[
a^*(b)=-G_{EE}^{-1}G_{EO}b.
\]

Let P_E be the orthogonal projection onto the span of the even tail atoms,
and let \(\widetilde t_d=(I-P_E)t_d\) for odd d. Their actual Gram matrix is

\[
\boxed{S_n=G_{OO}-G_{OE}G_{EE}^{-1}G_{EO}.}
\]

The screened odd atoms are proved linearly independent. Thus their Gram
inverse exists; this is not an extra positivity or invertibility premise.
For every signed even coefficient vector a and odd vector b, the exact
completion is

\[
\boxed{
\left\|\sum_{d\in E}a_dt_d+\sum_{d\in O}b_dt_d\right\|^2
=b^TS_nb+(a-a^*)^TG_{EE}(a-a^*).
}
\]

Equality with the first term holds precisely when a=a*. The odd moment
\(J=\sum_{d\in O}b_d/d^2\) is unchanged by this optimization. Odd composite
moduli are retained. The even vectors are optimized out with their exact
Schur correction; simply using G_OO would give a different problem.

## The same capacity in the smaller system

Let H(d)=kappa/d^2 for odd d, where kappa=pi^2/(pi^2-8), and H(d)=0 for
even d. The full defect minimum y_n is proved equal to the minimum
interpolant of H_O against the screened odd atoms. Consequently

\[
\boxed{Q_n=H_O^TS_n^{-1}H_O.}
\]

This is an equality for the original Q_n, not a replacement capacity or a
comparison bound. In particular, the original small-tail witness condition
is equivalent to

\[
\forall\varepsilon>0\;\exists n,b:\quad
\sum_{d\in O}\frac{b_d}{d^2}=1,
\qquad b^TS_nb<\varepsilon.
\]

`riemannHypothesis_of_screenedOdd_small_tail` proves that this condition
implies RH. Its arithmetic premise is **Open**. Neither the equality for
Q_n nor the finite inverse establishes that Q_n is unbounded.

## A concrete obstruction to nonnegative witnesses

For any finite full-dictionary coefficient vector c with c_d>=0 and odd
moment one, physical site two satisfies

\[
f(2)=\sum_{d=2}^{n+1}c_d\frac{2\bmod d}{d}
\ge 6\sum_{\substack{2\le d\le n+1\\d\text{ odd}}}\frac{c_d}{d^2}=6.
\]

The Pareto weight at site two is exactly 1/6. Hence

\[
\boxed{\|f\|_{\rm tail}^2\ge f(2)^2/6\ge6.}
\]

Lean checks this against the actual infinite tail norm. Therefore every
odd-moment-one witness with energy below six has a negative coefficient.
Positive averaging alone cannot construct the desired family. This does
not obstruct general signed witnesses or positive odd coefficients with
negative even corrections. No sharpness claim is made for the constant six.

## Formal scope and next target

Modules:

- `RH/ParetoOddMomentParity.lean`: exact parity synthesis and moment,
  unique optimal even correction, Schur Gram entries and independence,
  exact energy completion, identical defect representer and capacity,
  small-energy equivalence and conditional RH endpoint.
- `RH/ParetoOddMomentSignObstruction.lean`: physical site-two evaluation,
  value and full-energy lower bounds for nonnegative coefficients, and
  the necessary negative coefficient below energy six.

The next substantive target is to construct signed odd vectors b with
moment one and b^T S_n b tending to zero, while recovering the even
coefficients by the displayed exact optimizer. Equivalently, prove
H_O^T S_n^{-1} H_O unbounded. Both remain **Open**.

No RH, not-RH, critical-zero existence, or RH-to-density provider is
assumed in the new finite identities or sign obstruction. The RH endpoint
retains its stated small-energy hypothesis. No admitted proof,
project-local axiom, or unsafe declaration is introduced.

The combined candidate passed Lean with exit code 0 and no warnings in
about 64 seconds: `job_If5Zv1t_WMn6zZrGQoNME6BZDygUXq3B`.
Five key axiom audits reported only `[propext, Classical.choice, Quot.sound]`.
There are 22 proved theorems (including one private helper), five definitions,
and two index abbreviations. Final installed-module acceptance is the single
publishing checkpoint; its receipt is recorded in the updated handoff.
