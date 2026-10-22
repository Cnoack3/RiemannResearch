# Attempt to close the actual residual gain gap

Prepared October 12, 2026. **The RH gap was not closed.** The attempt proves
a conditional rate obstruction to the prime-only certificate and an exact
criterion for the remaining portion of the actual gain. It does not provide
the missing arithmetic nonsummability theorem.

## What was tested

For the actual Pareto two-seed fit, keep the dilation cutoff and write
\(F_M=P_{V_M}1\), \(D_M=\|1-F_M\|^2\). Let

\[
P_n=\{q\text{ prime}:q>3,\ 2^n<q\le2^{n+1}\},\qquad
c_{n,q}=\ell_q(F_{2^{n+1}})/q.
\]

These are the actual optimizer's prime coefficient sums, independent of a
chosen dependent representation. The previous exact observation energy is

\[
J_P(c)=\tfrac12\left(\sum_{q\in P}c_q^2-
\frac{(\sum_{q\in P}c_q/q)^2}{1+\sum_{q\in P}q^{-2}}\right).
\]

The attempted shortcut was to get a nonsummable prime observation schedule
from coefficient sums of order \(1/q\). The following proof identifies a
quantitative obstruction to that attempt.

## Verified rate obstruction, with its hypotheses visible

Suppose there are constants \(C\) and \(L>0\) such that, at every stage,

\[
|c_{n,q}|\le C/q\quad(q\in P_n),\qquad
D_{2^n}\ge L/(n+1).
\]

Because \(\#P_n\le2^n\) and \(q>2^n\), the finite cardinality estimate gives

\[
J_{P_n}(c_n)\le\frac12\sum_{q\in P_n}c_{n,q}^2
\le\frac{C^2}{2\cdot2^n}.
\]

Consequently the normalized observation satisfies the proved bound

\[
\boxed{a_n:=\frac{J_{P_n}(c_n)}{D_{2^n}}
\le\frac{C^2}{2L}(n+1)2^{-n},\qquad \sum_n a_n<\infty.}
\]

Lean also proves that every nonnegative minorant of this actual \(a_n\) is
summable under the same hypotheses. Thus the previous sufficient prime-only
RH criterion cannot be discharged by combining these particular bounds.
The criterion itself remains valid.

**Formal status:** both domain-specific bounds remain explicit hypotheses.
The uniform moving-prime coefficient bound has not been proved. Fixed-prime
coefficient convergence supplies no such uniform estimate. The logarithmic
floor is a classical analytic input whose actual specialization is not a
proved Lean provider in this work. Neither bound is assumed to follow from
the finite tests below.

## Complete actual gain and the remaining energy

Let \(u_P(c)\) be the exact minimum-norm prime interpolant from the preceding
module, and set

\[
b_n=\frac{\|F_{2^{n+1}}-F_{2^n}-u_{P_n}(c_n)\|^2}{D_{2^n}}.
\]

The extended `PrimeSensorGain.lean` proves the complete identity

\[
\boxed{\delta_n=a_n+b_n,\qquad a_n,b_n\ge0.}
\]

For any admissible prime observation sets with \(\sum_n a_n<\infty\), it
also proves

\[
\boxed{D_{2^n}\longrightarrow0
\quad\Longleftrightarrow\quad \neg\operatorname{Summable}(b_n).}
\]

The remainder is the part of the actual fit increment orthogonal to the
chosen prime sensor span. It is not identified with a purely composite
arithmetic atom family, nor asserted to be a legal correction by itself.

This isolates the remaining problem under a summable observation schedule:
prove a nonsummable lower estimate for these actual remainder energies.
The normal equations, exact Gram formula, and finite data do not prove it.
Unconditional full gain divergence remains an alternative sufficient target.

## Why the reviewed explicit approximants do not close the gap

Bettin, Conrey and Farmer's [arXiv:1211.5191](https://arxiv.org/abs/1211.5191),
Theorem 1, assumes RH and reciprocal-zeta-derivative control for its matching
upper distance asymptotic. Baez-Duarte's [arXiv:math/0205003](https://arxiv.org/abs/math/0205003),
Section 2.2, uses RH for its approximation construction. They cannot be used
as unconditional providers here.

Burnol's [arXiv:math/0103058](https://arxiv.org/abs/math/0103058), Theorem 1.3,
supplies the lower-distance obstruction in the classical Nyman--Beurling
space. It limits how fast approximation can occur; it does not establish
approximation or a lower gain schedule.

The paper-level transfer to this two-seed cutoff is as follows. For a finite
legal combination, its Mellin symbol

\[
A_F(s)=\sum_{p=2,3}\sum_{m\le M}c_{p,m}
\bigl(m^{1-s}-(pm)^{1-s}\bigr)
\]

is a Dirichlet polynomial supported on integers at most \(3M\). Mellin
Plancherel identifies its residual energy with the classical weighted
boundary integral, so \(D_M\ge d_{3M}^2\). Applying the classical positive
logarithmic floor yields an eventual two-seed logarithmic floor. This is an
inference from the established analytic comparison and lower-bound theorem,
not a newly verified Lean implementation of either analytic provider.
The existing `SharpLogarithmicResidualBarrier.lean` also keeps that provider
explicit; the present work does not silently discharge it.

## Finite tests: complete tail and dependent generators

Each Gram entry used its pairwise period \(Q\) and the complete infinite-tail
weight \(\Omega_Q(a)=[\psi((a+1)/Q)-\psi(a/Q)]/Q\). Target moments were
\(\log p\). Singular raw generating lists were handled by pseudoinverses.

| Enlargement | Full relative gain | Prime relative certificate | Prime share of gain |
|---|---:|---:|---:|
| 4 to 8 | 0.189471285 | 0.071240471 | 37.60% |
| 8 to 16 | 0.160225316 | 0.025936987 | 16.19% |
| 16 to 32 | 0.068433145 | 0.002149242 | 3.14% |
| 32 to 64 | 0.102572847 | 0.005744957 | 5.60% |

These are exploratory numerical results, not interval-certified inequalities
and not asymptotic evidence. The last row also shows that the displayed
prime share is not monotone. Local NumPy/SciPy calculations had maximum
normal-equation discrepancies below \(10^{-13}\). Wolfram independently
confirmed the 8-to-16 row to the displayed precision. The prior 50/80-digit
Wolfram check confirms the 4-to-8 row.

The maximum \(|q c_{n,q}|\) in these four blocks was approximately 0.414,
0.414, 0.239 and 0.544, respectively. This does not prove any uniform
moving-prime coefficient bound.

## Formal declarations and publication gate

Five theorems and two definitions extend `RH/PrimeSensorGain.lean`:
normalized observation and remainder energies, their nonnegativity, the
exact dyadic split, and the two summability/convergence equivalences.

Eight theorems and one definition are added in
`RH/PrimeSensorGainRateBarrier.lean`: finite coefficient/energy bounds,
actual new-prime block properties and cardinality, the explicit geometric
majorant, its summability, and the impossibility of a divergent nonnegative
prime minorant under the displayed bounds.

Candidate verification `job_5CAMFoReIAzcpmSrlM_yThF0q38qWzGQ` succeeded
(exit 0), with standard axioms for the decisive declarations. The final
persisted-module audit `job_krVfzyikEMLyr9lpPh3n0fpw4iL8-7HO` also succeeded
(exit 0). It built both modified modules and reported only `propext`,
`Classical.choice`, and `Quot.sound` for the decisive theorems.
Publication acceptance is the terminal server checkpoint result, validating
the final changed modules and required dependents before pushing.

**Open:** the actual full gain or remainder nonsummability provider.
**Open:** uniform moving-prime coefficient control.
**Analytic formalization pending:** the classical lower-floor provider and
its actual two-seed comparison. No unconditional RH proof is asserted.
