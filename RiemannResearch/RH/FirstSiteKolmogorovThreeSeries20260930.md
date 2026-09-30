# Exact angular variance and Kolmogorov three-series (2026-09-30)

The appropriate variance series is the series of increments
`Gamma_n = W_(n+1)-W_n`. The cumulative quantity `W_N` is not itself the
summand in a three-series criterion. A bounded positive cumulative variance
can have a nonsummable sequence of cumulative values.

Write `w_n=primeSchurWeight n`, `delta_n=factorialPrimeDelta n`,
`kappa_n=factorialPrimeError n`, and `u_n=w_n*delta_n^2`. The verified exact
increment is

\[
\Gamma_n=\frac{w_n(U_n\kappa_n-X_n\delta_n)^2}
 {U_n(U_n+u_n)},\qquad W_N=\sum_{n<N}\Gamma_n.
\]

The empty stage is zero. The complete signed screened CRT error and its
historical cross budget remain inside the determinant. At nonprime stages
the prime weight is zero.

## Classical probabilistic realization

On an auxiliary product space take independent fair signs `epsilon_n`.
For positive stages set

\[
a_n=\sqrt{\frac{w_n}{U_n(U_n+u_n)}}\,
       (U_n\kappa_n-X_n\delta_n),\quad
Z_n=a_n\varepsilon_n,
\]

and set `a_0=0`. Thus `a_n^2=Gamma_n`, `E Z_n=0`, and
`Var(Z_n)=Gamma_n`. For `M_N=sum_(n<N) Z_n`,

\[
\operatorname{Var}(M_N)=\langle M\rangle_N=W_N.
\]

These signs are auxiliary. Neither independence of CRT rows nor independence
of arithmetic correction terms follows from this construction.

At amplitude threshold 1 the three series become:

| Condition | Exact deterministic quantity |
|---|---|
| Tail probabilities | `sum_n 1_(Gamma_n>1)` |
| Truncated means | `0` |
| Truncated variances | `sum_n Gamma_n*1_(Gamma_n<=1)` |

Kolmogorov's three-series theorem and the tail 0-1 law consequently give

\[
\sum_n Z_n\text{ converges a.s.}
\iff \sum_n\Gamma_n<\infty
\iff \sup_N W_N<\infty.
\]

The clipping identity packages the two nonzero conditions exactly:

\[
\min(\Gamma_n,1)
=\mathbf 1_{\{\Gamma_n>1\}}
 +\Gamma_n\mathbf 1_{\{\Gamma_n\le1\}}.
\]

A fixed cutoff preserves summability: if the clipped series converges, its
terms tend to zero, so eventually the cutoff does nothing. Hence angular
nonsummability is also equivalent to unbounded clipped prefix energy.

Terminology and classical probability theorem: Dan Romik, *MATH/STAT 235A
Probability Theory*, Fall 2013, Theorem 10.6, Example 10.7, and Section 16.2,
[author's notes](https://www.math.ucdavis.edu/~romik/teaching-pages/mat235a-2013/lecturenotes235A.pdf).
The application to the complete arithmetic coefficients above is a direct
deduction. The probabilistic realization and a.s. theorem are not formalized
by this checkpoint.

## What the bridge proves and leaves open

`Analysis/NonnegativeSeriesTruncation.lean` kernel-verifies the exact clipping
identity, cutoff invariance of summability, and equivalence to the tail
indicator plus truncated energy for any nonnegative real sequence and any
positive energy cutoff. A general amplitude threshold `t>0` corresponds to
the energy cutoff `c=t^2`.

`RH/ParetoFirstSitePrimeThreeSeries.lean` specializes those results to the
actual `primeAngularInnovation`. Its
`riemannHypothesis_of_clipped_prime_angular_unbounded` keeps this provider
explicit:

\[
\forall B\in\mathbb R\ \exists N\in\mathbb N:\quad
  \sum_{n<N}\min(\Gamma_n,1)>B.
\]

This is an equivalent form of the angular sufficient condition, not an
unconditional proof of its hypothesis. Combining the classical realization
with the existing verified RH endpoint gives:
a.s. divergence of this auxiliary series implies RH; failure of RH forces
its a.s. convergence. The verified implications do not establish that RH
forces angular divergence alone.

The complete identity remains

\[
C_{N+1}=C_1+R_N+\sum_{n<N}\Gamma_n+J_N.
\]

`tailCapacity_tendsto_iff_prime_clipped_angular_channels` retains the exact
alternative: `R_N` fails to tend to zero, or the clipped angular energy is
unbounded, or the complete nonprime gain series is nonsummable. The weakest
full capacity inequality is still

\[
\forall B\in\mathbb R\ \exists N\ge1:\quad
 R_N+\sum_{n<N}\Gamma_n+J_N>B.
\]

Neither `U_N -> infinity` nor divergence of raw `V_N` supplies this.
In fact `W_N=V_N-X_N^2/U_N` at positive stages; the subtraction retains the
regression correlation and can absorb the raw error-energy growth.

For general independent variables, infinite raw variance does not force
series divergence. For example, take independent `Y_n`, for `n>=1`, with
probabilities `P(Y_n=n)=P(Y_n=-n)=1/(2n^2)` and otherwise zero.
Then `Var(Y_n)=1`, but summable nonzero probabilities imply only finitely
many nonzero terms almost surely. The three-series theorem uses truncated
variance. The symmetric-sign realization above avoids this rare-spike
obstruction because each coefficient has deterministic absolute size.

## Arithmetic research step

The existing verified inequality `E_n<=16*Gamma_n` uses

\[
E_n=\frac{1}{n+3}
 \left(\frac{\kappa_n}{\delta_n}-\frac{X_n}{U_n}\right)^2
\]

at positive prime stages and zero otherwise. A sufficient deterministic
target is a lower bound on disjoint prime blocks,

\[
\sum_{2^j\le n+3<2^{j+1}}E_n\ge b_j,
\qquad b_j\ge0,\quad \sum_j b_j=\infty.
\]

This allows individual centered errors to tend to zero. The required bound
must be proved for the actual screened factorial/CRT errors and running
slope; auxiliary independent signs do not provide it. These block lower
bounds and clipped angular unboundedness remain **Open**.
