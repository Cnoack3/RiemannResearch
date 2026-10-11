# Precise Selberg density input and strengthened actual-zero consequences

2026-10-11. All zero counts use actual analytic multiplicities and positive
ordinates. The all-sign count in the cited source dominates this count.

## Mathematical status and formalization boundary

Selberg's bound is an unconditional classical theorem for the Riemann zeta
function, not an unresolved mathematical hypothesis and not RH:

\[
N^+(\sigma,T)\le C T^{1-(\sigma-1/2)/4}\log T,
\qquad 1/2\le\sigma\le1,\quad T\ge T_0.
\]

The constants are independent of sigma and T. The exponent is explicit;
no numerical value of C is supplied. Source: Ford--Zaharescu, Lemma 2, p. 7:
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .

The new Analysis/ActualZeroSelbergDensity.lean module defines
`SelbergDensityBound T C a` and `UniformSelbergDensity a` precisely and proves
their consequences. It does not yet prove a provider of
`UniformSelbergDensity (1/4)`. That remaining obligation is **Open as a Lean
formalization**, while the classical result is established mathematics.
No project-local axiom, admitted proof, or RH premise is used.

## Verified deductions and stronger scope

For a general positive exponent a and positive T, the power density input is
exactly equivalent to

\[
N^+(\sigma,T)\le CT\log T\,
  e^{-a(\sigma-1/2)\log T}.
\]

The conventional inclusive count supplies the strict right-tail assumption
already used in ActualZeroFMZComparison. Multiplicity-preserving reflection
then gives the strict two-sided count bound, with the exact factor two.
Copies on the threshold remain good in the strict-tail convention.

With N(T) >= c T log T and c > 0, the new theorem proves

\[
\frac{\#\{0<\gamma\le T:
          |\beta-1/2|>\delta\}}{N(T)}
 \le \frac{2C}{c}e^{-a\delta\log T}.
\]

The existing unconditional Riemann--von Mangoldt result supplies such c.
For delta = (b/a) log(log T)/log T in [0,1/2], it proves the exact
shrinking-strip rate

\[
\frac{\#\{|\beta-1/2|>
        (b/a)\log\log T/\log T\}}{N(T)}
 \le \frac{2C}{c}(\log T)^{-b}.
\]

The statement allows real b and retains the strip admissibility condition;
b > 0 gives the intended decreasing rate.

For |u| < a log T the actual ordinate/Landau comparison is

\[
\left\|\frac{Z_T(u)-L_T(u)}{T}\right\|
 \le \frac{2C\log T\,u^2}{(a\log T)^2-u^2}.
\]

For every 0 <= theta < 1 and |u| <= theta a log T:

\[
\left\|\frac{Z_T(u)-L_T(u)}{T}\right\|
 \le \frac{2C}{a^2(1-\theta^2)}
       \frac{u^2}{\log T}.
\]

The classical a = 1/4, theta = 1/2 specialization returns 128 C / 3.
The uniform classical density input now feeds the already verified actual
fixed-mode limit directly. The full signed reflection identity and complete
finite endpoint formula remain in the imported comparison module.

## Scope of Haar/Poisson and RH statements

FMZ Corollary 1.1 already gives an unconditional finite prime-torus
specialization for its stated smooth Fourier-decay test class; Baker supplies
the required Diophantine condition for prime logarithms. The repository's
unfinished assembly of that theorem is a formalization gap. Stronger
infinite-prime or unrestricted test-space claims require their own precise
statements and proofs. Source: https://arxiv.org/abs/1511.06814 .

Sparse off-line zeros remain compatible with density concentration and phase
averages. The actual Pareto residual convergence and vanishing horizontal
detecting energy remain mathematical research obligations; none of the new
density consequences proves RH.

## Server verification

The coherent twelve-theorem candidate passed the server check
`job_g_2EoPheTC2qaVQM4c7q5f5fwp51Dpne`. Five selected transitive axiom
reports contain only propext, Classical.choice, and Quot.sound.
Publication of the persisted module and aggregate export is gated by the final
server checkpoint's source audit and affected-module validation.
