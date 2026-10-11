# Finite-prime FMZ assembly and the remaining Selberg provider

2026-10-11. This development completes the finite-prime arithmetic,
Haar/Poisson and classical Fourier-decay assembly **conditional on Selberg
density**. It does not prove the requested unconditional Selberg provider.

## Exact final theorem

The principal declaration is
`ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson_of_selberg`
in Analysis/ActualPrimeTorusFMZContinuous.lean.

Let P be any finite set of primes, d = card(P), and let f be a continuous
complex-valued function on (R/Z)^P. Assume its conventional Fourier
coefficients satisfy

    norm(fhat(k)) <= C * (1 + norm(k))^(-B),   C >= 0,   B > d + 2.

Here the norm on integer modes is the maximum-coordinate norm. The theorem
proves, with actual analytic zero multiplicities,

    [sum_(0 < gamma <= T) m_rho f((gamma log p / (2 pi))_(p in P))
       - N(T) integral f dHaar] / T
       -> integral f * g_P dHaar,

where Haar is the actual product of normalized circle Haar measures and

    g_P(x) = -sum_(p in P) (log p)/(2 pi) * (P_(1/sqrt p)(x_p) - 1).

The continuous Poisson kernel is the previously proved actual kernel:

    P_r(x) = (1 - r^2)/(1 - 2 r cos(2 pi x) + r^2).

The exact remaining analytic premise is

    UniformSelbergDensity (1 / 4).

It expands to constants C_D >= 0 and T_0 > 1, independent of sigma and T,
such that for every T >= T_0 and 1/2 <= sigma <= 1,

    N^+(sigma,T) <= C_D * T^(1 - (sigma - 1/2)/4) * log T.

N^+ counts all actual positive-height nontrivial zeros with beta >= sigma,
including analytic multiplicity. No RH, zero simplicity, assumed Landau
limit, assumed Haar coefficient, or assumed FMZ conclusion is used.

## Newly proved components

- ActualRationalFMZLimits: unconditional actual rational Landau limits;
  both ordinate signs and exact constant-mode centering under Selberg.
- ActualZeroCountUpper: unconditional uniform N(T) <= C T log T and
  the corresponding bound for every ordinate character.
- ActualRationalFMZDomination: an unconditional uniformly bounded rational
  Landau remainder when log(n) <= log(T)/8; under Selberg, one simultaneous
  bound K[1 + (log n + log m)^2] for every centered rational mode;
  infinite Fourier synthesis by dominated convergence.
- FinitePrimeModeArithmetic and FinitePrimeModeCoefficients: exact reduced
  prime numerator/denominator products, independence of prime logarithms,
  prime-power support and the coefficient -log(p)/(2 pi) p^(-abs(k_p)/2).
  Every mixed mode is proved to have coefficient zero.
- PrimeTorusHaarSpecialization: actual product Haar integrals, zero-mean
  signed Poisson density, single-axis coefficients and mixed-mode vanishing.
- PrimeTorusFourierSeries: actual continuous series and exact interchange
  with multiplicity-weighted zero sampling and product-Haar integration.
- ActualPrimeTorusFMZ and ActualPrimeTorusFMZPoisson: the literal centered
  finite polynomial theorem with the actual Poisson integral.
- ActualPrimeTorusFMZSeries: infinite weighted absolutely convergent series,
  with weight exactly 1 + (sum_p abs(k_p) log p)^2.
- PrimeTorusFourierDecay: the original strict threshold B > d + 2 implies
  this weighted summability by integer-lattice rpow summability.
- PrimeTorusFourierInversion: mathlib's multidimensional Fourier inversion
  identifies the series with the original arbitrary continuous function.
- ActualPrimeTorusFMZContinuous: the complete finite-prime specialization
  in the original Fourier-decay class, retaining only the Selberg premise.

No Baker-type input is needed in this prime specialization: the explicit
reduced rational frequencies and the proved uniform rational contour estimate
supply the necessary mode control directly. No general-frequency or
infinite-prime FMZ theorem is claimed.

## Why the unconditional request remains unfinished

Selberg's estimate is established mathematics, not an open conjecture.
A reference is Ford--Zaharescu, Lemma 2, p. 7:
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .

A complete proof route is Aleksander Simonic, Sections 2--4:
https://arxiv.org/pdf/1910.08274 .

The repository has actual Littlewood contour and mollifier-boundary machinery,
but not the uniform twisted zeta second moment needed for Selberg's optimal
mollifier. A full provider still requires approximate-functional-equation
estimates, uniform twisted mean-square control, the Selberg mollifier
arithmetic and moment bound, horizontal argument control, and dyadic assembly.
Merely citing these analytic theorems or declaring them as axioms would not
discharge the Lean premise. No such axiom or placeholder has been introduced.

The classical finite-prime FMZ source is Ford--Meng--Zaharescu,
Corollary 1.1: https://arxiv.org/abs/1511.06814 .

## Classification and validation

The final result is a **conditional research reduction** in Lean, with a
classical unconditional analytic input still **Open as a Lean formalization**.
All arithmetic, Haar, summability and reconstruction obligations in the
finite-prime specialization are discharged.

The full final theorem passed server job
`job_OtQVX0ftHIlDEPaKhFxqe0TSPsH7hZA5`, and its transitive axiom
report contains only propext, Classical.choice and Quot.sound. This axiom
report does not remove the displayed Selberg hypothesis. Publication is
gated by the task's final server checkpoint, which audits the source and
builds the exported development before committing and pushing.
