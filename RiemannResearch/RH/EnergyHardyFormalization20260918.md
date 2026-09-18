# Energy-to-holomorphy and Hardy implications in Lean

Date: 2026-09-18.

## Established analytic results

For a measurable complex function f on the real line, write

    E_s(f) = integral_(1,infinity) ||f(x)||^2 x^(-s-1) dx
    M_f(z) = integral_(1,infinity) f(x) x^(-z-1) dx.

FiniteEnergy means measurability AND integrability of the energy density.
It never means merely that Lean's totalized integral has a finite real value.

Analysis/WeightedMellinEnergy.lean establishes:
- transform_integrable: absolute integrability when Re(z)>s/2.
- transform_norm_sq_le: ||M_f(z)||^2 <= E_s(f)/(2 Re(z)-s).
- transform_hasDerivAt: differentiation under the integral, with -log(x).
- transform_analyticAt: holomorphy throughout Re(z)>s/2.
- finiteEnergy_mono and energy_mono: increased damping preserves integrability
  and decreases energy.
- energy_tendsto: energies approach E_s along any sequence of exponents >=s
  tending to s.

Analysis/WeightedMellinHardy.lean establishes:
- logLift_integrable and logLift_memLp: the logarithmic lift is L1 and L2
  on every interior vertical line.
- logLift_fourier: the actual Mellin integral equals the ordinary Fourier
  integral of that lift, with z=sigma+2*pi*i*w.
- vertical_memLp: the actual transformed function is L2, derived from
  unitary Plancherel rather than assumed.
- vertical_plancherel and angular_plancherel: exact line identity

    (1/(2*pi)) integral_R |M_f(sigma+i*t)|^2 dt = E_(2*sigma)(f).

- energy_to_hardy: finite E_s implies HardyH2 on Re(z)>s/2.
- hardy_energy_isLUB: the supremum of the normalized line energies is
  exactly E_s(f).

HardyH2 is defined explicitly by analyticity, actual L2 membership of
every vertical line, and a common bound for its squared integral norm.
It uses the equivalent Fourier-frequency parametrization 2*pi*w;
angular_plancherel provides the conventional angular normalization.

## Conditional Chebyshev consequences

RH/ChebyshevEnergyHardy.lean uses the existing actual errorMellin integral.
ErrorFiniteEnergy(s) is integrability of (psi(x)-x)^2 x^(-s-1).
Its measurability is proved using the existing psi_measurable theorem.

- errorMellin_analyticAt_of_energy proves holomorphy on Re(z)>s/2.
- errorMellin_hardy_of_energy proves HardyH2 on that half-plane.
- errorMellin_analyticAt_of_all_damping proves holomorphy on Re(z)>1/2
  from ErrorFiniteEnergy(1+epsilon) for every epsilon>0.

These are conditional research reductions: the actual arithmetic energy
hypotheses remain Open. No RH proof follows without supplying them and
completing the relevant continuation/identification arguments.

## Scope not claimed

This addition proves the forward energy-to-holomorphy/Hardy bridge.
It does not formalize the general Paley--Wiener converse, L2 boundary trace
convergence, reset-truncation identities, or the complete transfer from
prime-power signed prefix sums through geometric energy to Chebyshev error.
The all-positive-damping signed arithmetic bound remains unproved.
The earlier meromorphic RH criterion remains a separate checked equivalence.

## Provenance and verification

Source: user-requested mathematical companion
RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md.
The proof strategy is Cauchy--Schwarz, dominated differentiation, logarithmic
change of variables, the project's ordinary-integral Plancherel theorem,
and dominated convergence. No mathematical novelty is claimed.

The combined development passed Lean in
job_PinzcTHBSB7vOjYlI0mnbHFV5y6YXgrE, exit code 0, verified true.
Axiom inspection of the main point bound, analyticity, Hardy implication,
angular Plancherel, exact supremum, and Chebyshev implications reports only
propext, Classical.choice, and Quot.sound. The final checkpoint separately
validates the saved import graph and affected dependents before publication.
No proof placeholders or project-local axioms are added.
