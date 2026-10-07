# Actual source-resolvent product advance

Date: 7 October 2026. Base: da1d01a43df6cc60a04b7af8d2f20dfe415ee7a8.
This continues the supplied RH_Source_Resolvent_Continuation_20261007.md.
RH and the substantive arithmetic upper budget remain open.

## Results and exact indexing

At spectral stage n=4m put N=4m+4,
u_N=compactCorrectedHilbert N, U_N=||u_N||²,
q_N=compactReciprocalSum N, and P_m=U_N S_(4m).
T_n and S_n retain every constructed actual source weight and eigenvalue.
The established inputs U_N/N→0, q_N→0, S_n→0, T_n→δ are reused.

Analysis/FiniteSpectralResolvent.lean now supplies the exact identity,
for every t>0,

D(t)+(t−1)S−T
 = (t−1)² Σ_i w_i λ_i /[(1+λ_i)²(t+λ_i)].

The entire nonnegative remainder is displayed before estimation, including
t=1. Consequently T+S≤D(t)+tS at every positive scale. Combining the
already established complete actual trial estimate D(t)≤q_N²+U_N/t and
optimizing gives

T_(4m)+S_(4m) ≤ q_N²+2√P_m.

This improves the suggested threshold bound
S+2q²+2√(2US). The optimization proof includes U=0 and S=0.

The complete finite derivatives are now supplied:

F'(t)=−Σ_i w_i/(t+λ_i)²,
S=F(1)+F'(1), and D'(1)=−S.

Declarations include sourceDeficit_tangent_remainder,
correction_add_tail_le_trial_product,
optimizerTail_eq_sourceResolvent_add_deriv, and sourceDeficit_deriv_one.
The finite scalar candidate, including the calculus identities, passed an
isolated Lean check with exit code 0 and empty diagnostic output. The new
resolvent, source-coordinate and actual-product modules also passed the
checkpoint build. Final publication additionally validates reverse dependents.

## Sharper actual signed obstruction

The repository already established twoThree_actual_trial_signed_identity
and its complete-tail Cauchy bound in ParetoTrialTailConditions.lean.
No duplicate general projection theorem is introduced.

Define the literal signed pairing

L_m = <tail P_(V_(N−1))v, tail u_N>,  v=twoThreeDual.

The exact full residual equation is

||v−P_(V_(N−1))v||²
 = <Q_N(v−P_(V_(N−1))v), v−Q_N u_N> + L_m.

The head term is bounded in absolute value by
||v|| ||v−Q_Nu_N||, and the existing charge square supplies
||v−Q_Nu_N||≤|q_N|→0. Therefore, UNCONDITIONALLY,

L_m→δ,
L_m²≤||tail u_N||² S_(4m)≤U_N S_(4m)=P_m.

RH/ParetoCompactTailProduct.lean specializes the existing signed identity
to the literal trial and complete constructed spectrum. It supplies:

- compactFourfoldSignedTailPairing_tendsto_defect;
- compactFourfoldSignedTailPairing_sq_le_product;
- compactFourfoldTailProduct_lower_floor:
  every a<δ² is eventually strictly below P_m;
- compactFourfold_conductor_tail_tendsto_atTop_of_defect_pos:
  if δ>0, then (4m+4)S_(4m)→+∞.

The last assertion follows by writing
P_m=[(4m+4)S_(4m)] [U_N/(4m+4)] and using U_N/N→0.
It strengthens the earlier statement that a bounded cofinal conductor-tail
budget would contradict a positive defect. No positive defect is asserted.

At paper level the same signed equation immediately gives the stronger
finite full-error bound

||v−P_(V_(N−1))v||² ≤ √134 |q_N| + √P_m.

The exact equation and the asymptotic coefficient-one obstruction are the
primary results; the displayed simplified finite square-root bound is not a
separate newly exported Lean declaration.

## Conditional RH consumers

The actual product consumer now discharges every geometric/head provider.
Its sole substantive arithmetic hypothesis is cofinal P_(k_m)→0 with
k_m→∞. Arbitrarily late, arbitrarily small P_m is also enough.

A more flexible consumer requires, only cofinally,

P_(k_m) ≤ θ T_(4k_m)² + E_m,   θ<1,   E_m→0.

The exact signed pairing and correction both tend to δ, hence this budget
would yield δ²≤θδ² and force δ=0. The product need not be proved to vanish
as a separate premise.

Declarations:
riemannHypothesis_of_compactFourfold_cofinal_tailProduct,
riemannHypothesis_of_compactFourfold_arbitrarily_late_small_tailProduct,
riemannHypothesis_of_compactFourfold_cofinal_product_fraction.

These are **conditional research reductions**. Providers for the displayed
upper budgets remain **Open**. No RH-to-canonical-product converse is claimed.

## Original conductor coordinates and the full matrix

RH/ParetoOriginalSourceCoordinates.lean supplies the exact original source
pairing 3*C_2(x)+C_3(x). In conductor order 2,3,...,N the source is literally

b=(3,1,0,...,0).

This is not permission to discard later conductors. Their full interactions
remain in the head Gram H and complete infinite-tail Gram K.

The following complete finite matrix bridge is a paper proof, not a newly
exported inverse-transport Lean theorem. Let E send coefficients to their
physical head and A send them to the full tail. Head injectivity is already
checked; hence H=E*E is positive definite and K=A*A is positive semidefinite.
For t>0, M_t=K+tH is positive definite. The normal equation
M_t c_t=b and uniqueness transport c_t to the regularized head operator.
Thus

F(t)=bᵀ M_t^(-1)b,
F'(t)=−c_tᵀHc_t,
F(t)+tF'(t)=c_tᵀKc_t.

At t=1, G=H+K and S=bᵀG^(-1)KG^(-1)b.
The physical minimizer for loss t||v−head||²+||tail||² has coefficients
t*c_t; its tail square is t² c_tᵀKc_t. Keep this scaling explicit.

For a 2+(N−3) block decomposition, exact elimination uses the FULL
Schur complement M_11−M_12 M_22^(-1)M_21. The 2×2 principal block alone
does not give F(t). The sparse b leaves all later-conductor interactions in
the inverse and in the transported tail Gram.

## Quantitative arithmetic progress

RH/CanonicalMobiusLogEnvelopeEnergy.lean proves
canonicalMobius_energy_of_uniform_mertens_log, strengthening the existing
uniform Mertens-to-energy transfer. The proof also appears in
RH/ParetoUniformMertensEnergyTransfer20261007.md.
If |M(y)|≤εy for all y≥N and
h=ε(1+log(1/ε))≤1/2 with 0<ε≤1, then

|m_N|≤5h,   ||A_N||²≤3+260Nh.

The old square-root transfer costs sqrt(ε); the new proof costs
ε(1+log(1/ε)). It uses the already checked reciprocal cutoff inequality and
harmonic-energy inequality, retaining the full far tail.

For the existing checked stretched Mertens envelope B exp(−dΦ(N)), the
paper corollary permits any exponential coefficient ρd with 0<ρ<1, in place
of the assembled d/2 coefficient. The complete three-family compact trial
obeys U_N≤5130+1122 C N E(N/8) when ||A_Y||²≤3+C Y E(Y) and E decreases.
The finite logarithmic transfer passed a full-file Lean check with exit code
0 and empty diagnostics. The stretched-rate corollary and compact-trial
constants in this paragraph remain paper consequences.

Lee–Leong's substantially revised 9 September 2026 preprint supplies an
additional unconditional Korobov–Vinogradov Mertens envelope. It can feed
this paper transfer, after monotonicity and polynomial absorption. Its
analytic theorem is not currently a checked Lean provider.
Source: https://arxiv.org/html/2208.06141v5 (Theorem 1.1, equation (12)).

None of these stronger trial estimates supplies the actual product saving.

## Wolfram computations and their limits

Wolfram independently reduced the scalar tangent remainder difference to
0, checked the positive-scale optimizer substitution, and returned
D'(1)=−wλ/(1+λ)² for one mode.

It also evaluated the ORIGINAL all-conductor Gram numerically at 60-digit
working precision. For each pair (d,e), the infinite physical norm was
summed through its exact periodic digamma formula with l=lcm(d,e),

G_de=Σ_(a=1)^(l−1) (a mod d)/d * (a mod e)/e *
      [ψ((a+1)/l)−ψ(a/l)]/l.

H uses physical sites 1,...,N, K=G−H, c=G^(-1)b.
No physical-tail truncation is used in this numerical calculation.

| N | full projection error 134−bᵀG^(-1)b | S=cᵀKc | N S |
|---:|---:|---:|---:|
| 4 | 27.9798786200 | 19.5473127595 | 78.1892510379 |
| 8 | 17.9885695693 | 10.7881101046 | 86.3048808370 |
| 12 | 14.1742651296 | 8.1957471946 | 98.3489663351 |
| 16 | 13.2458762423 | 6.0955899206 | 97.5294387294 |
| 24 | 11.9130704625 | 5.3965625201 | 129.5175004817 |

These are finite high-precision explorations, not interval certificates or
asymptotic evidence of bounded NS. The matrix bridge's Lean transport is
still open. The nonmonotone small-N tail budget must not be extrapolated.

## Why better trial energy alone cannot close RH

Fix δ>0. In a one-dimensional graph take source mass δ, tail eigenvalue
λ_N→∞ with λ_N=o(N), and exact-head trial c=b. Its FULL physical energy
is U_N=δ(1+λ_N), and

T_N=δλ_N/(1+λ_N),
S_N=δλ_N/(1+λ_N)²,
D_N(t)=δλ_N/(t+λ_N).

Then U_N=o(N), D_N(t)≤U_N/t, S_N→0, and highMass(cN)→0 for every c>0,
yet T_N→δ and U_NS_N→δ². Thus the coefficient-one signed product floor
is sharp for general graph models. This is an abstract audit model,
not the actual arithmetic spectrum.

## Primary-source audit

- Báez-Duarte, strengthening of Nyman–Beurling:
  https://arxiv.org/abs/math/0205003. Quantitative approximation there
  assumes RH; it cannot discharge the present unconditional provider.
- Boţ–Hofmann, conditional stability and Lavrentiev regularization:
  https://www.mat.univie.ac.at/~rabot/publications/jour16-09.pdf,
  Section 4, equation (4.8). Quantitative rates require approximate-source
  distance control, which is additional input for changing stage operators.
- A recent ladder-decay claim in https://arxiv.org/pdf/2510.18132,
  Theorem 6.1, uses |a log2+b log3|≥min(log2,log3)(|a|+|b|).
  The pair a=1,b=−1 already violates it. That proof step cannot be used
  to provide the unsmoothed actual optimizer-tail estimate.

## Next work and ledger

1. Formalize the original full Gram inverse transport and the exact Schur
   complement in the conductor basis. Source coordinates and spectral
   derivatives are now available.
2. Attack the retained signed optimizer–trial pairing or its strict
   fractional product budget, using full Schur/CRT arithmetic before
   absolute values. Do not substitute a 2×2 principal truncation.
3. Assemble the sharper stretched-rate corollaries from the now-formalized
   logarithmic Mertens-to-energy transfer. They improve quantitative trial
   envelopes without resolving optimizer cancellation.
4. Seek a uniform arithmetic source-regularity estimate for the actual
   changing matrices. A standard regularization theorem with an unproved
   source condition is not a provider.

| Obligation | Status |
|---|---|
| Exact full-source tangent remainder and finite derivative identities | Lean formalization |
| Literal original source coordinates (3,1,0,...) | Lean formalization |
| Actual signed pairing→δ and product lower floor δ² | Lean formalization |
| Positive defect forces N S→+∞ | Lean formalization |
| Cofinal vanishing/strict fractional product implies RH | Conditional Lean reductions |
| Actual arithmetic product upper provider | Open |
| Original matrix inverse transport | Paper proof; Lean assembly open |
| Improved finite ε(1+log(1/ε)) energy transfer | Lean formalization |
| Sharper stretched-rate and compact-trial corollaries | Paper proof; Lean assembly open |
| Lee–Leong analytic rate imported as a Lean provider | Open formalization |
| RH | Open |

Publication policy: source audits and changed-module/reverse-dependent Lean
validation must succeed before the checkpoint publishes this development.
No separate full-project GitHub CI success is asserted.

Verification record: ten selected new declarations were audited together in
Lean with exit code 0. They cover the exact remainder, optimized product,
derivatives, actual signed limits, divergence, strict-fraction RH consumer,
original source and finite logarithmic energy transfer. Each uses only
propext, Classical.choice and Quot.sound; no research axiom is introduced.
