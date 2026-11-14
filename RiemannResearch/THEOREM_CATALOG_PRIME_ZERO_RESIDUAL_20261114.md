# Actual prime/zero residual criterion — 14 November 2026

Status: **conditional research reduction**. Arithmetic cancellation is Open.
Starting revision: `05e68bb04b2c7b4c061d1bc242c3df21e6d27cdd`.

## Actual objects

Let r_N = qOne - candidate N, where candidate N is the literal inverse-Gram
projection onto the full conductor stage (conductors 2 through N+1), and
let r_infinity = qOne - P_closure(qOne). The existing project proves strong
convergence r_N -> r_infinity without RH.

Set Q(n) = 1/(zeta(2)n^2), for n >= 1. The finite observation is

```math
E(N,H,T) = (1/N_zeta(T)) sum_{0<Im(rho)<=T} m(rho)
  | sum_{1<=n<=H} sqrt(Q(n)) r_N(n) exp(i Im(rho) log n) |^2.
```

Here N_zeta(T) counts all actual positive-ordinate zeros with analytic
multiplicity; r_N(n) denotes the physical Q-sequence, not its weighted l2
coordinate. `positiveCoefficients_physical` checks the normalization.
The value at an empty cutoff is zero by totalized division, and eventual
positive counts are supplied by the existing zero-count theorem.

## Established structural results

- `complexCoordinates_norm`, `fockResidual_norm`, and
  `fockResidual_integer_coordinates` put the actual residual isometrically
  in the new zeta-generated prime Fock subspace and identify its integer
  coordinates. This is not an identification with the entire Fock space.
- `sampledEnergy_eq_mean` is the exact actual-zero-copy energy identity.
- `sampledEnergy_signed_identity` retains the diagonal coefficient energy,
  the complete signed rational FMZ prime-power form, and the literal remainder:
  E = ||c||_2^2 + Re[(T/N_zeta(T)) B(c)] + Re[R_T(c)].
  No off-diagonal term is silently discarded.
- `sampledEnergy_tendsto_of_coefficients` permits simultaneous moving sample
  heights and converging coefficients on any fixed finite positive-integer head.
- `eventually_finite_detection` gives, for each fixed finite head, one
  eventual sampling threshold valid for every coefficient vector:
  (1/2)||c||_2^2 <= E_T(c) <= (3/2)||c||_2^2.
- `exists_cofinal_detection_schedule` selects cofinal heights for arbitrary
  prescribed finite heads. It asserts existence, not an explicit efficient rate.

Every sampling-limit result retains `0 < a` and `UniformSelbergDensity a`.
Thus a=1/4 suffices; the full Conrey--Baluyot range is unnecessary here.
Neither the classical density provider nor the improved provider is proved
by these modules.

## Exact residual target and RH consumers

For any cofinal N_j and T_j, the conditional theorem
`sampled_cancellation_iff_residual_zero` proves:

```math
[for every fixed H, E(N_j,H,T_j) -> 0] <-> r_infinity = 0.
```

The strong limit of the actual projections is essential. It prevents an
uncontrolled changing residual from escaping every fixed observation head.
This is detection on the actual convergent residuals, not a positive lower
frame bound on the entire infinite-dimensional sampled space.

`riemannHypothesis_of_sampled_residual_cancellation` then transfers actual
full-Q closure to the existing Pareto Mellin obstruction and yields RH.

For arbitrary cofinal residual stages N_j and head sizes H_j,
`exists_cofinal_sampling_RH_test` proves the existence of cofinal T_j such
that the single additional arithmetic statement

```math
E(N_j,H_j,T_j) -> 0
```

implies RH. The finite comparison is supplied by the density-based sampling
schedule; no separate infinite-tail estimate is assumed.
`residual_zero_of_growing_sampled_energy` states the stronger intermediate
conclusion r_infinity=0 with its finite comparison explicit.

## Open obligations

1. **Open:** prove the displayed sampled residual energy tends to zero for the
   actual full-conductor inverse-Gram coefficients. The definition
   `SampledResidualCancellation` records this proposition and supplies no proof.
2. **Formalization gap:** discharge the chosen positive Selberg density input
   independently. These files do not introduce an arithmetic axiom.
3. If quantitative usable heights are needed, replace the existential sampling
   schedule by an explicit rate with all coefficient/support dependence.

The new coordinate and sampling structure does not establish RH or arithmetic
cancellation. Raw residual-numerator values at full zeros, which the existing
`ResidualZeroSensors` module shows are constant, are not substituted for
these finite coefficient observations.

## Source and acceptance

Modules:
- `RiemannResearch/Analysis/ActualResidualSampling.lean`
- `RiemannResearch/RH/QFullPrimeZeroResidual.lean`

Source: user-directed research and the cited owning project modules.
FMZ sampling context: Ford--Meng--Zaharescu (2017),
https://arxiv.org/abs/1511.06814 .

Saved-module validation succeeded with Bazel/BuildBuddy:
- Job: `job_kLsBEFcSXjo58Xisy5TdIcLcVIhGpKqk`.
- Request SHA-256:
  `156b027dc1cc849677649b5df4af5127f2c0a95e6612de0a0ee909a4ec20cf4a`.
- Both saved modules were imported, and all 21 public theorems passed
  `#guard_msgs (whitespace := lax)` checks of `#print axioms`.
- Each dependency list is exactly
  `[propext, Classical.choice, Quot.sound]`; no arithmetic axiom or
  proof placeholder is hidden by the check.
- Server-reported verification duration: 47.995 seconds.
- BuildBuddy receipt:
  https://app.buildbuddy.io/invocation/2420da42-d506-4b7c-b2c1-96381a5f2698

These checks validate the conditional statements, not their open arithmetic
inputs. Managed publication additionally requires the checkpoint's source
audit and full-project Bazel/BuildBuddy validation.
