# Quantitative augmented density: Section 7.6

Source: user-provided *PQ_Augmented_Density_and_RH_Agenda.pdf*, dated 2026-11-14, Sections 2, 3, 5, 6.2 and 7.6. This catalog records the matching Lean implementation, not a proof of the remaining RH estimate.

All declarations below are in namespace `RiemannResearch.RH`. The implementation uses the repository's real Hilbert spaces, with exact physical sequences anchored at zero. The PDF also permits complex scalars; a separate complexification theorem is not added here.

## Finite tail estimates

Module: `RH/QuantitativeSieve.lean`.

`WeightedModel` records a continuous linear encoding, nonnegative summable physical weights, square summability, and the exact complete squared norm formula. Its concrete instances `qModel` and `pModel` discharge all these fields for Q and P. `tailMass A M` is exactly the sum of the indicated weights over physical sites n > M.

| PDF | Declaration | Exact content |
| --- | --- | --- |
| (8) | `approximation_error_sq` | Complete squared error of K D g_K at most tailMass(K-1). |
| (12) | `sieve_error_sq` | Complete squared error of the finite sieve at most tailMass(m N)/m². |
| (16) | `finiteApprox_error` | Two independent square-root tails divided by m. |
| (17) | `pointApprox_error` | Three-term indicator error with the exact m/(m+1) coefficient. |

The conductor L may be any nonzero integer satisfying `Covers L N`. This is the finite assertion that no integer from 2 through N is coprime to L. `primorial_covers` proves it for the PDF's actual L = primorial N. These finite coverage hypotheses are discharged, not open analytic inputs.

`sieve_sequence` identifies the finite Möbius sum with the coprime count divided by n. `finiteApprox_sub_sieve` retains the exact signed error identity before estimating. `finiteApprox_mem_augmentedSpan` verifies finite membership in the actual augmented family with conductors at least two. `tailMass_tendsto` proves that the complete tails vanish.

## Exact source and divergence

Module: `RH/PrimorialSieveLift.lean`.

`lift L` is exactly φ(L) g_L minus the divisor Möbius combination. `lift_mem_legalSpan` proves finite legal membership.

| PDF | Declaration | Exact content |
| --- | --- | --- |
| (36), floor form | `lift_sequence_floor` | C_L(n) - φ(L) floor(n/L). |
| (36), periodic form | `lift_sequence_count` | C_L(n mod L), at every physical site. |
| Half-count | `coprimeCount_half` | C_L(L/2) = φ(L)/2 for every even L > 2. |
| (37), first inequality | `lift_norm_sq_ge_half_sum` | Retains the finite inverse-square sum on [L/2,L). |
| (37), second inequality | `lift_norm_sq_lower` | Complete Q energy at least φ(L)²/(8 ζ(2) L). |
| Prime factorization | `totient_ratio_primorial` | Exact product of (p-1)²/p. |
| Divergence | `totient_ratio_primorial_tendsto` | The preceding product tends to positive infinity. |
| Correct damped target | `primorial_damped_lift_tendsto` | D(lift L_N) converges strongly to D1 in Q. |
| (38), source norms | `primorial_lift_norms_tendsto` | Complete undamped Q and P norms both tend to positive infinity. |

The divergence uses only finite prime products and infinitude of primes. The lower bound per odd-prime factor is 4/3. It makes no claim that other legal approximants must diverge.

## Two-measure leakage and conditional RH provider

Module: `RH/PQNormalizedLeakage.lean`.

`normalized_error_eq` is the exact signed orthogonal-projection identity. `q_normalized_error_le` and `p_normalized_error_le` prove equation (30) with the full Q and P weight tails respectively. The P statement uses the P-orthogonal projection onto the closed span of the same physical residue sequences; it does not transport the Q projection. `p_normalized_tendsto` retains the P residual as the actual limit. These are Hilbert norm estimates, not bounds uniform in the physical site.

The Priority 1 provider is:

```text
riemannHypothesis_of_finite_approximation_provider
  (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
  (a : ℕ → QHilbert)
  (ha : ∀ j, a j ∈ legalSpan)
  (hsmall : Tendsto
    (fun j => (k j : ℝ) * ‖B (qResidue (k j)) - a j‖)
    atTop (𝓝 0)) :
  RiemannHypothesis
```

Classification: **conditional research reduction**. The theorem is a proved implication. The remaining arithmetic obligation is **Open**: construct actual finite legal a_j along cofinal k_j and prove the complete small-o norm estimate hsmall. Neither augmented density, the tail estimates, nor the divergent diagonal lift discharges that premise.

`riemannHypothesis_of_cofinal_normalized_leakage` separately proves the subsequence criterion for the actual normalized Q leakage. Its zero-limit premise also remains **Open**.

Follow-up: [Finite density provider catalog](THEOREM_CATALOG_FINITE_DENSITY_PROVIDER_20261114.md)
records the explicit legal family
a_(k,N) = g_k/zetaTwo + candidate(N)/(zetaTwo*k).
Its scaled error converges to the actual constant residual for independently
cofinal k and N, and is asymptotically optimal. The new
QDensityFiniteProvider.one_mem_iff_finite_provider proves that the small-o
provider exists exactly when qOne is in the legal closure. The witness can
always be this explicit family; proving the small-o rate remains **Open**.

## Verification

The source files include explicit axiom reports for the central theorems. Accepted proofs must have only ordinary foundations (`propext`, `Classical.choice`, `Quot.sound`), with no unfinished proof or project-local arithmetic axiom. Publication is through the managed Bazel/BuildBuddy full-project checkpoint; the checkpoint job and exact commit are reported in the accompanying delivery.

Focused Bazel acceptance passed in job `job_GHal3wPTOw5Z1YZLaZW8oyELs4YYOflT`
(server verification time 105.738 seconds):
[BuildBuddy receipt](https://app.buildbuddy.io/invocation/875ed9f4-a7cf-4b6a-9337-8dd73040d483).

Thirteen central declarations also passed an independent guarded axiom-report
check in job `job_tZJO2n9s32l65tuK38hCQD6DGWH9LH4_`
(server verification time 50.518 seconds):
[BuildBuddy receipt](https://app.buildbuddy.io/invocation/f52af68e-7a64-4eea-8272-8a435f497a56).
The snippet used `#guard_msgs (whitespace := lax)` around each
`#print axioms`, requiring exactly `propext`, `Classical.choice`, and
`Quot.sound`. This covers the four finite error bounds, finite augmented
membership, the physical count, the source lower bound, damped convergence,
divergence in both norms, both leakage errors, the P limit, and the finite
approximation RH provider. These are focused acceptance receipts; final
publication additionally requires the complete-project checkpoint.
