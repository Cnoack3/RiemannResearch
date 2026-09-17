# Conditional iid / Cesàro completion: source coverage audit

Date: 2026-09-17. Scope: Sections 2–6 of `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`, plus the classical RH-to-density dependency.

This is a bounded **source audit**, not a new compilation or axiom audit. I read the workspace AGENTS instructions, searched declaration names first, and inspected relevant source ranges. I ran no Lean snippets, diagnostics, outlines, builds, or checkpoints and made no remote edits. The existing declarations below must not be represented as newly verified by this audit.

Namespace abbreviations:
- `CI` = `RiemannResearch.Probability.ConditionalIID`.
- `C` = `RiemannResearch.Analysis.Cesaro`.
- `P` = `RiemannResearch.RH.Pareto`.
- `AC` = `RiemannResearch.RH.ArithmeticCumulative`.

## Main finding

The actual infinite probability model, genuine conditional independence, full signed replica identities, Mellin coefficient estimates, and approximation-to-actual-Mathlib-RH implications already have substantial source coverage. The completion adds claims that are **not all covered**: exchangeability and latent recovery/SLLN; a packaged Cesàro continuous operator and explicit adjoint/kernel; the Mellin pairing for every unbounded Hilbert vector; and RH-to-density without an explicit classical provider.

The reverse classical theorem is an identified unproved provider, not a kernel-checked theorem hidden in an import.

## Section 2: actual common infinite probability space

| Completion claim | Existing declarations / module | Exact scope and caveat |
|---|---|---|
| One common measure with countably infinite rows | `CI.Path`, `CI.Omega`, `latentPMF`, `uniformLaw`, `pathLaw`, `pathKernel`, `probability` in `Probability/ConditionalIIDUniformModel.lean` | `Path = ℕ → ℕ`, `Omega = ℕ × Path`; latent predecessor k represents positive endpoint k+1. `probability = latentLaw.compProd pathKernel`; actual `IsProbabilityMeasure` instances. |
| Conditional uniform product cylinder law | `pathLaw_cylinder`, `joint_latent_cylinder`, `conditional_path_law`, `conditional_path_law_ae` in same module | Actual `condDistrib` of the entire infinite path, rather than assumed numerical moments. |
| Actual conditional iid | `conditional_path_event`, `conditional_coordinate_event`, `coordinates_iCondIndepFun` in same module | The last declaration concludes Mathlib's `iCondIndepFun latentSigma latentSigma_le coordinate probability`. Identical conditional laws are explicit in the event theorem. |
| Integrable-observable conditional expectation | `conditional_path_expectation` in same module | Assumes `StronglyMeasurable F` and actual `Integrable (fun ω => F ω.2) probability`. This is path-observable scope; it is not the completion's standalone atom formula for every arbitrary X on Omega. |
| Exact positive Pareto marginal | `coordinate_positive_mass`, `coordinate_zero_mass`, `coordinates_identDistrib` in `Probability/ConditionalIIDMarginal.lean` | Proves actual event probabilities and zero mass at 0. Identical marginal laws do **not** themselves prove exchangeability. |
| Prime-exponent row measurability, finite support, conditional iid | `exponentRow_measurable`, `exponentRow_finite_support`, `primeRows_iCondIndepFun`, `primeRow_conditional_event`, `primeRows_iCondIndepFun_endpoint` in `Probability/ConditionalIIDPrimeRows.lean` | Row is factorization of 2K. No prime-column independence asserted. |
| One common a.s. finite active-prime set and reconstruction | `all_coordinates_support`, `ae_finitely_many_active_columns`, `original_integers_ge_two`, `ae_primeRows_reconstruction` in `Probability/ConditionalIIDLatentSupport.lean` | Actual a.s. statements quantified over every row. |

Not located in the relevant model modules or declaration-name searches:
1. Invariance under all finite permutations / exchangeability.
2. Eventual equality of the running maximum with the latent endpoint, equation (2.5).
3. Empirical-frequency strong law and the single-event simultaneous statement for every arithmetic F, equation (2.6).
4. The explicit floor/lcm divisibility probability identities (2.7). The finite uniform event law is available as a starting point.
5. A standalone `E[X | σ(T)]` latent-atom formula for all integrable X (the existing stronger path-kernel API covers needed row observables).

## Section 3: moments, integrability, and signed energy

| Completion claim | Existing declaration / module | Exact hypotheses |
|---|---|---|
| Each finite uniform observable is integrable; mean formula | `CI.uniform_integrable`, `uniform_integral`, `path_integral_coordinate`, `conditional_coordinate_expectation` in `ConditionalIIDUniformMoments.lean` | Global conditional expectation requires actual observation integrability. |
| Conditional variance is actual condVar | `CI.conditional_variance_ae` in `ConditionalIIDWeightedEnergy.lean` | Assumes `MemLp (fun ω => F (coordinate i ω)) 2 probability`. |
| Sample mean conditional square identity | `CI.conditional_average_error` and `average_error` in `ConditionalIIDSampleMean.lean` | Positive sample size; global row L2 assumptions explicit. |
| Weighted sample error | `CI.average_error_weighted` in `ConditionalIIDWeightedEnergy.lean` | One actual marginal L2 assumption, positive r. Gives mean error plus expected actual conditional variance divided by r. |
| Cesàro weighted-square contraction | `CI.weighted_cesaro_energy_le` in same module | Assumes actual marginal MemLp at row 0. This is not yet a bundled H →L[ℝ] J operator. |
| Weighted integration / marginal link | `CI.coordinate_integral`, `latent_integral`, `coordinate_real_singleton` in same module | Integrability explicitly assumed for Bochner integrals. |
| Conditional cross products | `CI.conditional_cross_product`, `cross_product_integral` in `ConditionalIIDReplica.lean` | Distinct row indices and L2 hypotheses on F and G. |
| Full signed Gram / replica identities | `CI.signed_gram_identity`, `replica_energy_identity`, `replica_error_identity` in same module | Actual expectation identities; off-diagonal and mixed terms retained. |
| Legal witnesses supply their own L2 integrability | `P.legal_observation_memLp` in `RH/ConditionalIIDNymanCriterion.lean` | Legal seed span, all seed integers positive; proved from boundedness. |

For arbitrary F∈H, source coverage is expressed primarily by the actual `MemLp` hypothesis. The audit did not locate a completed general conversion from weighted-square summability to that MemLp hypothesis and a bundled Hilbert map. The exact (3.6) convex combination of *two weighted norms* follows mathematically from the recorded actual moment identities, but that precise assembled declaration was not found. Complex sesquilinear replica versions were not found; the audited probability declarations are real-valued.

## Section 4: inversion, operator, adjoint, and kernel

Established source:
- `C.recover` and `mean_injective_on_positive`, `Analysis/CesaroFiniteCalculus.lean`: exact positive-coordinate inversion with the zero boundary handled.
- `C.cesaro_adjacentPulse`, `adjacentPulse_fullSquaredNorm`, `adjacentPulse_conditionalMeanSquare`, `adjacentPulse_energy_ratio`, and `no_positive_cesaro_energy_lower_bound`, `Analysis/CesaroPulseObstruction.lean`: exact pulse norms and proof that no uniform positive lower energy constant exists. Actual summability is proved for these finite-support pulse vectors.
- `CI.weighted_cesaro_energy_le`: contraction inequality as above.

Not located:
- A constructed continuous linear operator C:H→J.
- Dense but nonclosed operator range.
- Bayes conditional endpoint distribution, explicit C* formula, C* contraction and injectivity.
- Exact two-row kernel K(max(a,b)), its reciprocal-square closed form, absolute double-series convergence, and the reversible Markov transition matrix C*C.

The pulse theorem does not claim the pulses are legal Nyman–Beurling functions, and it must not be interpreted as disproving a legal-witness-specific bound.

## Section 5: Mellin coefficients, normalization, and extension

| Claim | Existing declaration / file | Exact boundary |
|---|---|---|
| Pointwise first/second difference bounds | `C.mellinFirst_norm_le`, `mellinSecond_norm_le`, `Analysis/MellinDifferenceBounds.lean` | Positive integer coordinate; Re(s)>0. |
| Exact finite summation by parts | `C.finite_cesaro_abel`, `mellin_pairing_prefix`, `Analysis/CesaroFiniteCalculus.lean` | Keeps the terminal boundary term. |
| Exact coefficient prefix | `C.mellinSecond_prefix`, same file | Exact finite normalization. |
| Actual first-difference Mellin series | `C.hasSum_first_mellin_pairing`, `Analysis/MellinStepSeries.lean` | Every `ThresholdHilbert` vector, Re(s)>1/2; concludes first-difference HasSum = s·paretoMellin. |
| Weighted dual summability | `C.mellinSecond_dual_term_le`, `mellinSecond_dual_summable`, `Analysis/MellinCesaroSummability.lean` | Pointwise factor 3 bound; summability throughout Re(s)>1/2. |
| Quantitative dual tail | `C.dualTail_le`, `Analysis/CesaroDualTail.lean` | Exact constant 3‖s(s+1)‖²/(2 Re(s)−1), positive head N. |
| Boundary tends to zero | `C.terminal_pairing_tendsto_zero`, `Analysis/MellinCesaroSummability.lean` | Requires a uniform pointwise bound on F. |
| Infinite second-difference pairing | `C.cesaro_mellin_pairing`, same file | Requires f:`ThresholdHilbert` **and** `B` with `∀ n>0, ‖hilbertSequence f n‖≤B`. Completion equation (5.7) for every unbounded H vector is a genuine extension. |
| Analytic residue normalization | `P.paretoMellin_residue_conductor`, `paretoMellin_residue_zeta`, `RH/ParetoResidueMellinContinuation.lean` | Conductor identity holds Re(s)>0 including removable point. Explicit zeta quotient assumes s≠1; gives ζ(s)/s·(1−d^(1−s)) for unnormalized residue. Divide by d to match g_d and multiply by s to match L_s/Λ_s. |

Not yet located as the exact completed declarations:
- General all-H boundary bound (5.6) and all-H second-difference pairing (5.7).
- A complex continuous dual functional on a constructed J Hilbert space, with exact operator norm √D_s.
- The explicit total D_s upper bound written as 3|s(s+1)|²ζ(2σ) (pointwise domination and summability exist).
- The exact evaluation at s=1, (log d)/d, in the handoff's normalized g_d convention.
- The first-dual square bound written as 2|s|²ζ(2σ).

The analytic continuation itself is present; only the particular normalized wrappers and more general Hilbert statement above remain separate coverage items.

## Section 6: actual RH implications and precise remaining provider

Existing source in `RH/ConditionalMeanRHBridge.lean`:
- `P.conditionalMeanError_obstruction_of_zeta`: at an actual zero with Re(s)>1/2, s≠1, a legal g satisfies 1≤D_s·conditionalMeanError(g).
- `zeta_ne_zero_of_conditionalMeanApproximation`.
- `riemannHypothesis_of_conditionalMeanApproximation`.
- `riemannHypothesis_of_conditionalMeanError_tendsto`.

These conclude the actual Mathlib `RiemannHypothesis`, using proved Mellin annihilation and reflection. Their approximation hypothesis remains explicit. They do not assume the classical NB converse.

Existing source in `RH/ConditionalIIDNymanCriterion.lean`:
- `conditionalIIDError_eq`: genuine sample error = mean error + withinVariance/r.
- `conditionalMeanError_le_conditionalIIDError`, `conditionalIIDError_antitone`, `conditionalIIDError_tendsto`.
- `exists_sampleSize_error_lt`.
- `conditionalMeanApproximation_iff_conditionalIIDApproximation`: unconditional equivalence of the two approximation predicates.
- `riemannHypothesis_of_conditionalIIDApproximation`, `riemannHypothesis_of_conditionalIIDError_tendsto`.

Not located: the exact diagonal sample-size formula r_j=max(j,ceil(jv_j)) with r_j→∞ and 1/j rate; the explicit independent-row contrast using normalized g_2.

### Classical reverse is explicitly still a provider

`RH/ThresholdTwoSeedEquivalence.lean` defines:

```lean
def PositiveResidueDensityFromRH : Prop :=
  RiemannHypothesis → hilbertLegalClosure {n : ℕ | 0 < n} = ⊤
```

Its module documentation states that Bagchi's Theorem 1 supplies the classical mathematical statement but **is not a Lean provider**. A bounded literal search for `PositiveResidueDensityFromRH` found only its definition and four theorems taking it as a parameter, all in this module; no provider was located.

For example:

```lean
theorem riemannHypothesis_iff_twoSeed_closure_of_density_from_rh
    (hfull : PositiveResidueDensityFromRH) :
    RiemannHypothesis ↔ hilbertOne ∈ hilbertLegalClosure {2, 3}
```

The relevant exact identification is already stated in
`P.hilbertLegalClosure_positive_eq_residue_closure`, relying on
`legalSeedSpan_positive_eq_residue_span`.

Consequently, completion statements RH⇔1∈W, RH⇒W=J, and the later exact variational RH equivalence must continue to expose this classical formalization obligation until it is discharged. Defining the proposition or taking it as a hypothesis does not prove it. This is distinct from the genuinely open RH-strength signed arithmetic bound.
