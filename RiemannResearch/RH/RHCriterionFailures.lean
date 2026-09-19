import RiemannResearch.RH.ParetoMeanOneApproximation
import RiemannResearch.RH.ConditionalIIDNymanCriterion
import RiemannResearch.RH.ConditionalSignedSchurConjecture
import RiemannResearch.RH.ParetoExhaustiveWalk
import RiemannResearch.RH.ParetoGibbsSpectralGap
import RiemannResearch.RH.DyadicBoundaryLegalRecovery
import RiemannResearch.RH.BalancedMinimalTarget
import RiemannResearch.RH.TwoSeedExactHeadEnergy

/-!
# Necessary criterion failures under the negation of actual RH

Source: user-provided
RH_Equivalent_Formulations_Lean_Audit_2026-09-19(1)(1).md and
RH_Weighted_Telescoping_Construction_and_Tail_Repair_2026-09-19.md,
for the requested obstruction statements and comparison strategy.

The proofs specialize existing implications to Mathlib's RiemannHypothesis.
Uniform floors and divergent conditional head energy are stated with their
quantifiers explicit. General operator hypotheses remain explicit; the actual
Gibbs gap is supplied by its proved provider. No RH-to-density provider is
assumed. The canonical tail constraints belong to
RHFalseTailConstraints and are not repeated here. These consequences are not
asserted to be mutually contradictory, and this module does not prove RH.
-/

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Every positive seed family fails to approximate the actual constant target. -/
theorem not_RH_hilbertOne_not_mem_legalClosure
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertOne ∉ hilbertLegalClosure A := by
  intro hmem
  exact hRH (riemannHypothesis_of_hilbertOne_mem_legalClosure A hA hmem)

/-- In particular, no such legal closure is the whole Hilbert space. -/
theorem not_RH_hilbertLegalClosure_ne_top
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertLegalClosure A ≠ ⊤ := by
  intro htop
  exact hRH (riemannHypothesis_of_legalClosure_eq_top A hA htop)

/-- One strictly positive floor works for every finite legal witness. -/
theorem not_RH_paretoError_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, g ∈ legalSeedSpan A → ε ≤ paretoError g := by
  by_contra! h
  exact hRH (riemannHypothesis_of_legal_paretoError A hA h)

/-- The obstruction is uniform over all exactly mean-one legal witnesses. -/
theorem not_RH_meanOne_variance_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, g ∈ legalSeedSpan A → paretoMean g = 1 →
        ε ≤ paretoVariance g := by
  by_contra! h
  exact not_RH_hilbertOne_not_mem_legalClosure hRH A hA
    ((hilbertOne_mem_legalClosure_iff_meanOne_variance A hA).mpr h)

/-- The nonzero-mean condition is essential for the noise-to-signal criterion. -/
theorem not_RH_noiseSignalRatio_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, g ∈ legalSeedSpan A → paretoMean g ≠ 0 →
        ε ≤ noiseSignalRatio g := by
  by_contra! h
  exact hRH (riemannHypothesis_of_legal_noiseSignalRatio A hA h)

/-- Exhaustiveness is not needed to rule out vanishing complete walk error. -/
theorem not_RH_legalWalk_error_not_tendsto_zero
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) :
    ¬ Tendsto (walkError (legalPacket A hA) draw hilbertOne) atTop (𝓝 0) := by
  intro hlim
  exact hRH (riemannHypothesis_of_legalWalk_tendsto A hA draw hlim)

/-- Even a non-exhaustive legal walk must have summable relative gains. -/
theorem not_RH_legalWalk_relativeGain_summable
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) :
    Summable (legalWalk_relativeGain A hA draw) := by
  by_contra hgain
  exact hRH (riemannHypothesis_of_legalWalk_nonsummable_gain A hA draw hgain)

/-- The same positive error floor works for every ordering and every step. -/
theorem not_RH_legalWalk_error_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ draw : ℕ → LegalPacketIndex A, ∀ n : ℕ,
      ε ≤ walkError (legalPacket A hA) draw hilbertOne n := by
  obtain ⟨ε, hε, hfloor⟩ := not_RH_paretoError_uniform_floor hRH A hA
  refine ⟨ε, hε, ?_⟩
  intro draw n
  unfold walkError
  rw [hilbertOne_sub_norm_sq_eq_paretoError]
  exact hfloor _ (legalWalk_projection_mem A hA draw n hilbertOne)

/-- The weaker conditional-mean norm still has a uniform positive obstruction. -/
theorem not_RH_conditionalMeanError_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, g ∈ legalSeedSpan A → ε ≤ conditionalMeanError g := by
  by_contra! h
  exact hRH (riemannHypothesis_of_conditionalMeanApproximation A hA h)

/-- The conditional-mean floor survives every positive conditional-iid sample size.
Legal boundedness supplies the integrability required by the exact error split. -/
theorem not_RH_conditionalIIDError_uniform_floor
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : ℕ → ℝ, g ∈ legalSeedSpan A → ∀ r : ℕ, 0 < r →
        ε ≤ conditionalIIDError g r := by
  obtain ⟨ε, hε, hfloor⟩ := not_RH_conditionalMeanError_uniform_floor hRH A hA
  refine ⟨ε, hε, ?_⟩
  intro g hg r hr
  exact (hfloor g hg).trans (conditionalMeanError_le_conditionalIIDError g r hr
    (legal_observation_memLp A hA hg 0))

/-- The actual unrestricted conditional exact-head minima have no uniform bound. -/
theorem not_RH_not_bounded_conditionalHeadMinimum (hRH : ¬ RiemannHypothesis) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, conditionalHeadMinimum N ≤ C := by
  intro hbound
  exact hRH (riemannHypothesis_of_bounded_conditionalHeadMinimum hbound)

/-- Monotonicity upgrades unboundedness to divergence of the genuine minima. -/
theorem not_RH_conditionalHeadMinimum_tendsto_atTop (hRH : ¬ RiemannHypothesis) :
    Tendsto conditionalHeadMinimum atTop atTop := by
  have hunbounded : ∀ C : ℝ, ∃ N : ℕ, C < conditionalHeadMinimum N := by
    by_contra! h
    exact not_RH_not_bounded_conditionalHeadMinimum hRH h
  apply tendsto_atTop.mpr
  intro C
  obtain ⟨N, hN⟩ := hunbounded C
  filter_upwards [eventually_ge_atTop N] with M hM
  exact hN.le.trans (conditionalHeadMinimum_mono hM)

/-- Eventually every exact-head witness exceeds any prescribed energy budget. -/
theorem not_RH_conditional_head_energy_eventually_above
    (hRH : ¬ RiemannHypothesis) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ conditionalHeadClass N,
      C < conditionalMeanSquare g := by
  have hlarge : ∀ᶠ N : ℕ in atTop, C + 1 ≤ conditionalHeadMinimum N :=
    (not_RH_conditionalHeadMinimum_tendsto_atTop hRH).eventually
      (eventually_ge_atTop (C + 1))
  filter_upwards [hlarge] with N hN
  intro g hg
  have hle := conditionalHeadMinimum_le N hg
  linarith

/-- No cofinal exact-head family of positive-seed legal witnesses has bounded energy.
Legality, exact heads, and cofinality remain explicit. -/
theorem not_RH_not_bounded_conditionalMean_heads
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = 1)
    (hY : Tendsto Y atTop atTop) :
    ¬ ∃ C : ℝ, ∀ j : ℕ, conditionalMeanSquare (g j) ≤ C := by
  rintro ⟨C, hC⟩
  exact hRH
    (riemannHypothesis_of_bounded_conditionalMean_heads A hA g Y hg hhead hY C hC)

/-- Failure of the repair criterion with all actual operator assumptions retained. -/
theorem not_RH_not_contractive_repair_orbit
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (P : ThresholdHilbert →L[ℝ] ThresholdHilbert) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : P hilbertOne = hilbertOne)
    (hcontract : ∀ x, hilbertMeanContinuous x = 0 → ‖P x‖ ≤ q * ‖x‖) :
    ¬ Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace A) P hilbertMeanContinuous := by
  intro horbit
  exact not_RH_hilbertOne_not_mem_legalClosure hRH A hA
    ((threshold_vanishing_repair_orbit_iff_legalClosure
      A P hq0 hq1 hfix hcontract).mp horbit)

/-- The actual Gibbs obstruction uses the proved spectral gap, with no gap hypothesis. -/
theorem not_RH_not_Gibbs_repair_orbit
    (hRH : ¬ RiemannHypothesis) :
    ¬ Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace {2, 3}) hilbertGibbsContinuous hilbertMeanContinuous := by
  intro horbit
  exact hRH (riemannHypothesis_of_twoSeed_closure
    (hilbertGibbs_legal_repair_iff_closure_unconditional.mp horbit))

/-- All three complete dyadic recovery requirements cannot hold simultaneously. -/
theorem not_RH_not_dyadicBoundaryLegalRecovery
    (hRH : ¬ RiemannHypothesis) (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ¬ HasDyadicBoundaryLegalRecovery A := by
  intro hrecovery
  exact not_RH_hilbertOne_not_mem_legalClosure hRH A hA
    ((dyadicBoundaryLegalRecovery_iff_legalClosure A).mp hrecovery)

/-- No finite deletion of the balanced dictionary recovers the target.
The obstruction does not require the deleted coefficients to be zero. -/
theorem not_RH_balanced_finite_deletion_not_mem
    (hRH : ¬ RiemannHypothesis) (J : Finset BalancedArithmeticIndex) :
    hilbertOne ∉ RiemannResearch.Analysis.dictionaryClosure
      balancedIndexHilbert (Set.univ \ (J : Set BalancedArithmeticIndex)) := by
  intro hmem
  have hfull := ((balanced_finite_deletion_iff Set.univ J).mp hmem).1
  rw [balanced_dictionaryClosure_univ] at hfull
  exact hRH (riemannHypothesis_of_twoSeed_closure hfull)

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.ConditionalMeanGram
open RiemannResearch.RH.Pareto

/-- Only the proved forward Schur-to-RH implication is used; no converse is assumed.
The target retains its complete kernel parametrization and both inverse identities. -/
theorem not_RH_not_uniformSignedSchurTarget (hRH : ¬ RiemannHypothesis) :
    ¬ UniformSignedSchurTarget := by
  intro htarget
  exact hRH (riemannHypothesis_of_uniformSignedSchurTarget htarget)

/-- Even the weaker existential finite-tail energy bound must fail. -/
theorem not_RH_not_uniformFiniteTailTarget (hRH : ¬ RiemannHypothesis) :
    ¬ UniformFiniteTailTarget := by
  intro htarget
  exact hRH (riemannHypothesis_of_bounded_conditionalHeadMinimum
    (bounded_headMinimum_of_finiteTailTarget htarget))

end RiemannResearch.RH.ConditionalMeanGram

namespace RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy

/-- Exact negation of the cofinal subpower criterion: one positive exponent
forces eventual strict violation of every constant-multiple power bound. -/
theorem not_RH_eventual_subpower_failure (hRH : ¬ RiemannHypothesis) :
    ∃ p : ℝ, 0 < p ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * ((N : ℝ) + 1) ^ p < energy N := by
  by_contra! h
  exact hRH (riemannHypothesis_of_cofinal_subpower h)

end RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy
