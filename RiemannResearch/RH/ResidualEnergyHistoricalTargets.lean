import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RiemannResearch.RH.MeanOneResidualFloor
import RiemannResearch.RH.ResidualGainObstruction
import RiemannResearch.RH.MobiusResidualInfiniteDefects
import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.RH.ParetoGibbsSpectralGap
import RiemannResearch.RH.TwoSeedHeadEnergyGeometry
import RiemannResearch.RH.ActualLaguerreParseval
import RiemannResearch.RH.ResidualTailPNT
import RiemannResearch.RH.CanonicalMobiusSharpResidualEnergy

/-!
# Quantitative residual-energy assertions from the historical catalogue

Source: user-provided stringent-condition catalogue, conditions 1, 3--4,
11--14, and 16--18, 2026-09-21. The residual-tail floor is discharged below
using the later PNT provider. Statements marked OPEN remain formalization
targets with actual arithmetic objects and explicit quantifiers. No open
target is assumed as a theorem. In particular, the previously quoted
numerical certificate is recorded without pretending to have reverified it.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Physical finite legality with arbitrary finite conductor budget. -/
def FiniteResidueLegal (f : ThresholdHilbert) : Prop := ∃ n : ℕ, f ∈ finiteSpace n

/-- OPEN numerical certificate: the decimal is represented exactly as rational. -/
def HistoricalResidualCeilingTarget : Prop := limitEnergy < 242446 / 10000000

def finiteMeanOneVarianceValues : Set ℝ :=
  {v | ∃ f : ThresholdHilbert, FiniteResidueLegal f ∧
    inner ℝ hilbertOne f = 1 ∧ v = ‖f - hilbertOne‖ ^ 2}

/-- OPEN: the lower bound is now proved separately; this adds finite-legal
approximability to the exact infimum, with nonemptiness stated explicitly. -/
def FiniteMeanOneVarianceInfimumTarget : Prop :=
  finiteMeanOneVarianceValues.Nonempty ∧ BddBelow finiteMeanOneVarianceValues ∧
    sInf finiteMeanOneVarianceValues = limitEnergy / (1 - limitEnergy)

/-- OPEN assembly of the exact arithmetic floor and established Gibbs gap. -/
def MeanOneConditionalVarianceFloorTarget : Prop :=
  ∀ f : ThresholdHilbert, f ∈ closedSpace → inner ℝ hilbertOne f = 1 →
    (1 - Real.pi / 4) * (limitEnergy / (1 - limitEnergy)) ≤
      ‖f‖ ^ 2 - inner ℝ f (hilbertGibbs f)

/-- OPEN exact determinant-ratio limits for the actual full/tail Gram matrices. -/
def CapacityDeterminantRatioLimitsTarget : Prop :=
  ¬ RiemannHypothesis →
    Tendsto (fun n => (IntegerDPP.fullGram n).det / (IntegerDPP.tailGram n).det)
      atTop (𝓝 (1 + ‖TailCapacity.canonicalTailCertificate‖ ^ 2 / 2)) ∧
    Tendsto (fun n => (IntegerDPP.tailGram n).det / (IntegerDPP.fullGram n).det)
      atTop (𝓝 (2 / (‖TailCapacity.canonicalTailCertificate‖ ^ 2 + 2)))

def ExactHead (N : ℕ) (f : ThresholdHilbert) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ N → hilbertSequence f k = 1

def finiteExactHeadErrorValues (N : ℕ) : Set ℝ :=
  {v | ∃ f : ThresholdHilbert, FiniteResidueLegal f ∧ ExactHead N f ∧
    v = ‖hilbertOne - f‖ ^ 2}

/-- Proved by `linearExactHeadUpperWitness` below: the concrete upper witness
needed for the historical `liminf Nt_N`
constant. The witness is finite legal, with the complete error norm retained. -/
def LinearExactHeadUpperWitnessTarget : Prop :=
  ∀ N : ℕ, ∃ f : ThresholdHilbert, FiniteResidueLegal f ∧ ExactHead N f ∧
    ‖hilbertOne - f‖ ^ 2 ≤ 4 * (N : ℝ) + 1 / ((N : ℝ) + 1)

/-- The previously open linear witness exists unconditionally. -/
theorem linearExactHeadUpperWitness : LinearExactHeadUpperWitnessTarget := by
  intro N
  cases N with
  | zero =>
    refine ⟨0, ⟨0, (finiteSpace 0).zero_mem⟩, ?_, ?_⟩
    · intro k hk hkN
      omega
    · simp only [sub_zero]
      norm_num [hilbertOne_norm_sq]
  | succ N =>
    refine ⟨canonicalMobiusHilbert (N + 1),
      ⟨N + 1, canonicalMobiusHilbert_mem_finiteSpace (N + 1)⟩,
      canonicalMobiusHilbert_exact (N + 1), ?_⟩
    exact canonicalMobiusResidual_norm_sq_le_linear_ceiling (N + 1) (by omega)


/-- Historical target, now proved by `residualTailLinearFloor`: positive tails
and the precise liminf floor, stated without a
real-valued liminf convention for a possibly unbounded sequence. -/
def ResidualTailLinearFloorTarget : Prop :=
  ¬ RiemannHypothesis →
    (∀ N : ℕ, 0 < residualTailEnergy N) ∧
    (∀ b : ℝ, b < limitEnergy ^ 2 / 4 →
      ∀ᶠ N : ℕ in atTop, b < (N : ℝ) * residualTailEnergy N)

/-- The historical floor follows from the stronger PNT tail-divergence theorem.
The previously proposed linear upper witness is not required for this proof. -/
theorem residualTailLinearFloor : ResidualTailLinearFloorTarget := by
  intro hRH
  have hp := not_RH_limitEnergy_pos hRH
  refine ⟨residualTailEnergy_pos_of_limitEnergy_pos hp, ?_⟩
  intro b hb
  exact (normalized_residual_tail_tendsto_atTop hp).eventually_gt_atTop b

/-- Exact multiplicity expressed by actual derivatives at an actual zero. -/
def ZetaMultiplicity (ρ : ℂ) (m : ℕ) : Prop :=
  0 < m ∧ (∀ j : ℕ, j < m → iteratedDeriv j riemannZeta ρ = 0) ∧
    iteratedDeriv m riemannZeta ρ ≠ 0

/-- OPEN multiplicity strengthening, uniformly over all finite legal exact
heads, not merely a chosen family or a fixed conductor. -/
def MultiplicityExactHeadLowerTarget : Prop :=
  ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 → ∀ m : ℕ,
    ZetaMultiplicity ρ m → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ThresholdHilbert,
        FiniteResidueLegal f → ExactHead N f →
        c * (N : ℝ) ^ (2 * ρ.re - 1) * (Real.log (N : ℝ)) ^ (2 * m - 2) ≤ ‖f‖ ^ 2

/-- OPEN improvement from mean-one centering to the `|ρ-1|` denominator. -/
def MeanOneExactHeadSharpZeroTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ N : ℕ, ∀ f : ThresholdHilbert, f ∈ closedSpace → ExactHead N f →
      inner ℝ hilbertOne f = 1 →
      ((2 * ρ.re - 1) / ‖ρ - 1‖ ^ 2) * ((N : ℝ) + 1) ^ (2 * ρ.re - 1) ≤
        ‖hilbertOne - f‖ ^ 2

/-- The exact conditional variance on the full tail after physical coordinate N. -/
def actualTailVariance (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  ((N : ℝ) + 1) * (∑' j : ℕ, positiveWeight (j + N + 1) *
    hilbertSequence f (j + N + 1) ^ 2) -
    (((N : ℝ) + 1) * (∑' j : ℕ, positiveWeight (j + N + 1) *
      hilbertSequence f (j + N + 1))) ^ 2

/-- OPEN exact bias/variance identity; summability is inherited from actual H
membership, not an absolute truncation of the signed tail. -/
def ExactHeadTailBiasVarianceTarget : Prop :=
  ∀ N : ℕ, ∀ f : ThresholdHilbert, ExactHead N f →
    ‖hilbertOne - f‖ ^ 2 =
      ((N : ℝ) + 1) * (inner ℝ hilbertOne f - 1) ^ 2 +
      actualTailVariance N f / ((N : ℝ) + 1)

/-- OPEN: the sharper conditional tail-variance exponent after exact mean
normalization. -/
def MeanOneExactHeadTailVarianceTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ N : ℕ, ∀ f : ThresholdHilbert, f ∈ closedSpace → ExactHead N f →
      inner ℝ hilbertOne f = 1 →
      ((2 * ρ.re - 1) / ‖ρ - 1‖ ^ 2) * ((N : ℝ) + 1) ^ (2 * ρ.re) ≤
        actualTailVariance N f

/-- OPEN exact reciprocal budget of the actual decreasing projection errors. -/
def ReciprocalProjectionGainBudgetTarget : Prop :=
  ¬ RiemannHypothesis →
    HasSum (fun n => 1 / energy (n + 1) - 1 / energy n)
      (1 / limitEnergy - 1 / energy 0)

/-- Reconstruction indexed by physical moduli 2 through N, matching the prose. -/
def historicalReconstruction (N : ℕ) : ThresholdHilbert :=
  coordinatePartialSum limitResidual (N - 1)

def historicalReconstructionEnergy (N : ℕ) : ℝ := ‖historicalReconstruction N‖ ^ 2

/-- OPEN: the residual-tail product lower bound for the actual reconstruction. -/
def ReconstructionTailProductTarget : Prop :=
  ¬ RiemannHypothesis → ∀ b : ℝ, b < limitEnergy ^ 2 / 2 →
    ∀ᶠ N : ℕ in atTop, b < historicalReconstructionEnergy N * residualTailEnergy N

/-- OPEN: the explicit zero-dependent coefficient-reconstruction floor. -/
def ReconstructionZeroPowerTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ b : ℝ, b < (2 * ρ.re - 1) * ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 4 →
      ∀ᶠ N : ℕ in atTop,
        b < historicalReconstructionEnergy N / ((N : ℝ) + 1) ^ (2 * ρ.re - 1)

/-- OPEN: multiplicity strengthens growth of the same reconstruction. -/
def ReconstructionMultiplicityTarget : Prop :=
  ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 → ∀ m : ℕ,
    ZetaMultiplicity ρ m → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ (2 * ρ.re - 1) * (Real.log (N : ℝ)) ^ (2 * m - 2) ≤
          historicalReconstructionEnergy N

/-- OPEN: the reported universal upper rate, expressed as an exact ratio limit. -/
def ReconstructionUpperRateTarget : Prop :=
  Tendsto (fun N : ℕ => historicalReconstructionEnergy N /
    ((N : ℝ) * (Real.log (N : ℝ)) ^ 2)) atTop (𝓝 0)

/-- OPEN separate square-root weighted absolute defect divergence. -/
def ReconstructionWeightedAbsoluteDivergenceTarget : Prop :=
  ¬ RiemannHypothesis →
    ¬ Summable (fun i : ℕ =>
      |coefficientCLM (i + 2) limitResidual| / Real.sqrt ((i : ℝ) + 2))

def normalizedHistoricalReconstruction (N : ℕ) : ThresholdHilbert :=
  ‖historicalReconstruction N‖⁻¹ • historicalReconstruction N

/-- OPEN: normalized weak convergence and escape of every fixed finite head. -/
def NormalizedReconstructionEscapeTarget : Prop :=
  ¬ RiemannHypothesis →
    (∀ g : ThresholdHilbert,
      Tendsto (fun N => inner ℝ (normalizedHistoricalReconstruction N) g)
        atTop (𝓝 0)) ∧
    (∀ K : ℕ,
      Tendsto (fun N => ∑ n ∈ Finset.range K,
        (normalizedHistoricalReconstruction N n) ^ 2) atTop (𝓝 0)) ∧
    (∀ K : ℕ,
      Tendsto (fun N => ∑' j : ℕ,
        (normalizedHistoricalReconstruction N (j + K)) ^ 2) atTop (𝓝 1))

/-- OPEN concrete failure of uniform integrability: for every fixed amplitude
threshold, eventually all normalized energy is above that threshold. -/
def NormalizedReconstructionNotUniformlyIntegrableTarget : Prop :=
  ¬ RiemannHypothesis → ∀ A : ℝ,
    Tendsto (fun N => ∑' n : ℕ, positiveWeight n *
      (if A < hilbertSequence (normalizedHistoricalReconstruction N) n ^ 2
      then hilbertSequence (normalizedHistoricalReconstruction N) n ^ 2 else 0))
      atTop (𝓝 1)

def reconstructionCesaroMean (N n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, hilbertSequence (historicalReconstruction N) k) / (n : ℝ)

def reconstructionCesaroEnergy (N : ℕ) : ℝ :=
  ∑' n : ℕ, positiveWeight n * reconstructionCesaroMean N n ^ 2

/-- OPEN complete Cesàro energy statements, including the summability needed
to give the real tsum its intended meaning. -/
def ReconstructionCesaroTarget : Prop :=
  (∀ N : ℕ, Summable (fun n => positiveWeight n * reconstructionCesaroMean N n ^ 2)) ∧
  Tendsto (fun N : ℕ => reconstructionCesaroEnergy N / (N : ℝ)) atTop (𝓝 0) ∧
  (∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (2 * ρ.re - 1) ≤ reconstructionCesaroEnergy N)

/-- Laguerre moment-matching variance obstruction for the arithmetic coefficient integrals.
`RamanujanLaguerre.laguerreMatchingVariance` proves it in `RH.LaguerreMatchingVariance`. -/
def LaguerreMatchingVarianceTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ k : ℕ, ∀ f : ThresholdHilbert, FiniteResidueLegal f →
      inner ℝ hilbertOne f = 1 →
      (∀ j : ℕ, 1 ≤ j → j ≤ k →
        RamanujanLaguerre.coefficient (hilbertSequence f) j = 0) →
      (1 - ‖1 - 1 / ρ‖ ^ 2) / ‖1 - 1 / ρ‖ ^ (2 * (k + 1)) ≤
        ‖f - hilbertOne‖ ^ 2

end RiemannResearch.RH.Pareto.CoefficientStabilization
