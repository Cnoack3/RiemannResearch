import RiemannResearch.RH.DyadicCarryCRT
import RiemannResearch.RH.MobiusJointHeadCorrections

/-!
# Actual finite dyadic carry optimization and its remaining limit

Source: the user-provided dyadic-block/CRT argument of 20 September 2026,
Sections 7 and 8. All coefficients and legal approximants are constructed.
The final energy limit remains an explicit hypothesis; it is not proved by
the finite inverse-Gram calculation or by finite head interpolation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The actual Hilbert residual after simultaneous finite head repair. -/
def dyadicJointResidual (k N : ℕ) : ThresholdHilbert :=
  dyadicCarryBlock k (2^k+1) (by positivity) -
    jointHeadHilbert (dyadicCarryBlockSequence k) N

theorem dyadicJointResidual_sequence (k N : ℕ) :
    hilbertSequence (dyadicJointResidual k N) = dyadicCarryJointError k N := by
  change hilbertSequenceLinear (_ - _) = _
  rw [map_sub]
  change hilbertSequence (dyadicCarryBlock k (2^k+1) (by positivity)) -
    hilbertSequence (jointHeadHilbert (dyadicCarryBlockSequence k) N) = _
  rw [dyadicCarryBlock_sequence, jointHeadHilbert_sequence]
  rfl

theorem dyadicJointResidual_energy (k N : ℕ) :
    ‖dyadicJointResidual k N‖^2 =
      ∑' n, positiveWeight n * (dyadicCarryJointError k N n)^2 := by
  rw [hilbert_norm_weighted_sq, dyadicJointResidual_sequence]

/-- Every modulus from N+2 through N+L+1 is available for correction.
L=0 is allowed and returns the uncorrected exact-head interpolant. -/
def dyadicRepairedBlock (k N L : ℕ) : ThresholdHilbert :=
  jointHeadHilbert (dyadicCarryBlockSequence k) N +
    headCorrection N L (dyadicJointResidual k N)

theorem dyadicRepairedBlock_mem (k N L : ℕ) :
    dyadicRepairedBlock k N L ∈ closedSpace :=
  closedSpace.add_mem (jointHeadHilbert_mem _ _) (headCorrection_mem _ _ _)

theorem dyadicRepairedBlock_head (k N L n : ℕ) (hn : n ≤ N) :
    hilbertSequence (dyadicRepairedBlock k N L) n = dyadicCarryBlockSequence k n := by
  change (hilbertSequenceLinear (_ + _)) n = _
  rw [map_add]
  change hilbertSequence (jointHeadHilbert (dyadicCarryBlockSequence k) N) n +
    hilbertSequence (headCorrection N L (dyadicJointResidual k N)) n = _
  rw [headCorrection_head N L _ n hn, add_zero]
  apply jointHeadHilbert_exact _ _ _ n hn
  simp [dyadicCarryBlockSequence, residue]

/-- The complete signed Schur remainder, with an actual inverse and actual data. -/
def dyadicRepairEnergy (k N L : ℕ) : ℝ :=
  ‖dyadicJointResidual k N‖^2 -
    ∑ i : Fin L, headCorrectionCoefficients N L (dyadicJointResidual k N) i *
      inner ℝ (headNullHilbert N i.val) (dyadicJointResidual k N)

theorem dyadicRepairEnergy_eq_norm (k N L : ℕ) :
    dyadicRepairEnergy k N L =
      ‖dyadicCarryBlock k (2^k+1) (by positivity) - dyadicRepairedBlock k N L‖^2 := by
  rw [dyadicRepairEnergy, ← headCorrection_energy]
  congr 1
  congr 1
  unfold dyadicJointResidual dyadicRepairedBlock
  abel

theorem dyadicRepairEnergy_nonneg (k N L : ℕ) : 0 ≤ dyadicRepairEnergy k N L := by
  rw [dyadicRepairEnergy_eq_norm]
  positivity

/-- Every finite correction still obeys the exact closed-space distance bound. -/
theorem dyadicRepairEnergy_lower_bound (k N L : ℕ) :
    (dyadicCarryGap k)^2 ≤ dyadicRepairEnergy k N L := by
  let B := dyadicCarryBlock k (2^k+1) (by positivity)
  have hb : BddBelow (Set.range (fun x : closedSpace => ‖B - (x : ThresholdHilbert)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact norm_nonneg _
  have hmin := ciInf_le hb
    (⟨dyadicRepairedBlock k N L, dyadicRepairedBlock_mem k N L⟩ : closedSpace)
  have hn : dyadicCarryGap k ≤ ‖B - dyadicRepairedBlock k N L‖ := by
    rw [dyadicCarryGap, Submodule.starProjection_minimal]
    exact hmin
  rw [dyadicRepairEnergy_eq_norm]
  change (dyadicCarryGap k)^2 ≤ ‖B - dyadicRepairedBlock k N L‖^2
  have hg : 0 ≤ dyadicCarryGap k := norm_nonneg _
  nlinarith

/-- If the optimized energies have a limit, it cannot fall below the constant
target's squared distance. Positivity and finite optimization alone do not
show that this distance vanishes. -/
theorem dyadicRepairEnergy_limit_lower_bound
    (stages : ℕ → ℕ) (hs : Tendsto stages atTop atTop) (N L : ℕ → ℕ)
    (a : ℝ) (he : Tendsto (fun j => dyadicRepairEnergy (stages j) (N j) (L j))
      atTop (𝓝 a)) : ‖hilbertOne - closedSpace.starProjection hilbertOne‖^2 ≤ a := by
  have hg := (dyadicCarryGap_tendsto.comp hs).pow 2
  exact le_of_tendsto_of_tendsto hg he
    (Eventually.of_forall (fun j => dyadicRepairEnergy_lower_bound _ _ _))

/-- Optimality is for the entire infinite weighted residual, including all
mixed terms, rather than a first-period or diagonal-only surrogate. -/
theorem dyadicRepairEnergy_minimizes (k N L : ℕ) (c : Fin L → ℝ) :
    dyadicRepairEnergy k N L ≤
      ‖dyadicJointResidual k N -
        Fintype.linearCombination ℝ (fun i : Fin L => headNullHilbert N i.val) c‖^2 := by
  rw [dyadicRepairEnergy, ← headCorrection_energy]
  exact headCorrection_minimizes N L (dyadicJointResidual k N) c

/-- Exact finite CRT expression for the initial energy in the Schur remainder. -/
theorem dyadicJointResidual_energy_crt (k N P : ℕ) (hP0 : 0 < P)
    (hkP : 2^k+1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N+1 → m ∣ P) :
    ‖dyadicJointResidual k N‖^2 =
      ∑ r : Fin P, progressionWeight P (r.val+1) *
        (dyadicCarryJointError k N (r.val+1))^2 := by
  rw [dyadicJointResidual_energy]
  exact dyadicCarryJointError_energy_crt k N P hP0 hkP hP

/-- Conditional endpoint with no unspecified inverse, legal-vector provider,
or head correction. The only substantive remaining input is the displayed
vanishing of the actual full signed energies along unbounded dyadic stages. -/
theorem hilbertOne_mem_of_dyadicRepairEnergy_tendsto
    (stages : ℕ → ℕ) (hs : Tendsto stages atTop atTop) (N L : ℕ → ℕ)
    (he : Tendsto (fun j => dyadicRepairEnergy (stages j) (N j) (L j))
      atTop (𝓝 0)) : hilbertOne ∈ closedSpace := by
  apply hilbertOne_mem_of_dyadicCarryBlock_approx stages hs
    (fun j => dyadicRepairedBlock (stages j) (N j) (L j))
    (fun j => dyadicRepairedBlock_mem _ _ _)
  have he' : Tendsto (fun j =>
      ‖dyadicCarryBlock (stages j) (2^stages j+1) (by positivity) -
        dyadicRepairedBlock (stages j) (N j) (L j)‖^2) atTop (𝓝 0) := by
    simpa only [dyadicRepairEnergy_eq_norm] using he
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp he'
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

theorem riemannHypothesis_of_dyadicRepairEnergy_tendsto
    (stages : ℕ → ℕ) (hs : Tendsto stages atTop atTop) (N L : ℕ → ℕ)
    (he : Tendsto (fun j => dyadicRepairEnergy (stages j) (N j) (L j))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr
      (hilbertOne_mem_of_dyadicRepairEnergy_tendsto stages hs N L he))

end RiemannResearch.RH.Pareto
