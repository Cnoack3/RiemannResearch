import Mathlib.Tactic.Ring
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ResidualGainProduct
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete Q packet gains, limiting error, and cofinal coordinate criteria

Source: user-requested second Ramanujan transfer program, 23 October 2026.
The exact nested-projection identity is applied to the actual Q inverse-Gram
optimizer. Error positivity follows from an explicit common-multiple zero.
All coordinate rates retain the unconditional limiting error.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QRamanujanCanonicalOptimizer
open Pareto ZetaTwoHilbert SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ResidualGain

def packetError (n : ℕ) : ℝ := 1 - packetMass n
def packetLimitEnergy : ℝ :=
  ‖qOne - QFullResidueProjection.closure.starProjection qOne‖ ^ 2
def packetGain (n : ℕ) : ℝ := ‖packetCandidate (n+1) - packetCandidate n‖ ^ 2
def packetRelativeGain (n : ℕ) : ℝ := packetGain n / packetError n

theorem packetError_eq_walkError (n : ℕ) :
    packetError n = walkError (fun i => qResidue (i + 2)) id qOne n := by
  rw [packetError, ← packet_error, packetCandidate_eq_residueCandidate,
    QFullResidueProjection.candidate_eq_projection]
  rfl

theorem packetLimitEnergy_eq_limitingError :
    packetLimitEnergy = limitingError (fun i => qResidue (i + 2)) qOne := rfl

theorem packetError_tendsto :
    Tendsto packetError atTop (𝓝 packetLimitEnergy) := by
  simp only [show packetError = walkError (fun i => qResidue (i + 2)) id qOne
    from funext packetError_eq_walkError, packetLimitEnergy_eq_limitingError]
  exact walkError_tendsto _ id Function.surjective_id qOne

theorem packetLimitEnergy_zero_iff_closure :
    packetLimitEnergy = 0 ↔ qOne ∈ QFullResidueProjection.closure := by
  exact limitingError_eq_zero_iff (fun i => qResidue (i + 2)) qOne

/-- Exact complete energy excess equals distance to the actual limiting projection. -/
theorem packet_energy_limit_identity (n : ℕ) :
    packetError n = packetLimitEnergy +
      ‖QFullResidueProjection.closure.starProjection qOne - packetCandidate n‖ ^ 2 := by
  have h := walkError_eq_limitingError_add
    (fun i => qResidue (i + 2)) id qOne n
  rw [← packetError_eq_walkError, ← packetLimitEnergy_eq_limitingError] at h
  simpa only [packetCandidate_eq_residueCandidate,
    QFullResidueProjection.candidate_eq_projection, QFullResidueProjection.stage, QFullResidueProjection.closure,
    QFullResidueProjection.legalSpan, dictionaryClosure] using h

/-- Every fixed actual Q coordinate has an explicit convergence rate in the energy excess. -/
theorem packetCoordinate_error_bound (n m : ℕ) (hm : 1 < m) :
    ‖limitCoordinate m - packetCoordinate n m‖ ^ 2 ≤
      ‖qCoefficientCLM m‖ ^ 2 * (packetError n - packetLimitEnergy) := by
  have h := walkProjection_map_error_bound
    (fun i => qResidue (i + 2)) id qOne n (qCoefficientCLM m)
  rw [← packetError_eq_walkError, ← packetLimitEnergy_eq_limitingError] at h
  simpa only [packetCoordinate_eq n m hm, limitCoordinate,
    packetCandidate_eq_residueCandidate, QFullResidueProjection.candidate_eq_projection,
    QFullResidueProjection.stage, QFullResidueProjection.closure,
    QFullResidueProjection.legalSpan, dictionaryClosure] using h

theorem packetError_antitone : Antitone packetError := by
  intro m n hmn
  simpa only [← packetError_eq_walkError] using
    walkError_antitone (fun i => qResidue (i + 2)) id qOne hmn

/-- The full Q residual has an explicit nonzero coordinate at a common multiple. -/
theorem packetCandidate_factorial_zero (n : ℕ) :
    qSequence (packetCandidate n) (Nat.factorial (n+1)) = 0 := by
  rw [packetCandidate_eq_residueCandidate]
  change qSequenceLinear (∑ i : Fin n,
    QFullResidueProjection.coefficients n i • qResidue (i.val + 2))
      (Nat.factorial (n+1)) = 0
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  change QFullResidueProjection.coefficients n i *
    qSequence (qResidue (i.val + 2)) (Nat.factorial (n+1)) = 0
  rw [qSequence_qResidue]
  simp [ArithmeticCumulative.residueFraction, Nat.mod_eq_zero_of_dvd
    (Nat.dvd_factorial (by omega : 0 < i.val + 2) (by omega : i.val + 2 ≤ n+1))]

theorem packetError_pos (n : ℕ) : 0 < packetError n := by
  rw [packetError, ← packet_error]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have he := sub_eq_zero.mp hz
  have h := congrArg (fun f : QHilbert => qSequence f (Nat.factorial (n+1))) he
  rw [packetCandidate_factorial_zero, qSequence_qOne] at h
  simp [qOneSequence, ne_of_gt (Nat.factorial_pos (n+1))] at h

theorem packetError_zero : packetError 0 = 1 := by
  simp [packetError, packetMass]

/-- Complete Q innovation energy, without a scalar Schur approximation. -/
theorem packetError_step (n : ℕ) :
    packetError n = packetError (n+1) + packetGain n := by
  have h := walkError_step (fun i => qResidue (i + 2)) id qOne n
  rw [← packetError_eq_walkError, ← packetError_eq_walkError] at h
  simpa only [packetGain, packetCandidate_eq_residueCandidate,
    QFullResidueProjection.candidate_eq_projection, QFullResidueProjection.stage, QFullResidueProjection.closure,
    QFullResidueProjection.legalSpan, dictionaryClosure] using h

theorem packetMass_monotone : Monotone packetMass := by
  intro m n hmn
  have h := packetError_antitone hmn
  unfold packetError at h
  linarith

theorem packetGain_eq_mass_increment (n : ℕ) :
    packetGain n = packetMass (n+1) - packetMass n := by
  have h := packetError_step n
  unfold packetError at h
  linarith

theorem packet_gain_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, packetGain j) = packetMass n := by
  induction n with
  | zero => simp [packetMass]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, packetGain_eq_mass_increment]
      ring

theorem packetRelativeGain_nonneg (n : ℕ) : 0 ≤ packetRelativeGain n :=
  div_nonneg (sq_nonneg _) (packetError_pos n).le

theorem packetRelativeGain_lt_one (n : ℕ) : packetRelativeGain n < 1 := by
  unfold packetRelativeGain
  apply (div_lt_iff₀ (packetError_pos n)).mpr
  linarith [packetError_step n, packetError_pos (n+1)]

theorem packetError_relativeGain_step (n : ℕ) :
    packetError (n+1) = packetError n * (1 - packetRelativeGain n) := by
  have hc : packetError n * packetRelativeGain n = packetGain n := by
    unfold packetRelativeGain
    field_simp [ne_of_gt (packetError_pos n)]
  nlinarith [packetError_step n]

theorem packet_error_product (n : ℕ) :
    packetError n = ∏ j ∈ Finset.range n, (1 - packetRelativeGain j) := by
  have h := recurrence_eq_mul_product packetError_relativeGain_step n
  simpa only [packetError_zero, survivalProduct, one_mul] using h

theorem packet_error_log_identity (n : ℕ) :
    Real.log (packetError n) =
      -∑ j ∈ Finset.range n, -Real.log (1 - packetRelativeGain j) := by
  have h := log_recurrence_eq_initial_sub_sum
    (packetError_pos 0) packetRelativeGain_lt_one packetError_relativeGain_step n
  simpa only [packetError_zero, Real.log_one, zero_sub] using h

theorem packet_relativeGain_not_summable_iff :
    ¬ Summable packetRelativeGain ↔ packetLimitEnergy = 0 := by
  have ht : Tendsto packetError atTop (𝓝 0) ↔ packetLimitEnergy = 0 := by
    constructor
    · intro h
      exact tendsto_nhds_unique packetError_tendsto h
    · intro h
      simpa only [h] using packetError_tendsto
  exact (residual_tendsto_zero_iff_not_summable (packetError_pos 0)
    packetRelativeGain_nonneg packetRelativeGain_lt_one packetError_relativeGain_step).symm.trans ht

theorem packet_cofinal_mass_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => packetMass (N i)) l (𝓝 1) ↔ packetLimitEnergy = 0 := by
  have ht : Tendsto (fun i => packetMass (N i)) l (𝓝 (1 - packetLimitEnergy)) :=
    packet_mass_tendsto.comp hN
  constructor
  · intro h
    have he := tendsto_nhds_unique ht h
    linarith
  · intro h
    simpa only [h, sub_zero] using ht

theorem packet_cofinal_coordinates_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∀ m : ℕ, 1 < m →
      Tendsto (fun i => packetCoordinate (N i) m) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ packetLimitEnergy = 0 := by
  rw [packetLimitEnergy_zero_iff_closure]
  constructor
  · intro h
    apply limitCoordinates_eq_moebius_iff_closure.mp
    intro m hm
    exact tendsto_nhds_unique ((packetCoordinate_tendsto m hm).comp hN) (h m hm)
  · intro h m hm
    have hc := limitCoordinates_eq_moebius_iff_closure.mpr h m hm
    simpa only [Function.comp_def, hc] using (packetCoordinate_tendsto m hm).comp hN

theorem packet_cofinal_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ)
    (hN : Tendsto N l atTop) :
    (Tendsto (fun i => packetMass (N i)) l (𝓝 1) ↔ RiemannHypothesis) ∧
    ((∀ m : ℕ, 1 < m → Tendsto (fun i => packetCoordinate (N i) m) l
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis) ∧
    (¬ Summable packetRelativeGain ↔ RiemannHypothesis) := by
  have he : packetLimitEnergy = 0 ↔ RiemannHypothesis :=
    packetLimitEnergy_zero_iff_closure.trans
      (packetCoordinate_limits_moebius_iff_closure.symm.trans
        (packetCoordinate_limits_iff_rh hBaezDuarte))
  exact ⟨(packet_cofinal_mass_iff N hN).trans he,
    (packet_cofinal_coordinates_iff N hN).trans he,
    packet_relativeGain_not_summable_iff.trans he⟩

end RiemannResearch.RH.QRamanujanCanonicalOptimizer
