import RiemannResearch.RH.CanonicalMobiusScreeningBridge

/-!
# Exact full-space source mass and a necessary harmonic summability condition

This module keeps the full signed arithmetic source and the actual full-space
innovation denominator. It identifies its normalized mass with the exact
first-head error drop and sums those masses without an RH assumption.

Nondensity forces harmonic-weighted source summability. The harmonic weight
cannot be removed merely from the denominator LOWER bounds: an upper bound
is required for that comparison. No source nonsummability is asserted here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

def firstHeadSignedSource (M : ℕ) : ℝ :=
  inner ℝ (windowStepTail 1 M) (windowNormal 1 M (by omega))

def firstHeadFullInnovationEnergy (M : ℕ) : ℝ :=
  ‖consecutiveResidueHilbert M -
    (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2

def firstHeadSourceMass (M : ℕ) : ℝ :=
  singleHeadError M ^ 2 * firstHeadSignedSource M ^ 2 /
    firstHeadFullInnovationEnergy M

theorem firstHeadSourceMass_nonneg (M : ℕ) : 0 ≤ firstHeadSourceMass M := by
  unfold firstHeadSourceMass firstHeadFullInnovationEnergy
  positivity

/-- The full-space source mass equals exactly the decrease of the actual
first-head projection defect. -/
theorem firstHeadSourceMass_eq_error_drop (M : ℕ) (hM : 1 ≤ M) :
    firstHeadSourceMass M = singleHeadError M - singleHeadError (M + 1) := by
  let B := firstHeadFullInnovationEnergy M
  let D := ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M))
    (windowStepTail 1 M)‖ ^ 2
  let E := singleHeadError M
  let F := singleHeadError (M + 1)
  let s := firstHeadSignedSource M
  have hB : (1 / 42 : ℝ) ≤ B := consecutiveResidue_full_innovation_energy_lower M hM
  have hBne : B ≠ 0 := by linarith
  have hEne : E ≠ 0 := ne_of_gt (singleHeadError_pos M hM)
  have hsplit : B = D + E * s ^ 2 := consecutiveResidue_full_tail_screening_energy M hM
  have hratio : D = B * F / E := windowStepScreened_energy_eq_full_mul_error_ratio M hM
  have hcross : D * E = B * F := (eq_div_iff hEne).mp hratio
  change E ^ 2 * s ^ 2 / B = E - F
  apply (div_eq_iff hBne).mpr
  calc
    E ^ 2 * s ^ 2 = E * (B - D) := by rw [hsplit]; ring
    _ = (E - F) * B := by nlinarith [hcross]

/-- Every finite source accumulation retains its exact terminal error. -/
theorem firstHeadSourceMass_sum (L : ℕ) :
    (∑ j ∈ Finset.range L, firstHeadSourceMass (1 + j)) =
      singleHeadError 1 - singleHeadError (1 + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih,
      firstHeadSourceMass_eq_error_drop (1 + L) (by omega)]
    simp only [Nat.add_assoc]
    ring

/-- An unconditional exact source Parseval identity. The limiting defect
is retained and is not assumed to vanish. -/
theorem firstHeadSourceMass_hasSum :
    HasSum (fun j : ℕ => firstHeadSourceMass (1 + j))
      (singleHeadError 1 - singleHeadLimitError) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => firstHeadSourceMass_nonneg (1 + j)) _).2
  have hs : Tendsto (fun L : ℕ => 1 + L) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with L hL
    omega
  simpa only [firstHeadSourceMass_sum, Function.comp_def] using
    (tendsto_const_nhds.sub (singleHeadError_tendsto.comp hs) :
      Tendsto (fun L : ℕ => singleHeadError 1 - singleHeadError (1 + L)) atTop
        (𝓝 (singleHeadError 1 - singleHeadLimitError)))

theorem firstHeadSourceMass_tsum :
    (∑' j : ℕ, firstHeadSourceMass (1 + j)) =
      singleHeadError 1 - singleHeadLimitError := firstHeadSourceMass_hasSum.tsum_eq

/-- Full exhaustion of the available source mass is exactly density. This
equivalence does not supply the missing exhaustion statement. -/
theorem firstHeadSourceMass_tsum_eq_iff_density :
    (∑' j : ℕ, firstHeadSourceMass (1 + j)) = singleHeadError 1 ↔ closedSpace = ⊤ := by
  rw [firstHeadSourceMass_tsum, ← singleHeadLimitError_eq_zero_iff_density]
  constructor <;> intro h <;> linarith

/-- In the nondense case, the signed gain sum has this exact finite value. -/
theorem firstHeadWindowGain_hasSum_of_not_density (hd : closedSpace ≠ ⊤) :
    HasSum (fun j : ℕ => windowGain 1 (1 + j) (by omega))
      (singleHeadLimitError⁻¹ - 2 - windowCapacity 1 1 (by omega)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => windowGain_nonneg 1 (1 + j) (by omega)) _).2
  have hs : Tendsto (fun L : ℕ => 1 + L) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with L hL
    omega
  have ht := ((singleHeadCapacity_limit_of_not_density hd).comp hs).sub_const
    (windowCapacity 1 1 (by omega))
  apply ht.congr'
  filter_upwards [] with L
  have he := windowCapacity_telescope 1 1 L (by omega) (by omega)
  dsimp only [Function.comp_def]
  linarith

/-- The existing harmonic upper bound on the ACTUAL screened denominator
gives this necessary arithmetic summability condition under nondensity. -/
theorem firstHead_harmonic_source_summable_of_not_density (hd : closedSpace ≠ ⊤) :
    Summable (fun j : ℕ => firstHeadSignedSource (1 + j) ^ 2 /
      (harmonic (1 + j + 1) : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun j => div_nonneg (sq_nonneg _)
      ((sq_nonneg ‖consecutiveResidueHilbert (1 + j)‖).trans
        (consecutiveResidueHilbert_energy_le_harmonic (1 + j))))
    (fun j => windowGain_harmonic_source_lower 1 (1 + j) (by omega) (by omega))
    (firstHeadWindowGain_hasSum_of_not_density hd).summable

/-- Nonsummability of these ACTUAL harmonic-weighted signed sources is a
sufficient RH criterion. Its nonsummability remains the arithmetic target. -/
theorem riemannHypothesis_of_firstHead_harmonic_source_not_summable
    (h : ¬ Summable (fun j : ℕ => firstHeadSignedSource (1 + j) ^ 2 /
      (harmonic (1 + j + 1) : ℝ))) : RiemannHypothesis := by
  have hd : closedSpace = ⊤ := by
    by_contra hnd
    exact h (firstHead_harmonic_source_summable_of_not_density hnd)
  exact riemannHypothesis_of_all_fixed_head_capacity_divergence
    (density_iff_canonicalWindow_capacity_diverges.mp hd)

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
