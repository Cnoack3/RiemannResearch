import RiemannResearch.Analysis.NonnegativeSeriesTightness
import RiemannResearch.RH.DyadicArithmeticFourierBridge

/-!
# Exact signed boundary tails at the zero-damping frontier

Source: user-provided FourierSignedBridgeVerification20260911(2).md,
Sections 5–6. The independently developed finite-head/tail argument here
identifies a conditional convergence criterion, not a provider of coordinate
limits, tail tightness, a uniform energy bound, legal recovery, or RH.

Every frequency cross term stays inside the squared complete Fourier row.
The parameter may follow any path of positive dampings and any filter.
-/

namespace RiemannResearch.RH.Pareto

open Filter
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- Complete signed energy in one actual boundary coordinate. -/
def dyadicSignedFourierBoundaryEnergy (ε : ℝ) (i : ℕ) : ℝ :=
  (1 / 4 : ℝ) * ‖∑' h, dyadicSignedFourierTerm ε i h‖ ^ 2

/-- The entire boundary-index tail outside a fixed finite set. No frequency
diagonal or finite frequency approximation is substituted here. -/
def dyadicSignedFourierBoundaryTail (ε : ℝ) (s : Finset ℕ) : ℝ :=
  ∑' i : {i : ℕ // i ∉ s}, dyadicSignedFourierBoundaryEnergy ε i

theorem dyadicSignedFourierBoundaryEnergy_eq_actual
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    dyadicSignedFourierBoundaryEnergy ε i =
      (1 / 4 : ℝ) * dyadicNormalizationBoundaryCoefficient ε i ^ 2 := by
  unfold dyadicSignedFourierBoundaryEnergy
  rw [(dyadicSignedFourierBridge_proved ε hε i).tsum_eq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem dyadicSignedFourierBoundaryEnergy_summable
    {ε : ℝ} (hε : 0 < ε) :
    Summable (dyadicSignedFourierBoundaryEnergy ε) :=
  dyadicNormalizationFourier_energy_summable_of_hasSum hε
    (dyadicSignedFourierTerm ε) (dyadicSignedFourierBridge_proved ε hε)

/-- Exact finite-head / full-tail decomposition of the actual remainder norm. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_head_add_signed_tail
    {ε : ℝ} (hε : 0 < ε) (s : Finset ℕ) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      (∑ i ∈ s, dyadicSignedFourierBoundaryEnergy ε i) +
        dyadicSignedFourierBoundaryTail ε s := by
  rw [dyadicNormalizationRemainder_norm_sq_eq_signed_fourier hε]
  exact ((dyadicSignedFourierBoundaryEnergy_summable hε).sum_add_tsum_subtype_compl s).symm

theorem dyadicSignedFourierBoundaryTail_nonneg (ε : ℝ) (s : Finset ℕ) :
    0 ≤ dyadicSignedFourierBoundaryTail ε s := by
  apply tsum_nonneg
  intro i
  dsimp [dyadicSignedFourierBoundaryEnergy]
  positivity

/-- A vanishing actual boundary coefficient gives a vanishing complete signed
Fourier energy at that coordinate. Only eventual positive damping is needed. -/
theorem dyadicSignedFourierBoundaryEnergy_tendsto_zero
    {α : Type*} {l : Filter α} (ε : α → ℝ) (hε : ∀ᶠ a in l, 0 < ε a)
    (i : ℕ) (hcoord : Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (nhds 0)) :
    Tendsto (fun a => dyadicSignedFourierBoundaryEnergy (ε a) i) l (nhds 0) := by
  have he : (fun a => dyadicSignedFourierBoundaryEnergy (ε a) i) =ᶠ[l]
      (fun a => (1 / 4 : ℝ) * dyadicNormalizationBoundaryCoefficient (ε a) i ^ 2) := by
    filter_upwards [hε] with a ha
    exact dyadicSignedFourierBoundaryEnergy_eq_actual ha i
  apply (tendsto_congr' he).mpr
  simpa using (hcoord.pow 2).const_mul (1 / 4 : ℝ)

/-- Coordinate limits control exactly the finite boundary heads. -/
theorem dyadicSignedFourierBoundaryHead_tendsto_zero
    {α : Type*} {l : Filter α} (ε : α → ℝ) (hε : ∀ᶠ a in l, 0 < ε a)
    (hcoord : ∀ i, Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (nhds 0))
    (s : Finset ℕ) :
    Tendsto (fun a => ∑ i ∈ s, dyadicSignedFourierBoundaryEnergy (ε a) i)
      l (nhds 0) := by
  apply finite_sum_tendsto_zero_of_coordinate_tendsto
  intro i
  exact dyadicSignedFourierBoundaryEnergy_tendsto_zero ε hε i (hcoord i)

/-- Conditional research reduction: once actual coordinates vanish, strong
energy convergence is equivalent to asymptotic tightness in the boundary
index. Positive-damping summability and the bridge need no new hypothesis. -/
theorem dyadicNormalizationRemainder_energy_tendsto_zero_iff_tail_tight
    {α : Type*} {l : Filter α} (ε : α → ℝ) (hε : ∀ᶠ a in l, 0 < ε a)
    (hcoord : ∀ i, Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (nhds 0)) :
    Tendsto (fun a => ‖dyadicNormalizationRemainder (ε a)‖ ^ 2) l (nhds 0) ↔
      NonnegativeSeriesTailTightAt
        (fun a => dyadicSignedFourierBoundaryEnergy (ε a)) l := by
  have he : (fun a => ∑' i, dyadicSignedFourierBoundaryEnergy (ε a) i) =ᶠ[l]
      (fun a => ‖dyadicNormalizationRemainder (ε a)‖ ^ 2) := by
    filter_upwards [hε] with a ha
    exact (dyadicNormalizationRemainder_norm_sq_eq_signed_fourier ha).symm
  have ht := nonnegative_tsum_tendsto_zero_iff_tail_tight
    (l := l) (f := fun a => dyadicSignedFourierBoundaryEnergy (ε a))
    (Eventually.of_forall fun a i => by dsimp [dyadicSignedFourierBoundaryEnergy]; positivity)
    (hε.mono fun a ha => dyadicSignedFourierBoundaryEnergy_summable ha)
    (fun i => dyadicSignedFourierBoundaryEnergy_tendsto_zero ε hε i (hcoord i))
  exact (tendsto_congr' he).symm.trans ht

/-- Actual escape-of-energy consequence. If the remainder energy persists,
coordinate convergence forces that energy beyond every fixed boundary set. -/
theorem dyadicSignedFourierBoundaryTail_eventually_ge_of_energy_lower
    {α : Type*} {l : Filter α} (ε : α → ℝ) (hε : ∀ᶠ a in l, 0 < ε a)
    (hcoord : ∀ i, Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (nhds 0))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ a in l, c ≤ ‖dyadicNormalizationRemainder (ε a)‖ ^ 2)
    (s : Finset ℕ) :
    ∀ᶠ a in l, c / 2 ≤ dyadicSignedFourierBoundaryTail (ε a) s := by
  have hhead := dyadicSignedFourierBoundaryHead_tendsto_zero ε hε hcoord s
  filter_upwards [hlower,
    hhead.eventually_lt_const (show (0 : ℝ) < c / 2 by linarith), hε]
    with a ha hhead hε
  have hsplit := dyadicNormalizationRemainder_norm_sq_eq_head_add_signed_tail hε s
  linarith

end
end RiemannResearch.RH.Pareto
