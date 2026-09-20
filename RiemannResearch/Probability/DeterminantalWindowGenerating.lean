import RiemannResearch.Probability.DeterminantalWindow
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Actual finite-window probability generating functions

Source: Hough--Krishnapur--Peres--Virag, Determinantal Processes and
Independence, arXiv:math/0503110, for the determinantal generating-function
statement. The expectation below is a Bochner integral under the actual DPP
law. The proof transports the complete finite restriction law to its explicit
PMF and then uses determinant row multilinearity.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section FiniteLaw
variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem finiteLaw_generating_integral (Q : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight Q S) (z : ι → ℝ) :
    (∫ S, ∏ i : ι, if i ∈ S then z i else 1 ∂(finiteLaw Q hpos).toMeasure) =
      (Matrix.diagonal z * Q + (1 - Q)).det := by
  rw [PMF.integral_eq_sum]
  calc
    _ = ∑ S : Finset ι, (∏ i : ι, if i ∈ S then z i else 1) *
        ((finiteLaw Q hpos) S).toReal := by
      apply Finset.sum_congr rfl
      intro S hS
      simp only [smul_eq_mul]
      ring
    _ = _ := finiteLaw_generating Q hpos z

end FiniteLaw

theorem finiteBoolLaw_generating_integral (Q : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight Q S) (z : ι → ℝ) :
    (∫ x, ∏ i : ι, if x i = true then z i else 1 ∂(finiteBoolLaw Q hpos).toMeasure) =
      (Matrix.diagonal z * Q + (1 - Q)).det := by
  letI : MeasurableSpace (Finset ι) := ⊤
  let b : Finset ι → (ι → Bool) := fun S i => decide (i ∈ S)
  let F : (ι → Bool) → ℝ := fun x => ∏ i : ι, if x i = true then z i else 1
  have hb : Measurable b := measurable_of_finite b
  have hF : Measurable F := measurable_of_finite F
  change (∫ x, F x ∂((finiteLaw Q hpos).map b).toMeasure) = _
  rw [← PMF.toMeasure_map b (finiteLaw Q hpos) hb]
  rw [integral_map hb.aemeasurable hF.aestronglyMeasurable]
  simpa [F, b] using finiteLaw_generating_integral Q hpos z

variable {α Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

/-- The multivariate finite-window generating function under an arbitrary
actual DPP law. No independence is asserted for the site occupations. -/
theorem IsDPP.window_generating (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S)
    (z : ι → ℝ) :
    (∫ ω, ∏ i : ι, if e i ∈ X ω then z i else 1 ∂μ) =
      (Matrix.diagonal z * Matrix.of (fun i j : ι => K (e i) (e j)) +
        (1 - Matrix.of (fun i j : ι => K (e i) (e j)))).det := by
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  let F : (ι → Bool) → ℝ := fun x => ∏ i : ι, if x i = true then z i else 1
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hF : Measurable F := measurable_of_finite F
  have hp := finiteBoolLaw_generating_integral
    (Matrix.of (fun i j : ι => K (e i) (e j))) hpos z
  rw [← h.finite_restriction_law e hpos] at hp
  change (∫ x, F x ∂μ.map r) = _ at hp
  rw [integral_map hr.aemeasurable hF.aestronglyMeasurable] at hp
  simpa [F, r] using hp

/-- Setting all occupancy weights to z gives the count PGF, written as a
product so it is valid for every real z without fractional powers. -/
theorem IsDPP.window_count_generating (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S)
    (z : ℝ) :
    (∫ ω, ∏ i : ι, if e i ∈ X ω then z else 1 ∂μ) =
      (1 + (z - 1) • Matrix.of (fun i j : ι => K (e i) (e j))).det := by
  have hmat :
      Matrix.diagonal (fun _ : ι => z) * Matrix.of (fun i j : ι => K (e i) (e j)) +
        (1 - Matrix.of (fun i j : ι => K (e i) (e j))) =
      1 + (z - 1) • Matrix.of (fun i j : ι => K (e i) (e j)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [← hmat]
  exact h.window_generating e hpos (fun _ => z)

end RiemannResearch.Probability.DPP
