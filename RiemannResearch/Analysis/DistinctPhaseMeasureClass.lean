import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite multiplicity sampling and measure-class consequences

Source: user-provided argument, `Prime_Phases_Agenda_Proof_Attempts.tex`,
Corollary `newdistinctregularity` and the growing finite phase Gram proof.

This module proves the finite sampling and abstract measure-theoretic steps.
It does not prove a zeta-zero second-multiplicity-moment bound, a Landau/Ford-
Meng-Zaharescu estimate, or the weak-limit passage from zero empirical laws to
the stated Borel inequalities. Those analytic providers remain separate.
-/

open scoped BigOperators MeasureTheory ENNReal NNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A quadratic Borel-set domination forces absolute continuity. -/
theorem absolutelyContinuous_of_quadratic_set_bound {C : ℝ≥0∞}
    (h : ∀ s : Set α, MeasurableSet s → (μ s) ^ 2 ≤ C * ν s) : μ ≪ ν := by
  apply AbsolutelyContinuous.mk
  intro s hs hν
  have hsq : (μ s) ^ 2 = 0 := le_antisymm (by simpa [hν] using h s hs) bot_le
  exact sq_eq_zero_iff.mp hsq

/-- The two bounds in the distinct-ordinate manuscript have the same null sets.
    Both conclusions are Mathlib absolute continuity relations on actual measures. -/
theorem mutual_absoluteContinuity_of_set_sandwich {C : ℝ≥0∞}
    (hupper : ∀ s : Set α, MeasurableSet s → ν s ≤ C * μ s)
    (hlower : ∀ s : Set α, MeasurableSet s → (μ s) ^ 2 ≤ C * ν s) :
    (ν ≪ μ) ∧ (μ ≪ ν) := by
  constructor
  · apply AbsolutelyContinuous.mk
    intro s hs hμ
    exact le_antisymm (by simpa [hμ] using hupper s hs) bot_le
  · exact absolutelyContinuous_of_quadratic_set_bound hlower

/-- An explicit null-set equivalence, without any assertion of equality of measures. -/
theorem null_iff_of_set_sandwich {C : ℝ≥0∞}
    (hupper : ∀ s : Set α, MeasurableSet s → ν s ≤ C * μ s)
    (hlower : ∀ s : Set α, MeasurableSet s → (μ s) ^ 2 ≤ C * ν s)
    (s : Set α) : ν s = 0 ↔ μ s = 0 := by
  obtain ⟨hνμ, hμν⟩ := mutual_absoluteContinuity_of_set_sandwich hupper hlower
  exact ⟨fun hs => hμν hs, fun hs => hνμ hs⟩

end MeasureTheory.Measure

namespace Finset

variable {ι : Type*} (s : Finset ι) (h f : ι → ℝ)

/-- A multiplicity square budget controls total multiplicity per distinct sample. -/
theorem sum_le_card_mul_of_square_budget {C : ℝ}
    (htotal : 0 < ∑ i ∈ s, h i)
    (hbudget : ∑ i ∈ s, (h i) ^ 2 ≤ C * ∑ i ∈ s, h i) :
    (∑ i ∈ s, h i) ≤ C * (s.card : ℝ) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s h (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  have hc := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
  have hp : (∑ i ∈ s, h i) * (∑ i ∈ s, h i) ≤
      (∑ i ∈ s, h i) * (C * (s.card : ℝ)) := by
    calc
      _ = (∑ i ∈ s, h i) ^ 2 := by ring
      _ ≤ (∑ i ∈ s, (h i) ^ 2) * (s.card : ℝ) := hcs
      _ ≤ (C * ∑ i ∈ s, h i) * (s.card : ℝ) := hc
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ htotal).mp hp

/-- Multiplicities at least one imply that distinct count is at most total count. -/
theorem card_le_sum_of_one_le (hh : ∀ i ∈ s, 1 ≤ h i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, h i := by
  simpa using sum_le_sum hh

/-- Finite sampling domination prior to normalization. -/
theorem sum_test_le_weighted_test
    (hh : ∀ i ∈ s, 1 ≤ h i) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ s, h i * f i := by
  apply sum_le_sum
  intro i hi
  simpa using mul_le_mul_of_nonneg_right (hh i hi) (hf i hi)

/-- The normalized distinct law is bounded by C times the multiplicity law.
    The constant C comes only from the square budget, via the proved count bound. -/
theorem distinct_mean_le_mul_weighted_mean {C : ℝ}
    (hcard : 0 < (s.card : ℝ)) (htotal : 0 < ∑ i ∈ s, h i)
    (hh : ∀ i ∈ s, 1 ≤ h i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hbudget : ∑ i ∈ s, (h i) ^ 2 ≤ C * ∑ i ∈ s, h i) :
    (∑ i ∈ s, f i) / (s.card : ℝ) ≤
      C * ((∑ i ∈ s, h i * f i) / (∑ i ∈ s, h i)) := by
  have hcount := sum_le_card_mul_of_square_budget s h htotal hbudget
  have hsum := sum_test_le_weighted_test s h f hh hf
  have hnonneg : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hf
  have hmul := mul_le_mul_of_nonneg_left hcount hnonneg
  have hmul' := mul_le_mul_of_nonneg_right hsum (htotal.le)
  have hC : 0 ≤ C := by
    by_contra hneg
    have : C * (s.card : ℝ) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcard
    linarith
  have hweighted : 0 ≤ ∑ i ∈ s, h i * f i := le_trans hnonneg hsum
  have hcompare : (∑ i ∈ s, f i) * (∑ i ∈ s, h i) ≤
      C * (∑ i ∈ s, h i * f i) * (s.card : ℝ) := by
    calc
      _ ≤ (∑ i ∈ s, f i) * (C * (s.card : ℝ)) := hmul
      _ ≤ (∑ i ∈ s, h i * f i) * (C * (s.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg hC hcard.le)
      _ = _ := by ring
  rw [show C * ((∑ i ∈ s, h i * f i) / (∑ i ∈ s, h i)) =
    (C * (∑ i ∈ s, h i * f i)) / (∑ i ∈ s, h i) by ring]
  exact (div_le_div_iff₀ hcard htotal).mpr hcompare

/-- The normalized multiplicity test is quadratically bounded by the distinct
    square test. This is the crucial finite Cauchy--Schwarz inequality. -/
theorem weighted_mean_sq_le_mul_distinct_square_mean {C : ℝ}
    (hcard : 0 < (s.card : ℝ)) (htotal : 0 < ∑ i ∈ s, h i)
    (hh : ∀ i ∈ s, 1 ≤ h i)
    (hbudget : ∑ i ∈ s, (h i) ^ 2 ≤ C * ∑ i ∈ s, h i) :
    ((∑ i ∈ s, h i * f i) / (∑ i ∈ s, h i)) ^ 2 ≤
      C * ((∑ i ∈ s, (f i) ^ 2) / (s.card : ℝ)) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s h f
  have hsum : 0 ≤ ∑ i ∈ s, (f i) ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hcount := card_le_sum_of_one_le s h hh
  have hC : 0 ≤ C := by
    have hb := sum_le_card_mul_of_square_budget s h htotal hbudget
    by_contra hneg
    have : C * (s.card : ℝ) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcard
    linarith
  have h1 : (∑ i ∈ s, h i * f i) ^ 2 ≤
      C * (∑ i ∈ s, h i) * (∑ i ∈ s, (f i) ^ 2) := by
    calc
      _ ≤ (∑ i ∈ s, (h i) ^ 2) * (∑ i ∈ s, (f i) ^ 2) := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hsum
  have h2 := mul_le_mul_of_nonneg_right h1 hcard.le
  have h3 := mul_le_mul_of_nonneg_left hcount
    (mul_nonneg (mul_nonneg hC htotal.le) hsum)
  have hbound : (∑ i ∈ s, h i * f i) ^ 2 * (s.card : ℝ) ≤
      (C * (∑ i ∈ s, (f i) ^ 2)) * (∑ i ∈ s, h i) ^ 2 := by
    calc
      _ ≤ (C * (∑ i ∈ s, h i) * (∑ i ∈ s, (f i) ^ 2)) * (s.card : ℝ) := h2
      _ ≤ (C * (∑ i ∈ s, h i) * (∑ i ∈ s, (f i) ^ 2)) * (∑ i ∈ s, h i) := h3
      _ = _ := by ring
  rw [div_pow]
  rw [show C * ((∑ i ∈ s, (f i) ^ 2) / (s.card : ℝ)) =
    (C * (∑ i ∈ s, (f i) ^ 2)) / (s.card : ℝ) by ring]
  exact (div_le_div_iff₀ (sq_pos_of_pos htotal) hcard).mpr hbound

end Finset

namespace RiemannResearch.Fourier

variable {ι : Type*}

/-- A bounded character error transfers to a finite Fourier polynomial with
    its exact Wiener budget. The character estimate is an explicit hypothesis. -/
theorem finite_fourier_error_le_wiener_budget (s : Finset ι)
    (a e : ι → ℂ) (η : ℝ) (he : ∀ i ∈ s, ‖e i‖ ≤ η) :
    ‖∑ i ∈ s, a i * e i‖ ≤ (∑ i ∈ s, ‖a i‖) * η := by
  calc
    _ ≤ ∑ i ∈ s, ‖a i * e i‖ := norm_sum_le s _
    _ ≤ ∑ i ∈ s, ‖a i‖ * η := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he i hi) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

end RiemannResearch.Fourier
