import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Exact cumulative-charge kernels, with the finite upper boundary retained

All coefficients may be complex. The strict cutoff convention differs from
q <= x only on the finite set of jump locations, hence not in the integrals.
No equidistribution or number-theoretic asymptotic is used in this module.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.CumulativeTailKernel

/-- A complex-valued weighted tail indicator. -/
def tail (a s x : ℝ) : ℂ := if a < x then (x ^ (-s - 1) : ℝ) else 0

lemma tail_eq_indicator (a s : ℝ) :
    tail a s = (Ioi a).indicator (fun x => ((x ^ (-s - 1) : ℝ) : ℂ)) := by
  funext x
  simp [tail, indicator, mem_Ioi]

lemma tail_integrable (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    Integrable (tail a s) := by
  rw [tail_eq_indicator, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) ha).ofReal

lemma integral_tail (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    (∫ x : ℝ, tail a s x) = ((a ^ (-s) / s : ℝ) : ℂ) := by
  rw [tail_eq_indicator, integral_indicator measurableSet_Ioi, integral_complex_ofReal]
  congr 1
  rw [integral_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) ha]
  simp only [sub_add_cancel, neg_div_neg_eq]

variable {ι : Type*}

/-- Cumulative finite complex charges. -/
def cumulative (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ S, if q i < x then c i else 0

/-- Exact expansion into the max-kernel tails. -/
theorem weighted_expansion (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (s x : ℝ) :
    cumulative S q c x * star (cumulative S q c x) * (x ^ (-s - 1) : ℝ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) * tail (max (q i) (q j)) s x := by
  classical
  simp only [cumulative, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hiq : q i < x <;> by_cases hjq : q j < x <;>
    simp [tail, hiq, hjq]

/-- The full signed cumulative energy. -/
theorem integral_weighted_expansion (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s : ℝ) (hs : 0 < s) (hq : ∀ i ∈ S, 0 < q i) :
    (∫ x : ℝ, cumulative S q c x * star (cumulative S q c x) *
      (x ^ (-s - 1) : ℝ)) =
      ∑ i ∈ S, ∑ j ∈ S,
        (c i * star (c j)) * ((max (q i) (q j) ^ (-s) / s : ℝ) : ℂ) := by
  simp_rw [weighted_expansion]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj =>
    (tail_integrable _ s (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj =>
    (tail_integrable _ s (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_tail _ s (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs]

lemma norm_square_cast (z : ℂ) (w : ℝ) :
    ((‖z‖ ^ 2 * w : ℝ) : ℂ) = z * star z * (w : ℂ) := by
  rw [Complex.ofReal_mul, Complex.sq_norm]
  exact congrArg (fun t : ℂ => t * (w : ℂ)) (Complex.mul_conj z).symm

/-- Real-valued energy identity with every signed cross term retained. -/
theorem cumulative_energy (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s : ℝ) (hs : 0 < s) (hq : ∀ i ∈ S, 0 < q i) :
    (∫ x : ℝ, ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1)) =
      ∑ i ∈ S, ∑ j ∈ S,
        (c i * star (c j)).re * (max (q i) (q j) ^ (-s) / s) := by
  have h := integral_weighted_expansion S q c s hs hq
  have he : (∫ x : ℝ, cumulative S q c x * star (cumulative S q c x) *
      (x ^ (-s - 1) : ℝ)) =
      ((∫ x : ℝ, ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1) : ℝ) : ℂ) := by
    simp_rw [← norm_square_cast]
    exact integral_complex_ofReal
  rw [he] at h
  simpa only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero] using congrArg Complex.re h

lemma cumulative_zero_below (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (a x : ℝ) (hq : ∀ i ∈ S, a ≤ q i) (hx : x ≤ a) : cumulative S q c x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (not_lt_of_ge (hx.trans (hq i hi)))

/-- Original Pareto-domain form (all charges are at locations at least one). -/
theorem cumulative_energy_Ioi_one (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s : ℝ) (hs : 0 < s) (hq : ∀ i ∈ S, 1 ≤ q i) :
    (∫ x : ℝ in Ioi 1, ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1)) =
      ∑ i ∈ S, ∑ j ∈ S,
        (c i * star (c j)).re * (max (q i) (q j) ^ (-s) / s) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact cumulative_energy S q c s hs (fun i hi => lt_of_lt_of_le zero_lt_one (hq i hi))
  · intro x hx
    simp only [mem_Ioi, not_lt] at hx
    rw [cumulative_zero_below S q c 1 x hq hx]
    simp

/-- The finite upper boundary is a difference of two integrable tails. -/
lemma tail_boundary (a s Y x : ℝ) (haY : a ≤ Y) :
    (if x ≤ Y then tail a s x else 0) = tail a s x - tail Y s x := by
  by_cases hx : x ≤ Y
  · simp [tail, hx, not_lt_of_ge hx]
  · have hYx : Y < x := lt_of_not_ge hx
    simp [tail, hx, hYx, lt_of_le_of_lt haY hYx]

/-- Exact complex finite-boundary energy, including the negative boundary term. -/
theorem cumulative_energy_boundary_complex (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s Y : ℝ) (hs : 0 < s) (hY : 0 < Y)
    (hq : ∀ i ∈ S, 0 < q i) (hqY : ∀ i ∈ S, q i ≤ Y) :
    (∫ x : ℝ, if x ≤ Y then
      cumulative S q c x * star (cumulative S q c x) * (x ^ (-s - 1) : ℝ) else 0) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((max (q i) (q j) ^ (-s) - Y ^ (-s)) / s : ℝ) : ℂ) := by
  have hex (x : ℝ) :
      (if x ≤ Y then cumulative S q c x * star (cumulative S q c x) *
        (x ^ (-s - 1) : ℝ) else 0) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (tail (max (q i) (q j)) s x - tail Y s x) := by
    by_cases hx : x ≤ Y
    · simp only [if_pos hx, weighted_expansion]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [tail, not_lt_of_ge hx]
    · simp only [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      have hmax : max (q i) (q j) ≤ Y := max_le (hqY i hi) (hqY j hj)
      rw [← tail_boundary _ s Y x hmax, if_neg hx, mul_zero]
  simp_rw [hex]
  have hint (i : ι) (hi : i ∈ S) (j : ι) (_hj : j ∈ S) :
      Integrable (fun x => (c i * star (c j)) *
        (tail (max (q i) (q j)) s x - tail Y s x)) :=
    ((tail_integrable _ s (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs).sub
      (tail_integrable Y s hY hs)).const_mul _
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hint i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj => hint i hi j hj)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_sub
    (tail_integrable _ s (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs)
    (tail_integrable Y s hY hs), integral_tail _ s
    (lt_of_lt_of_le (hq i hi) (le_max_left _ _)) hs, integral_tail Y s hY hs]
  push_cast
  ring

/-- The real finite-boundary identity, without dropping the boundary energy. -/
theorem cumulative_energy_boundary (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s Y : ℝ) (hs : 0 < s) (hY : 0 < Y)
    (hq : ∀ i ∈ S, 0 < q i) (hqY : ∀ i ∈ S, q i ≤ Y) :
    (∫ x : ℝ, if x ≤ Y then ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1) else 0) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)).re *
        ((max (q i) (q j) ^ (-s) - Y ^ (-s)) / s) := by
  have h := cumulative_energy_boundary_complex S q c s Y hs hY hq hqY
  have he (x : ℝ) :
      (if x ≤ Y then cumulative S q c x * star (cumulative S q c x) *
        (x ^ (-s - 1) : ℝ) else 0) =
      ((if x ≤ Y then ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1) else 0 : ℝ) : ℂ) := by
    by_cases hx : x ≤ Y
    · simp only [if_pos hx]
      exact (norm_square_cast _ _).symm
    · simp [hx]
  simp_rw [he] at h
  rw [integral_complex_ofReal] at h
  simpa only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero] using congrArg Complex.re h

/-- The same finite-boundary identity on the original interval (1,Y]. -/
theorem cumulative_energy_Ioc (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s Y : ℝ) (hs : 0 < s) (hY : 0 < Y)
    (hq : ∀ i ∈ S, 1 ≤ q i) (hqY : ∀ i ∈ S, q i ≤ Y) :
    (∫ x : ℝ in Ioc 1 Y, ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1)) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)).re *
        ((max (q i) (q j) ^ (-s) - Y ^ (-s)) / s) := by
  rw [← integral_indicator measurableSet_Ioc]
  have hi (x : ℝ) :
      (Ioc 1 Y).indicator (fun x => ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1)) x =
      if x ≤ Y then ‖cumulative S q c x‖ ^ 2 * x ^ (-s - 1) else 0 := by
    by_cases hx1 : 1 < x
    · simp [indicator, mem_Ioc, hx1]
    · have hz := cumulative_zero_below S q c 1 x hq (le_of_not_gt hx1)
      simp [indicator, mem_Ioc, hx1, hz]
  simp_rw [hi]
  exact cumulative_energy_boundary S q c s Y hs hY
    (fun i hi => lt_of_lt_of_le zero_lt_one (hq i hi)) hqY

/-- The conventional non-strict cumulative sum. -/
def cumulativeLE (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i ∈ S, if q i ≤ x then c i else 0

/-- Strict and non-strict cutoffs agree outside finitely many jump locations. -/
theorem cumulative_eq_ae (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ) :
    cumulative S q c =ᵐ[volume] cumulativeLE S q c := by
  classical
  induction S using Finset.induction with
  | empty => exact Filter.Eventually.of_forall (fun x => by simp [cumulative, cumulativeLE])
  | @insert a S ha ih =>
      have hne : ∀ᵐ x : ℝ, x ≠ q a := by simp [ae_iff]
      filter_upwards [ih, hne] with x hx hnx
      have hiff : q a < x ↔ q a ≤ x := by
        constructor
        · exact le_of_lt
        · intro h
          exact lt_of_le_of_ne h hnx.symm
      simp only [cumulative, cumulativeLE, Finset.sum_insert ha] at hx ⊢
      simp only [hiff, hx]

/-- The max-kernel identity for the conventional cumulative charges q <= x. -/
theorem cumulativeLE_energy (S : Finset ι) (q : ι → ℝ) (c : ι → ℂ)
    (s : ℝ) (hs : 0 < s) (hq : ∀ i ∈ S, 1 ≤ q i) :
    (∫ x : ℝ in Ioi 1, ‖cumulativeLE S q c x‖ ^ 2 * x ^ (-s - 1)) =
      ∑ i ∈ S, ∑ j ∈ S,
        (c i * star (c j)).re * (max (q i) (q j) ^ (-s) / s) := by
  rw [← cumulative_energy_Ioi_one S q c s hs hq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (cumulative_eq_ae S q c)] with x hx
  rw [hx]

end RiemannResearch.Analysis.CumulativeTailKernel
