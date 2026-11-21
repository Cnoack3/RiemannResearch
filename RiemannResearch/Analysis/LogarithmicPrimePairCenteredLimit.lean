import RiemannResearch.Analysis.LogarithmicPrimePairFejer
import RiemannResearch.Analysis.MangoldtCumulativeDivergence
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalPrefix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Centered Fejér energy and the sharp logarithmic prime-pair law

The diagonal and translated endpoint limits are consequences of the prime
number theorem and finite estimates. The centered second moment is the
remaining arithmetic input. -/
noncomputable section
open Finset Filter
open scoped Topology BigOperators ArithmeticFunction
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open FractionalFejer

private theorem prefix_sub (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Ioc a b, f n) = (∑ n ∈ Icc 0 b, f n) - ∑ n ∈ Icc 0 a, f n := by
  have hu : Icc 0 b = Icc 0 a ∪ Ioc a b := by
    ext n
    simp only [mem_Icc, mem_Ioc, mem_union]
    omega
  rw [hu, sum_union (disjoint_left.mpr (fun n ha hb =>
    (not_lt_of_ge (mem_Icc.mp ha).2) (mem_Ioc.mp hb).1))]
  ring

private theorem scaled_square_prefix {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => (∑ n ∈ Icc 0 ⌊c*X⌋₊, (Λ n)^2)/(X*Real.log X)) atTop (𝓝 c) := by
  obtain ⟨C,hC,h⟩ := MontgomeryHorizontalBessel.mangoldtSquare_error_logPow 0
  let K := C*c + c*(|Real.log c|+1) + 1
  have hlim : Tendsto (fun X : ℝ => K/Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have herr : Tendsto (fun X : ℝ =>
      (∑ n ∈ Icc 0 ⌊c*X⌋₊, (Λ n)^2)/(X*Real.log X)-c) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [(tendsto_id.const_mul_atTop hc).eventually_ge_atTop 2,
      eventually_gt_atTop (1:ℝ)] with X hcx hX
    have hx : 0 < X := by linarith
    have hl := Real.log_pos hX
    have he := h (c*X) hcx
    rw [pow_zero, div_one, Real.log_mul hc.ne' hx.ne'] at he
    rw [Real.norm_eq_abs, show (∑ n ∈ Icc 0 ⌊c*X⌋₊, (Λ n)^2)/(X*Real.log X)-c =
      ((∑ n ∈ Icc 0 ⌊c*X⌋₊, (Λ n)^2)-c*(X*Real.log X))/(X*Real.log X) by
        field_simp [hx.ne',hl.ne'], abs_div,
      abs_of_pos (mul_pos hx hl)]
    apply (div_le_div_iff₀ (mul_pos hx hl) hl).mpr
    have hb : |(∑ n ∈ Icc 0 ⌊c*X⌋₊, (Λ n)^2) - c*(X*Real.log X)| ≤ K*X := by
      apply abs_le.mpr
      obtain ⟨lo,hi⟩ := abs_le.mp he
      have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log c)) (mul_pos hc hx).le
      have h2 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) (mul_pos hc hx).le
      dsimp [K]
      constructor <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hb hl.le]
  simpa only [sub_add_cancel, zero_add] using herr.add_const c

theorem annular_diagonal_limit {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    Tendsto (fun X : ℝ => (∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊, (Λ n)^2)/(X*Real.log X))
      atTop (𝓝 (B-A)) := by
  apply ((scaled_square_prefix (hA.trans hAB)).sub (scaled_square_prefix hA)).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
  rw [prefix_sub _ (Nat.floor_mono (mul_le_mul_of_nonneg_right hAB.le hX)), sub_div]

private theorem first_prefix {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => (∑ n ∈ Icc 0 ⌊c*X⌋₊, Λ n)/X) atTop (𝓝 c) := by
  have h := (MangoldtCumulativeDivergence.psi_ratio_tendsto.comp
    (tendsto_id.const_mul_atTop hc)).const_mul c
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  change c*(Chebyshev.psi (c*X)/(c*X)) = _
  rw [Chebyshev.psi_eq_sum_Icc]
  field_simp [hc.ne',hX.ne']

private theorem floor_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => (⌊c*X⌋₊:ℝ)/X) atTop (𝓝 c) := by
  have hlo := (tendsto_const_nhds (x := c)).sub
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun X : ℝ => 1/X) atTop (𝓝 0))
  rw [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    apply (le_div_iff₀ hX).mpr
    rw [sub_mul, div_mul_cancel₀ _ hX.ne']
    linarith [Nat.lt_floor_add_one (c*X)]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact (div_le_iff₀ hX).mpr (Nat.floor_le (mul_pos hc hX).le)

private theorem annular_mean_limit {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    Tendsto (fun X : ℝ => (∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊, (2*Λ n-1))/X)
      atTop (𝓝 (B-A)) := by
  have h := (((first_prefix (hA.trans hAB)).sub (first_prefix hA)).const_mul 2).sub
    ((floor_ratio (hA.trans hAB)).sub (floor_ratio hA))
  rw [show 2*(B-A)-(B-A) = B-A by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
  have hab := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB.le hX)
  simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc,
    Nat.cast_sub hab, prefix_sub (fun n => Λ n) hab]
  ring

/-- Centering changes the squared-coefficient mass by a lower-order first moment. -/
theorem annular_centered_diagonal_limit {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    Tendsto (fun X : ℝ => (∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊, (Λ n - 1)^2) / (X * Real.log X))
      atTop (𝓝 (B-A)) := by
  have h := (annular_diagonal_limit hA hAB).sub
    ((annular_mean_limit hA hAB).div_atTop Real.tendsto_log_atTop)
  rw [sub_zero] at h
  apply h.congr
  intro X
  rw [div_div, ← sub_div, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

private theorem endpoint_limits (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    Tendsto (fun X : ℝ => rightEndpoint ⌊A*X⌋₊ ⌊B*X⌋₊ (shiftWidth u X) (u*Real.log X) /
      (X*(Real.log X)^2)) atTop (𝓝 0) ∧
    Tendsto (fun X : ℝ => meanEndpoint ⌊A*X⌋₊ ⌊B*X⌋₊ (shiftWidth u X) (u*Real.log X) /
      (X*(Real.log X)^2)) atTop (𝓝 0) := by
  have hb : ∀ᶠ X : ℝ in atTop,
      let L := Real.log X
      let s := u*L
      let H := shiftWidth u X
      let a := ⌊A*X⌋₊
      let b := ⌊B*X⌋₊
      |rightEndpoint a b H s| ≤ 5*u^3*L^5 ∧ |meanEndpoint a b H s| ≤ 5*u^3*L^5 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (1:ℝ), eventually_window_mangoldt hB hu] with X hL hX hn
    dsimp only
    let L := Real.log X
    let H := shiftWidth u X
    have hx : 0 < X := by linarith
    have hL0 : 0 ≤ L := (Real.log_pos hX).le
    have hH : (H:ℝ) ≤ u*L := Nat.floor_le (mul_nonneg hu.le hL0)
    have he := fejer_endpoint_bounds (a := ⌊A*X⌋₊) hH (by positivity : 0 ≤ 2*L) hn
    have hW : (∑ h ∈ Ioc 0 H, (h:ℝ)*(u*L-h)) ≤ (u*L)^3 := by
      calc
        _ ≤ ∑ _h ∈ Ioc 0 H, (u*L)^2 := by
          apply sum_le_sum
          intro h hh
          have hle : (h:ℝ) ≤ u*L := (show (h:ℝ) ≤ H by exact_mod_cast (mem_Ioc.mp hh).2).trans hH
          rw [sq]
          exact mul_le_mul hle (by linarith [Nat.cast_nonneg (α := ℝ) h]) (by linarith) (by positivity)
        _ = (H:ℝ)*(u*L)^2 := by simp
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg (u*L))]
    have h1 : (2*L)^2 ≤ 5*L^2 := by nlinarith [sq_nonneg L]
    have h2 : 2*(2*L)+1 ≤ 5*L^2 := by
      change 1 ≤ L at hL
      nlinarith [sq_nonneg (L-1)]
    have up (K : ℝ) (hK : 0 ≤ K) (hk : K ≤ 5*L^2) :
        K*(∑ h ∈ Ioc 0 H, (h:ℝ)*(u*L-h)) ≤ 5*u^3*L^5 := by
      calc
        _ ≤ K*(u*L)^3 := mul_le_mul_of_nonneg_left hW hK
        _ ≤ (5*L^2)*(u*L)^3 := mul_le_mul_of_nonneg_right hk (by positivity)
        _ = _ := by ring
    exact ⟨he.1.trans (up _ (sq_nonneg _) h1), he.2.trans (up _ (by positivity) h2)⟩
  have hlog : Tendsto (fun X : ℝ => (Real.log X)^3 / X) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop (1:ℝ) 3 (by norm_num)
  have hlim := hlog.const_mul (5*u^3)
  rw [mul_zero] at hlim
  constructor <;> apply squeeze_zero_norm' _ hlim
  all_goals
    filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with X he hX
    obtain ⟨h1,h2⟩ := he
    have hx : 0 < X := by linarith
    have hl := Real.log_pos hX
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < X*(Real.log X)^2)]
    apply (div_le_iff₀ (by positivity : 0 < X*(Real.log X)^2)).mpr
    rw [show 5*u^3*(Real.log X^3/X)*(X*Real.log X^2) = 5*u^3*Real.log X^5 by
      field_simp [(by linarith : X ≠ 0)]
      <;> ring]
    assumption

private theorem kernel_mass_limit {u : ℝ} (hu : 0 < u) :
    Tendsto (fun X : ℝ =>
      ((u*Real.log X)^2 + (u*Real.log X-shiftWidth u X)*(1-(u*Real.log X-shiftWidth u X))) /
        (Real.log X)^2) atTop (𝓝 (u^2)) := by
  have hrec : Tendsto (fun X : ℝ => 1/Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h0 : Tendsto (fun X : ℝ => 1/(Real.log X)^2) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, zero_pow (by decide : 2 ≠ 0)] using hrec.pow 2
  have hr : Tendsto (fun X : ℝ =>
      (u*Real.log X-shiftWidth u X)*(1-(u*Real.log X-shiftWidth u X))/(Real.log X)^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ h0
    all_goals filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    all_goals
      have hl := Real.log_pos hX
      have hw : (shiftWidth u X:ℝ) ≤ u*Real.log X := Nat.floor_le (mul_pos hu hl).le
      have hw' := Nat.lt_floor_add_one (u*Real.log X)
      change u*Real.log X < (shiftWidth u X:ℝ)+1 at hw'
    · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
    · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (u*Real.log X-shiftWidth u X-1/2)])
        (sq_nonneg _)
  have hh := hr.const_add (u^2)
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  field_simp [(Real.log_pos hX).ne']
  <;> ring

/-- Removing the diagonal and restoring pairs crossing the endpoint in the
uncentered energy leaves twice the triangular statistic. -/
theorem uncentered_energy_sub_triangle_limit {A B u : ℝ} (hA : 0 < A) (hAB : A < B)
    (hu : 0 < u) :
    Tendsto (fun X : ℝ => annularEnergy A B u X (fun n => Λ n) / (X * (Real.log X)^2) -
      2 * trianglePairAverage A B u X) atTop (𝓝 (u * (B - A))) := by
  have hD := (annular_diagonal_limit hA hAB).const_mul u
  have hE := (endpoint_limits A (hA.trans hAB) hu).1
  have ht := hD.sub (hE.const_mul 2)
  rw [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have he := triangle_fejer_exact A B u hX
  field_simp [(Real.log_pos hX).ne', (by linarith : X ≠ 0)]
  simp only [mul_comm X B] at *
  linear_combination he

/-- Fixed-width uncentered Fejér criterion, including the diagonal main term. -/
theorem triangle_iff_uncentered_energy {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) :
    Tendsto (trianglePairAverage A B u) atTop (𝓝 ((B - A) * u^2 / 2)) ↔
    Tendsto (fun X : ℝ => annularEnergy A B u X (fun n => Λ n) / (X * (Real.log X)^2))
      atTop (𝓝 ((B - A) * (u^2 + u))) := by
  have h := uncentered_energy_sub_triangle_limit hA hAB hu
  constructor
  · intro ht
    have hsum := h.add (ht.const_mul 2)
    rw [show u * (B - A) + 2 * ((B - A) * u^2 / 2) = (B - A) * (u^2 + u) by ring] at hsum
    simpa only [sub_add_cancel] using hsum
  · intro ht
    have hdiff := (ht.sub h).div_const 2
    rw [show ((B - A) * (u^2 + u) - u * (B - A)) / 2 = (B - A) * u^2 / 2 by ring] at hdiff
    exact hdiff.congr (fun X => by ring)

/-- The difference of the two normalized actual observables has a known limit. -/
theorem centered_energy_sub_triangle_limit {A B u : ℝ} (hA : 0 < A) (hAB : A < B)
    (hu : 0 < u) :
    Tendsto (fun X : ℝ => annularEnergy A B u X (fun n => Λ n-1)/(X*(Real.log X)^2) -
      2*trianglePairAverage A B u X) atTop (𝓝 ((B-A)*(u-u^2))) := by
  have hD := (annular_diagonal_limit hA hAB).const_mul u
  have hM := (kernel_mass_limit hu).mul (annular_mean_limit hA hAB)
  obtain ⟨hE,hJ⟩ := endpoint_limits A (hA.trans hAB) hu
  have ht := ((hD.sub hM).sub (hE.const_mul 2)).add (hJ.const_mul 2)
  rw [show u*(B-A)-u^2*(B-A)-2*0+2*0 = (B-A)*(u-u^2) by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  have h1 := triangle_fejer_exact A B u hX
  have h2 := centered_fejer_exact ⌊A*X⌋₊ ⌊B*X⌋₊ (shiftWidth u X) (u*Real.log X)
  change annularEnergy A B u X (fun n => Λ n) - annularEnergy A B u X (fun n => Λ n-1) = _ at h2
  field_simp [(Real.log_pos hX).ne', (by linarith : X ≠ 0)]
  simp only [mul_comm X B] at *
  linear_combination h1 + h2

/-- At each fixed positive width the centered variance law is equivalent to the triangular law. -/
theorem triangle_iff_centered_energy {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) :
    Tendsto (trianglePairAverage A B u) atTop (𝓝 ((B-A)*u^2/2)) ↔
    Tendsto (fun X : ℝ => annularEnergy A B u X (fun n => Λ n-1)/(X*(Real.log X)^2))
      atTop (𝓝 ((B-A)*u)) := by
  have h := centered_energy_sub_triangle_limit hA hAB hu
  constructor
  · intro ht
    have hsum := h.add (ht.const_mul 2)
    rw [show (B-A)*(u-u^2) + 2*((B-A)*u^2/2) = (B-A)*u by ring] at hsum
    simpa only [sub_add_cancel] using hsum
  · intro ht
    have hdiff := (ht.sub h).div_const 2
    rw [show ((B-A)*u - (B-A)*(u-u^2))/2 = (B-A)*u^2/2 by ring] at hdiff
    exact hdiff.congr (fun X => by ring)

/-- Positivity of the centered energy yields a one-sided estimate for actual
prime pairs without any conjectural two-point input. -/
theorem eventually_triangle_gt_of_centered_nonneg {A B u y : ℝ} (hA : 0 < A) (hAB : A < B)
    (hu : 0 < u) (hy : y < (B-A)*(u^2-u)/2) :
    ∀ᶠ X : ℝ in atTop, y < trianglePairAverage A B u X := by
  have h := centered_energy_sub_triangle_limit hA hAB hu
  filter_upwards [h.eventually (eventually_lt_nhds (show (B-A)*(u-u^2) < -2*y by linarith)),
    eventually_gt_atTop (1:ℝ)] with X hb hX
  have hl := Real.log_pos hX
  have hw : (shiftWidth u X:ℝ) ≤ u*Real.log X := Nat.floor_le (mul_pos hu hl).le
  have hw' := Nat.lt_floor_add_one (u*Real.log X)
  change u*Real.log X < (shiftWidth u X:ℝ)+1 at hw'
  have he : 0 ≤ annularEnergy A B u X (fun n => Λ n-1) := by
    apply MeasureTheory.integral_nonneg
    intro t
    exact mul_nonneg (kernel_nonneg (sub_nonneg.mpr hw) (by linarith) _ t) (sq_nonneg _)
  linarith [div_nonneg he (mul_nonneg (by linarith : 0 ≤ X) (sq_nonneg (Real.log X)))]

theorem sharpPairAverage_of_centered_energy {A B : ℝ} (hA : 0 < A) (hAB : A < B)
    (hc : ∀ u : ℝ, 0 < u → Tendsto (fun X : ℝ =>
      annularEnergy A B u X (fun n => Λ n-1)/(X*(Real.log X)^2)) atTop (𝓝 ((B-A)*u)))
    {d : ℝ} (hd : 0 < d) : Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B-A)*d)) :=
  sharpPairAverage_of_triangle hAB (fun u hu => (triangle_iff_centered_energy hA hAB hu).2 (hc u hu)) hd

end RiemannResearch.Analysis.LogarithmicPrimePairs
