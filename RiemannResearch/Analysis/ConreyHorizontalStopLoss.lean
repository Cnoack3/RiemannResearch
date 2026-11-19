/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCriticalLineTailFraction
import RiemannResearch.Analysis.ConreyStopLossPolynomialEnvelope
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Conrey's stop-loss bound and microscopic endpoint windows

Conrey, J. reine angew. Math. 399 (1989), Section 5,
https://doi.org/10.1515/crll.1989.399.1, supplies the Gaussian mollified mean
square. The one-piece optimization and transfer to cumulative heights are recorded in
`RiemannResearch/RH/OptimizedHorizontalMoments20261119.md`. Its analytic statement is a named
hypothesis. All finite mark inequalities and compact-window implications below
are derived from that statement. The global finite-height Selberg input has its
own quantifiers. -/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

def microscopicExcess (T u : ℝ) : ℝ :=
  (∑ c : Copies T, max (copyDisplacement T c * Real.log T - u) 0) / (Ncount 0 T : ℝ)

def microscopicClosedTail (T s : ℝ) : ℝ :=
  (∑ c : Copies T, if s ≤ copyDisplacement T c * Real.log T then (1 : ℝ) else 0) /
    (Ncount 0 T : ℝ)

def conreyStopLossProfile (u : ℝ) : ℝ :=
  if u = 0 then Real.log (11 / 4) else
    Real.log ((1 - Real.exp (-(22 / 7) * u)) / (1 - Real.exp (-(8 / 7) * u)))

/-- External analytic hypothesis with the height limit preceding the threshold limit. -/
def ConreyStopLossHypothesis : Prop :=
  ∀ u : ℝ, 0 ≤ u → ∀ B : ℝ, conreyStopLossProfile u < B →
    ∀ᶠ T : ℝ in atTop, microscopicExcess T u ≤ B

def microscopicEndpointConstant : ℝ := (8 / 7) * (267 / 250) * Real.exp 1

theorem microscopicClosedTail_nonneg (T s : ℝ) : 0 ≤ microscopicClosedTail T s := by
  unfold microscopicClosedTail
  positivity

theorem microscopicClosedTail_le_one (T s : ℝ) : microscopicClosedTail T s ≤ 1 := by
  unfold microscopicClosedTail
  by_cases hz : (Ncount 0 T : ℝ) = 0
  · simp [hz]
  apply (div_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hz))).mpr
  calc
    _ ≤ ∑ _ : Copies T, (1 : ℝ) := Finset.sum_le_sum (fun c _ => by split_ifs <;> norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul, card_copies]

theorem microscopicClosedTail_antitone (T : ℝ) : Antitone (microscopicClosedTail T) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro c _
  by_cases ht : t ≤ copyDisplacement T c * Real.log T
  · rw [if_pos ht, if_pos (hst.trans ht)]
  · rw [if_neg ht]
    split_ifs <;> norm_num

theorem microscopicClosedTail_le_excess (T s h : ℝ) :
    h * microscopicClosedTail T s ≤ microscopicExcess T (s-h) := by
  unfold microscopicClosedTail microscopicExcess
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · rw [mul_one]
    exact (by linarith : h ≤ copyDisplacement T c * Real.log T - (s - h)).trans (le_max_left _ _)
  · simp

/-- Shifting the strike costs at most its increment times the off-line mass. -/
theorem microscopicExcess_le_shifted {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    microscopicExcess T u ≤ microscopicExcess T v +
      (v-u) * (strictTail T 0 / (Ncount 0 T : ℝ)) := by
  unfold microscopicExcess strictTail FiniteStrictTail.tail
  rw [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 0 < copyDisplacement T c
  · rw [if_pos hc, mul_one]
    apply max_le
    · linarith only [le_max_left (copyDisplacement T c * Real.log T-v) 0]
    · linarith only [le_max_right (copyDisplacement T c * Real.log T-v) 0, huv]
  · have hz : copyDisplacement T c = 0 := le_antisymm (not_lt.mp hc) (abs_nonneg _)
    simp only [hz, zero_mul, zero_sub, lt_self_iff_false, if_false, mul_zero, add_zero]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]

/-- The gain from any available critical-line proportion, expressed as an
upper bound for the normalized strict tail. -/
theorem microscopicExcess_asymptotic_cap (h : ConreyStopLossHypothesis)
    {u v d B : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hd : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, strictTail T 0 / (Ncount 0 T : ℝ) ≤ d+ε)
    (hB : conreyStopLossProfile v + (v-u)*d < B) :
    ∀ᶠ T : ℝ in atTop, microscopicExcess T u ≤ B := by
  let e := (B-(conreyStopLossProfile v + (v-u)*d))/(1+(v-u))
  have he : 0 < e := div_pos (sub_pos.mpr hB) (by linarith)
  have heq : e*(1+(v-u)) = B-(conreyStopLossProfile v + (v-u)*d) :=
    div_mul_cancel₀ _ (by linarith)
  filter_upwards [h v (hu.trans huv) (conreyStopLossProfile v+e) (by linarith), hd e he]
    with T hT ht
  apply (microscopicExcess_le_shifted (T:=T) hu huv).trans
  calc
    _ ≤ (conreyStopLossProfile v+e)+(v-u)*(d+e) :=
      add_le_add hT (mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr huv))
    _ = B := by linarith only [heq]

/-- The repository's critical-line input gives the explicit one-third cap. -/
theorem microscopicExcess_asymptotic_third (h : ConreyStopLossHypothesis)
    {u v B : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hB : conreyStopLossProfile v + (v - u) * (1 / 3) < B) :
    ∀ᶠ T : ℝ in atTop, microscopicExcess T u ≤ B := by
  apply microscopicExcess_asymptotic_cap h hu huv _ hB
  intro ε hε
  exact (eventually_normalized_strictTail_le_third ε hε).mono fun _ hT => hT 0 le_rfl

/-- Near-optimal explicit exponential majorant for the one-piece profile. -/
theorem conreyStopLossProfile_le_endpoint {u : ℝ} (hu : 0 ≤ u) :
    conreyStopLossProfile u ≤ (267 / 250) * Real.exp (-(8 / 7) * u) := by
  by_cases hzero : u = 0
  · subst u
    simp only [conreyStopLossProfile, if_pos rfl, mul_zero, Real.exp_zero, mul_one]
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr ConreyStopLossEnvelope.boundary_le_exp
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
  let t := Real.exp (-(2 / 7) * u)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht4 : t^4 = Real.exp (-(8 / 7)*u) := by
    dsimp only [t]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    <;> ring
  have ht11 : t^11 = Real.exp (-(22 / 7)*u) := by
    dsimp only [t]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    <;> ring
  rw [conreyStopLossProfile, if_neg hzero, ← ht4, ← ht11]
  have hp : 0 < (1-t^11)/(1-t^4) :=
    div_pos (sub_pos.mpr (pow_lt_one₀ ht.le ht1 (by norm_num)))
      (sub_pos.mpr (pow_lt_one₀ ht.le ht1 (by norm_num)))
  exact (Real.log_le_iff_le_exp hp).mpr (ConreyStopLossEnvelope.quotient_le_exp ht.le ht1)

/-- Endpoint bound at one fixed scaled threshold, allowing any strict upper constant. -/
theorem microscopic_endpoint_at_fixed (h : ConreyStopLossHypothesis) {s B : ℝ}
    (hB : microscopicEndpointConstant < B) :
    ∀ᶠ T : ℝ in atTop, Real.exp ((8 / 7) * s) * microscopicClosedTail T s ≤ B := by
  by_cases hshort : s < 7 / 8
  · apply Filter.Eventually.of_forall
    intro T
    calc
      _ ≤ Real.exp ((8 / 7) * s) := by
        simpa using mul_le_mul_of_nonneg_left (microscopicClosedTail_le_one T s) (Real.exp_pos _).le
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ microscopicEndpointConstant := by
        dsimp [microscopicEndpointConstant]
        exact le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
      _ ≤ B := hB.le
  have hu : 0 ≤ s-7/8 := by linarith
  have he : (267 / 250) * Real.exp (-(8 / 7) * (s-7/8)) =
      microscopicEndpointConstant * (7/8) * Real.exp (-(8 / 7) * s) := by
    rw [show -(8 / 7) * (s-7/8) = 1 + (-(8 / 7) * s) by ring, Real.exp_add]
    dsimp only [microscopicEndpointConstant]
    ring
  have hgap : conreyStopLossProfile (s-7/8) < B*(7/8)*Real.exp (-(8 / 7) * s) := by
    apply (conreyStopLossProfile_le_endpoint hu).trans_lt
    rw [he]
    gcongr
  filter_upwards [h _ hu _ hgap] with T hT
  have htail := (microscopicClosedTail_le_excess T s (7/8)).trans hT
  have hk : microscopicClosedTail T s ≤ B * Real.exp (-(8 / 7) * s) := by linarith only [htail]
  calc
    _ ≤ Real.exp ((8 / 7) * s) * (B * Real.exp (-(8 / 7) * s)) :=
      mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = B := by rw [neg_mul, Real.exp_neg]; field_simp

/-- The endpoint is uniform on each fixed compact interval of scaled thresholds. -/
theorem microscopic_endpoint_on_compact (h : ConreyStopLossHypothesis) {B : ℝ}
    (hB : microscopicEndpointConstant < B) (M : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) M,
      Real.exp ((8 / 7) * s) * microscopicClosedTail T s ≤ B := by
  let A := (microscopicEndpointConstant+B)/2
  have hC0 : 0 < microscopicEndpointConstant := by unfold microscopicEndpointConstant; positivity
  have hCA : microscopicEndpointConstant < A := by dsimp [A]; linarith
  have hAB : A < B := by dsimp [A]; linarith
  have hA : 0 < A := hC0.trans hCA
  let d := Real.log (B/A) / (8/7)
  have hd : 0 < d := div_pos (Real.log_pos ((one_lt_div hA).mpr hAB)) (by norm_num)
  have hscale : Real.exp ((8/7)*d)*A = B := by
    rw [show (8/7)*d = Real.log (B/A) by dsimp [d]; ring,
      Real.exp_log (div_pos (hA.trans hAB) hA)]
    field_simp
  let J := Finset.range (⌊M/d⌋₊ + 1)
  have hgrid : ∀ᶠ T : ℝ in atTop, ∀ n ∈ J,
      Real.exp ((8/7)*((n:ℝ)*d)) * microscopicClosedTail T ((n:ℝ)*d) ≤ A :=
    (Filter.eventually_all_finset J).mpr fun n _ =>
      microscopic_endpoint_at_fixed h hCA
  filter_upwards [hgrid] with T hT
  intro s hs
  let n := ⌊s/d⌋₊
  have hn : n ∈ J := Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Nat.floor_le_floor (div_le_div_of_nonneg_right hs.2 hd.le)))
  have hfloor := (Nat.floor_eq_iff (div_nonneg hs.1 hd.le)).mp (show ⌊s/d⌋₊ = n from rfl)
  have hlo : (n:ℝ)*d ≤ s := (le_div_iff₀ hd).mp hfloor.1
  have hhi : s ≤ d+(n:ℝ)*d := by linarith only [(div_lt_iff₀ hd).mp hfloor.2]
  calc
    _ ≤ Real.exp ((8/7)*(d+(n:ℝ)*d)) * microscopicClosedTail T ((n:ℝ)*d) :=
      mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (microscopicClosedTail_antitone T hlo)
        (microscopicClosedTail_nonneg T s) (Real.exp_pos _).le
    _ = Real.exp ((8/7)*d) *
        (Real.exp ((8/7)*((n:ℝ)*d)) * microscopicClosedTail T ((n:ℝ)*d)) := by
      rw [mul_add, Real.exp_add, mul_assoc]
    _ ≤ Real.exp ((8/7)*d)*A := mul_le_mul_of_nonneg_left (hT n hn) (Real.exp_pos _).le
    _ = B := hscale

/-- Existence of a diverging microscopic window. Its growth is unspecified. -/
theorem microscopic_endpoint_on_growing_window (h : ConreyStopLossHypothesis) {B : ℝ}
    (hB : microscopicEndpointConstant < B) :
    ∃ W : ℝ → ℕ, Tendsto W atTop atTop ∧
      ∀ᶠ T : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) (W T : ℝ),
        Real.exp ((8 / 7)*s) * microscopicClosedTail T s ≤ B := by
  classical
  let P (T : ℝ) (n : ℕ) := ∀ s ∈ Icc (0 : ℝ) (n:ℝ),
    Real.exp ((8/7)*s) * microscopicClosedTail T s ≤ B
  let W (T : ℝ) := Nat.findGreatest (P T) ⌊T⌋₊
  have hp (n : ℕ) : ∀ᶠ T : ℝ in atTop, P T n := microscopic_endpoint_on_compact h hB n
  refine ⟨W, tendsto_atTop.mpr ?_, ?_⟩
  · intro n
    filter_upwards [hp n, eventually_ge_atTop (n:ℝ)] with T hT hn
    by_contra! hlt
    exact (Nat.findGreatest_is_greatest hlt (Nat.le_floor hn)) hT
  · filter_upwards [hp 0] with T hT
    have hspec := Nat.findGreatest_eq_iff.mp (show Nat.findGreatest (P T) ⌊T⌋₊ = W T from rfl)
    by_cases hz : W T = 0
    · simpa only [hz] using hT
    · exact hspec.2.1 hz

end RiemannResearch.Analysis.ActualZeroOrdinate
