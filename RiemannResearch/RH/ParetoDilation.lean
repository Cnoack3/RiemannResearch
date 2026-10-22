import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ParetoWeights
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
Source: user-provided argument in RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md
and RH_Smoothing_Mixed_Controls_and_Large_Prime_Gains_2026-09-07.md §7.3.
The zero index has weight zero. All positive masses are the actual Pareto masses.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def positiveWeight (k : ℕ) : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1))

theorem positiveWeight_nonneg (k : ℕ) : 0 ≤ positiveWeight k := by
  unfold positiveWeight; positivity

theorem positiveWeight_difference (k : ℕ) (hk : 0 < k) :
    positiveWeight k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  unfold positiveWeight
  field_simp
  <;> ring

theorem positiveWeight_interval (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, positiveWeight k) = 1 / (a : ℝ) - 1 / (b : ℝ) := by
  calc
    _ = ∑ k ∈ Finset.Ico a b, ((1 / (k : ℝ)) - 1 / ((k + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Nat.cast_add, Nat.cast_one] using
        positiveWeight_difference k (lt_of_lt_of_le ha (Finset.mem_Ico.mp hk).1)
    _ = _ := by
      have h := Finset.sum_Ico_sub (fun k : ℕ => -(1 / (k : ℝ))) hab
      simpa only [neg_sub_neg] using h

theorem positiveWeight_block (p j : ℕ) (hp : 0 < p) (hj : 0 < j) :
    (∑ k ∈ Finset.Ico (p*j) (p*(j+1)), positiveWeight k) = positiveWeight j / p := by
  rw [positiveWeight_interval _ _ (Nat.mul_pos hp hj) (Nat.mul_le_mul_left p (by omega))]
  unfold positiveWeight
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem dilation_block (p j : ℕ) (hp : 0 < p) (hj : 0 < j) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Ico (p*j) (p*(j+1)), positiveWeight k * dilation p f k) =
      positiveWeight j * f j := by
  have hd (k : ℕ) (hk : k ∈ Finset.Ico (p*j) (p*(j+1))) : k / p = j := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using (Finset.mem_Ico.mp hk).1
    · simpa [Nat.mul_comm] using (Finset.mem_Ico.mp hk).2
  calc
    _ = (∑ k ∈ Finset.Ico (p*j) (p*(j+1)), positiveWeight k) * ((p : ℝ) * f j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dilation, hd k hk]
    _ = _ := by
      rw [positiveWeight_block p j hp hj]
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      field_simp

theorem dilation_product_block (p j : ℕ) (hp : 0 < p) (hj : 0 < j) (f g : ℕ → ℝ) :
    (∑ k ∈ Finset.Ico (p*j) (p*(j+1)),
      positiveWeight k * (dilation p f k * dilation p g k)) =
        p * (positiveWeight j * (f j * g j)) := by
  have h := dilation_block p j hp hj (fun k => f k * g k)
  calc
    _ = (p : ℝ) * (∑ k ∈ Finset.Ico (p*j) (p*(j+1)),
        positiveWeight k * dilation p (fun k => f k * g k) k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      unfold dilation
      ring
    _ = _ := by rw [h]

/-- The block below p vanishes because the sequence is anchored at zero. -/
theorem dilation_block_all (p j : ℕ) (hp : 0 < p) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    (∑ k ∈ Finset.Ico (p*j) (p*(j+1)), positiveWeight k * dilation p f k) =
      positiveWeight j * f j := by
  by_cases hj : j = 0
  · subst j
    simp only [Nat.mul_zero, zero_add, Nat.mul_one, hf0, mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < p := (Finset.mem_Ico.mp hk).2
    simp [dilation, Nat.div_eq_of_lt hk', hf0]
  · exact dilation_block p j hp (Nat.pos_of_ne_zero hj) f

/-- Complete finite-block mean identity, including the first block. -/
theorem dilation_partial_sum (p N : ℕ) (hp : 0 < p) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    (∑ k ∈ Finset.range (p*N), positiveWeight k * dilation p f k) =
      ∑ j ∈ Finset.range N, positiveWeight j * f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have hb := dilation_block_all p N hp f hf0
    rw [Finset.sum_Ico_eq_sum_range] at hb
    simpa [Nat.mul_add, Nat.add_sub_cancel_left] using hb

/-- Full Pareto mean preservation for integrable sequences and their dilations.
The hypotheses are ordinary absolute summability, not arithmetic convergence estimates. -/
theorem dilation_tsum (p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun k => positiveWeight k * f k))
    (hd : Summable (fun k => positiveWeight k * dilation p f k)) :
    (∑' k, positiveWeight k * dilation p f k) = ∑' k, positiveWeight k * f k := by
  have hpn : Filter.Tendsto (fun N : ℕ => p*N) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
    exact Nat.le_mul_of_pos_left N hp
  have hlim := hd.hasSum.tendsto_sum_nat.comp hpn
  have heq : (fun N => ∑ k ∈ Finset.range (p*N), positiveWeight k * dilation p f k) =
      (fun N => ∑ k ∈ Finset.range N, positiveWeight k * f k) := by
    funext N
    exact dilation_partial_sum p N hp f hf0
  simp only [Function.comp_def] at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hf.hasSum.tendsto_sum_nat

/-- Compatibility of zero-anchored and shifted positive indexing. -/
theorem positiveWeight_succ (k : ℕ) : positiveWeight (k+1) = paretoWeight k := by
  unfold positiveWeight paretoWeight
  push_cast
  congr 1 <;> ring

theorem positiveWeight_summable : Summable positiveWeight := by
  apply (summable_nat_add_iff 1).mp
  simpa only [positiveWeight_succ] using paretoWeight_hasSum.summable

theorem positiveWeight_tsum : (∑' k, positiveWeight k) = 1 := by
  rw [positiveWeight_summable.tsum_eq_zero_add]
  simp only [positiveWeight_succ, paretoWeight_tsum]
  norm_num [positiveWeight]

/-- All bounded sequences have absolutely convergent Pareto means. -/
theorem weighted_summable_of_bounded {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) :
    Summable (fun k => positiveWeight k * f k) := by
  apply (positiveWeight_summable.mul_right C).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveWeight_nonneg k)]
  exact mul_le_mul_of_nonneg_left (hC k) (positiveWeight_nonneg k)

theorem dilation_abs_le {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) (p k : ℕ) :
    |dilation p f k| ≤ (p : ℝ) * C := by
  unfold dilation
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
  exact mul_le_mul_of_nonneg_left (hC _) (Nat.cast_nonneg p)

def paretoMean (f : ℕ → ℝ) : ℝ := ∑' k, positiveWeight k * f k

def paretoInner (f g : ℕ → ℝ) : ℝ :=
  ∑' k, positiveWeight k * (f k * g k)

/-- Mean preservation with summability discharged for every bounded anchored sequence. -/
theorem paretoMean_dilation {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C)
    (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoMean (dilation p f) = paretoMean f := by
  exact dilation_tsum p hp f hf0 (weighted_summable_of_bounded hC)
    (weighted_summable_of_bounded (dilation_abs_le hC p))

theorem bounded_product {f g : ℕ → ℝ} {C D : ℝ}
    (hC : ∀ k, |f k| ≤ C) (hD : ∀ k, |g k| ≤ D) :
    ∀ k, |f k * g k| ≤ C * D := by
  intro k
  rw [abs_mul]
  exact mul_le_mul (hC k) (hD k) (abs_nonneg _) (le_trans (abs_nonneg _) (hC k))

/-- Exact inner-product scaling for actual Pareto weights, with no periodicity needed. -/
theorem paretoInner_dilation {f g : ℕ → ℝ} {C D : ℝ}
    (hC : ∀ k, |f k| ≤ C) (hD : ∀ k, |g k| ≤ D)
    (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoInner (dilation p f) (dilation p g) = (p : ℝ) * paretoInner f g := by
  have hprod := bounded_product hC hD
  have hdprod := dilation_abs_le hprod p
  have hs := weighted_summable_of_bounded hdprod
  have he : (fun k => positiveWeight k * (dilation p f k * dilation p g k)) =
      (fun k => (p : ℝ) * (positiveWeight k * dilation p (fun j => f j * g j) k)) := by
    funext k
    unfold dilation
    ring
  unfold paretoInner
  rw [he, hs.tsum_mul_left]
  change (p : ℝ) * paretoMean (dilation p (fun j => f j * g j)) = _
  rw [paretoMean_dilation hprod (by simp [hf0]) p hp]
  rfl

theorem error_square_bounded {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) :
    ∀ k, |(1-f k)^2| ≤ (1+C)^2 := by
  intro k
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC k)
  rw [abs_of_nonneg (sq_nonneg _)]
  have hb : |1-f k| ≤ 1+C := by
    calc
      _ ≤ |(1 : ℝ)| + |f k| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (1 : ℝ) 0 (f k)
      _ ≤ _ := by simpa using add_le_add (le_refl (1 : ℝ)) (hC k)
  nlinarith [sq_abs (1-f k), abs_nonneg (1-f k)]

/-- Full-tail finite real packet combinations always have a finite squared error. -/
theorem packetCombination_error_summable (s : Finset ℕ) (c : ℕ → ℝ) :
    Summable (fun k => positiveWeight k * (1-∑ q ∈ s, c q*ramanujanPacket q k)^2) := by
  obtain ⟨C,hC⟩ := packetCombination_bounded s c
  exact weighted_summable_of_bounded (error_square_bounded hC)

/-- A square-summable linear sequence for the Pareto weights must be zero. -/
theorem linear_square_summable_iff (c : ℝ) :
    Summable (fun k => positiveWeight k * (c * (k : ℝ))^2) ↔ c = 0 := by
  constructor
  · intro hs
    have hshift := (summable_nat_add_iff 1).mpr hs
    have hconst : Summable (fun _ : ℕ => c^2 / 2) := by
      apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hshift
      intro k
      unfold positiveWeight
      push_cast
      have hk1 : (k : ℝ)+1 > 0 := by positivity
      have hk2 : (k : ℝ)+2 > 0 := by positivity
      rw [show (k : ℝ)+1+1 = (k : ℝ)+2 by ring]
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ (mul_pos hk1 hk2)).mpr
      nlinarith [mul_nonneg (sq_nonneg c) (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hk1.le)]
    have hz : c^2 / 2 = 0 := (summable_const_iff (c^2 / 2)).mp hconst
    nlinarith [sq_nonneg c]
  · rintro rfl
    simp

end
end RiemannResearch.RH.Pareto
