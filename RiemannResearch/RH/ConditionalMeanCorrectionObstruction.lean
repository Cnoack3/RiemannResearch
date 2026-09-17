import RiemannResearch.Probability.ConditionalIIDUniformMoments
import RiemannResearch.RH.ConditionalUniformMixture
import RiemannResearch.RH.SingleCorrectionObstruction
import Mathlib.Tactic

/-!
# Finite conditional-mean correction obstructions

Source: `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 8. It reuses the project's actual conditional
mean `Probability.ConditionalIID.cesaro`, latent `mixtureWeight`, and
`singleRepair`, including the canonical floor window.

All energies here are finite sums; no Mertens estimate or existence of an
RH approximation family is assumed.
-/

namespace RiemannResearch.RH.ArithmeticCumulative.ConditionalMeanCorrection
noncomputable section
open scoped BigOperators
open RiemannResearch.Probability.ConditionalIID (cesaro)

lemma cesaro_eq_sum_range (F : ℕ → ℝ) (t : ℕ) :
    cesaro F t = (∑ n ∈ Finset.range t, F (n + 1)) / (t : ℝ) := by
  unfold cesaro
  congr 1
  symm
  refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

lemma sum_positive_ints (t : ℕ) :
    (∑ n ∈ Finset.range t, ((n : ℝ) + 1)) = (t : ℝ) * ((t : ℝ) + 1) / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The exact mean of the affine initial segment, with no global assumption on F. -/
theorem cesaro_affine_head (F : ℕ → ℝ) (α : ℝ) (t : ℕ) (ht : 0 < t)
    (hF : ∀ n, 1 ≤ n → n ≤ t → F n = 1 - α * (n : ℝ)) :
    cesaro F t = 1 - α * ((t : ℝ) + 1) / 2 := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hs : (∑ n ∈ Finset.range t, F (n + 1)) =
      (t : ℝ) - α * ((t : ℝ) * ((t : ℝ) + 1) / 2) := by
    calc
      _ = ∑ n ∈ Finset.range t, (1 - α * ((n : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hF (n + 1) (by omega) (by have := Finset.mem_range.mp hn; omega)]
        simp only [Nat.cast_add, Nat.cast_one]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_positive_ints]
        simp
  rw [cesaro_eq_sum_range, hs]
  field_simp
  <;> ring

lemma affine_weighted_error_lower (α : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    α ^ 2 / 3 ≤ mixtureWeight t * (-α * ((t : ℝ) + 1) / 2) ^ 2 := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  have ht01 : (t : ℝ) + 1 ≠ 0 := by positivity
  have heq : mixtureWeight t * (-α * ((t : ℝ) + 1) / 2) ^ 2 =
      α ^ 2 * ((t : ℝ) + 1) / (2 * ((t : ℝ) + 2)) := by
    unfold mixtureWeight
    field_simp
    <;> ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((t : ℝ) + 2))).2
  nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr ht1)]

/-- The finite part already forces the α²Y/3 obstruction (8.2). -/
theorem naive_sieve_smoothed_lower_bound (F : ℕ → ℝ) (α : ℝ) (Y : ℕ)
    (hF : ∀ n, 1 ≤ n → n ≤ Y → F n = 1 - α * (n : ℝ)) :
    α ^ 2 * (Y : ℝ) / 3 ≤
      ∑ t ∈ Finset.range Y, mixtureWeight (t + 1) * (cesaro F (t + 1) - 1) ^ 2 := by
  calc
    _ = ∑ _t ∈ Finset.range Y, α ^ 2 / 3 := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have htY : t + 1 ≤ Y := by have := Finset.mem_range.mp ht; omega
      rw [cesaro_affine_head F α (t + 1) (by omega)
        (fun n hn hnt => hF n hn (le_trans hnt htY))]
      have heq : 1 - α * (((t + 1 : ℕ) : ℝ) + 1) / 2 - 1 =
          -α * (((t + 1 : ℕ) : ℝ) + 1) / 2 := by ring
      rw [heq]
      exact affine_weighted_error_lower α (t + 1) (by omega)

lemma sum_successor_squares_lower (N : ℕ) :
    (N : ℝ) ^ 3 / 3 ≤ ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]

lemma window_weight_lower (D L j : ℕ) (β : ℝ)
    (hβ8 : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (hL : (L : ℝ) ≤ β / 4) (hj : j ≤ L) :
    1 / (3 * (D : ℝ) ^ 2) ≤ mixtureWeight (D + j) := by
  have hDj : (j : ℝ) + 2 ≤ D := by
    have hjL : (j : ℝ) ≤ L := by exact_mod_cast hj
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hden : ((D : ℝ) + j + 1) * ((D : ℝ) + j + 2) ≤ 6 * (D : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * (D : ℝ)) * (2 * (D : ℝ)) := by
        apply mul_le_mul <;> first | linarith | positivity
      _ ≤ _ := by nlinarith [sq_nonneg (D : ℝ)]
  unfold mixtureWeight
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Exact finite energy lower bound from the signed prefix-error estimate.
The two L hypotheses are precisely those supplied by L=floor(β/4). -/
theorem finite_signed_window_lower_bound (E : ℕ → ℝ) (D L : ℕ) (β : ℝ)
    (hβ8 : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (hL : (L : ℝ) ≤ β / 4) (hβL : β ≤ 4 * ((L : ℝ) + 1))
    (hE : ∀ j, j ≤ L → E j ≤ -(((j : ℝ) + 1) * β / (4 * (D : ℝ)))) :
    β ^ 5 / (9216 * (D : ℝ) ^ 4) ≤
      ∑ j ∈ Finset.range (L + 1), mixtureWeight (D + j) * (E j) ^ 2 := by
  have hDpos : (0 : ℝ) < D := by linarith
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hβpos : (0 : ℝ) ≤ β := by linarith
  have hterm : ∀ j, j ≤ L →
      β ^ 2 / (48 * (D : ℝ) ^ 4) * ((j : ℝ) + 1) ^ 2 ≤
        mixtureWeight (D + j) * (E j) ^ 2 := by
    intro j hj
    have hA : (0 : ℝ) ≤ ((j : ℝ) + 1) * β / (4 * (D : ℝ)) := by positivity
    have hEA : ((j : ℝ) + 1) * β / (4 * (D : ℝ)) ≤ -E j := by
      linarith [hE j hj]
    have hsq : (((j : ℝ) + 1) * β / (4 * (D : ℝ))) ^ 2 ≤ (E j) ^ 2 := by
      have hm := mul_self_le_mul_self hA hEA
      nlinarith
    calc
      _ = (1 / (3 * (D : ℝ) ^ 2)) *
          (((j : ℝ) + 1) * β / (4 * (D : ℝ))) ^ 2 := by field_simp; ring
      _ ≤ _ := mul_le_mul (window_weight_lower D L j β hβ8 hβD hL hj)
        hsq (sq_nonneg _) (by unfold mixtureWeight; positivity)
  have hsum : β ^ 2 / (48 * (D : ℝ) ^ 4) *
      (((L : ℝ) + 1) ^ 3 / 3) ≤
      ∑ j ∈ Finset.range (L + 1), mixtureWeight (D + j) * (E j) ^ 2 := by
    calc
      _ ≤ β ^ 2 / (48 * (D : ℝ) ^ 4) *
          (∑ j ∈ Finset.range (L + 1), ((j : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · simpa using sum_successor_squares_lower (L + 1)
        · positivity
      _ = ∑ j ∈ Finset.range (L + 1),
          β ^ 2 / (48 * (D : ℝ) ^ 4) * ((j : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hterm j (by
        have := Finset.mem_range.mp hj
        omega))
  have hcube : β ^ 3 ≤ (4 * ((L : ℝ) + 1)) ^ 3 := by
    gcongr <;> assumption
  have hnum : β ^ 5 ≤ 64 * β ^ 2 * ((L : ℝ) + 1) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hcube (sq_nonneg β)
    nlinarith
  calc
    _ ≤ (64 * β ^ 2 * ((L : ℝ) + 1) ^ 3) / (9216 * (D : ℝ) ^ 4) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = β ^ 2 / (48 * (D : ℝ) ^ 4) * (((L : ℝ) + 1) ^ 3 / 3) := by
      field_simp
      <;> ring
    _ ≤ _ := hsum

/-- Signed Cesaro error forced by a unit head and a negative correction window. -/
theorem signed_cesaro_error_of_head_window (F : ℕ → ℝ) (D L : ℕ) (β : ℝ)
    (hD : 0 < D) (hL : L ≤ D) (hβ : 0 ≤ β)
    (hhead : ∀ n, 1 ≤ n → n < D → F n = 1)
    (hblock : ∀ k, k ≤ L → F (D + k) ≤ 1 - β / 2) :
    ∀ j, j ≤ L →
      cesaro F (D + j) - 1 ≤ -(((j : ℝ) + 1) * β / (4 * (D : ℝ))) := by
  intro j hj
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hjD : (j : ℝ) ≤ D := by exact_mod_cast le_trans hj hL
  have htpos : (0 : ℝ) < ((D + j : ℕ) : ℝ) := by positivity
  have hzero : (∑ n ∈ Finset.range (D - 1), (F (n + 1) - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [hhead (n + 1) (by omega) (by have := Finset.mem_range.mp hn; omega)]
    ring
  have htail : (∑ k ∈ Finset.range (j + 1), (F ((D - 1) + k + 1) - 1)) ≤
      -((j : ℝ) + 1) * β / 2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (j + 1), (-β / 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkL : k ≤ L := by have := Finset.mem_range.mp hk; omega
        rw [show (D - 1) + k + 1 = D + k by omega]
        linarith [hblock k hkL]
      _ = _ := by simp; ring
  have hsum : (∑ n ∈ Finset.range (D + j), (F (n + 1) - 1)) ≤
      -((j : ℝ) + 1) * β / 2 := by
    rw [show D + j = (D - 1) + (j + 1) by omega, Finset.sum_range_add]
    simpa only [hzero, zero_add] using htail
  have hmean : cesaro F (D + j) - 1 =
      (∑ n ∈ Finset.range (D + j), (F (n + 1) - 1)) / ((D + j : ℕ) : ℝ) := by
    rw [cesaro_eq_sum_range, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
  calc
    _ = _ := hmean
    _ ≤ (-((j : ℝ) + 1) * β / 2) / ((D + j : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hsum (le_of_lt htpos)
    _ = -(((j : ℝ) + 1) * β / (2 * ((D : ℝ) + j))) := by
      push_cast
      field_simp
      <;> ring
    _ ≤ -(((j : ℝ) + 1) * β / (4 * (D : ℝ))) := by
      apply neg_le_neg
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg (show 0 ≤ ((j : ℝ) + 1) * β by positivity)
        (sub_nonneg.mpr hjD)]

/-- Concrete finite Cesaro-energy version of the one-divisor obstruction.
For the handoff's repair, its elementary floor calculation gives `hhead` and
`hblock`. This theorem proves the complete subsequent smoothing calculation. -/
theorem finite_head_window_smoothed_obstruction (F : ℕ → ℝ) (D L : ℕ) (β : ℝ)
    (hβ8 : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (hL : (L : ℝ) ≤ β / 4) (hβL : β ≤ 4 * ((L : ℝ) + 1))
    (hhead : ∀ n, 1 ≤ n → n < D → F n = 1)
    (hblock : ∀ k, k ≤ L → F (D + k) ≤ 1 - β / 2) :
    β ^ 5 / (9216 * (D : ℝ) ^ 4) ≤
      ∑ j ∈ Finset.range (L + 1), mixtureWeight (D + j) * (cesaro F (D + j) - 1) ^ 2 := by
  apply finite_signed_window_lower_bound (fun j => cesaro F (D + j) - 1)
    D L β hβ8 hβD hL hβL
  apply signed_cesaro_error_of_head_window F D L β
  · have : (0 : ℝ) < D := by linarith
    exact_mod_cast this
  · have : (L : ℝ) ≤ D := by linarith
    exact_mod_cast this
  · linarith
  · exact hhead
  · exact hblock

/-- The exact single-divisor repair, with canonical L=floor(β/4), already
has the handoff's β^5/(9216D^4) lower bound in its finite conditional-mean window. -/
theorem singleRepair_smoothed_obstruction (R : ℕ → ℝ) (D : ℕ) (β : ℝ)
    (hβ8 : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (hhead : ∀ n, 1 ≤ n → n < D → R n = 1)
    (hR : ∀ j ≤ ⌊β / 4⌋₊, R (D + j) ≤ (j : ℝ) + 2) :
    β ^ 5 / (9216 * (D : ℝ) ^ 4) ≤
      ∑ j ∈ Finset.range (⌊β / 4⌋₊ + 1), mixtureWeight (D + j) *
        (cesaro (singleRepair R D β) (D + j) - 1) ^ 2 := by
  have hDreal : (0 : ℝ) < D := by linarith
  have hD : 0 < D := by exact_mod_cast hDreal
  have hL : (⌊β / 4⌋₊ : ℝ) ≤ β / 4 := Nat.floor_le (by linarith)
  have hβL : β ≤ 4 * ((⌊β / 4⌋₊ : ℝ) + 1) := by
    have h := Nat.lt_floor_add_one (β / 4)
    linarith
  apply finite_head_window_smoothed_obstruction (singleRepair R D β) D ⌊β / 4⌋₊ β
    hβ8 hβD hL hβL
  · intro n hn hnD
    exact singleRepair_head R D n β hnD (hhead n hn hnD)
  · intro j hj
    have hjβ : (j : ℝ) ≤ β / 4 := le_trans (by exact_mod_cast hj) hL
    have hjD : j < D := by
      have : (j : ℝ) < (D : ℝ) := by linarith
      exact_mod_cast this
    have ho := singleRepair_overshoot R D j β hD hjD hβ8 hjβ (hR j hj)
    linarith

/-- Counting sources with an exact unit head give the concrete smoothed
one-divisor obstruction without any prime-asymptotic input. -/
theorem singleRepair_counting_smoothed_obstruction (a : ℕ → ℝ) (D : ℕ) (β : ℝ)
    (hβ8 : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (ha : ∀ n, a n ≤ 1)
    (hhead : ∀ n, 1 ≤ n → n < D → cumulative a n = 1) :
    β ^ 5 / (9216 * (D : ℝ) ^ 4) ≤
      ∑ j ∈ Finset.range (⌊β / 4⌋₊ + 1), mixtureWeight (D + j) *
        (cesaro (singleRepair (cumulative a) D β) (D + j) - 1) ^ 2 := by
  have hD8 : 8 ≤ D := by exact_mod_cast (show (8 : ℝ) ≤ D by linarith)
  apply singleRepair_smoothed_obstruction (cumulative a) D β hβ8 hβD hhead
  intro j hj
  apply counting_source_window_bound a D j (by omega) ha
  exact hhead (D - 1) (by omega) (by omega)

end
end RiemannResearch.RH.ArithmeticCumulative.ConditionalMeanCorrection
