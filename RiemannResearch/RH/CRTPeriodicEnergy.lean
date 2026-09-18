/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTTrigammaBounds
import RiemannResearch.RH.ConditionalUniformMixture
import RiemannResearch.RH.CesaroResidueMean
import Mathlib.Analysis.SumOverResidueClass

/-!
# Exact periodic conditional-mean energy and certified infinite tails

Source: the prime-block CRT conversation, September 18, 2026.
The arithmetic averages are identified with the existing conditional-iid Cesaro
operator. No uniform CRT norm is substituted for the actual weights.
-/

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open scoped BigOperators
open ArithmeticCumulative
open RiemannResearch.Probability.ConditionalIID (cesaro)

def periodMean (F : ℕ → ℝ) (Q : ℕ) : ℝ := cumulative F Q / (Q : ℝ)

def periodDefect (F : ℕ → ℝ) (Q r : ℕ) : ℝ :=
  cumulative F r - (r : ℝ) * periodMean F Q

theorem cumulative_period_shift (F : ℕ → ℝ) (Q n : ℕ)
    (hp : ∀ k, F (k + Q) = F k) :
    cumulative F (Q + n) = cumulative F Q + cumulative F n := by
  unfold cumulative
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hp (k + 1)

theorem cumulative_periods (F : ℕ → ℝ) (Q k r : ℕ)
    (hp : ∀ n, F (n + Q) = F n) :
    cumulative F (Q * k + r) = (k : ℝ) * cumulative F Q + cumulative F r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show Q * (k + 1) + r = Q + (Q * k + r) by ring,
      cumulative_period_shift F Q _ hp, ih]
    push_cast
    ring

theorem cesaro_period_formula (F : ℕ → ℝ) (Q k r : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) (hp : ∀ n, F (n + Q) = F n) :
    cesaro F (Q * k + r) = periodMean F Q +
      periodDefect F Q r / ((Q * k + r : ℕ) : ℝ) := by
  rw [CesaroResidue.cesaro_eq_cumulative, cumulative_periods F Q k r hp]
  unfold periodDefect periodMean
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have htr : ((Q * k + r : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  <;> ring

theorem periodDefect_periodic (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (n : ℕ) :
    periodDefect F Q (n + Q) = periodDefect F Q n := by
  unfold periodDefect periodMean
  rw [Nat.add_comm n Q, cumulative_period_shift F Q n hp]
  push_cast
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem cesaro_from_defect (F : ℕ → ℝ) (Q t : ℕ) (ht : 0 < t) :
    cesaro F t = periodMean F Q + periodDefect F Q t / (t : ℝ) := by
  rw [CesaroResidue.cesaro_eq_cumulative]
  unfold periodDefect
  have htR : (t : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem hasSum_mixtureWeight_tail (M : ℕ) :
    HasSum (fun k : ℕ => mixtureWeight (M + k + 1)) (2 / ((M : ℝ) + 2)) := by
  have h := (hasSum_weight_from (M + 2) (by omega)).mul_left 2
  have he : (fun k : ℕ => mixtureWeight (M + k + 1)) =
      (fun k : ℕ => 2 * weight (M + 2 + k)) := by
    funext k
    unfold mixtureWeight weight
    push_cast
    ring
  rw [he]
  convert h using 1 <;> try rfl
  push_cast
  ring

theorem cesaro_error_bound_of_defect (F : ℕ → ℝ) (Q M t : ℕ)
    (B c : ℝ) (ht : M < t) (hB : 0 ≤ B)
    (hb : |periodDefect F Q t| ≤ B) :
    |cesaro F t - c| ≤ |periodMean F Q - c| + B / ((M : ℝ) + 1) := by
  rw [cesaro_from_defect F Q t (by omega)]
  have he : periodMean F Q + periodDefect F Q t / (t : ℝ) - c =
      (periodMean F Q - c) + periodDefect F Q t / (t : ℝ) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_div, abs_of_pos (show (0 : ℝ) < (t : ℝ) by
    exact_mod_cast (show 0 < t by omega))]
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans
  apply div_le_div_of_nonneg_left hB (by positivity)
  exact_mod_cast (show M + 1 ≤ t by omega)

/-- Summability is proved, rather than relying on the totalized real tsum. -/
theorem periodic_error_tail_summable (F : ℕ → ℝ) (Q M : ℕ) (B c : ℝ)
    (hB : 0 ≤ B) (hb : ∀ t, M < t → |periodDefect F Q t| ≤ B) :
    Summable (fun k : ℕ => mixtureWeight (M + k + 1) *
      (cesaro F (M + k + 1) - c)^2) := by
  have hs := (hasSum_mixtureWeight_tail M).summable.mul_right
    ((|periodMean F Q - c| + B / ((M : ℝ) + 1))^2)
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))
    _ hs
  intro k
  apply mul_le_mul_of_nonneg_left _ (mixtureWeight_nonneg _)
  have h := cesaro_error_bound_of_defect F Q M (M + k + 1) B c (by omega) hB
    (hb _ (by omega))
  have hR : 0 ≤ |periodMean F Q - c| + B / ((M : ℝ) + 1) := by positivity
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 h

/-- The entire omitted tail has an explicit positive upper certificate. -/
theorem periodic_error_tail_bound (F : ℕ → ℝ) (Q M : ℕ) (B c : ℝ)
    (hB : 0 ≤ B) (hb : ∀ t, M < t → |periodDefect F Q t| ≤ B) :
    (∑' k : ℕ, mixtureWeight (M + k + 1) * (cesaro F (M + k + 1) - c)^2) ≤
      2 / ((M : ℝ) + 2) * (|periodMean F Q - c| + B / ((M : ℝ) + 1))^2 := by
  have hs := (hasSum_mixtureWeight_tail M).summable.mul_right
    ((|periodMean F Q - c| + B / ((M : ℝ) + 1))^2)
  calc
    _ ≤ ∑' k : ℕ, mixtureWeight (M + k + 1) *
        (|periodMean F Q - c| + B / ((M : ℝ) + 1))^2 := by
      apply Summable.tsum_le_tsum _ (periodic_error_tail_summable F Q M B c hB hb) hs
      intro k
      apply mul_le_mul_of_nonneg_left _ (mixtureWeight_nonneg _)
      have h := cesaro_error_bound_of_defect F Q M (M + k + 1) B c (by omega) hB
        (hb _ (by omega))
      have hR : 0 ≤ |periodMean F Q - c| + B / ((M : ℝ) + 1) := by positivity
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 h
    _ = _ := by rw [tsum_mul_right, (hasSum_mixtureWeight_tail M).tsum_eq]

theorem periodic_error_prefix_tail (F : ℕ → ℝ) (Q M : ℕ) (B c : ℝ)
    (hB : 0 ≤ B) (hb : ∀ t, 0 < t → |periodDefect F Q t| ≤ B) :
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) =
      (∑ k ∈ Finset.range M, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) +
      ∑' k : ℕ, mixtureWeight (M + k + 1) * (cesaro F (M + k + 1) - c)^2 := by
  have hs := periodic_error_tail_summable F Q 0 B c hB (by simpa using hb)
  have h := hs.sum_add_tsum_nat_add M
  simpa only [Nat.zero_add, Nat.add_comm M] using h.symm

/-- Reducing a periodic sequence to its finite set of residues is exact. -/
theorem periodic_value_mod (g : ℕ → ℝ) (Q : ℕ)
    (hp : ∀ n, g (n + Q) = g n) (n : ℕ) : g n = g (n % Q) := by
  have hm (k : ℕ) : g (n % Q + Q * k) = g (n % Q) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]
  calc
    g n = g (n % Q + Q * (n / Q)) := by rw [Nat.mod_add_div]
    _ = _ := hm _

theorem periodDefect_bound_of_finite (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (B : ℝ)
    (hb : ∀ r, r < Q → |periodDefect F Q r| ≤ B) (t : ℕ) :
    |periodDefect F Q t| ≤ B := by
  rw [periodic_value_mod (periodDefect F Q) Q (periodDefect_periodic F Q hQ hp) t]
  exact hb _ (Nat.mod_lt t hQ)

theorem periodDefect_exists_bound (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |periodDefect F Q t| ≤ B := by
  let B := ∑ r ∈ Finset.range Q, |periodDefect F Q r|
  refine ⟨B, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  apply periodDefect_bound_of_finite F Q hQ hp B
  intro r hr
  change |periodDefect F Q r| ≤ ∑ j ∈ Finset.range Q, |periodDefect F Q j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (periodDefect F Q j))
    (Finset.mem_range.mpr hr)

theorem periodic_error_summable (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (c : ℝ) :
    Summable (fun k : ℕ => mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) := by
  obtain ⟨B, hB, hb⟩ := periodDefect_exists_bound F Q hQ hp
  simpa using periodic_error_tail_summable F Q 0 B c hB (fun t _ => hb t)

def qKernel (t : ℝ) : ℝ := 2 / ((t + 1) * (t + 2))

def progressionQ (Q r : ℝ) : ℝ := ∑' k : ℕ, qKernel (Q * (k : ℝ) + r)

theorem qKernel_le_square (t : ℝ) (ht : 0 < t) : qKernel t ≤ 2 * (1 / t^2) := by
  unfold qKernel
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem progressionQ_summable {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => qKernel (Q * (k : ℝ) + r)) := by
  apply Summable.of_nonneg_of_le (fun k => by unfold qKernel; positivity)
    (fun k => qKernel_le_square _ (by positivity))
    ((progressionSquare_summable hQ hr).mul_left 2)

theorem qKernel_quadratic (t a b : ℝ) (ht : 0 < t) :
    qKernel t * (a + b / t)^2 = a^2 * qKernel t +
      (2 * a * b) * lKernel t + b^2 * (lKernel t / t) := by
  unfold qKernel lKernel
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem progression_quadratic_identity (Q r a b : ℝ) (hQ : 0 < Q) (hr : 0 < r) :
    (∑' k : ℕ, qKernel (Q * (k : ℝ) + r) * (a + b / (Q * (k : ℝ) + r))^2) =
      a^2 * progressionQ Q r + (2 * a * b) * progressionL Q r +
        b^2 * progressionM Q r := by
  have h0 := (progressionQ_summable hQ hr).mul_left (a^2)
  have h1 := (progressionL_summable hQ hr).mul_left (2 * a * b)
  have h2 := (progressionM_summable hQ hr).mul_left (b^2)
  calc
    _ = ∑' k : ℕ, (a^2 * qKernel (Q * (k : ℝ) + r) +
        (2 * a * b) * lKernel (Q * (k : ℝ) + r) +
        b^2 * (lKernel (Q * (k : ℝ) + r) / (Q * (k : ℝ) + r))) :=
      tsum_congr (fun k => qKernel_quadratic _ a b (by positivity))
    _ = _ := by
      rw [(h0.add h1).tsum_add h2, h0.tsum_add h1]
      simp only [tsum_mul_left, progressionQ, progressionL, progressionM]

theorem progressionQ_normalization (Q : ℕ) (hQ : 0 < Q) :
    (∑ r : Fin Q, progressionQ Q (r.val + 1)) = 1 := by
  cases Q with
  | zero => omega
  | succ N =>
    have h := Nat.sumByResidueClasses hasSum_mixtureWeight.summable (N + 1)
    rw [hasSum_mixtureWeight.tsum_eq] at h
    calc
      _ = ∑ r : Fin (N+1), ∑' k : ℕ, mixtureWeight (r.val + (N+1)*k+1) := by
        apply Finset.sum_congr rfl
        intro r hr
        unfold progressionQ
        apply tsum_congr
        intro k
        unfold qKernel mixtureWeight
        push_cast
        ring
      _ = 1 := h.symm

/-- Exact residue-class energy identity; the signed mixed term is not discarded. -/
theorem periodic_error_energy_identity (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (c : ℝ) :
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) =
      (periodMean F Q - c)^2 +
      2 * (periodMean F Q - c) *
        (∑ r : Fin Q, progressionL Q (r.val + 1) * periodDefect F Q (r.val + 1)) +
      ∑ r : Fin Q, progressionM Q (r.val + 1) * (periodDefect F Q (r.val + 1))^2 := by
  cases Q with
  | zero => omega
  | succ N =>
    rw [Nat.sumByResidueClasses (periodic_error_summable F (N+1) hQ hp c) (N+1)]
    change (∑ r : Fin (N+1), ∑' k : ℕ,
      mixtureWeight (r.val + (N+1)*k+1) *
        (cesaro F (r.val + (N+1)*k+1) - c)^2) = _
    have hterm (r : Fin (N + 1)) :
        (∑' k : ℕ, mixtureWeight (r.val + (N + 1) * k + 1) *
          (cesaro F (r.val + (N + 1) * k + 1) - c)^2) =
        (periodMean F (N+1) - c)^2 * progressionQ (N+1) (r.val+1) +
        (2 * (periodMean F (N+1) - c) * periodDefect F (N+1) (r.val+1)) *
          progressionL (N+1) (r.val+1) +
        (periodDefect F (N+1) (r.val+1))^2 * progressionM (N+1) (r.val+1) := by
      rw [← progression_quadratic_identity (N+1) (r.val+1)
        (periodMean F (N+1) - c) (periodDefect F (N+1) (r.val+1))
        (by positivity) (by positivity)]
      apply tsum_congr
      intro k
      have hi : r.val + (N+1)*k+1 = (N+1)*k+(r.val+1) := by omega
      rw [hi, cesaro_period_formula F (N+1) k (r.val+1) hQ (by omega) hp]
      unfold mixtureWeight qKernel
      push_cast
      ring
    calc
      _ = ∑ r : Fin (N+1), (
          (periodMean F (N+1) - c)^2 * progressionQ (N+1) (r.val+1) +
          2 * (periodMean F (N+1) - c) *
            (progressionL (N+1) (r.val+1) * periodDefect F (N+1) (r.val+1)) +
          progressionM (N+1) (r.val+1) * (periodDefect F (N+1) (r.val+1))^2) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hterm r]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
        have hnorm := progressionQ_normalization (N+1) hQ
        simp only [Nat.cast_add, Nat.cast_one] at hnorm ⊢
        rw [hnorm, mul_one]

end
end RiemannResearch.RH.CRTBlock
