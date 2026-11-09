import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variation in the residue conductor in the complete Pareto norm

A block of adjacent conductor differences admits simultaneous bounds of
order n and M² at physical coordinate n. These give bounded energy for its
normalized variation envelope, including the full infinite tail. Pairings
with any fixed Hilbert vector therefore have vanishing mean absolute
adjacent difference over the blocks [M,2M).
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

def residueConductorVariation (M n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, |residue (M + i + 1) n - residue (M + i) n|

theorem residueConductorVariation_eq_zero_of_lt {M n : ℕ} (hn : n < M) :
    residueConductorVariation M n = 0 := by
  unfold residueConductorVariation
  apply Finset.sum_eq_zero
  intro i _
  simp [residue, Nat.mod_eq_of_lt (show n < M + i by omega),
    Nat.mod_eq_of_lt (show n < M + i + 1 by omega)]

private theorem residue_eq_sub_mul_div (m n : ℕ) :
    residue m n = (n : ℝ) - m * ((n / m : ℕ) : ℝ) := by
  have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div n m)
  push_cast at h
  unfold residue
  linarith

theorem residueConductorVariation_le_linear (M n : ℕ) (hM : 0 < M) :
    residueConductorVariation M n ≤ 3 * (n : ℝ) := by
  let a : ℕ → ℝ := fun i => ((n / (M + i) : ℕ) : ℝ)
  have ha (i : ℕ) : a (i + 1) ≤ a i := by
    dsimp [a]
    exact_mod_cast Nat.div_le_div_left (show M + i ≤ M + (i + 1) by omega) (by omega)
  have ha0 (i : ℕ) : 0 ≤ a i := Nat.cast_nonneg _
  have ham (i : ℕ) : a (i + 1) ≤ a 0 := by
    dsimp [a]
    exact_mod_cast Nat.div_le_div_left (show M + 0 ≤ M + (i + 1) by omega) (by omega)
  have hterm (i : ℕ) (hi : i ∈ Finset.range M) :
      |residue (M + i + 1) n - residue (M + i) n| ≤
        (2 * (M : ℝ)) * (a i - a (i + 1)) + a 0 := by
    have he : residue (M + i + 1) n - residue (M + i) n =
        ((M + i : ℕ) : ℝ) * (a i - a (i + 1)) - a (i + 1) := by
      rw [residue_eq_sub_mul_div, residue_eq_sub_mul_div]
      simp only [a, Nat.add_assoc, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    have hM' : ((M + i : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
      have hi' := Finset.mem_range.mp hi
      push_cast
      exact_mod_cast (show M + i ≤ 2 * M by omega)
    have hn : 0 ≤ a i - a (i + 1) := sub_nonneg.mpr (ha i)
    calc
      _ ≤ |((M + i : ℕ) : ℝ) * (a i - a (i + 1))| + |a (i + 1)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (((M + i : ℕ) : ℝ) * (a i - a (i + 1))) 0 (a (i + 1))
      _ ≤ _ := by
        rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hn), abs_of_nonneg (ha0 _)]
        exact add_le_add (mul_le_mul_of_nonneg_right hM' hn) (ham i)
  have hm : (M : ℝ) * a 0 ≤ n := by
    simp only [a, Nat.add_zero, mul_comm (M : ℝ)]
    exact_mod_cast Nat.div_mul_le_self n M
  calc
    _ ≤ ∑ i ∈ Finset.range M, ((2 * (M : ℝ)) * (a i - a (i + 1)) + a 0) :=
      Finset.sum_le_sum hterm
    _ = (2 * (M : ℝ)) * (a 0 - a M) + (M : ℝ) * a 0 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub']
      simp
    _ ≤ _ := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      nlinarith [mul_nonneg hM0 (ha0 M)]

theorem residueConductorVariation_le_quadratic (M n : ℕ) :
    residueConductorVariation M n ≤ 2 * (M : ℝ) ^ 2 := by
  unfold residueConductorVariation
  calc
    _ ≤ ∑ _i ∈ Finset.range M, 2 * (M : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hA : residue (M + i + 1) n ≤ 2 * (M : ℝ) := by
        have he : (M + i + 1 : ℕ) ≤ 2 * M := by omega
        exact ((le_abs_self _).trans (residue_abs_le (M + i + 1) n (by omega))).trans
          (by exact_mod_cast he)
      have hB : residue (M + i) n ≤ 2 * (M : ℝ) := by
        have he : (M + i : ℕ) ≤ 2 * M := by omega
        exact ((le_abs_self _).trans (residue_abs_le (M + i) n (by omega))).trans
          (by exact_mod_cast he)
      have ha : 0 ≤ residue (M + i + 1) n := Nat.cast_nonneg _
      have hb : 0 ≤ residue (M + i) n := Nat.cast_nonneg _
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := by simp [pow_two]; ring

/-- Complete Pareto energy bound for any signed average dominated by the
adjacent-conductor variation. The tail is split at M². -/
theorem norm_sq_le_of_residueConductorVariation {v : ThresholdHilbert} {M : ℕ}
    (hM : 0 < M)
    (hv : ∀ n, |hilbertSequence v n| ≤ residueConductorVariation M n / (M : ℝ)) :
    ‖v‖ ^ 2 ≤ 13 := by
  let L : ℕ := M * M
  have hL : 0 < L := Nat.mul_pos hM hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlinear (n : ℕ) : |hilbertSequence v n| ≤ 3 * (n : ℝ) / (M : ℝ) :=
    (hv n).trans (div_le_div_of_nonneg_right
      (residueConductorVariation_le_linear M n hM) hMr.le)
  have hconst (n : ℕ) : |hilbertSequence v n| ≤ 2 * (M : ℝ) := by
    refine (hv n).trans ((div_le_iff₀ hMr).mpr ?_)
    simpa only [pow_two, mul_assoc] using residueConductorVariation_le_quadratic M n
  let f : ℕ → ℝ := fun n => positiveWeight n * hilbertSequence v n ^ 2
  have hpre : (∑ n ∈ Finset.range L, f n) ≤ 9 := by
    calc
      _ ≤ ∑ _n ∈ Finset.range L, (9 : ℝ) / (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : n = 0
        · subst n
          simp only [f, hilbertSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
          positivity
        · have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hsq : hilbertSequence v n ^ 2 ≤ (3 * (n : ℝ) / (M : ℝ)) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hlinear n)
          have hfrac : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
            (div_le_one (by positivity)).mpr (by linarith)
          calc
            _ ≤ positiveWeight n * (3 * (n : ℝ) / (M : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg _)
            _ = ((n : ℝ) / ((n : ℝ) + 1)) * ((9 : ℝ) / (M : ℝ) ^ 2) := by
              unfold positiveWeight
              field_simp; ring
            _ ≤ _ := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac (by positivity :
                0 ≤ (9 : ℝ) / (M : ℝ) ^ 2)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, L, Nat.cast_mul]
        field_simp
  have hsum : Summable f := hilbertSequence_square_summable v
  have htail : (∑' n : ℕ, f (n + L)) ≤ 4 := by
    have hw := (summable_nat_add_iff L).mpr positiveWeight_summable
    calc
      _ ≤ ∑' n : ℕ, positiveWeight (n + L) * (2 * (M : ℝ)) ^ 2 := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff L).mpr hsum) (hw.mul_right _)
        intro n
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hconst (n + L))
      _ = _ := by
        rw [tsum_mul_right, positiveWeight_tail_tsum L hL]
        simp only [L, Nat.cast_mul]
        field_simp; ring
  rw [hilbert_norm_weighted_sq, ← hsum.sum_add_tsum_nat_add L]
  linarith

def residuePairing (h : ThresholdHilbert) (m : ℕ) : ℝ :=
  if 1 < m then inner ℝ (rawResidueAtom (m - 2)) h else 0

private def pairingVariation (h : ThresholdHilbert) (M : ℕ) : ℝ :=
  (∑ i ∈ Finset.range M, |residuePairing h (M + i + 1) - residuePairing h (M + i)|) / (M : ℝ)

private theorem pairingVariation_sq_le_tail (h : ThresholdHilbert) {M : ℕ} (hM : 2 ≤ M) :
    pairingVariation h M ^ 2 ≤ 13 * ‖hilbertTailShift h (M - 1)‖ ^ 2 := by
  let A : ℕ → ThresholdHilbert := fun i =>
    rawResidueAtom (M + i + 1 - 2) - rawResidueAtom (M + i - 2)
  let d : ℕ → ℝ := fun i => inner ℝ (A i) h
  let c : ℕ → ℝ := fun i => if 0 ≤ d i then 1 else -1
  let v : ThresholdHilbert := (M : ℝ)⁻¹ • ∑ i ∈ Finset.range M, c i • A i
  have hd (i : ℕ) :
      d i = residuePairing h (M + i + 1) - residuePairing h (M + i) := by
    simp only [d, A, inner_sub_left, residuePairing, if_pos (show 1 < M + i + 1 by omega),
      if_pos (show 1 < M + i by omega)]
  have hc (i : ℕ) : c i * d i = |d i| := by
    dsimp [c]
    split_ifs with hi
    · rw [one_mul, abs_of_nonneg hi]
    · rw [neg_one_mul, abs_of_nonpos (le_of_not_ge hi)]
  have hi : inner ℝ v h = pairingVariation h M := by
    simp only [v, real_inner_smul_left, sum_inner]
    change (M : ℝ)⁻¹ * (∑ i ∈ Finset.range M, c i * d i) = _
    simp_rw [hc, hd]
    rw [pairingVariation, div_eq_mul_inv, mul_comm]
  have hM' : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hvc (n : ℕ) : hilbertSequence v n =
      (M : ℝ)⁻¹ * ∑ i ∈ Finset.range M,
        c i * (residue (M + i + 1) n - residue (M + i) n) := by
    rw [← anchoredEvaluationCLM_apply]
    simp only [v, A, map_sum, map_smul, smul_eq_mul, map_sub, anchoredEvaluationCLM_apply,
      rawResidueAtom_sequence, show ∀ i : ℕ, M + i + 1 - 2 + 2 = M + i + 1 by omega,
      show ∀ i : ℕ, M + i - 2 + 2 = M + i by omega]
  have hv (n : ℕ) : |hilbertSequence v n| ≤ residueConductorVariation M n / (M : ℝ) := by
    rw [hvc, abs_mul, abs_of_nonneg (inv_nonneg.mpr hM'.le)]
    have hcs (i : ℕ) : |c i| = 1 := by dsimp [c]; split_ifs <;> norm_num
    have hs := Finset.abs_sum_le_sum_abs
      (fun i => c i * (residue (M + i + 1) n - residue (M + i) n)) (Finset.range M)
    simp only [abs_mul, hcs, one_mul] at hs
    rw [div_eq_mul_inv, mul_comm (residueConductorVariation M n)]
    exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hM'.le)
  have hv0 (n : ℕ) (hn : n < M - 1) : v n = 0 := by
    have he := hv (n + 1)
    rw [residueConductorVariation_eq_zero_of_lt (by omega), zero_div] at he
    have hz := abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
    have hs := hilbertSequence_weighted_square v n
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hs
    simpa only [pow_two, mul_eq_zero, or_self] using hs.symm
  have hh := hilbertTailShift_inner_sq_le h v (M - 1) hv0
  rw [real_inner_comm, hi] at hh
  exact hh.trans (by
    rw [mul_comm (13 : ℝ)]
    exact mul_le_mul_of_nonneg_left (norm_sq_le_of_residueConductorVariation (by omega) hv)
      (sq_nonneg _))

theorem residuePairing_dyadic_variation_tendsto (h : ThresholdHilbert) :
    Tendsto (fun M : ℕ => (∑ i ∈ Finset.range M,
      |residuePairing h (M + i + 1) - residuePairing h (M + i)|) / (M : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun M : ℕ => M - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (n + 1)] with M hM
    omega
  have ht : Tendsto (fun M : ℕ => 13 * ‖hilbertTailShift h (M - 1)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((hilbertTailShift_energy_tendsto_zero h).comp hi).const_mul 13
  have hs : Tendsto (fun M => pairingVariation h M ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ ht
    filter_upwards [eventually_ge_atTop 2] with M hM
    exact pairingVariation_sq_le_tail h hM
  have hpos (M : ℕ) : 0 ≤ pairingVariation h M := by
    unfold pairingVariation
    positivity
  have hs' : Tendsto (fun M => Real.sqrt (pairingVariation h M ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hs.sqrt
  exact hs'.congr (fun M => Real.sqrt_sq (hpos M))

end RiemannResearch.RH.Pareto
