import RiemannResearch.RH.ArithmeticFloorAllLogEnvelope
import RiemannResearch.RH.DampedMobiusAllLogProviders
import RiemannResearch.RH.DampedMobiusArbitraryLogNorm

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Every fixed logarithmic coordinate saving has an unconditional provider.
The arithmetic prefixes are truncated before the hyperbola argument is applied. -/
theorem dampedMobius_half_partial_all_log_envelope (k : ℕ) (hk : 1 < k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n| ≤
        K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-((k : ℝ) / 2)) := by
  obtain ⟨B, hB, hP⟩ := dampedMobius_half_prefix_all_log_bound k
  obtain ⟨D, hD, hT⟩ := dampedMobius_half_density_tail_all_log_bound k
  apply arithmeticFloorHilbertPartial_envelope_of_critical_log_bounds
    (dampedMobiusWeight (1 / 2)) (dampedMobiusWeight_zero _) _
    (dampedMobius_density_hasSum (by norm_num : (0 : ℝ) < 1 / 2))
    (W := 1) (B := B) (D := D) (ε := 1 / 2) (b := k) (c := logPowerShift k)
    (by norm_num) hB hD (by norm_num) le_rfl (by exact_mod_cast hk)
    (by unfold logPowerShift; have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (by unfold logPowerShift; have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith)
  · intro t ht
    rw [dampedMobiusWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t)))
      (Real.rpow_nonneg (Nat.cast_nonneg t) _)
  · intro t ht
    simpa only [Real.sqrt_eq_rpow] using hP t ht
  · intro t ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hL := shiftedLogPower_pos k ht1
    have h := hT t ht
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg ht0.le, Real.rpow_neg hL.le] at h
    norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

/-- The whole finite physical head inherits every fixed squared-log rate. -/
theorem dampedMobius_half_head_error_all_log_bound (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H M : ℕ, H ≤ M → 1 ≤ M →
      (∑ n ∈ Finset.range H, positiveWeight n *
        (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n -
          (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
            (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re)) ^ 2) ≤
        K * (6 + Real.log (M : ℝ)) ^ (-2 * (k : ℝ)) := by
  obtain ⟨D, hD, htail⟩ := dampedMobius_half_density_tail_all_log_bound k
  refine ⟨D ^ 2, sq_nonneg _, ?_⟩
  intro H M hHM hM
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hLp : 0 < 6 + Real.log (M : ℝ) := shiftedLog_pos (by exact_mod_cast hM)
  have htail' :
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        positiveArithmeticPrefix (fun d => dampedMobiusWeight (1 / 2) d / (d : ℝ)) M| ≤
        D * (M : ℝ) ^ (-1 / 2 : ℝ) * (6 + Real.log (M : ℝ)) ^ (-(k : ℝ)) := by
    apply (htail M hM).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_nonpos hLp
    · unfold logPowerShift
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · exact neg_nonpos.mpr (Nat.cast_nonneg k)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ D * (M : ℝ) ^ (-1 / 2 : ℝ) * (6 + Real.log (M : ℝ)) ^ (-(k : ℝ)))).mpr htail'
  rw [sq_abs] at hsq
  simp only [positiveArithmeticPrefix] at hsq
  simp only [dampedMobiusPrefix]
  rw [arithmeticFloorPartial_head_error _ _ H M hHM]
  calc
    _ ≤ (D * (M : ℝ) ^ (-1 / 2 : ℝ) *
        (6 + Real.log (M : ℝ)) ^ (-(k : ℝ))) ^ 2 * (M : ℝ) :=
      mul_le_mul hsq ((paretoHead_linear_mass_le H).trans (by exact_mod_cast hHM))
        (Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
        (sq_nonneg _)
    _ = _ := by
      have hm : ((M : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (M : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
        norm_num [Real.rpow_neg]
      have hl : ((6 + Real.log (M : ℝ)) ^ (-(k : ℝ))) ^ 2 =
          (6 + Real.log (M : ℝ)) ^ (-2 * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
        congr 1
        ring
      rw [mul_pow, mul_pow, hm, hl]
      field_simp

theorem dampedMobius_half_cutoffs_eventual_all_nat_log_rate (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * (6 + Real.log (M : ℝ)) ^ (-(r : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := dampedMobius_half_partial_all_log_envelope (2 * r + 2) (by omega)
  obtain ⟨D, hD, hd⟩ := dampedMobius_half_head_error_all_log_bound r
  have he : ((2 * r + 2 : ℕ) : ℝ) / 2 = (r : ℝ) + 1 := by push_cast; ring
  simp only [he] at hb
  apply dampedMobius_half_cutoffs_eventual_log_rate_of_coordinate_and_head
    (r := (r : ℝ)) (Nat.cast_nonneg r) hK hD hb
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  simpa only [hilbertSequence_sub, Pi.sub_apply,
    (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using hd M M le_rfl hM

end RiemannResearch.RH.Pareto

namespace RiemannResearch.Analysis

private theorem shifted_log_succ_rpow_bound {r : ℝ} (hr : 0 ≤ r)
    {M : ℕ} (hM : 1 ≤ M) :
    (6 + Real.log (M : ℝ)) ^ (-r) ≤
      (2 : ℝ) ^ r * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-r) := by
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hm1
  have hlog1 : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 1 by omega))
  have hL0 : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hL1 : 0 < 6 + Real.log ((M + 1 : ℕ) : ℝ) := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log (M : ℝ) := by
    calc
      _ ≤ Real.log (2 * (M : ℝ)) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      _ = Real.log 2 + Real.log (M : ℝ) :=
        Real.log_mul (by norm_num) hm0.ne'
      _ ≤ _ := by linarith
  have hLle : 6 + Real.log ((M + 1 : ℕ) : ℝ) ≤
      2 * (6 + Real.log (M : ℝ)) := by linarith
  have hpow : (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ r ≤
      (2 : ℝ) ^ r * (6 + Real.log (M : ℝ)) ^ r := by
    calc
      _ ≤ (2 * (6 + Real.log (M : ℝ))) ^ r :=
        Real.rpow_le_rpow hL1.le hLle hr
      _ = _ := Real.mul_rpow (by norm_num) hL0.le
  rw [Real.rpow_neg hL0.le, Real.rpow_neg hL1.le]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)

/-- Finite initial cutoffs can be absorbed without losing any fixed log exponent. -/
theorem eventual_shifted_log_bound_global_succ
    (E : ℕ → ℝ) (hE : ∀ M, 0 ≤ E M) {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ᶠ M : ℕ in atTop, E M ≤ C * (6 + Real.log (M : ℝ)) ^ (-r)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℕ,
      E M ≤ D * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-r) := by
  let R : ℕ → ℝ := fun M => (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-r)
  let A : ℝ := C * (2 : ℝ) ^ r
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR (M : ℕ) : 0 < R M := by
    apply Real.rpow_pos_of_pos
    have hlog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 1 by omega) :
      (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))
    linarith
  have hevent : ∀ᶠ M : ℕ in atTop, E M ≤ A * R M := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with M hb hM
    calc
      _ ≤ C * (6 + Real.log (M : ℝ)) ^ (-r) := hb
      _ ≤ C * ((2 : ℝ) ^ r * R M) :=
        mul_le_mul_of_nonneg_left (shifted_log_succ_rpow_bound hr hM) hC
      _ = _ := by dsimp [A]; ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let S := ∑ k ∈ Finset.range N, E k / R k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => div_nonneg (hE k) (hR k).le)
  refine ⟨A + S, by positivity, ?_⟩
  intro M
  by_cases hMN : M < N
  · have hsingle : E M / R M ≤ S :=
      Finset.single_le_sum (fun k _ => div_nonneg (hE k) (hR k).le)
        (Finset.mem_range.mpr hMN)
    have hratio : E M / R M ≤ A + S := hsingle.trans (by linarith)
    exact (div_le_iff₀ (hR M)).mp hratio
  · exact (hN M (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + S) (hR M).le)

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Every fixed logarithmic endpoint rate, valid uniformly over all conductor cutoffs.
The rate constant depends on the requested exponent. -/
theorem dampedMobius_half_cutoffs_all_log_rate (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-a) := by
  obtain ⟨r, har⟩ := exists_nat_ge a
  obtain ⟨C, hC, hb⟩ := dampedMobius_half_cutoffs_eventual_all_nat_log_rate r
  obtain ⟨D, hD, hd⟩ := eventual_shifted_log_bound_global_succ
    (fun M => ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖)
    (fun _ => norm_nonneg _) (Nat.cast_nonneg r) hC hb
  refine ⟨D, hD, fun M => (hd M).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hD
  apply Real.rpow_le_rpow_of_exponent_le
  · have hlog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 1 by omega) :
      (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))
    linarith
  · linarith

end RiemannResearch.RH.Pareto
