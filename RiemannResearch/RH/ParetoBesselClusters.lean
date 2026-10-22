import RiemannResearch.RH.ParetoNoiseResearchTargets
import RiemannResearch.RH.ParetoRepairCovariance
import RiemannResearch.RH.ParetoResidueMoments

/-!
# Shared old scales force large normalized covariance

The exact common head interval is retained as a contribution to the complete
Pareto squared norm. A normalized Bessel estimate therefore bounds the number
of distinct prime repairs sharing an old scale by a constant times its square
root. No prime-counting estimate or smooth-gap theorem is assumed here.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem cluster_denominator_cancel (C A E : ℝ) (hE : E ≠ 0) :
    C * (A * (6 * Real.log 2 / E)) * E^2 = 6 * C * Real.log 2 * A * E := by
  field_simp [hE]
  <;> ring

theorem arithmeticRepair_binary_between_scales (p E k : ℕ)
    (hp : 0 < p) (hpk : p ≤ k) (hkE : k < E) (hEp : E ≤ 2 * p) :
    arithmeticRepair 2 p E k = -1 := by
  have hkp : k / p = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hpk
    · simpa [Nat.mul_comm] using lt_of_lt_of_le hkE hEp
  rw [arithmeticRepair_eq_floor 2 p E k hp]
  simp [Nat.div_eq_of_lt hkE, hkp, residue]

private theorem repair_sum_bounded_cluster (s : Finset ℕ) (E : ℕ) :
    ∀ k, |∑ p ∈ s, arithmeticRepair 2 p E k| ≤
      ∑ p ∈ s, |(p : ℝ)⁻¹| * ((E : ℝ) * 2 + (p : ℝ) * 2) := by
  intro k
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  rw [arithmeticRepair_eq_scaleRepair]
  exact scaleRepair_abs_le (fun k => residue_abs_le 2 k (by norm_num)) p E k

/-- An exact common head contribution to the full squared norm. -/
theorem commonScale_head_energy_lower (s : Finset ℕ) (L E : ℕ)
    (hL : 0 < L) (hLE : L ≤ E)
    (hs : ∀ p ∈ s, 0 < p ∧ p ≤ L ∧ E ≤ 2 * p) :
    (s.card : ℝ)^2 * (1 / (L : ℝ) - 1 / (E : ℝ)) ≤
      paretoInner (fun k => ∑ p ∈ s, arithmeticRepair 2 p E k)
        (fun k => ∑ p ∈ s, arithmeticRepair 2 p E k) := by
  let F : ℕ → ℝ := fun k => ∑ p ∈ s, arithmeticRepair 2 p E k
  have hsum := weighted_summable_of_bounded
    (bounded_product (repair_sum_bounded_cluster s E) (repair_sum_bounded_cluster s E))
  have hval : ∀ k ∈ Finset.Ico L E, F k = -(s.card : ℝ) := by
    intro k hk
    dsimp [F]
    have he : (∑ p ∈ s, arithmeticRepair 2 p E k) = ∑ _p ∈ s, (-1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact arithmeticRepair_binary_between_scales p E k (hs p hp).1
        (le_trans (hs p hp).2.1 (Finset.mem_Ico.mp hk).1)
        (Finset.mem_Ico.mp hk).2 (hs p hp).2.2
    rw [he]
    simp
  have hfinite : (∑ k ∈ Finset.Ico L E, positiveWeight k * (F k * F k)) =
      (s.card : ℝ)^2 * (1 / (L : ℝ) - 1 / (E : ℝ)) := by
    calc
      _ = ∑ k ∈ Finset.Ico L E, (s.card : ℝ)^2 * positiveWeight k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hval k hk]
        ring
      _ = _ := by rw [← Finset.mul_sum, positiveWeight_interval L E hL hLE]
  rw [← hfinite]
  exact hsum.sum_le_tsum _ (fun k _ =>
    mul_nonneg (positiveWeight_nonneg k) (mul_self_nonneg _))

theorem commonScale_head_energy_lower_crude (s : Finset ℕ) (L E : ℕ)
    (hL : 0 < L) (hLE : L ≤ E)
    (hs : ∀ p ∈ s, 0 < p ∧ p ≤ L ∧ E ≤ 2 * p) :
    (s.card : ℝ)^2 * ((E : ℝ) - L) / (E : ℝ)^2 ≤
      paretoInner (fun k => ∑ p ∈ s, arithmeticRepair 2 p E k)
        (fun k => ∑ p ∈ s, arithmeticRepair 2 p E k) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hLER : (L : ℝ) ≤ E := by exact_mod_cast hLE
  have hER : (0 : ℝ) < E := lt_of_lt_of_le hLR hLER
  have hmass : ((E : ℝ) - L) / (E : ℝ)^2 ≤ 1 / (L : ℝ) - 1 / (E : ℝ) := by
    have h := div_le_div_of_nonneg_left (sub_nonneg.mpr hLER)
      (mul_pos hLR hER) (mul_le_mul_of_nonneg_right hLER hER.le)
    have he : ((E : ℝ) - L) / ((L : ℝ) * E) =
        1 / (L : ℝ) - 1 / (E : ℝ) := by
      field_simp [ne_of_gt hLR, ne_of_gt hER]
      <;> ring
    simpa only [← sq, he] using h
  have h := mul_le_mul_of_nonneg_left hmass (sq_nonneg (s.card : ℝ))
  have h' : (s.card : ℝ)^2 * ((E : ℝ) - L) / (E : ℝ)^2 ≤
      (s.card : ℝ)^2 * (1 / (L : ℝ) - 1 / (E : ℝ)) := by
    simpa only [mul_div_assoc] using h
  exact h'.trans (commonScale_head_energy_lower s L E hL hLE hs)

/-- Exact covariance first gives the diagonal bound used by the cluster argument. -/
theorem arithmeticRepair_binary_diagonal_le (p E : ℕ)
    (hp : 0 < p) (hpE : p < E) (hEp : E ≤ 2 * p) :
    paretoInner (arithmeticRepair 2 p E) (arithmeticRepair 2 p E) ≤
      6 * Real.log 2 / (E : ℝ) := by
  have hE : 0 < E := lt_trans hp hpE
  have h := paretoInner_scaleRepair_self_le
    (fun k => residue_abs_le 2 k (by norm_num)) (by simp [residue])
    (fun k => Nat.cast_nonneg _) p E hp hE
  rw [← arithmeticRepair_eq_scaleRepair, paretoInner_residue_two] at h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hpER : (p : ℝ) < E := by exact_mod_cast hpE
  have hEpR : (E : ℝ) ≤ 2 * p := by exact_mod_cast hEp
  have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hcoef : ((E : ℝ) + p) / (p : ℝ)^2 ≤ 6 / (E : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hpR) hER).mpr
    have hfac := mul_nonneg (sub_nonneg.mpr hEpR)
      (show (0 : ℝ) ≤ 3 * p + E by positivity)
    nlinarith
  exact h.trans (by simpa only [div_mul_eq_mul_div, mul_comm] using
    mul_le_mul_of_nonneg_right hcoef hlog)

/-- A concrete finite cluster consequence of the proposed all-coefficient bound.
The constant is uniform in the old scale and finite prime set. -/
theorem repairBessel_commonScale_card_sq_le
    (scale : ℕ → ℕ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      (∀ p ∈ s, p.Prime ∧ 7 ≤ p) →
      paretoInner (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (scale p) k)
        (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (scale p) k) ≤
      C * ∑ p ∈ s, (a p)^2 *
        paretoInner (arithmeticRepair 2 p (scale p)) (arithmeticRepair 2 p (scale p)))
    (Q : Finset ℕ) (E : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 7 ≤ p ∧ scale p = E ∧ p < E ∧ E ≤ 2 * p) :
    (Q.card : ℝ)^2 ≤ (1 + 108 * C * Real.log 2) * (E : ℝ) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmE : Q.card ≤ E := by
    calc
      _ ≤ (Finset.range E).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (hQ p hp).2.2.2.1)
      _ = E := Finset.card_range E
  by_cases hm : Q.card < 2
  · have hmR : (Q.card : ℝ) ≤ 1 := by exact_mod_cast (show Q.card ≤ 1 by omega)
    have hmER : (Q.card : ℝ) ≤ E := by exact_mod_cast hmE
    have hm0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
    have hCE : 0 ≤ 108 * C * Real.log 2 * (E : ℝ) := by positivity
    nlinarith
  have hm2 : 2 ≤ Q.card := by omega
  let l : ℕ := Q.card / 2
  let L : ℕ := E - l
  let s : Finset ℕ := Q.filter (fun p => p ≤ L)
  have hl : 0 < l := by dsimp [l]; omega
  have hlE : l ≤ E := by dsimp [l]; omega
  have hL : 0 < L := by dsimp [L, l]; omega
  have hLE : L ≤ E := Nat.sub_le _ _
  have hEL : E = L + l := by dsimp [L]; omega
  have hsdiff : (Q \ s).card ≤ l := by
    calc
      _ ≤ (Finset.Ico L E).card := Finset.card_le_card (by
        intro p hp
        have hpQ := (Finset.mem_sdiff.mp hp).1
        have hps := (Finset.mem_sdiff.mp hp).2
        have hpL : L < p := by
          by_contra h
          exact hps (Finset.mem_filter.mpr ⟨hpQ, by omega⟩)
        exact Finset.mem_Ico.mpr ⟨hpL.le, (hQ p hpQ).2.2.2.1⟩)
      _ = l := by rw [Nat.card_Ico]; omega
  have hpart : (Q \ s).card + s.card = Q.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hms : Q.card ≤ 2 * s.card := by dsimp [l] at hsdiff; omega
  have hml : Q.card ≤ 3 * l := by dsimp [l]; omega
  have hspos : 0 < s.card := by omega
  have hsQ : ∀ p ∈ s, p ∈ Q := fun p hp => (Finset.mem_filter.mp hp).1
  have hshead : ∀ p ∈ s, 0 < p ∧ p ≤ L ∧ E ≤ 2 * p := by
    intro p hp
    exact ⟨(hQ p (hsQ p hp)).1.pos, (Finset.mem_filter.mp hp).2,
      (hQ p (hsQ p hp)).2.2.2.2⟩
  have hlow := commonScale_head_energy_lower_crude s L E hL hLE hshead
  have hupper := hb s (fun _ => 1) (fun p hp =>
    ⟨(hQ p (hsQ p hp)).1, (hQ p (hsQ p hp)).2.1⟩)
  simp only [one_mul, one_pow] at hupper
  have heF : (fun k => ∑ p ∈ s, arithmeticRepair 2 p (scale p) k) =
      (fun k => ∑ p ∈ s, arithmeticRepair 2 p E k) := by
    funext k
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hQ p (hsQ p hp)).2.2.1]
  rw [heF] at hupper
  have hdiag : (∑ p ∈ s,
      paretoInner (arithmeticRepair 2 p (scale p)) (arithmeticRepair 2 p (scale p))) ≤
      (s.card : ℝ) * (6 * Real.log 2 / (E : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ s, 6 * Real.log 2 / (E : ℝ) := Finset.sum_le_sum (by
        intro p hp
        rw [(hQ p (hsQ p hp)).2.2.1]
        exact arithmeticRepair_binary_diagonal_le p E (hQ p (hsQ p hp)).1.pos
          (hQ p (hsQ p hp)).2.2.2.1 (hQ p (hsQ p hp)).2.2.2.2)
      _ = _ := by simp
  have hchain := hlow.trans (hupper.trans (mul_le_mul_of_nonneg_left hdiag hC.le))
  have hER : (0 : ℝ) < E := by exact_mod_cast (lt_of_lt_of_le hL hLE)
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast hspos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hELR : (E : ℝ) - L = l := by
    exact_mod_cast (show E - L = l by omega)
  rw [hELR] at hchain
  have hclear : (s.card : ℝ)^2 * l ≤ 6 * C * Real.log 2 * s.card * E := by
    have h := (div_le_iff₀ (sq_pos_of_pos hER)).mp hchain
    have he : C * ((s.card : ℝ) * (6 * Real.log 2 / (E : ℝ))) * (E : ℝ)^2 =
        6 * C * Real.log 2 * s.card * E := by
      exact cluster_denominator_cancel C (s.card : ℝ) (E : ℝ) (ne_of_gt hER)
    rw [he] at h
    exact h
  have hcancel : (s.card : ℝ) * l ≤ 6 * C * Real.log 2 * E := by
    apply (mul_le_mul_iff_of_pos_left hsR).mp
    nlinarith [hclear]
  have hmsR : (Q.card : ℝ) ≤ 2 * s.card := by exact_mod_cast hms
  have hmlR : (Q.card : ℝ) ≤ 3 * l := by exact_mod_cast hml
  have hmul := mul_le_mul hmsR hmlR (Nat.cast_nonneg Q.card)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsR.le)
  have hpos : 0 ≤ C * Real.log 2 * (E : ℝ) := by positivity
  nlinarith

end
end RiemannResearch.RH.Pareto
