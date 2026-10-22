import RiemannResearch.RH.ArithmeticFloorLogConvergence

noncomputable section
open Filter Set RiemannResearch.Analysis
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Complete critical logarithmic criterion with conductor-uniform signed
prefix bounds. The original density-tail estimate is automatically made
uniform by truncation. All arithmetic hypotheses are explicit. -/
theorem arithmeticFloorHilbertPartial_envelope_of_uniform_critical_log_bounds
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε b : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hb : 1 < b)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ M t : ℕ, 0 < t →
      |positiveArithmeticPrefix (arithmeticCutoffWeight w M) t| ≤
        B * (t : ℝ) ^ ε / (6 + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (6 + Real.log (t : ℝ)) ^ b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
        K * Real.sqrt (N : ℝ) * (6 + Real.log (N : ℝ)) ^ (-(b / 2)) := by
  have hp : 0 < 1 - ε := by linarith
  have hlog (t : ℕ) (ht : 0 < t) : 0 < 6 + Real.log (t : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Real.log_nonneg ht1]
  let T := fun t : ℕ => D / ((t : ℝ) ^ (1 - ε) * (6 + Real.log (t : ℝ)) ^ b)
  have htmono : AntitoneOn T (Set.Ici 1) := by
    intro i hi j hj hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by change 1 ≤ i at hi; omega)
    have hiN : 0 < i := by exact_mod_cast hi0
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hl := hlog i hiN
    apply div_le_div_of_nonneg_left hD (by positivity)
    apply mul_le_mul
    · exact Real.rpow_le_rpow hi0.le hijR hp.le
    · exact Real.rpow_le_rpow hl.le (by linarith [Real.log_le_log hi0 hijR]) (by linarith)
    · positivity
    · positivity
  have hE (M N y : ℕ) (hy : 0 < y) (hyN : y ≤ N) :
      |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
        (W / (1 - ε)) * (y : ℝ) ^ (1 - ε) +
        (B * (1 + 1 / (1 - ε)) + 2 * D) * (N : ℝ) /
          ((y : ℝ) ^ (1 - ε) * (6 + Real.log (y : ℝ)) ^ b) := by
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
    have ht := arithmeticCutoff_density_tail_profile_bound w C T htmono
      (fun t ht => by dsimp [T]; positivity) hT M y hy
    have ht' : |positiveArithmeticPrefix (fun k => w k / (k : ℝ)) M -
        ∑ k ∈ Finset.range (y + 1), arithmeticCutoffWeight w M k / (k : ℝ)| ≤
        (2 * D) / ((y : ℝ) ^ (1 - ε) * (6 + Real.log (y : ℝ)) ^ b) := by
      simpa only [T, mul_div_assoc] using ht
    have hwcut (t : ℕ) (ht : 0 < t) :
        |arithmeticCutoffWeight w M t| ≤ W * (t : ℝ) ^ (-ε) := by
      unfold arithmeticCutoffWeight
      split_ifs
      · exact hw t ht
      · simp only [abs_zero]; positivity
    rw [arithmeticFloorHilbertPartial_sequence_cutoff]
    apply arithmeticFloorPrefix_centered_hyperbola_critical_profile_bound
      (arithmeticCutoffWeight w M) (arithmeticCutoffWeight_zero w hw0 M) _
      hy hyN hW hB (Real.rpow_pos_of_pos (hlog y hy) b) hε.le (by linarith) hwcut _ ht'
    intro t hyt
    have ht0 : 0 < t := hy.trans_le hyt
    exact (hP M t ht0).trans (div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (hlog y hy) b)
      (Real.rpow_le_rpow (hlog y hy).le
        (by linarith [Real.log_le_log hy0 (show (y : ℝ) ≤ t by exact_mod_cast hyt)]) (by linarith)))
  obtain ⟨K, hK, hbound⟩ := eventual_sqrt_log_envelope_of_hyperbola_bound
    (fun M N => hilbertSequence (arithmeticFloorHilbertPartial w M) N)
    (1 - ε) b (W / (1 - ε)) (B * (1 + 1 / (1 - ε)) + 2 * D)
    (by linarith) (by linarith) hb (div_nonneg hW hp.le) (by positivity) hE

  exact ⟨K, hK, hbound⟩

/-- Critical prefix and density exponents suffice with any common
logarithmic saving greater than one. The shift is a free deterministic
parameter ensuring prefix monotonicity down to index one. -/
theorem arithmeticFloorHilbertPartial_envelope_of_critical_log_bounds
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε b c : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hb : 1 < b)
    (hc : 6 ≤ c) (hbc : b ≤ ε * c)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * (t : ℝ) ^ ε / (c + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (c + Real.log (t : ℝ)) ^ b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
        K * Real.sqrt (N : ℝ) * (6 + Real.log (N : ℝ)) ^ (-(b / 2)) := by
  have hc0 : 0 < c := by linarith
  have hpmono : Monotone (fun t : ℕ => B * powerLogNatProfile ε b c t) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (powerLogNatProfile_monotone hc0 hε.le hbc hij) hB
  have hpall (t : ℕ) : |positiveArithmeticPrefix w t| ≤ B * powerLogNatProfile ε b c t := by
    by_cases ht : t = 0
    · simp [ht, powerLogNatProfile, positiveArithmeticPrefix_zero]
    · simpa only [powerLogNatProfile, if_neg ht, ← mul_div_assoc] using hP t (Nat.pos_of_ne_zero ht)
  have hlog (t : ℕ) (ht : 0 < t) : 0 < 6 + Real.log (t : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Real.log_nonneg ht1]
  apply arithmeticFloorHilbertPartial_envelope_of_uniform_critical_log_bounds
    w hw0 C hdensity hW hB hD hε hεhalf hb hw
  · intro M t ht
    have hcut := arithmeticCutoff_prefix_profile_bound w _ hpmono hpall M t
    simp only [powerLogNatProfile, if_neg (Nat.ne_of_gt ht), ← mul_div_assoc] at hcut
    exact hcut.trans (div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (hlog t ht) b)
      (Real.rpow_le_rpow (hlog t ht).le (by linarith) (by linarith)))
  · intro t ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    apply (hT t ht).trans
    apply div_le_div_of_nonneg_left hD (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hlog t ht).le (by linarith) (by linarith))
      (Real.rpow_nonneg ht0.le _)


end RiemannResearch.RH.Pareto
