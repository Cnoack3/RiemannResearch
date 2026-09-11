import RiemannResearch.RH.DyadicResidueFourierBridge

/-!
# Logarithmic conductor bounds for actual signed residue kernels

Source: user-provided FourierResidueBridgeVerification20260911(1).md,
September 11, 2026. The exact reset-multiple harmonic identity bounds the
physical head; signed modular Abel summation bounds the remaining tail.
Both terminal corrections are retained before taking absolute values.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.Analysis

/-- Exact harmonic reindexing of conductor reset multiples. -/
theorem sum_reset_harmonic_eq (a : ℕ) (ha : 0 < a) (K : ℕ) :
    (∑ j ∈ Finset.range K, if a ∣ j+1 then (a : ℝ) / ((j+1 : ℕ) : ℝ) else 0) =
      ∑ j ∈ Finset.range (K / a), 1 / ((j+1 : ℕ) : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hd : a ∣ K+1
      · rw [if_pos hd, Nat.succ_div_of_dvd hd, Finset.sum_range_succ]
        congr 1
        have hmul : (K / a + 1) * a = K+1 := by
          rw [← Nat.succ_div_of_dvd hd]
          exact Nat.div_mul_cancel hd
        have hmulR : (((K / a + 1 : ℕ) : ℝ) * (a : ℝ)) = ((K+1 : ℕ) : ℝ) := by
          exact_mod_cast hmul
        rw [← hmulR]
        have haR : (a : ℝ) ≠ 0 := by positivity
        have hkR : ((K / a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      · rw [if_neg hd, Nat.succ_div_of_not_dvd hd, add_zero]

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- The physical kernel head has only harmonic, rather than linear, conductor cost. -/
theorem norm_dyadicResidueFourierKernel_le_harmonic_head
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h‖ ≤
      (∑ j ∈ Finset.range K, 1 / ((j+1 : ℕ) : ℝ)) +
        ∑ j ∈ Finset.range (K/a), 1 / ((j+1 : ℕ) : ℝ) := by
  rw [← sum_reset_harmonic_eq a ha K, ← Finset.sum_add_distrib]
  unfold dyadicResidueFourierKernel
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul, norm_dyadicIntegerFourierPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_div]
  have hjR : (0 : ℝ) < j+1 := by positivity
  rw [abs_of_pos hjR]
  by_cases hd : a ∣ j+1
  · simp only [if_pos hd]
    have hnum : |1 - (a : ℝ)| ≤ 1 + (a : ℝ) := by
      calc
        _ ≤ |(1 : ℝ)| + |(a : ℝ)| := abs_sub _ _
        _ = _ := by simp
    have hh := div_le_div_of_nonneg_right hnum hjR.le
    simpa only [Nat.cast_add, Nat.cast_one, add_div] using hh
  · simp [if_neg hd]

/-- The actual finite Abel tail includes both endpoint contributions in its bound. -/
theorem norm_dyadicResidueFourierKernel_tail_le
    (a : ℕ) (ha : 0 < a) (N M : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a (N+M) h - dyadicResidueFourierKernel a N h‖ ≤
      ((a : ℝ) * (3 + |dyadicLogFrequency h|)) / ((N+1 : ℕ) : ℝ) := by
  let B : ℝ := (a : ℝ) * (1 + |dyadicLogFrequency h|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he (K : ℕ) :
      ‖((K % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (K+1)‖ ≤
        (a : ℝ) / ((K+1 : ℕ) : ℝ) := by
    rw [norm_mul, Complex.norm_natCast, norm_dyadicHarmonicFourierWeight,
      mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (Nat.mod_lt K ha).le
  have heNM :
      ‖(((N+M) % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (N+M+1)‖ ≤
        (a : ℝ) / ((N+1 : ℕ) : ℝ) := by
    apply (he (N+M)).trans
    gcongr
    omega
  have hs :
      ‖∑ j ∈ Finset.range M, (((N+j+1) % a : ℕ) : ℂ) *
        (dyadicHarmonicFourierWeight h (N+j+1) -
          dyadicHarmonicFourierWeight h (N+j+2))‖ ≤
      B / ((N+1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, ‖(((N+j+1) % a : ℕ) : ℂ) *
          (dyadicHarmonicFourierWeight h (N+j+1) -
            dyadicHarmonicFourierWeight h (N+j+2))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range M,
          B / (((N+j+1 : ℕ) : ℝ) * ((N+j+2 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [B, positiveWeight, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          mul_one_div, add_assoc, one_add_one_eq_two] using
          norm_dyadicResidue_abelTerm_le a ha h (N+j)
      _ = B * (1 / ((N+1 : ℕ) : ℝ) - 1 / ((N+M+1 : ℕ) : ℝ)) := by
        rw [← sum_reciprocal_adjacent_tail, Finset.mul_sum]
        simp only [mul_one_div]
      _ ≤ B / ((N+1 : ℕ) : ℝ) := by
        have hz : 0 ≤ B / ((N+M+1 : ℕ) : ℝ) := by positivity
        simp only [mul_sub, mul_one_div]
        linarith
  rw [dyadicResidueFourierKernel_abel_tail a ha]
  calc
    _ ≤ ‖(((N+M) % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (N+M+1)‖ +
        ‖((N % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (N+1)‖ +
        ‖∑ j ∈ Finset.range M, (((N+j+1) % a : ℕ) : ℂ) *
          (dyadicHarmonicFourierWeight h (N+j+1) -
            dyadicHarmonicFourierWeight h (N+j+2))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (a : ℝ) / ((N+1 : ℕ) : ℝ) +
        (a : ℝ) / ((N+1 : ℕ) : ℝ) + B / ((N+1 : ℕ) : ℝ) :=
      add_le_add (add_le_add heNM (he N)) hs
    _ = _ := by dsimp [B]; ring

/-- A conductor-aware physical head and signed Abel tail, uniform in the cutoff. -/
theorem norm_dyadicResidueFourierKernel_le_conductor_split
    (a : ℕ) (ha : 0 < a) (K N : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h‖ ≤
      2 * (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) +
        ((a : ℝ) * (3 + |dyadicLogFrequency h|)) / ((N+1 : ℕ) : ℝ) := by
  have hmono (k n : ℕ) (hkn : k ≤ n) :
      (∑ j ∈ Finset.range k, 1 / ((j+1 : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range n, 1 / ((j+1 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
      (fun j hj hjk => by positivity)
  have hhead (k : ℕ) : ‖dyadicResidueFourierKernel a k h‖ ≤
      2 * (∑ j ∈ Finset.range k, 1 / ((j+1 : ℕ) : ℝ)) := by
    have hh := norm_dyadicResidueFourierKernel_le_harmonic_head a ha k h
    have hm := hmono (k/a) k (Nat.div_le_self k a)
    linarith
  by_cases hKN : K ≤ N
  · have hm := hmono K N hKN
    have ht : 0 ≤ ((a : ℝ) * (3 + |dyadicLogFrequency h|)) /
        ((N+1 : ℕ) : ℝ) := by positivity
    linarith [hhead K]
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ K by omega)
    calc
      _ ≤ ‖dyadicResidueFourierKernel a N h‖ +
          ‖dyadicResidueFourierKernel a (N+M) h -
            dyadicResidueFourierKernel a N h‖ := by
        convert norm_add_le
          (dyadicResidueFourierKernel a N h)
          (dyadicResidueFourierKernel a (N+M) h - dyadicResidueFourierKernel a N h)
          using 1; congr 1; ring
      _ ≤ _ := add_le_add (hhead N) (norm_dyadicResidueFourierKernel_tail_le a ha N M h)

/-- Uniform logarithmic dependence on both the conductor and the Fourier frequency. -/
theorem norm_dyadicResidueFourierKernel_le_log_conductor
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h‖ ≤
      5 + 2 * Real.log a + 2 * Real.log (1 + |dyadicLogFrequency h|) := by
  let B : ℝ := (a : ℝ) * (1 + |dyadicLogFrequency h|)
  let N : ℕ := ⌊B⌋₊
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [abs_nonneg (dyadicLogFrequency h)]
  have hH : (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) ≤ 1 + Real.log B := by
    simpa only [N, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one, one_div] using
      harmonic_floor_le_one_add_log B hB
  have hBN : B ≤ ((N+1 : ℕ) : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one B).le
  have htail : ((a : ℝ) * (3 + |dyadicLogFrequency h|)) /
      ((N+1 : ℕ) : ℝ) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hz : 0 ≤ (a : ℝ) * |dyadicLogFrequency h| := by positivity
    dsimp [B] at hBN
    nlinarith
  have hlog : Real.log B = Real.log a + Real.log (1 + |dyadicLogFrequency h|) := by
    exact Real.log_mul (by positivity) (by positivity)
  have hs := norm_dyadicResidueFourierKernel_le_conductor_split a ha K N h
  rw [hlog] at hH
  linarith

end RiemannResearch.RH.Pareto


open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

/-- The limiting residue Fourier symbol has the same optimal-order conductor bound. -/
theorem norm_dyadicResidueFourierSymbol_le_log_conductor
    (a : ℕ) (ha : 0 < a) (h : ℤ) :
    ‖dyadicResidueFourierSymbol a h‖ ≤
      5 + 2 * Real.log a + 2 * Real.log (1 + |dyadicLogFrequency h|) := by
  exact le_of_tendsto (dyadicResidueFourierKernel_tendsto_symbol a ha h).norm
    (Filter.Eventually.of_forall (fun K =>
      norm_dyadicResidueFourierKernel_le_log_conductor a ha K h))

/-- The signed modular Abel tail yields an inverse-cutoff error for the actual symbol. -/
theorem norm_dyadicResidueFourierKernel_sub_symbol_le
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h - dyadicResidueFourierSymbol a h‖ ≤
      ((a : ℝ) * (3 + |dyadicLogFrequency h|)) / ((K+1 : ℕ) : ℝ) := by
  have hshift : Filter.Tendsto (fun M : ℕ => K+M) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun M : ℕ => show M ≤ K+M by omega) Filter.tendsto_id
  have ht := ((dyadicResidueFourierKernel_tendsto_symbol a ha h).comp hshift).sub_const
    (dyadicResidueFourierKernel a K h)
  have hb : ‖dyadicResidueFourierSymbol a h - dyadicResidueFourierKernel a K h‖ ≤
      ((a : ℝ) * (3 + |dyadicLogFrequency h|)) / ((K+1 : ℕ) : ℝ) :=
    le_of_tendsto ht.norm (Filter.Eventually.of_forall (fun M =>
      norm_dyadicResidueFourierKernel_tail_le a ha K M h))
  rw [norm_sub_rev]
  exact hb

end RiemannResearch.RH.Pareto
