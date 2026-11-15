import RiemannResearch.Analysis.KloostermanCompletion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.FiniteHarmonicBounds

/-!
# Harmonic Fourier bounds for incomplete Kloosterman sums

Source for the application: Baluyot, *On the Zeros of Riemann's
Zeta-function* (2017), Lemma 3.1.5 and §3.3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The unit-circle chord estimate and Fourier-mass bound hold for every
positive modulus and interval length. The zero mode is retained exactly.
The final bound takes an explicit estimate for the nonzero complete sums;
it does not prove the Weil bound for those sums.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.Analysis.Kloosterman

/-- Unit-circle chord identity. -/
theorem norm_one_sub_exp_double (x : ℝ) :
    ‖(1 : ℂ) - Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)‖ =
      2 * |Real.sin x| := by
  have hsq :
      ‖(1 : ℂ) - Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
        (2 * Real.sin x) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]
    have he : 2 * x = x + x := by ring
    rw [he, Real.sin_add, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hnorm : 0 ≤ ‖(1 : ℂ) - Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)‖ :=
    norm_nonneg _
  have habs : 0 ≤ |Real.sin x| := abs_nonneg _
  nlinarith [sq_abs (Real.sin x)]

/-- The unit-circle chord is bounded below by the distance to the nearest integer. -/
theorem norm_chord_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    4 * min t (1 - t) ≤ ‖(1 : ℂ) -
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ := by
  rw [show (2 * Real.pi * t : ℝ) = 2 * (Real.pi * t) by ring,
    norm_one_sub_exp_double]
  by_cases hhalf : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    have hsin : 2 * t ≤ Real.sin (Real.pi * t) := by
      have ha : 0 ≤ 2 * t := by linarith
      have hb : 2 * t ≤ 1 := by linarith
      have hs := Real.le_sin_mul ha hb
      have he : Real.pi / 2 * (2 * t) = Real.pi * t := by ring
      rwa [he] at hs
    linarith [le_abs_self (Real.sin (Real.pi * t))]
  · rw [min_eq_right (by linarith)]
    have hsin : 2 * (1 - t) ≤ Real.sin (Real.pi * (1 - t)) := by
      have ha : 0 ≤ 2 * (1 - t) := by linarith
      have hb : 2 * (1 - t) ≤ 1 := by linarith
      have hs := Real.le_sin_mul ha hb
      have he : Real.pi / 2 * (2 * (1 - t)) = Real.pi * (1 - t) := by ring
      rwa [he] at hs
    have he : Real.pi * (1 - t) = Real.pi - Real.pi * t := by ring
    rw [he, Real.sin_pi_sub] at hsin
    linarith [le_abs_self (Real.sin (Real.pi * t))]


theorem norm_chord_negative_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    4 * min t (1 - t) ≤ ‖(1 : ℂ) -
      Complex.exp (((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I)‖ := by
  have he :
      ‖(1 : ℂ) - Complex.exp (((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I)‖ =
      ‖(1 : ℂ) - Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ := by
    rw [show -(2 * Real.pi * t) = 2 * (-(Real.pi * t)) by ring,
      show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
      norm_one_sub_exp_double, norm_one_sub_exp_double]
    simp only [Real.sin_neg, abs_neg]
  rw [he]
  exact norm_chord_lower h0 h1

theorem norm_stdAddChar_sub_one_lower {q : ℕ} [NeZero q] (k : ZMod q) :
    4 * min ((k.val : ℝ) / q) (1 - (k.val : ℝ) / q) ≤
      ‖1 - ZMod.stdAddChar (-k)‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hk : (k.val : ℝ) ≤ q := by exact_mod_cast (ZMod.val_lt k).le
  have h0 : 0 ≤ (k.val : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hq.le
  have h1 : (k.val : ℝ) / q ≤ 1 := (div_le_one hq).mpr hk
  have hchar : ZMod.stdAddChar (-k) =
      Complex.exp (((-(2 * Real.pi * ((k.val : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
    have he : (-k : ZMod q) = (-(k.val : ℤ) : ℤ) := by simp
    rw [he, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hchar]
  exact norm_chord_negative_lower h0 h1


variable {q : ℕ} [NeZero q]

theorem frequency_weight_bound (b k : ZMod q) (L : ℕ) (hk : k ≠ 0) :
    ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖ ≤
      (q : ℝ) / (2 * min (k.val : ℝ) ((q : ℝ) - k.val)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hknat : 0 < k.val := Nat.pos_of_ne_zero (by
    intro hz
    apply hk
    simpa [hz] using (ZMod.natCast_zmod_val k).symm)
  have hka : (0 : ℝ) < k.val := by exact_mod_cast hknat
  have hkb : (k.val : ℝ) < q := by exact_mod_cast ZMod.val_lt k
  let d := min (k.val : ℝ) ((q : ℝ) - k.val)
  have hd : 0 < d := lt_min hka (by linarith)
  have hden := norm_stdAddChar_sub_one_lower k
  have he : min ((k.val : ℝ) / q) (1 - (k.val : ℝ) / q) = d / q := by
    dsimp [d]
    have hsub : 1 - (k.val : ℝ) / q = ((q : ℝ) - k.val) / q := by
      field_simp
    rw [hsub]
    by_cases hcase : (k.val : ℝ) ≤ (q : ℝ) - k.val
    · rw [min_eq_left hcase, min_eq_left (div_le_div_of_nonneg_right hcase hq.le)]
    · have hcase' := le_of_not_ge hcase
      rw [min_eq_right hcase', min_eq_right (div_le_div_of_nonneg_right hcase' hq.le)]
  rw [he] at hden
  have hdenpos : 0 < ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) (div_pos hd hq)) hden
  have hbound := RiemannResearch.Analysis.Kloosterman.norm_dft_intervalWeight_le b k L hk
  apply hbound.trans
  apply (div_le_div_iff₀ hdenpos (mul_pos (by norm_num) hd)).mpr
  have hh : 4 * d ≤ q * ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
    have hh : (4 * d) / q ≤ ‖(1 : ℂ) - ZMod.stdAddChar (-k)‖ := by
      (convert hden using 1; ring)
    nlinarith only [(div_le_iff₀ hq).mp hh]
  nlinarith


/-- The zero-frequency coefficient counts every occurrence in the interval. -/
theorem dft_intervalWeight_zero (b : ZMod q) (L : ℕ) :
    ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) 0 = L := by
  simp [RiemannResearch.Analysis.Kloosterman.dft_intervalWeight]

/-- The reciprocals of the nonzero residue representatives form H_{q-1}. -/
theorem sum_residue_reciprocal :
    (∑ k : ZMod q, (k.val : ℝ)⁻¹) = (harmonic (q - 1) : ℝ) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change (∑ k : Fin (n + 1), ((k.val : ℕ) : ℝ)⁻¹) =
      (harmonic (n + 1 - 1) : ℝ)
    have he := Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℝ)⁻¹)) (n + 1)
    rw [he, Finset.sum_range_succ']
    simp only [Nat.cast_zero, inv_zero, add_zero, Nat.add_sub_cancel]
    rw [RiemannResearch.Analysis.harmonic_cast_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [one_div, Nat.cast_add]


theorem sum_residue_neg_reciprocal :
    (∑ k : ZMod q, ((-k).val : ℝ)⁻¹) = (harmonic (q - 1) : ℝ) := by
  let en : ZMod q ≃ ZMod q := ⟨Neg.neg, Neg.neg, neg_neg, neg_neg⟩
  calc
    _ = ∑ k : ZMod q, (k.val : ℝ)⁻¹ :=
      en.sum_comp (fun k => (k.val : ℝ)⁻¹)
    _ = _ := sum_residue_reciprocal

theorem frequency_weight_reciprocal_bound (b k : ZMod q) (L : ℕ) (hk : k ≠ 0) :
    ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖ ≤
      (q : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hkpos : 0 < k.val := (ZMod.val_pos).mpr hk
  have hqk : k.val ≤ q := (ZMod.val_lt k).le
  have hneg : (((-k).val : ℕ) : ℝ) = (q : ℝ) - k.val := by
    rw [ZMod.neg_val, if_neg hk, Nat.cast_sub hqk]
  have ha : 0 ≤ (k.val : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb : 0 ≤ (((-k).val : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmin :
      (min (k.val : ℝ) ((q : ℝ) - k.val))⁻¹ ≤
        (k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹ := by
    by_cases h : (k.val : ℝ) ≤ (q : ℝ) - k.val
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right (le_of_not_ge h)]
      rw [← hneg]
      linarith
  calc
    _ ≤ (q : ℝ) / (2 * min (k.val : ℝ) ((q : ℝ) - k.val)) :=
      frequency_weight_bound b k L hk
    _ = (q : ℝ) / 2 * (min (k.val : ℝ) ((q : ℝ) - k.val))⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by positivity)

theorem fourier_mass_le_harmonic (b : ZMod q) (L : ℕ) :
    (∑ k : ZMod q,
      ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖) ≤
      (L : ℝ) + (q : ℝ) * (harmonic (q - 1) : ℝ) := by
  classical
  have hp (k : ZMod q) :
      ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖ ≤
        (if k = 0 then (L : ℝ) else 0) +
          (q : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
    by_cases hk : k = 0
    · subst k
      simp [dft_intervalWeight_zero]
    · simpa [hk] using frequency_weight_reciprocal_bound b k L hk
  calc
    _ ≤ ∑ k : ZMod q, ((if k = 0 then (L : ℝ) else 0) +
          (q : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹)) :=
      Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        sum_residue_reciprocal, sum_residue_neg_reciprocal]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring


/-- Exact completion after removing the zero Fourier mode. -/
theorem interval_inverseSum_centered_eq_complete (b m : ZMod q) (L : ℕ) :
    (∑ j ∈ Finset.range L, RiemannResearch.Analysis.Kloosterman.inversePhase
      m (b + (j : ZMod q))) -
        (L : ℂ) / (q : ℂ) * RiemannResearch.Analysis.Kloosterman.completeSum 0 m =
      (q : ℂ)⁻¹ * ∑ k ∈ Finset.univ.erase 0,
        ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k *
          RiemannResearch.Analysis.Kloosterman.completeSum k m := by
  classical
  rw [RiemannResearch.Analysis.Kloosterman.interval_inverseSum_eq_complete]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
    (fun k => ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k *
      RiemannResearch.Analysis.Kloosterman.completeSum k m)
    (Finset.mem_univ 0)
  rw [← hs, dft_intervalWeight_zero]
  ring

/-- The nonzero Fourier modes have at most q times H_{q-1} total mass. -/
theorem nonzero_fourier_mass_le_harmonic (b : ZMod q) (L : ℕ) :
    (∑ k ∈ Finset.univ.erase 0,
      ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖) ≤
        (q : ℝ) * (harmonic (q - 1) : ℝ) := by
  classical
  have hs := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
    (fun k => ‖ZMod.dft
      (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖)
    (Finset.mem_univ 0)
  have hz : ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) 0‖ =
      (L : ℝ) := by rw [dft_intervalWeight_zero, Complex.norm_natCast]
  rw [hz] at hs
  linarith [fourier_mass_le_harmonic b L]

/-- An all-frequency complete-sum bound is needed only for nonzero modes.
The zero-frequency Ramanujan term is retained exactly for every interval length. -/
theorem norm_centered_interval_inverseSum_le_of_complete
    (b m : ZMod q) (L : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k : ZMod q, k ≠ 0 →
      ‖RiemannResearch.Analysis.Kloosterman.completeSum k m‖ ≤ B) :
    ‖(∑ j ∈ Finset.range L, RiemannResearch.Analysis.Kloosterman.inversePhase
        m (b + (j : ZMod q))) -
      (L : ℂ) / (q : ℂ) * RiemannResearch.Analysis.Kloosterman.completeSum 0 m‖ ≤
        B * (harmonic (q - 1) : ℝ) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [interval_inverseSum_centered_eq_complete, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase 0,
        ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k *
          RiemannResearch.Analysis.Kloosterman.completeSum k m‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq.le)
    _ ≤ (q : ℝ)⁻¹ *
        ((∑ k ∈ Finset.univ.erase 0,
          ‖ZMod.dft (RiemannResearch.Analysis.Kloosterman.intervalWeight b L) k‖) * B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB k (Finset.ne_of_mem_erase hk)) (norm_nonneg _)
    _ ≤ (q : ℝ)⁻¹ * (((q : ℝ) * (harmonic (q - 1) : ℝ)) * B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (nonzero_fourier_mass_le_harmonic b L) hB0)
        (inv_nonneg.mpr hq.le)
    _ = _ := by field_simp

/-- The explicit logarithmic consequence of the harmonic completion bound. -/
theorem norm_centered_interval_inverseSum_le_log_of_complete
    (b m : ZMod q) (L : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k : ZMod q, k ≠ 0 →
      ‖RiemannResearch.Analysis.Kloosterman.completeSum k m‖ ≤ B) :
    ‖(∑ j ∈ Finset.range L, RiemannResearch.Analysis.Kloosterman.inversePhase
        m (b + (j : ZMod q))) -
      (L : ℂ) / (q : ℂ) * RiemannResearch.Analysis.Kloosterman.completeSum 0 m‖ ≤
        B * (1 + Real.log q) := by
  have hmono := (RiemannResearch.Analysis.harmonic_interval_bounds
    (q - 1) q (Nat.sub_le q 1)).1
  have hlog := harmonic_le_one_add_log q
  exact (norm_centered_interval_inverseSum_le_of_complete b m L hB0 hB).trans
    (mul_le_mul_of_nonneg_left (by linarith) hB0)

end RiemannResearch.Analysis.Kloosterman
