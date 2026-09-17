import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.CesaroResidueMean
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Canonical Möbius exact heads with unconditional linear conditional energy

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 10.2. The ordinary mathematical proof was completed first in
`MobiusHeadProof.md`. All coefficients, heads, and energies below use the
actual project definitions. No useful uniform or subpolynomial energy estimate
is asserted. This source awaits coordinator verification.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro ArithmeticCumulative Probability.ConditionalIID
open ArithmeticCumulative.CesaroResidue

/-- The actual finite reciprocal Möbius sum; its support is positive. -/
def mobiusReciprocalSum (Y : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

/-- The manuscript's canonical legal witness. The d=1 residue is identically zero. -/
def canonicalMobiusHead (Y : ℕ) (n : ℕ) : ℝ :=
  -(∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
    ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y * residueFraction (Y + 1) n

private theorem mobius_real_abs_le_one (d : ℕ) :
    |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

private theorem mobius_real_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have hi := (mobius_inversion
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun k => (if k = 0 then 0 else 1 : ℝ) -
      (if k - 1 = 0 then 0 else 1 : ℝ))).mpr
      (fun d hd => mobiusDifference_one d hd)
  have hh := hi n (Nat.pos_of_ne_zero hn0)
  simpa [hn0, hn1, show n - 1 ≠ 0 by omega] using hh

private theorem finite_mobius_divisorIndicator (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d n) =
      if n = 1 then 1 else 0 := by
  have hfilter : (Finset.Icc 1 Y).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hdn⟩
      exact ⟨hdn, ne_of_gt hn⟩
    · rintro ⟨hdn, hn0⟩
      refine ⟨⟨?_, (Nat.le_of_dvd hn hdn).trans hnY⟩, hdn⟩
      exact Nat.pos_of_dvd_of_pos hdn hn
  simp only [divisorIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter, mobius_real_divisor_sum]

/-- Exact finite divisor counting, at every endpoint through the chosen cutoff. -/
theorem finite_mobius_floor_sum (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) = 1 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * cumulative (divisorIndicator d) n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [cumulative_divisorIndicator d n (Finset.mem_Icc.mp hd).1]
    _ = cumulative (fun k => ∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d k) n := by
      unfold cumulative
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = cumulative (fun k => if k = 1 then (1 : ℝ) else 0) n := by
      unfold cumulative
      apply Finset.sum_congr rfl
      intro k hk
      exact finite_mobius_divisorIndicator Y (k + 1) (by omega)
        (by have := Finset.mem_range.mp hk; omega)
    _ = 1 := cumulative_delta_one n hn

private theorem residueFraction_eq_div_sub_floor (d n : ℕ) (hd : 0 < d) :
    residueFraction d n = (n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have he : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mod_add_div n d
  unfold residueFraction
  field_simp
  nlinarith

/-- The exact signed arithmetic identity preceding both the head and m_Y bounds. -/
theorem mobius_residue_prefix_identity (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) =
      (n : ℝ) * mobiusReciprocalSum Y - 1 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 Y,
        ((n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) -
          (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residueFraction_eq_div_sub_floor d n (Finset.mem_Icc.mp hd).1]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, finite_mobius_floor_sum Y n hn hnY]
      rfl

/-- The constructed function is exactly one on the entire requested positive head. -/
theorem canonicalMobiusHead_exact (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    canonicalMobiusHead Y n = 1 := by
  have hY : ((Y + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold canonicalMobiusHead
  rw [mobius_residue_prefix_identity Y n hn hnY]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < Y + 1)]
  field_simp
  <;> ring

private theorem residueFraction_mem_full_legal (d : ℕ) (hd : 0 < d) :
    residueFraction d ∈ legalSeedSpan (Set.Ici 1) := by
  have hr : residue d ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [dilation_one] using
      (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1)
        (show d ∈ Set.Ici 1 from hd) (by omega))
  have he : residueFraction d = (1 / (d : ℝ)) • residue d := by
    funext n
    simp [residueFraction, residue, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (legalSeedSpan _).smul_mem _ hr

theorem canonicalMobiusHead_mem_legal (Y : ℕ) :
    canonicalMobiusHead Y ∈ legalSeedSpan (Set.Ici 1) := by
  have hs : (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) • residueFraction d) ∈
      legalSeedSpan (Set.Ici 1) := by
    apply (legalSeedSpan _).sum_mem
    intro d hd
    exact (legalSeedSpan _).smul_mem _
      (residueFraction_mem_full_legal d (Finset.mem_Icc.mp hd).1)
  have hc := (legalSeedSpan (Set.Ici 1)).smul_mem
    (((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y)
    (residueFraction_mem_full_legal (Y + 1) (Nat.succ_pos _))
  have h := (legalSeedSpan (Set.Ici 1)).add_mem ((legalSeedSpan _).neg_mem hs) hc
  convert h using 1
  funext n
  simp only [canonicalMobiusHead, Pi.add_apply, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem canonicalMobiusHead_mem_class (Y : ℕ) :
    canonicalMobiusHead Y ∈ conditionalHeadClass Y :=
  ⟨canonicalMobiusHead_mem_legal Y, fun n hn hnY => canonicalMobiusHead_exact Y n hn hnY⟩

private theorem finite_mobius_sum_abs (Y : ℕ) (hY : 0 < Y) (a : ℕ → ℝ) (B : ℝ)
    (ha1 : a 1 = 0) (ha : ∀ d ∈ Finset.Icc 1 Y, |a d| ≤ B) :
    |∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * a d| ≤
      ((Y : ℝ) - 1) * B := by
  classical
  have h1 : 1 ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨le_refl _, hY⟩
  have hsplit := Finset.sum_erase_add (s := Finset.Icc 1 Y)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) * a d) h1
  rw [ha1, mul_zero, add_zero] at hsplit
  have hcard : ((Finset.Icc 1 Y).erase 1).card = Y - 1 := by
    rw [Finset.card_erase_of_mem h1]
    simp [Nat.card_Icc]
  rw [← hsplit]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 Y).erase 1,
        |(ArithmeticFunction.moebius d : ℝ) * a d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 Y).erase 1, B := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      calc
        _ ≤ 1 * B := mul_le_mul (mobius_real_abs_le_one d)
          (ha d (Finset.mem_of_mem_erase hd)) (abs_nonneg _) (by norm_num)
        _ = B := one_mul _
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      rw [Nat.cast_sub (by omega : 1 ≤ Y)]
      norm_num

private theorem residueFraction_abs_le_one (d n : ℕ) (hd : 0 < d) :
    |residueFraction d n| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ((n % d : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (Nat.mod_lt n hd).le
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdR).2
  simpa using hm

/-- Elementary uniform bound for the actual reciprocal Möbius sum. -/
theorem mobiusReciprocalSum_abs_le_one (Y : ℕ) (hY : 0 < Y) :
    |mobiusReciprocalSum Y| ≤ 1 := by
  have hsum := finite_mobius_sum_abs Y hY (fun d => residueFraction d Y) 1
    (by simp [residueFraction, Nat.mod_one])
    (fun d hd => residueFraction_abs_le_one d Y (Finset.mem_Icc.mp hd).1)
  have hid := mobius_residue_prefix_identity Y Y hY (le_refl _)
  have hprod : |(Y : ℝ) * mobiusReciprocalSum Y| ≤ (Y : ℝ) := by
    calc
      _ = |1 + ∑ d ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius d : ℝ) * residueFraction d Y| := by congr 1; linarith
      _ ≤ |(1 : ℝ)| + |∑ d ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius d : ℝ) * residueFraction d Y| := abs_add_le _ _
      _ ≤ _ := by norm_num at *; linarith
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at hprod
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  nlinarith

private theorem cesaro_canonicalMobiusHead (Y t : ℕ) :
    cesaro (canonicalMobiusHead Y) t =
      -(∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) *
        cesaro (residueFraction d) t) +
      ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y * cesaro (residueFraction (Y + 1)) t := by
  simp only [cesaro, canonicalMobiusHead, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_div, add_div, neg_div, mul_div_assoc]
  rw [Finset.sum_comm]

/-- The actual shared-latent conditional mean is bounded by the head length. -/
theorem canonicalMobiusHead_mean_abs_le (Y : ℕ) (hY : 0 < Y) (t : ℕ) :
    |cesaro (canonicalMobiusHead Y) t| ≤ (Y : ℝ) := by
  have hsum := finite_mobius_sum_abs Y hY
    (fun d => cesaro (residueFraction d) t) (1 / 2)
    (by simp [cesaro, residueFraction, Nat.mod_one]) (by
      intro d hd
      rw [abs_of_nonneg (cesaro_residue_nonneg d t)]
      exact cesaro_residue_le_half d t (Finset.mem_Icc.mp hd).1)
  have hm := mobiusReciprocalSum_abs_le_one Y hY
  have hgen : |cesaro (residueFraction (Y + 1)) t| ≤ 1 / 2 := by
    rw [abs_of_nonneg (cesaro_residue_nonneg _ _)]
    exact cesaro_residue_le_half _ _ (Nat.succ_pos _)
  have hc : |((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y *
      cesaro (residueFraction (Y + 1)) t| ≤ ((Y + 1 : ℕ) : ℝ) / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hmgen := mul_le_mul hm hgen (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hmul := mul_le_mul_of_nonneg_left hmgen (Nat.cast_nonneg (Y + 1) : (0 : ℝ) ≤ _)
    nlinarith
  rw [cesaro_canonicalMobiusHead]
  calc
    _ ≤ |-(∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) *
        cesaro (residueFraction d) t)| +
        |((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y * cesaro (residueFraction (Y + 1)) t| :=
      abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; push_cast at hc ⊢; linarith

/-- The canonical witness has the explicit unconditional linear energy bound. -/
theorem canonicalMobiusHead_energy_le (Y : ℕ) (hY : 0 < Y) :
    conditionalMeanSquare (canonicalMobiusHead Y) ≤
      (Y : ℝ) * (2 * (Y : ℝ) + 1) / ((Y : ℝ) + 2) := by
  have hclass := canonicalMobiusHead_mem_class Y
  have hE := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hclass.1
  have hEt : Summable (fun k : ℕ => conditionalWeight (k + Y) *
      (cesaro (canonicalMobiusHead Y) (k + Y + 1)) ^ 2) :=
    hE.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hq : Summable conditionalWeight := hasSum_mixtureWeight.summable
  have hqt : Summable (fun k : ℕ => conditionalWeight (k + Y)) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htail : (∑' k : ℕ, conditionalWeight (k + Y) *
      (cesaro (canonicalMobiusHead Y) (k + Y + 1)) ^ 2) ≤
      (2 / ((Y : ℝ) + 2)) * (Y : ℝ) ^ 2 := by
    calc
      _ ≤ ∑' k : ℕ, conditionalWeight (k + Y) * (Y : ℝ) ^ 2 := by
        apply Summable.tsum_le_tsum _ hEt (hqt.mul_right ((Y : ℝ) ^ 2))
        intro k
        apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos _).le
        have hm := mul_self_le_mul_self
          (abs_nonneg (cesaro (canonicalMobiusHead Y) (k + Y + 1)))
          (canonicalMobiusHead_mean_abs_le Y hY (k + Y + 1))
        simpa only [← pow_two, sq_abs] using hm
      _ = _ := by rw [tsum_mul_right, conditionalWeight_tsum_tail]
  rw [conditionalMeanSquare_exact_head_split Y hclass]
  calc
    _ ≤ (Y : ℝ) / ((Y : ℝ) + 2) + (2 / ((Y : ℝ) + 2)) * (Y : ℝ) ^ 2 :=
      add_le_add le_rfl htail
    _ = _ := by ring

/-- The genuine variational infimum inherits the bound from an explicit legal witness. -/
theorem conditionalHeadMinimum_le_linear (Y : ℕ) (hY : 0 < Y) :
    conditionalHeadMinimum Y ≤ (Y : ℝ) * (2 * (Y : ℝ) + 1) / ((Y : ℝ) + 2) :=
  (conditionalHeadMinimum_le Y (canonicalMobiusHead_mem_class Y)).trans
    (canonicalMobiusHead_energy_le Y hY)

/-- The manuscript's strict bound E_Y<2Y is unconditional for every positive head. -/
theorem conditionalHeadMinimum_lt_two_mul (Y : ℕ) (hY : 0 < Y) :
    conditionalHeadMinimum Y < 2 * (Y : ℝ) := by
  apply lt_of_le_of_lt (conditionalHeadMinimum_le_linear Y hY)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (Y : ℝ) + 2)).2
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  nlinarith

end RiemannResearch.RH.Pareto
