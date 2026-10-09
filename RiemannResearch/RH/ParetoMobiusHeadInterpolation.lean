import RiemannResearch.RH.CanonicalMobiusHeadRepair
import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.RH.ParetoInversePolynomial
import RiemannResearch.RH.ParetoPrimeSourceDivergence

/-!
# Explicit full-tail Möbius head interpolation

Source: user-provided Green--Pareto--Schur continuation, the explicit repair
in RH/GreenParetoGitHubAdvance20261006.md, Section 3. The proof strategy below
uses the existing complete canonical Möbius norm and exact integer dilation.
The boundary conductor H+1 and every interior conductor are retained.

This supplies a concrete repair norm rather than assuming one. It does not
supply complete-source tightness, a strict spectral moment budget, or the
RH-to-density converse.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

/-- A unit step on sites k through H with boundary conductor H+1. -/
def mobiusHeadStep (H k : ℕ) (hk : 0 < k) : ThresholdHilbert :=
  -(∑ q ∈ (Finset.Icc 1 (H / k)).attach,
      (ArithmeticFunction.moebius (q : ℕ) : ℝ) •
        normalizedResidueHilbert (k * q)
          (Nat.mul_pos hk (by have := (Finset.mem_Icc.mp q.property).1; omega))) +
    (((H + 1 : ℕ) : ℝ) / (k : ℝ) * mobiusReciprocalSum (H / k)) •
      normalizedResidueHilbert (H + 1) (Nat.succ_pos _)

theorem mobiusHeadStep_sequence (H k : ℕ) (hk : 0 < k) (j : ℕ) :
    hilbertSequence (mobiusHeadStep H k hk) j =
      -(∑ q ∈ Finset.Icc 1 (H / k),
        (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j) +
      (((H+1 : ℕ) : ℝ) / (k : ℝ) * mobiusReciprocalSum (H/k)) *
        residueFraction (H+1) j := by
  change hilbertSequenceLinear (mobiusHeadStep H k hk) j = _
  unfold mobiusHeadStep
  simp only [map_add, map_neg, map_sum, map_smul, Pi.add_apply,
    Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change -(∑ q ∈ (Finset.Icc 1 (H/k)).attach,
      (ArithmeticFunction.moebius (q : ℕ) : ℝ) *
        hilbertSequence (normalizedResidueHilbert (k*q) _) j) +
      (((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) *
        hilbertSequence (normalizedResidueHilbert (H+1) _) j = _
  simp_rw [normalizedResidueHilbert_sequence]
  rw [Finset.sum_attach (Finset.Icc 1 (H/k))
    (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j)]

/-- The literal step lies in the complete dictionary through H+1. -/
theorem mobiusHeadStep_mem (H k : ℕ) (hk : 0 < k) :
    mobiusHeadStep H k hk ∈ finiteSpace H := by
  unfold mobiusHeadStep
  apply (finiteSpace H).add_mem
  · apply (finiteSpace H).neg_mem
    apply (finiteSpace H).sum_mem
    intro q hq
    apply (finiteSpace H).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hqle := (Finset.mem_Icc.mp q.property).2
    have hmul : k * (q : ℕ) ≤ H := calc
      _ ≤ k * (H/k) := Nat.mul_le_mul_left k hqle
      _ ≤ H := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self H k
    omega
  · apply (finiteSpace H).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace H (H+1) (Nat.succ_pos _) le_rfl

private theorem residueFraction_mul (k q j : ℕ) (hk : 0 < k) (hq : 0 < q) :
    residueFraction (k*q) j =
      residueFraction q (j/k) + residueFraction k j / (q : ℝ) := by
  simp only [residueFraction, Nat.mod_mul, Nat.cast_add, Nat.cast_mul]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  field_simp
  ring

/-- Exact full-vector equality before any boundary term is estimated. -/
theorem mobiusHeadStep_decomposition (H k : ℕ) (hk : 0 < k) :
    mobiusHeadStep H k hk =
      (k : ℝ)⁻¹ • hilbertDilation k hk (canonicalMobiusHilbert (H/k)) -
        (((k * (H/k+1) : ℕ) : ℝ) / (k : ℝ) * mobiusReciprocalSum (H/k)) •
          normalizedResidueHilbert (k * (H/k+1)) (by positivity) +
        (((H+1 : ℕ) : ℝ) / (k : ℝ) * mobiusReciprocalSum (H/k)) •
          normalizedResidueHilbert (H+1) (Nat.succ_pos _) := by
  apply hilbertSequence_injective
  funext j
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hsum :
      (∑ q ∈ Finset.Icc 1 (H/k),
        (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j) =
      (∑ q ∈ Finset.Icc 1 (H/k),
        (ArithmeticFunction.moebius q : ℝ) * residueFraction q (j/k)) +
        residueFraction k j * mobiusReciprocalSum (H/k) := by
    unfold mobiusReciprocalSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [residueFraction_mul k q j hk (by have := (Finset.mem_Icc.mp hq).1; omega)]
    ring
  have hD : (k : ℝ)⁻¹ *
      hilbertSequence (hilbertDilation k hk (canonicalMobiusHilbert (H/k))) j =
      canonicalMobiusHead (H/k) (j/k) := by
    rw [hilbertDilation_sequence, canonicalMobiusHilbert_sequence]
    simp only [dilation]
    rw [← mul_assoc, inv_mul_cancel₀ hkR, one_mul]
  change hilbertSequenceLinear (mobiusHeadStep H k hk) j =
    hilbertSequenceLinear (_ + _) j
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  change hilbertSequence (mobiusHeadStep H k hk) j =
    (k : ℝ)⁻¹ * hilbertSequence (hilbertDilation k hk
      (canonicalMobiusHilbert (H/k))) j -
      _ * hilbertSequence (normalizedResidueHilbert (k*(H/k+1)) _) j +
      _ * hilbertSequence (normalizedResidueHilbert (H+1) _) j
  rw [mobiusHeadStep_sequence, hD, normalizedResidueHilbert_sequence,
    normalizedResidueHilbert_sequence, hsum,
    residueFraction_mul k (H/k+1) j hk (Nat.succ_pos _)]
  unfold canonicalMobiusHead
  push_cast
  field_simp
  ring

theorem mobiusHeadStep_exact (H k : ℕ) (hk : 0 < k)
    (j : ℕ) (hjH : j ≤ H) :
    hilbertSequence (mobiusHeadStep H k hk) j = if k ≤ j then 1 else 0 := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hp : H < k * (H/k+1) := by
    have he := Nat.mod_add_div H k
    have hm := Nat.mod_lt H hk
    nlinarith
  have hpR : ((k * (H/k+1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hHR : ((H+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hhead : hilbertSequence (mobiusHeadStep H k hk) j =
      canonicalMobiusHead (H/k) (j/k) := by
    rw [mobiusHeadStep_decomposition]
    change hilbertSequenceLinear (_ + _) j = _
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    change (k : ℝ)⁻¹ *
        hilbertSequence (hilbertDilation k hk (canonicalMobiusHilbert (H/k))) j -
      (((k*(H/k+1) : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) *
        hilbertSequence (normalizedResidueHilbert (k*(H/k+1)) _) j +
      (((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) *
        hilbertSequence (normalizedResidueHilbert (H+1) _) j = _
    rw [hilbertDilation_sequence, canonicalMobiusHilbert_sequence,
      normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]
    simp only [dilation, residueFraction,
      Nat.mod_eq_of_lt (show j < k * (H/k+1) by omega),
      Nat.mod_eq_of_lt (show j < H+1 by omega)]
    field_simp
    ring
  rw [hhead]
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    exact canonicalMobiusHead_exact (H/k) (j/k) (Nat.div_pos hkj hk)
      (Nat.div_le_div_right hjH)
  · rw [if_neg hkj, Nat.div_eq_of_lt (by omega : j < k)]
    simp [canonicalMobiusHead, residueFraction]

private theorem norm_le_two_sqrt_div (H k : ℕ) (hk : 0 < k)
    (v : ThresholdHilbert) (hv : (k : ℝ)^2 * ‖v‖^2 ≤ 4 * (H : ℝ)) :
    ‖v‖ ≤ 2 * Real.sqrt (H : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkR).mpr
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
  have hsq : (‖v‖ * (k : ℝ))^2 ≤ (2 * Real.sqrt (H : ℝ))^2 := by
    nlinarith only [hv, hs]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg v) hkR.le) (by positivity)).mp hsq

private theorem scaledResidue_norm_le (H k d : ℕ) (hk : 0 < k) (hd : 0 < d)
    (hdH : d ≤ 2*H) (m : ℝ) (hm : |m| ≤ 1) :
    ‖((d : ℝ)/(k : ℝ)*m) • normalizedResidueHilbert d hd‖ ≤
      2 * Real.sqrt (H : ℝ)/(k : ℝ) := by
  apply norm_le_two_sqrt_div H k hk
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hm2 : m^2 ≤ 1 := by nlinarith [sq_abs m, abs_nonneg m]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    _ ≤ (k : ℝ)^2 * ((d : ℝ)/(k : ℝ)*m)^2 * (2/(d : ℝ)) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (normalizedResidue_norm_sq_le d hd)
          (show 0 ≤ (k : ℝ)^2 * ((d : ℝ)/(k : ℝ)*m)^2 by positivity)
    _ = 2 * (d : ℝ) * m^2 := by field_simp
    _ ≤ 2 * (d : ℝ) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 2 * (d : ℝ) by positivity)
    _ ≤ 4 * (H : ℝ) := by exact_mod_cast (show 2*d ≤ 4*H by omega)

/-- The whole infinite tail is covered by a uniform bound for each unit step. -/
theorem mobiusHeadStep_norm_le (H k : ℕ) (hk : 0 < k) (hkH : k ≤ H) :
    ‖mobiusHeadStep H k hk‖ ≤ 6 * Real.sqrt (H : ℝ)/(k : ℝ) := by
  have hH : 0 < H := lt_of_lt_of_le hk hkH
  have hL : 0 < H/k := Nat.div_pos hkH hk
  have hprod : k * (H/k) ≤ H := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self H k
  have hboundary : k*(H/k+1) ≤ 2*H := by nlinarith
  have hm := mobiusReciprocalSum_abs_le_one (H/k) hL
  have hA : ‖(k : ℝ)⁻¹ • hilbertDilation k hk (canonicalMobiusHilbert (H/k))‖ ≤
      2 * Real.sqrt (H : ℝ)/(k : ℝ) := by
    apply norm_le_two_sqrt_div H k hk
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertDilation_norm_sq]
    have hcancel : (k : ℝ)^2 * (((k : ℝ)⁻¹)^2 *
        ((k : ℝ) * ‖canonicalMobiusHilbert (H/k)‖^2)) =
        (k : ℝ) * ‖canonicalMobiusHilbert (H/k)‖^2 := by field_simp
    rw [hcancel]
    have hnorm := (canonicalMobiusHilbert_norm_sq_lt_four_mul (H/k) hL).le
    have hpR : (k : ℝ) * (H/k : ℕ) ≤ (H : ℝ) := by exact_mod_cast hprod
    have hmul := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (α := ℝ) k)
    nlinarith only [hmul, hpR]
  have hB := scaledResidue_norm_le H k (k*(H/k+1)) hk (by positivity)
    hboundary (mobiusReciprocalSum (H/k)) hm
  have hC := scaledResidue_norm_le H k (H+1) hk (Nat.succ_pos _)
    (by omega) (mobiusReciprocalSum (H/k)) hm
  rw [mobiusHeadStep_decomposition]
  calc
    _ ≤ ‖(k : ℝ)⁻¹ • hilbertDilation k hk (canonicalMobiusHilbert (H/k)) -
          (((k*(H/k+1) : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) •
            normalizedResidueHilbert (k*(H/k+1)) (by positivity)‖ +
        ‖(((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) •
            normalizedResidueHilbert (H+1) (Nat.succ_pos _)‖ := norm_add_le _ _
    _ ≤ ‖(k : ℝ)⁻¹ • hilbertDilation k hk (canonicalMobiusHilbert (H/k))‖ +
        ‖(((k*(H/k+1) : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) •
          normalizedResidueHilbert (k*(H/k+1)) (by positivity)‖ +
        ‖(((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) •
          normalizedResidueHilbert (H+1) (Nat.succ_pos _)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 2 * Real.sqrt (H : ℝ)/(k : ℝ) +
        2 * Real.sqrt (H : ℝ)/(k : ℝ) +
        2 * Real.sqrt (H : ℝ)/(k : ℝ) :=
      add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

/-- The signed increments are combined before any norm estimate. -/
def mobiusHeadInterpolation (H : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑ k ∈ (Finset.Icc 1 H).attach,
    (hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)) •
      mobiusHeadStep H k (by have := (Finset.mem_Icc.mp k.property).1; omega)

theorem mobiusHeadInterpolation_mem (H : ℕ) (f : ThresholdHilbert) :
    mobiusHeadInterpolation H f ∈ finiteSpace H := by
  unfold mobiusHeadInterpolation
  apply (finiteSpace H).sum_mem
  intro k hk
  exact (finiteSpace H).smul_mem _ (mobiusHeadStep_mem H k _)

theorem mobiusHeadInterpolation_exact (H : ℕ) (f : ThresholdHilbert)
    (j : ℕ) (hjH : j ≤ H) :
    hilbertSequence (mobiusHeadInterpolation H f) j = hilbertSequence f j := by
  have ht (n : ℕ) :
      (∑ k ∈ Finset.Icc 1 n,
        (hilbertSequence f k - hilbertSequence f (k-1))) = hilbertSequence f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring
  have he : hilbertSequence (mobiusHeadInterpolation H f) j =
      ∑ k ∈ Finset.Icc 1 H,
        if k ≤ j then hilbertSequence f k - hilbertSequence f (k-1) else 0 := by
    change hilbertSequenceLinear (mobiusHeadInterpolation H f) j = _
    unfold mobiusHeadInterpolation
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ k ∈ (Finset.Icc 1 H).attach,
      (hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)) *
        hilbertSequence (mobiusHeadStep H k _) j) = _
    simp_rw [mobiusHeadStep_exact H _ _ j hjH, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_attach (Finset.Icc 1 H)
      (fun k : ℕ => if k ≤ j then
        hilbertSequence f k - hilbertSequence f (k-1) else 0)]
  rw [he]
  calc
    _ = ∑ k ∈ Finset.Icc 1 j,
        if k ≤ j then hilbertSequence f k - hilbertSequence f (k-1) else 0 := by
      symm
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
          (Finset.mem_Icc.mp hk).2.trans hjH⟩
      · intro k hk hkj
        rw [if_neg (by
          intro h
          exact hkj (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,h⟩))]
    _ = _ := by
      rw [← ht j]
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_Icc.mp hk).2]

theorem compactHead_mobiusHeadInterpolation (H : ℕ) (f : ThresholdHilbert) :
    compactHead H (mobiusHeadInterpolation H f) = compactHead H f := by
  apply hilbertSequence_injective
  funext j
  rw [compactHead_sequence, compactHead_sequence]
  by_cases hj : j ≤ H
  · rw [if_pos hj, if_pos hj, mobiusHeadInterpolation_exact H f j hj]
  · rw [if_neg hj, if_neg hj]

theorem mobiusHeadInterpolation_depends_on_head (H : ℕ) (f : ThresholdHilbert) :
    mobiusHeadInterpolation H (compactHead H f) = mobiusHeadInterpolation H f := by
  unfold mobiusHeadInterpolation
  apply Finset.sum_congr rfl
  intro k hk
  rw [compactHead_sequence, compactHead_sequence,
    if_pos (Finset.mem_Icc.mp k.property).2,
    if_pos (by have := (Finset.mem_Icc.mp k.property).2; omega)]

private theorem normalizedDifference_abs_sum_le (H : ℕ) (f : ThresholdHilbert) :
    (∑ k ∈ Finset.Icc 1 H, |normalizedDifference f k|) ≤
      2 * Real.sqrt (H : ℝ) * ‖f‖ := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 H)
    (r := fun k => |normalizedDifference f k|)
    (f := fun _ => (1 : ℝ))
    (g := fun k => normalizedDifference f k ^ 2)
    (by intro k hk; norm_num)
    (by intro k hk; positivity)
    (by intro k hk; simp)
  have hcard : (∑ k ∈ Finset.Icc 1 H, (1 : ℝ)) = (H : ℝ) := by simp
  rw [hcard] at hcs
  have hd := normalizedDifference_energy_le H f
  have hmul := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) H)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 H, |normalizedDifference f k| :=
    Finset.sum_nonneg (by intro k hk; exact abs_nonneg _)
  have hrhs : 0 ≤ 2 * Real.sqrt (H : ℝ) * ‖f‖ := by positivity
  have hsq : (∑ k ∈ Finset.Icc 1 H, |normalizedDifference f k|)^2 ≤
      (2 * Real.sqrt (H : ℝ) * ‖f‖)^2 := by
    rw [mul_pow, mul_pow, hs]
    nlinarith only [hcs, hmul]
  exact (sq_le_sq₀ hsum hrhs).mp hsq

private theorem mobiusHeadInterpolation_norm_le_full (H : ℕ) (f : ThresholdHilbert) :
    ‖mobiusHeadInterpolation H f‖ ≤ 12 * (H : ℝ) * ‖f‖ := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 H).attach,
        ‖(hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)) •
          mobiusHeadStep H k _‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 H).attach,
        6 * Real.sqrt (H : ℝ) * |normalizedDifference f k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs]
      have hkpos : 0 < (k : ℕ) := by have := (Finset.mem_Icc.mp k.property).1; omega
      have hkR : (0 : ℝ) < (k : ℕ) := Nat.cast_pos.mpr hkpos
      have hb := mul_le_mul_of_nonneg_left
        (mobiusHeadStep_norm_le H k hkpos (Finset.mem_Icc.mp k.property).2)
        (abs_nonneg (hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)))
      convert hb using 1
      rw [normalizedDifference, abs_div, abs_of_pos hkR]
      ring
    _ = 6 * Real.sqrt (H : ℝ) *
        (∑ k ∈ Finset.Icc 1 H, |normalizedDifference f k|) := by
      rw [← Finset.mul_sum, Finset.sum_attach (Finset.Icc 1 H)
        (fun k : ℕ => |normalizedDifference f k|)]
    _ ≤ 6 * Real.sqrt (H : ℝ) * (2 * Real.sqrt (H : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (normalizedDifference_abs_sum_le H f) (by positivity)
    _ = 12 * (Real.sqrt (H : ℝ))^2 * ‖f‖ := by ring
    _ = _ := by rw [hs]

/-- Concrete operator cost: the norm is over the FULL infinite Pareto space.
The constant 12H improves the paper's coarser 12H+4 cap. -/
theorem mobiusHeadInterpolation_norm_le (H : ℕ) (f : ThresholdHilbert) :
    ‖mobiusHeadInterpolation H f‖ ≤ 12 * (H : ℝ) * ‖compactHead H f‖ := by
  rw [← mobiusHeadInterpolation_depends_on_head H f]
  exact mobiusHeadInterpolation_norm_le_full H (compactHead H f)


/-- The explicit interpolation is the inverse of the first H observations
on the entire H-dimensional legal stage. -/
theorem mobiusHeadInterpolation_eq_of_mem (H : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace H) : mobiusHeadInterpolation H f = f := by
  have hz := finiteSpace_eq_zero_of_head_zero H (mobiusHeadInterpolation H f - f)
    ((finiteSpace H).sub_mem (mobiusHeadInterpolation_mem H f) hf) (by
      intro j hj hjH
      change hilbertSequenceLinear (mobiusHeadInterpolation H f - f) j = 0
      rw [map_sub]
      change hilbertSequence (mobiusHeadInterpolation H f) j - hilbertSequence f j = 0
      rw [mobiusHeadInterpolation_exact H f j hjH, sub_self])
  exact sub_eq_zero.mp hz

/-- Unconditional full-stage conditioning with an explicit linear cost. -/
theorem finiteSpace_norm_le_head (H : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace H) :
    ‖f‖ ≤ 12 * (H : ℝ) * ‖compactHead H f‖ := by
  have h := mobiusHeadInterpolation_norm_le H f
  rwa [mobiusHeadInterpolation_eq_of_mem H f hf] at h

def mobiusHeadInterpolationLinear (H : ℕ) :
    ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := mobiusHeadInterpolation H
  map_add' f g := by
    unfold mobiusHeadInterpolation
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hilbertSequence_add, Pi.add_apply]
    module
  map_smul' c f := by
    change mobiusHeadInterpolation H (c • f) = c • mobiusHeadInterpolation H f
    unfold mobiusHeadInterpolation
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, smul_smul]

/-- A concrete bounded legal right inverse for the physical head. -/
def mobiusHeadInterpolationContinuous (H : ℕ) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (mobiusHeadInterpolationLinear H).mkContinuous (12*(H : ℝ))
    (mobiusHeadInterpolation_norm_le_full H)

private theorem residueFraction_abs_le_one_for_head_tail
    (d j : ℕ) (hd : 0 < d) : |residueFraction d j| ≤ 1 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hm : ((j % d : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (Nat.mod_lt j hd).le
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdR).2
  simpa using hm

private theorem moebius_abs_le_one_for_head_tail (q : ℕ) :
    |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> simp [h]

/-- Every site, including the infinite tail, of the literal legal unit
step is bounded by (2H+1)/k. -/
theorem mobiusHeadStep_sequence_abs_le (H k : ℕ) (hk : 0 < k)
    (hkH : k ≤ H) (j : ℕ) :
    |hilbertSequence (mobiusHeadStep H k hk) j| ≤
      (2 * (H : ℝ) + 1) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hL : 0 < H / k := Nat.div_pos hkH hk
  have hm := mobiusReciprocalSum_abs_le_one (H / k) hL
  have hsum :
      |∑ q ∈ Finset.Icc 1 (H / k),
        (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j| ≤
        (H / k : ℕ) := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 (H / k),
          |(ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 (H / k), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos : 0 < q := by
          have := (Finset.mem_Icc.mp hq).1
          omega
        rw [abs_mul]
        calc
          _ ≤ 1 * 1 := mul_le_mul
            (moebius_abs_le_one_for_head_tail q)
            (residueFraction_abs_le_one_for_head_tail (k*q) j
              (Nat.mul_pos hk hqpos))
            (abs_nonneg _) (by norm_num)
          _ = 1 := by ring
      _ = _ := by simp
  have hb :
      |(((H+1 : ℕ) : ℝ) / (k : ℝ) * mobiusReciprocalSum (H/k)) *
        residueFraction (H+1) j| ≤ ((H+1 : ℕ) : ℝ) / (k : ℝ) := by
    rw [abs_mul, abs_mul, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (H+1)), abs_of_pos hkR]
    calc
      _ = (((H+1 : ℕ) : ℝ) / (k : ℝ)) *
          (|mobiusReciprocalSum (H/k)| * |residueFraction (H+1) j|) := by ring
      _ ≤ (((H+1 : ℕ) : ℝ) / (k : ℝ)) * (1 * 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hm
          (residueFraction_abs_le_one_for_head_tail (H+1) j (Nat.succ_pos _))
          (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hquot : (H / k : ℕ) ≤ (H : ℝ) / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    exact_mod_cast Nat.div_mul_le_self H k
  rw [mobiusHeadStep_sequence]
  calc
    _ ≤ |∑ q ∈ Finset.Icc 1 (H/k),
        (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j| +
        |(((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) *
          residueFraction (H+1) j| := by
      simpa only [abs_neg] using abs_add_le
        (-(∑ q ∈ Finset.Icc 1 (H/k),
          (ArithmeticFunction.moebius q : ℝ) * residueFraction (k*q) j))
        ((((H+1 : ℕ) : ℝ)/(k : ℝ)*mobiusReciprocalSum (H/k)) *
          residueFraction (H+1) j)
    _ ≤ (H/k : ℕ) + ((H+1 : ℕ) : ℝ)/(k : ℝ) := add_le_add hsum hb
    _ ≤ (H : ℝ)/(k : ℝ) + ((H+1 : ℕ) : ℝ)/(k : ℝ) :=
      add_le_add hquot le_rfl
    _ = _ := by push_cast; ring

/-- Concrete uniform site bound for the complete Möbius lift.  The right
side involves its input norm and no unknown arithmetic provider. -/
theorem mobiusHeadInterpolation_sequence_abs_le (H : ℕ)
    (f : ThresholdHilbert) (j : ℕ) :
    |hilbertSequence (mobiusHeadInterpolation H f) j| ≤
      2 * (2 * (H : ℝ) + 1) * Real.sqrt (H : ℝ) * ‖f‖ := by
  have he : hilbertSequence (mobiusHeadInterpolation H f) j =
      ∑ k ∈ (Finset.Icc 1 H).attach,
        (hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)) *
          hilbertSequence (mobiusHeadStep H k
            (by have := (Finset.mem_Icc.mp k.property).1; omega)) j := by
    change hilbertSequenceLinear (mobiusHeadInterpolation H f) j = _
    unfold mobiusHeadInterpolation
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [he]
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 H).attach,
        |(hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)) *
          hilbertSequence (mobiusHeadStep H k _) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 H).attach,
        (2 * (H : ℝ) + 1) * |normalizedDifference f k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      have hkpos : 0 < (k : ℕ) := by
        have := (Finset.mem_Icc.mp k.property).1
        omega
      have hkR : (0 : ℝ) < (k : ℕ) := Nat.cast_pos.mpr hkpos
      have hb := mul_le_mul_of_nonneg_left
        (mobiusHeadStep_sequence_abs_le H k hkpos
          (Finset.mem_Icc.mp k.property).2 j)
        (abs_nonneg (hilbertSequence f k - hilbertSequence f ((k : ℕ)-1)))
      convert hb using 1
      rw [normalizedDifference, abs_div, abs_of_pos hkR]
      ring
    _ = (2 * (H : ℝ) + 1) *
        (∑ k ∈ Finset.Icc 1 H, |normalizedDifference f k|) := by
      rw [← Finset.mul_sum, Finset.sum_attach (Finset.Icc 1 H)
        (fun k : ℕ => |normalizedDifference f k|)]
    _ ≤ (2 * (H : ℝ) + 1) * (2 * Real.sqrt (H : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (normalizedDifference_abs_sum_le H f) (by positivity)
    _ = _ := by ring

/-- An actual finite legal vector has a universal uniform sequence bound. -/
theorem finiteSpace_sequence_abs_le (H : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace H) (j : ℕ) :
    |hilbertSequence f j| ≤
      2 * (2 * (H : ℝ) + 1) * Real.sqrt (H : ℝ) * ‖f‖ := by
  have h := mobiusHeadInterpolation_sequence_abs_le H f j
  rwa [mobiusHeadInterpolation_eq_of_mem H f hf] at h

/-- Exact complete physical tail; the cutoff through N is removed before
the infinite sum is estimated. -/
theorem compactHead_complete_tail_norm_sq (N : ℕ) (f : ThresholdHilbert) :
    ‖f - compactHead N f‖^2 =
      ∑' j : ℕ, positiveWeight (j+(N+1)) *
        hilbertSequence f (j+(N+1))^2 := by
  rw [hilbert_norm_weighted_sq]
  have hs := hilbertSequence_square_summable (f - compactHead N f)
  rw [← hs.sum_add_tsum_nat_add (N+1)]
  have hz : (∑ k ∈ Finset.range (N+1), positiveWeight k *
      hilbertSequence (f - compactHead N f) k ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hilbertSequence_sub]
    simp only [Pi.sub_apply, compactHead_sequence,
      if_pos (by have := Finset.mem_range.mp hk; omega : k ≤ N),
      sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [hz, zero_add]
  apply tsum_congr
  intro j
  rw [hilbertSequence_sub]
  simp only [Pi.sub_apply, compactHead_sequence,
    if_neg (by omega : ¬ j+(N+1) ≤ N), sub_zero]

/-- A uniform physical sequence bound controls the entire infinite tail,
with the exact physical Pareto factor 1/(N+1). -/
theorem compactHead_complete_tail_norm_sq_le_of_sequence_bound
    (N : ℕ) (f : ThresholdHilbert) (C : ℝ)
    (hbound : ∀ j, |hilbertSequence f j| ≤ C) :
    ‖f - compactHead N f‖^2 ≤ C^2 / ((N : ℝ) + 1) := by
  rw [compactHead_complete_tail_norm_sq]
  have hle (j : ℕ) :
      positiveWeight (j+(N+1)) * hilbertSequence f (j+(N+1))^2 ≤
        positiveWeight (j+(N+1)) * C^2 := by
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
    have hh := mul_self_le_mul_self (abs_nonneg _) (hbound (j+(N+1)))
    simpa only [← pow_two, sq_abs] using hh
  have hm := (positiveWeight_summable.comp_injective
    (fun a b h => Nat.add_right_cancel h :
      Function.Injective (fun j : ℕ => j+(N+1)))).mul_right (C^2)
  have hs := Summable.of_nonneg_of_le
    (fun j => mul_nonneg (positiveWeight_nonneg (j+(N+1)))
      (sq_nonneg (hilbertSequence f (j+(N+1))))) hle hm
  calc
    _ ≤ ∑' j : ℕ, positiveWeight (j+(N+1)) * C^2 := by
      apply Summable.tsum_le_tsum _ hs hm
      intro j
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      have hh := mul_self_le_mul_self (abs_nonneg _)
        (hbound (j+(N+1)))
      simpa only [← pow_two, sq_abs] using hh
    _ = _ := by
      rw [tsum_mul_right, positiveWeight_tail_tsum (N+1) (by omega)]
      push_cast
      ring

/-- Unconditional complete physical leakage bound for every finite legal
stage.  H indexes the complete dictionary through conductor H+1. -/
theorem finiteSpace_complete_tail_norm_sq_le (H N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace H) :
    ‖f - compactHead N f‖^2 ≤
      4 * (2 * (H : ℝ) + 1)^2 * (H : ℝ) * ‖f‖^2 /
        ((N : ℝ) + 1) := by
  have h := compactHead_complete_tail_norm_sq_le_of_sequence_bound N f
    (2 * (2 * (H : ℝ) + 1) * Real.sqrt (H : ℝ) * ‖f‖)
    (finiteSpace_sequence_abs_le H f hf)
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
  have hC : (2 * (2 * (H : ℝ) + 1) * Real.sqrt (H : ℝ) * ‖f‖)^2 =
      4 * (2 * (H : ℝ) + 1)^2 * (H : ℝ) * ‖f‖^2 := by
    simp only [mul_pow, hsqrt]
    ring
  simpa only [hC] using h

/-- Paper-compatible form in the conductor parameter M=H+1. -/
theorem finiteSpace_complete_tail_norm_sq_le_cubic (H N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace H) :
    ‖f - compactHead N f‖^2 ≤
      16 * ((H+1 : ℕ) : ℝ)^3 * ‖f‖^2 / ((N : ℝ) + 1) := by
  apply (finiteSpace_complete_tail_norm_sq_le H N f hf).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖f‖)
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  push_cast
  nlinarith [sq_nonneg (H : ℝ)]

end RiemannResearch.RH.Pareto.CoefficientStabilization
