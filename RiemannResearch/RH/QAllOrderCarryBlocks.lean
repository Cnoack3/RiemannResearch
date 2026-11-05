/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QAllOrderCarryPackets
import RiemannResearch.RH.QRamanujanContrastGram
import RiemannResearch.RH.QCRTPairCarryBlocks
import RiemannResearch.RH.ParetoArithmeticRepair

/-! # Signed block bounds for centered primitive residue components

Source: the interval Ramanujan Gram identity, the positive congruence
quadratic form, and finite summation by parts. This works on complete
periods and on arbitrary physical inverse-square blocks. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The numerator of the primitive-conductor energy is a nonnegative share
of the full interval variance. The lower bound retains the exact residue. -/
theorem centeredResiduePacket_prefix_bounds (D t : ℕ) (hs : Squarefree D) (hD : 1 < D) :
    -residuePrefixTriangle D t / (2 * (D : ℝ)) ≤
        ∑ n ∈ Finset.range t, centeredResiduePacket D n ∧
      (∑ n ∈ Finset.range t, centeredResiduePacket D n) ≤ 0 := by
  let U (d : ℕ) : ℝ := ∑ e ∈ d.divisors, (ArithmeticFunction.moebius (d / e) : ℝ) *
    residuePrefixTriangle e t
  have pos (d : ℕ) (hd : d ∈ D.divisors) : 0 ≤ U d := by
    have hd0 := Nat.pos_of_mem_divisors hd
    by_cases h1 : d = 1
    · subst d
      simp [U, residuePrefixTriangle, Nat.mod_one]
    have hd1 : 1 < d := by omega
    have hdS : Squarefree d := hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    have hh : (∑ n ∈ Finset.range t, centeredResiduePacket d n) ≤ 0 := by
      rw [centeredResiduePacket_prefix_ramanujan_gram d t hd1]
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (ramanujan_double_gram_nonneg d t hdS)) (by positivity)
    rw [centeredResiduePacket_prefix d t hd1] at hh
    change -(U d) / (2 * (d : ℝ)) ≤ 0 at hh
    have hz := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mp hh
    linarith
  have hd0 : 0 < D := by omega
  have hmem : D ∈ D.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, hd0.ne'⟩
  have hsum := (mobius_inversion U (fun d => residuePrefixTriangle d t)).mpr
    (fun _ _ => rfl) D hd0
  have hle : U D ≤ residuePrefixTriangle D t := by
    rw [← hsum]
    exact Finset.single_le_sum pos hmem
  rw [centeredResiduePacket_prefix D t hD]
  change -residuePrefixTriangle D t / (2 * (D : ℝ)) ≤ -(U D) / (2 * (D : ℝ)) ∧
    -(U D) / (2 * (D : ℝ)) ≤ 0
  exact ⟨div_le_div_of_nonneg_right (neg_le_neg hle) (by positivity),
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pos D hmem)) (by positivity)⟩

private theorem centeredResiduePacket_prefix_dvd (D t : ℕ) (hD : 1 < D) (ht : D ∣ t) :
    (∑ n ∈ Finset.range t, centeredResiduePacket D n) = 0 := by
  rw [centeredResiduePacket_prefix D t hD]
  have hz : (∑ d ∈ D.divisors, (ArithmeticFunction.moebius (D / d) : ℝ) *
      residuePrefixTriangle d t) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdt := (Nat.dvd_of_mem_divisors hd).trans ht
    simp [residuePrefixTriangle, Nat.mod_eq_zero_of_dvd hdt]
  rw [hz]
  simp

/-- Signed Abel estimate for each primitive interaction, in every squarefree order. -/
theorem weighted_centeredResiduePacket_block (D A t : ℕ) (hs : Squarefree D) (hD : 1 < D)
    (hA : D ∣ A) (hB : D ∣ A + t) (w : ℕ → ℝ) (hw : Antitone w) :
    -(D : ℝ) / 8 * (w A - w (A + t)) ≤
        ∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k) ∧
      (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k)) ≤ 0 := by
  let F (k : ℕ) := ∑ n ∈ Finset.range k, centeredResiduePacket D n
  have hstep (k : ℕ) : F (k + 1) - F k = centeredResiduePacket D k := by
    simp [F, Finset.sum_range_succ]
  have hAb : F A = 0 := centeredResiduePacket_prefix_dvd D A hD hA
  have hBb : F (A + t) = 0 := centeredResiduePacket_prefix_dvd D (A + t) hD hB
  have he : (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k)) =
      ∑ k ∈ Finset.range t, F (A + k + 1) * (w (A + k) - w (A + k + 1)) := by
    simp only [← hstep]
    rw [QCRTPairCarryBlocks.summation_by_parts, hAb, hBb]
    ring
  rw [he]
  have hdec (k : ℕ) : 0 ≤ w (A + k) - w (A + k + 1) := sub_nonneg.mpr (hw (by omega))
  have hLo (u : ℕ) : -(D : ℝ) / 8 ≤ F u := by
    apply le_trans _ (centeredResiduePacket_prefix_bounds D u hs hD).1
    have hp : (0 : ℝ) < 2 * D := by positivity
    apply (le_div_iff₀ hp).mpr
    dsimp only [residuePrefixTriangle]
    nlinarith [sq_nonneg ((D : ℝ) - 2 * ((u % D : ℕ) : ℝ))]
  constructor
  · rw [← QCRTPairCarryBlocks.sum_decrements w A t, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hLo _) (hdec k)
  · exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg
      (centeredResiduePacket_prefix_bounds D _ hs hD).2 (hdec k)

/-- The actual inverse-square weights on a block of complete periods. -/
theorem inverseSquare_centeredResiduePacket_block (D A t : ℕ) (hs : Squarefree D)
    (hD : 1 < D) (hpos : 0 < A) (hA : D ∣ A) (hB : D ∣ A + t) :
    -(D : ℝ) / 8 * (1 / (A : ℝ) ^ 2 - 1 / ((A + t : ℕ) : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) / ((A + k : ℕ) : ℝ) ^ 2 ∧
      (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) / ((A + k : ℕ) : ℝ) ^ 2) ≤ 0 := by
  let w (j : ℕ) : ℝ := 1 / (max (1 : ℝ) (j : ℝ)) ^ 2
  have hw : Antitone w := by
    intro i j hij
    have hi : 0 < max (1 : ℝ) (i : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    apply one_div_le_one_div_of_le (sq_pos_of_pos hi)
    exact pow_le_pow_left₀ hi.le (max_le_max_left 1 (by exact_mod_cast hij)) 2
  have hW (k : ℕ) : w (A + k) = 1 / ((A + k : ℕ) : ℝ) ^ 2 := by
    have hk : (1 : ℝ) ≤ ((A + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ A + k by omega)
    simp only [w, max_eq_right hk]
  have hWA : w A = 1 / (A : ℝ) ^ 2 := by simpa only [Nat.add_zero] using hW 0
  simpa only [hW, hWA, mul_one_div] using
    weighted_centeredResiduePacket_block D A t hs hD hA hB w hw

/-- No alignment with the modulus is required. The bound depends only on
the starting site and weights, uniformly over all squarefree conductors. -/
theorem weighted_centeredResiduePacket_incomplete (D A t : ℕ) (hs : Squarefree D)
    (hD : 1 < D) (w : ℕ → ℝ) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) :
    -((A : ℝ) * w A + ∑ k ∈ Finset.range t, w (A + k)) / 2 ≤
        ∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k) ∧
      (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k)) ≤
        (A : ℝ) * w A / 2 := by
  let F (u : ℕ) := ∑ n ∈ Finset.range u, centeredResiduePacket D n
  have hstep (k : ℕ) : F (k + 1) - F k = centeredResiduePacket D k := by
    simp [F, Finset.sum_range_succ]
  have lower (u : ℕ) : -(u : ℝ) / 2 ≤ F u := by
    apply le_trans _ (centeredResiduePacket_prefix_bounds D u hs hD).1
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D)).mpr
    have hr : 0 ≤ ((u % D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr' : ((u % D : ℕ) : ℝ) ≤ u := by exact_mod_cast Nat.mod_le u D
    have h1 := mul_le_mul_of_nonneg_right hr' (Nat.cast_nonneg D (α := ℝ))
    dsimp only [residuePrefixTriangle]
    nlinarith [sq_nonneg ((u % D : ℕ) : ℝ)]
  have upper (u : ℕ) : F u ≤ 0 := (centeredResiduePacket_prefix_bounds D u hs hD).2
  let dw (k : ℕ) := w (A + k) - w (A + k + 1)
  have hdec (k : ℕ) : 0 ≤ dw k := sub_nonneg.mpr (hw (by omega))
  have linearStep (k : ℕ) : ((A + k + 1 : ℕ) : ℝ) - ((A + k : ℕ) : ℝ) = 1 := by
    push_cast
    ring
  have hlin := QCRTPairCarryBlocks.summation_by_parts (fun n : ℕ => (n : ℝ)) w A t
  simp only [linearStep, one_mul] at hlin
  change _ = _ - _ + ∑ k ∈ Finset.range t, ((A + k + 1 : ℕ) : ℝ) * dw k at hlin
  have hsum : -(∑ k ∈ Finset.range t, ((A + k + 1 : ℕ) : ℝ) * dw k) / 2 ≤
      ∑ k ∈ Finset.range t, F (A + k + 1) * dw k := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro k _
    calc
      _ = (-((A + k + 1 : ℕ) : ℝ) / 2) * dw k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (lower _) (hdec k)
  have hsum' : (∑ k ∈ Finset.range t, F (A + k + 1) * dw k) ≤ 0 :=
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg (upper _) (hdec k)
  have hAb := mul_le_mul_of_nonneg_right (lower A) (hw0 A)
  have hBb := mul_le_mul_of_nonneg_right (lower (A + t)) (hw0 (A + t))
  have hAu := mul_nonpos_of_nonpos_of_nonneg (upper A) (hw0 A)
  have hBu := mul_nonpos_of_nonpos_of_nonneg (upper (A + t)) (hw0 (A + t))
  have he : (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) * w (A + k)) =
      F (A + t) * w (A + t) - F A * w A +
        ∑ k ∈ Finset.range t, F (A + k + 1) * dw k := by
    simp only [← hstep]
    exact QCRTPairCarryBlocks.summation_by_parts F w A t
  rw [he]
  constructor <;> linarith

/-- Actual inverse-square weights on an arbitrary block of the positive integers. -/
theorem inverseSquare_centeredResiduePacket_incomplete (D A t : ℕ) (hs : Squarefree D)
    (hD : 1 < D) (hpos : 0 < A) :
    -(1 / (A : ℝ) + ∑ k ∈ Finset.range t, 1 / ((A + k : ℕ) : ℝ) ^ 2) / 2 ≤
        ∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) / ((A + k : ℕ) : ℝ) ^ 2 ∧
      (∑ k ∈ Finset.range t, centeredResiduePacket D (A + k) / ((A + k : ℕ) : ℝ) ^ 2) ≤
        (1 / (A : ℝ)) / 2 := by
  let w (j : ℕ) : ℝ := 1 / (max (1 : ℝ) (j : ℝ)) ^ 2
  have hw : Antitone w := by
    intro i j hij
    have hi : 0 < max (1 : ℝ) (i : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    apply one_div_le_one_div_of_le (sq_pos_of_pos hi)
    exact pow_le_pow_left₀ hi.le (max_le_max_left 1 (by exact_mod_cast hij)) 2
  have hW (k : ℕ) : w (A + k) = 1 / ((A + k : ℕ) : ℝ) ^ 2 := by
    have hk : (1 : ℝ) ≤ ((A + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ A + k by omega)
    simp only [w, max_eq_right hk]
  have hWA : w A = 1 / (A : ℝ) ^ 2 := by simpa only [Nat.add_zero] using hW 0
  have hp : (A : ℝ) / (A : ℝ) ^ 2 = 1 / (A : ℝ) := by
    have hh : (A : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp [hh]
    <;> ring
  simpa only [hW, hWA, mul_one_div, hp] using
    weighted_centeredResiduePacket_incomplete D A t hs hD w hw (fun j => by dsimp [w]; positivity)

end RiemannResearch.RH.Pareto
