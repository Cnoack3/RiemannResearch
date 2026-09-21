/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoCoprimeDefectVariational

/-!
# The necessary reciprocal head and an exact admissible normalization

Source: continuation of the user-provided Pareto dyadic handoff, 2026-09-21.
The existing coprime certificate excludes every odd-moment-one witness whose
reciprocal coefficient head is zero, including growing dyadic repair families.
Changing only the modulus-two coefficient imposes the correct nonzero head
without changing the odd moment or the existence of small-energy witnesses.
No small-energy family, or unconditional RH, is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The reciprocal coefficient head, before the first coordinate is removed. -/
def oddMomentHead (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, c i / ((i.val + 2 : ℕ) : ℝ)

/-- The original odd reciprocal-square moment. -/
def oddMomentValue (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, if 2 ∣ i.val + 2 then 0 else c i / ((i.val + 2 : ℕ) : ℝ)^2

def oddHeadConstant : ℝ := 1 + ‖infiniteCoprimeCertificate 2‖^2 / 2

theorem oddHeadConstant_pos : 0 < oddHeadConstant := by
  unfold oddHeadConstant
  nlinarith [sq_nonneg ‖infiniteCoprimeCertificate 2‖]

/-- Exact pairing with the fixed infinite coprime certificate. -/
theorem oddMomentHead_certificate_identity (n : ℕ) (c : Fin n → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
      (infiniteCoprimeCertificate 2) =
      oddMomentHead n c - oddHeadConstant * oddMomentValue n c := by
  have h := coprimeDefect_pairing_explicit n c
  rw [coprimeDefectSource_eq_sub_observed] at h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, cross] at h
  rw [← inner_synthesis_left] at h
  have hh : (∑ i, c i * reciprocalSource n i) = oddMomentHead n c := by
    simp only [reciprocalSource, oddMomentHead, div_eq_mul_inv, one_mul]
  rw [hh] at h
  change oddMomentHead n c - _ = oddHeadConstant * oddMomentValue n c at h
  linarith

/-- Quantitative necessary head condition, with the complete tail norm. -/
theorem oddMomentHead_mismatch_le (n : ℕ) (c : Fin n → ℝ) :
    |oddMomentHead n c - oddHeadConstant * oddMomentValue n c| ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ *
        ‖infiniteCoprimeCertificate 2‖ := by
  rw [← oddMomentHead_certificate_identity]
  simpa only [Real.norm_eq_abs] using
    (norm_inner_le_norm (𝕜 := ℝ)
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
      (infiniteCoprimeCertificate 2))

theorem oddMomentHead_mismatch_sq_le (n : ℕ) (c : Fin n → ℝ) :
    (oddMomentHead n c - oddHeadConstant * oddMomentValue n c)^2 ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 *
        ‖infiniteCoprimeCertificate 2‖^2 := by
  have h := (sq_le_sq₀ (abs_nonneg
    (oddMomentHead n c - oddHeadConstant * oddMomentValue n c))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (oddMomentHead_mismatch_le n c)
  simpa only [sq_abs, mul_pow] using h

theorem coprimeCertificate_two_observation_zero :
    inner ℝ (tailAtom 0) (infiniteCoprimeCertificate 2) = 1 / 2 := by
  have h := oddMomentHead_certificate_identity 1 (fun _ => (1 : ℝ))
  norm_num [oddMomentHead, oddMomentValue, Fintype.linearCombination_apply] at h ⊢
  exact h

theorem coprimeCertificate_two_norm_pos : 0 < ‖infiniteCoprimeCertificate 2‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have h := coprimeCertificate_two_observation_zero
  rw [hz, inner_zero_right] at h
  norm_num at h

/-- No exactly head-cancelling signed family can have arbitrarily small energy. -/
theorem head_zero_oddMoment_energy_lower (n : ℕ) (c : Fin n → ℝ)
    (hm : oddMomentValue n c = 1) (hh : oddMomentHead n c = 0) :
    oddHeadConstant^2 / ‖infiniteCoprimeCertificate 2‖^2 ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 := by
  apply (div_le_iff₀ (sq_pos_of_pos coprimeCertificate_two_norm_pos)).mpr
  have h := oddMomentHead_mismatch_sq_le n c
  simpa only [hm, hh, mul_one, zero_sub, neg_sq] using h

theorem head_zero_oddMoment_floor_pos :
    0 < oddHeadConstant^2 / ‖infiniteCoprimeCertificate 2‖^2 :=
  div_pos (sq_pos_of_pos oddHeadConstant_pos)
    (sq_pos_of_pos coprimeCertificate_two_norm_pos)

theorem oddMomentHead_add (n : ℕ) (c d : Fin n → ℝ) :
    oddMomentHead n (c + d) = oddMomentHead n c + oddMomentHead n d := by
  simp [oddMomentHead, Pi.add_apply, add_div, Finset.sum_add_distrib]

theorem oddMomentValue_add (n : ℕ) (c d : Fin n → ℝ) :
    oddMomentValue n (c + d) = oddMomentValue n c + oddMomentValue n d := by
  unfold oddMomentValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  split_ifs <;> simp [add_div]

theorem oddMomentHead_single_zero (n : ℕ) (hn : 0 < n) (r : ℝ) :
    oddMomentHead n (Pi.single (⟨0, hn⟩ : Fin n) r) = r / 2 := by
  classical
  unfold oddMomentHead
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem oddMomentValue_single_zero (n : ℕ) (hn : 0 < n) (r : ℝ) :
    oddMomentValue n (Pi.single (⟨0, hn⟩ : Fin n) r) = 0 := by
  classical
  unfold oddMomentValue
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = (⟨0, hn⟩ : Fin n)
  · subst i
    simp
  · simp [hi]

/-- The only changed coefficient is the even modulus two. -/
def normalizeOddHead (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) : Fin n → ℝ :=
  c + Pi.single (⟨0, hn⟩ : Fin n)
    (2 * (oddHeadConstant * oddMomentValue n c - oddMomentHead n c))

theorem normalizeOddHead_moment (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    oddMomentValue n (normalizeOddHead n hn c) = oddMomentValue n c := by
  rw [normalizeOddHead, oddMomentValue_add, oddMomentValue_single_zero, add_zero]

theorem normalizeOddHead_head (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    oddMomentHead n (normalizeOddHead n hn c) =
      oddHeadConstant * oddMomentValue n c := by
  rw [normalizeOddHead, oddMomentHead_add, oddMomentHead_single_zero]
  ring

theorem normalizeOddHead_synthesis (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (normalizeOddHead n hn c) =
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c -
      (2 * inner ℝ
        (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
        (infiniteCoprimeCertificate 2)) • tailAtom 0 := by
  classical
  have hs : Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (Pi.single (⟨0, hn⟩ : Fin n)
        (2 * (oddHeadConstant * oddMomentValue n c - oddMomentHead n c))) =
      (2 * (oddHeadConstant * oddMomentValue n c - oddMomentHead n c)) •
        tailAtom 0 := by
    simp [Fintype.linearCombination_apply]
  rw [normalizeOddHead, map_add, hs, oddMomentHead_certificate_identity]
  have he : 2 * (oddHeadConstant * oddMomentValue n c - oddMomentHead n c) =
      -(2 * (oddMomentHead n c - oddHeadConstant * oddMomentValue n c)) := by ring
  rw [he, neg_smul]
  rfl

/-- Exact full signed energy of the normalization, retaining its cross term. -/
theorem normalizeOddHead_energy_exact (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (normalizeOddHead n hn c)‖^2 =
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 -
      4 * inner ℝ
        (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
        (infiniteCoprimeCertificate 2) *
      inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
        (tailAtom 0) +
      4 * (inner ℝ
        (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
        (infiniteCoprimeCertificate 2))^2 * ‖tailAtom 0‖^2 := by
  rw [normalizeOddHead_synthesis, norm_sub_sq_real, inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem normalizeOddHead_orthogonal (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    inner ℝ
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (normalizeOddHead n hn c)) (infiniteCoprimeCertificate 2) = 0 := by
  rw [oddMomentHead_certificate_identity, normalizeOddHead_head,
    normalizeOddHead_moment, sub_self]

theorem normalizeOddHead_norm_le (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (normalizeOddHead n hn c)‖ ≤
      (1 + 2 * ‖infiniteCoprimeCertificate 2‖ * ‖tailAtom 0‖) *
        ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ := by
  rw [normalizeOddHead_synthesis]
  calc
    _ ≤ ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ +
        ‖(2 * inner ℝ
          (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
          (infiniteCoprimeCertificate 2)) • tailAtom 0‖ := norm_sub_le _ _
    _ = ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ +
        2 * ‖inner ℝ
          (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
          (infiniteCoprimeCertificate 2)‖ * ‖tailAtom 0‖ := by
      rw [norm_smul, norm_mul]
      norm_num
    _ ≤ ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ +
        2 * (‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ *
          ‖infiniteCoprimeCertificate 2‖) * ‖tailAtom 0‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = _ := by ring

theorem oddMoment_small_tail_iff_normalized_head :
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      oddMomentValue n c = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      oddMomentValue n c = 1 ∧ oddMomentHead n c = oddHeadConstant ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε) := by
  constructor
  · intro h ε hε
    let A : ℝ := 1 + 2 * ‖infiniteCoprimeCertificate 2‖ * ‖tailAtom 0‖
    have hA : 0 < A := by dsimp [A]; positivity
    obtain ⟨n,c,hm,he⟩ := h (ε / A^2) (div_pos hε (sq_pos_of_pos hA))
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      simp [oddMomentValue] at hm
    refine ⟨n, normalizeOddHead n hn c, ?_, ?_, ?_⟩
    · rw [normalizeOddHead_moment, hm]
    · rw [normalizeOddHead_head, hm, mul_one]
    · have hb := normalizeOddHead_norm_le n hn c
      change ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (normalizeOddHead n hn c)‖ ≤ A *
          ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ at hb
      have hs := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hA.le (norm_nonneg _))).mpr hb
      rw [mul_pow] at hs
      have hh := (lt_div_iff₀ (sq_pos_of_pos hA)).mp he
      nlinarith
  · intro h ε hε
    obtain ⟨n,c,hm,_,he⟩ := h ε hε
    exact ⟨n,c,hm,he⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
