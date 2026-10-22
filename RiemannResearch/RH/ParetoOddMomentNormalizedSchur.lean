/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoOddMomentParity
import RiemannResearch.RH.ParetoOddMomentHeadNormalization

/-!
# Exact reciprocal-head normalization after full even optimization

Source: continuation of the user-provided Pareto head-normalization handoff,
2026-09-21. Fixed signed odd coefficients are screened against the complete
finite even dictionary, then corrected in the projected certificate direction.
The additional energy is an exact nonnegative rank-one term. An affine energy
completion proves uniqueness among all normalized even corrections, and a
uniform factor proves equivalence with the original small-tail problem.
No witness sequence with vanishing energy is constructed; the RH endpoint
retains that explicit, Open arithmetic premise.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Projection of the fixed certificate onto the complete finite even dictionary. -/
def evenHeadRepresenter (n : ℕ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ (evenTailAtom n)
    (inverseCoeff (evenTailAtom_independent n) (infiniteCoprimeCertificate 2))

def evenHeadEnergy (n : ℕ) : ℝ := ‖evenHeadRepresenter n‖^2

theorem evenHeadRepresenter_observation (n : ℕ) (i : EvenTailIndex n) :
    inner ℝ (evenTailAtom n i) (evenHeadRepresenter n) =
      inner ℝ (evenTailAtom n i) (infiniteCoprimeCertificate 2) :=
  inverseCoeff_normal (evenTailAtom_independent n) (infiniteCoprimeCertificate 2) i

theorem evenHeadRepresenter_synthesis_observation (n : ℕ) (a : EvenTailIndex n → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ (evenTailAtom n) a) (evenHeadRepresenter n) =
      inner ℝ (Fintype.linearCombination ℝ (evenTailAtom n) a)
        (infiniteCoprimeCertificate 2) := by
  simp only [inner_synthesis_left, evenHeadRepresenter_observation]

theorem evenHeadRepresenter_inner_certificate (n : ℕ) :
    inner ℝ (evenHeadRepresenter n) (infiniteCoprimeCertificate 2) =
      evenHeadEnergy n := by
  change inner ℝ (Fintype.linearCombination ℝ (evenTailAtom n)
    (inverseCoeff (evenTailAtom_independent n) (infiniteCoprimeCertificate 2)))
    (infiniteCoprimeCertificate 2) = evenHeadEnergy n
  rw [← evenHeadRepresenter_synthesis_observation]
  exact real_inner_self_eq_norm_sq _

theorem evenHeadEnergy_pos (n : ℕ) (hn : 0 < n) : 0 < evenHeadEnergy n := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  let i : EvenTailIndex n := ⟨⟨0, hn⟩, by simp⟩
  have h := evenHeadRepresenter_observation n i
  rw [hz, inner_zero_right] at h
  change 0 = inner ℝ (tailAtom 0) (infiniteCoprimeCertificate 2) at h
  rw [coprimeCertificate_two_observation_zero] at h
  norm_num at h

theorem screenedOdd_synthesis_even_orthogonal (n : ℕ)
    (b : OddTailIndex n → ℝ) (a : EvenTailIndex n → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
      (Fintype.linearCombination ℝ (evenTailAtom n) a) = 0 := by
  rw [screenedOdd_synthesis]
  exact residual_orthogonal (evenTailAtom_independent n)
    (Fintype.linearCombination ℝ (oddTailAtom n) b) a

def screenedOddHeadMismatch (n : ℕ) (b : OddTailIndex n → ℝ) : ℝ :=
  inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
    (infiniteCoprimeCertificate 2)

/-- Unique even correction subject to exact certificate orthogonality. -/
def normalizedEvenTailCoefficients (n : ℕ) (b : OddTailIndex n → ℝ) :
    EvenTailIndex n → ℝ :=
  optimalEvenTailCoefficients n b -
    (screenedOddHeadMismatch n b / evenHeadEnergy n) •
      inverseCoeff (evenTailAtom_independent n) (infiniteCoprimeCertificate 2)

theorem normalizedEvenTail_synthesis (n : ℕ) (b : OddTailIndex n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b) =
    Fintype.linearCombination ℝ (screenedOddTailAtom n) b -
      (screenedOddHeadMismatch n b / evenHeadEnergy n) • evenHeadRepresenter n := by
  rw [parityTailCoefficients_synthesis, normalizedEvenTailCoefficients, map_sub,
    map_smul, optimalEvenTailCoefficients, map_neg, screenedOdd_synthesis]
  unfold evenHeadRepresenter
  abel

theorem normalizedEvenTail_orthogonal (n : ℕ) (hn : 0 < n)
    (b : OddTailIndex n → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b))
      (infiniteCoprimeCertificate 2) = 0 := by
  rw [normalizedEvenTail_synthesis, inner_sub_left, real_inner_smul_left,
    evenHeadRepresenter_inner_certificate]
  change screenedOddHeadMismatch n b -
    screenedOddHeadMismatch n b / evenHeadEnergy n * evenHeadEnergy n = 0
  field_simp [ne_of_gt (evenHeadEnergy_pos n hn)]
  <;> ring

theorem normalizedEvenTail_moment (n : ℕ) (b : OddTailIndex n → ℝ) :
    oddMomentValue n (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b) =
      ∑ j : OddTailIndex n, b j / ((j.val.val + 2 : ℕ) : ℝ)^2 :=
  parityTailCoefficients_moment n _ b

theorem normalizedEvenTail_head (n : ℕ) (hn : 0 < n) (b : OddTailIndex n → ℝ) :
    oddMomentHead n (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b) =
      oddHeadConstant * (∑ j : OddTailIndex n, b j / ((j.val.val + 2 : ℕ) : ℝ)^2) := by
  have h := normalizedEvenTail_orthogonal n hn b
  rw [oddMomentHead_certificate_identity, normalizedEvenTail_moment] at h
  exact sub_eq_zero.mp h

/-- Exact positive rank-one addition to the full odd Schur energy. -/
theorem normalizedEvenTail_energy (n : ℕ) (hn : 0 < n) (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 =
    ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 +
      (screenedOddHeadMismatch n b)^2 / evenHeadEnergy n := by
  rw [normalizedEvenTail_synthesis, norm_sub_sq_real, inner_smul_right]
  have h := screenedOdd_synthesis_even_orthogonal n b
    (inverseCoeff (evenTailAtom_independent n) (infiniteCoprimeCertificate 2))
  change inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
    (evenHeadRepresenter n) = 0 at h
  rw [h, mul_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hd : (screenedOddHeadMismatch n b / evenHeadEnergy n)^2 *
      evenHeadEnergy n = (screenedOddHeadMismatch n b)^2 / evenHeadEnergy n := by
    field_simp [ne_of_gt (evenHeadEnergy_pos n hn)]
    <;> ring
  dsimp [evenHeadEnergy] at hd ⊢
  nlinarith [hd]

/-- Normalization adds no energy exactly when the screened witness already has the correct head. -/
theorem normalizedEvenTail_energy_eq_iff (n : ℕ) (hn : 0 < n)
    (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 =
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 ↔
    screenedOddHeadMismatch n b = 0 := by
  rw [normalizedEvenTail_energy n hn]
  have hK := evenHeadEnergy_pos n hn
  constructor
  · intro h
    have hz : (screenedOddHeadMismatch n b)^2 / evenHeadEnergy n = 0 := by linarith
    have hs : (screenedOddHeadMismatch n b)^2 = 0 := by
      exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hK)
    nlinarith [sq_nonneg (screenedOddHeadMismatch n b)]
  · intro h
    simp [h]

/-- Exact affine completion against every other normalized even correction. -/
theorem normalizedEvenTail_energy_completion (n : ℕ) (hn : 0 < n)
    (a : EvenTailIndex n → ℝ) (b : OddTailIndex n → ℝ)
    (ha : inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)) (infiniteCoprimeCertificate 2) = 0) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)‖^2 =
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 +
    ‖Fintype.linearCombination ℝ (evenTailAtom n)
      (a - normalizedEvenTailCoefficients n b)‖^2 := by
  let u := Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
    (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)
  let w := Fintype.linearCombination ℝ (evenTailAtom n)
    (a - normalizedEvenTailCoefficients n b)
  have he : Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b) = u + w := by
    dsimp [u, w]
    rw [parityTailCoefficients_synthesis, parityTailCoefficients_synthesis, map_sub]
    abel
  have hwz : inner ℝ w (infiniteCoprimeCertificate 2) = 0 := by
    rw [he, inner_add_left] at ha
    have hu := normalizedEvenTail_orthogonal n hn b
    change inner ℝ u (infiniteCoprimeCertificate 2) = 0 at hu
    linarith
  have hwp : inner ℝ w (evenHeadRepresenter n) = 0 := by
    rw [show inner ℝ w (evenHeadRepresenter n) = inner ℝ w
      (infiniteCoprimeCertificate 2) from evenHeadRepresenter_synthesis_observation n _]
    exact hwz
  have huw : inner ℝ u w = 0 := by
    dsimp [u]
    rw [normalizedEvenTail_synthesis, inner_sub_left, real_inner_smul_left]
    have hx := screenedOdd_synthesis_even_orthogonal n b
      (a - normalizedEvenTailCoefficients n b)
    change inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b) w = 0 at hx
    have hwp' : inner ℝ (evenHeadRepresenter n) w = 0 :=
      (real_inner_comm (evenHeadRepresenter n) w).symm.trans hwp
    rw [hx, hwp']
    ring
  rw [he, norm_add_sq_real, huw]
  change ‖u‖^2 + 2 * 0 + ‖w‖^2 = ‖u‖^2 + ‖w‖^2
  ring

/-- Uniqueness holds for actual signed even coefficient arrays. -/
theorem normalizedEvenTail_minimizer_unique (n : ℕ) (hn : 0 < n)
    (a : EvenTailIndex n → ℝ) (b : OddTailIndex n → ℝ)
    (ha : inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)) (infiniteCoprimeCertificate 2) = 0)
    (he : ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)‖^2 =
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2) :
    a = normalizedEvenTailCoefficients n b := by
  have h := normalizedEvenTail_energy_completion n hn a b ha
  have hz : Fintype.linearCombination ℝ (evenTailAtom n)
      (a - normalizedEvenTailCoefficients n b) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (Fintype.linearCombination ℝ (evenTailAtom n)
      (a - normalizedEvenTailCoefficients n b))]
  apply sub_eq_zero.mp
  apply (evenTailAtom_independent n).fintypeLinearCombination_injective
  simpa only [map_zero] using hz

/-- Pythagorean decomposition of the fixed certificate under even screening. -/
theorem evenHeadEnergy_pythagoras (n : ℕ) :
    ‖infiniteCoprimeCertificate 2 - evenHeadRepresenter n‖^2 +
      evenHeadEnergy n = ‖infiniteCoprimeCertificate 2‖^2 := by
  rw [norm_sub_sq_real, real_inner_comm,
    evenHeadRepresenter_inner_certificate]
  unfold evenHeadEnergy
  ring

/-- Exact control of the rank-one correction by the screened certificate. -/
theorem screenedOddHeadMismatch_sq_le (n : ℕ) (b : OddTailIndex n → ℝ) :
    (screenedOddHeadMismatch n b)^2 ≤
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 *
        ‖infiniteCoprimeCertificate 2 - evenHeadRepresenter n‖^2 := by
  have hx := screenedOdd_synthesis_even_orthogonal n b
    (inverseCoeff (evenTailAtom_independent n) (infiniteCoprimeCertificate 2))
  change inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
    (evenHeadRepresenter n) = 0 at hx
  have hi : inner ℝ (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
      (infiniteCoprimeCertificate 2 - evenHeadRepresenter n) =
      screenedOddHeadMismatch n b := by
    rw [inner_sub_right, hx, sub_zero]
    rfl
  have h := norm_inner_le_norm (𝕜 := ℝ)
    (Fintype.linearCombination ℝ (screenedOddTailAtom n) b)
    (infiniteCoprimeCertificate 2 - evenHeadRepresenter n)
  rw [hi, Real.norm_eq_abs] at h
  have hs := (sq_le_sq₀ (abs_nonneg (screenedOddHeadMismatch n b))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow] using hs

/-- Screening first yields a sharper uniform normalization cost. -/
theorem normalizedEvenTail_energy_le (n : ℕ) (hn : 0 < n)
    (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 ≤
    (‖infiniteCoprimeCertificate 2‖^2 / evenHeadEnergy n) *
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 := by
  rw [normalizedEvenTail_energy n hn]
  have hK := evenHeadEnergy_pos n hn
  have hb := screenedOddHeadMismatch_sq_le n b
  have hp := evenHeadEnergy_pythagoras n
  have hp' := congrArg (fun r : ℝ =>
    r * ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2) hp
  have hd : (screenedOddHeadMismatch n b)^2 / evenHeadEnergy n *
      evenHeadEnergy n = (screenedOddHeadMismatch n b)^2 :=
    div_mul_cancel₀ _ (ne_of_gt hK)
  have hr : (‖infiniteCoprimeCertificate 2‖^2 / evenHeadEnergy n) *
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 * evenHeadEnergy n =
      ‖infiniteCoprimeCertificate 2‖^2 *
        ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 := by
    field_simp [ne_of_gt hK]
  by_contra! hbad
  have hm := mul_lt_mul_of_pos_right hbad hK
  nlinarith [hd, hr, hm, hp']

/-- The modulus-two observation prevents the normalization denominator from collapsing. -/
theorem evenHeadEnergy_uniform_lower (n : ℕ) (hn : 0 < n) :
    1 ≤ 4 * ‖tailAtom 0‖^2 * evenHeadEnergy n := by
  let i : EvenTailIndex n := ⟨⟨0, hn⟩, by simp⟩
  have hi := evenHeadRepresenter_observation n i
  change inner ℝ (tailAtom 0) (evenHeadRepresenter n) =
    inner ℝ (tailAtom 0) (infiniteCoprimeCertificate 2) at hi
  rw [coprimeCertificate_two_observation_zero] at hi
  have h := norm_inner_le_norm (𝕜 := ℝ) (tailAtom 0) (evenHeadRepresenter n)
  rw [hi] at h
  norm_num at h
  have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow] at hs
  change 1 ≤ 4 * ‖tailAtom 0‖^2 * ‖evenHeadRepresenter n‖^2
  nlinarith

/-- The sharp finite normalization factor has a uniform arithmetic upper bound. -/
theorem evenHeadEnergy_factor_le (n : ℕ) (hn : 0 < n) :
    ‖infiniteCoprimeCertificate 2‖^2 / evenHeadEnergy n ≤
      4 * ‖tailAtom 0‖^2 * ‖infiniteCoprimeCertificate 2‖^2 := by
  apply (div_le_iff₀ (evenHeadEnergy_pos n hn)).mpr
  have h := mul_le_mul_of_nonneg_right (evenHeadEnergy_uniform_lower n hn)
    (sq_nonneg ‖infiniteCoprimeCertificate 2‖)
  nlinarith [h]

/-- Full normalized even optimization has a dictionary-independent energy cost. -/
theorem normalizedEvenTail_energy_le_uniform (n : ℕ) (hn : 0 < n)
    (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 ≤
    (4 * ‖tailAtom 0‖^2 * ‖infiniteCoprimeCertificate 2‖^2) *
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 := by
  exact (normalizedEvenTail_energy_le n hn b).trans
    (mul_le_mul_of_nonneg_right (evenHeadEnergy_factor_le n hn) (sq_nonneg _))

theorem normalizedEvenTail_uniform_factor_ge_one :
    1 ≤ 4 * ‖tailAtom 0‖^2 * ‖infiniteCoprimeCertificate 2‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (tailAtom 0) (infiniteCoprimeCertificate 2)
  rw [coprimeCertificate_two_observation_zero] at h
  norm_num at h
  have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow] at hs
  nlinarith

/-- Exact normalization and optimal even correction preserve the original small-tail problem. -/
theorem oddMoment_small_tail_iff_normalizedEven :
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      oddMomentValue n c = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (b : OddTailIndex n → ℝ),
      (∑ j : OddTailIndex n, b j / ((j.val.val + 2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 < ε) := by
  constructor
  · intro h ε hε
    have hs := oddMoment_small_tail_iff_screened.mp h
    let A : ℝ := 4 * ‖tailAtom 0‖^2 * ‖infiniteCoprimeCertificate 2‖^2
    have hA : 0 < A := by
      have h1 := normalizedEvenTail_uniform_factor_ge_one
      change 1 ≤ A at h1
      linarith
    obtain ⟨n, b, hb, he⟩ := hs (ε / A) (div_pos hε hA)
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      simp at hb
    refine ⟨n, b, hb, ?_⟩
    have hc := normalizedEvenTail_energy_le_uniform n hn b
    change ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 ≤
      A * ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 at hc
    have he' := (lt_div_iff₀ hA).mp he
    nlinarith
  · intro h ε hε
    obtain ⟨n, b, hb, he⟩ := h ε hε
    refine ⟨n, parityTailCoefficients n (normalizedEvenTailCoefficients n b) b, ?_, he⟩
    rw [normalizedEvenTail_moment, hb]

/-- CONDITIONAL RESEARCH REDUCTION: normalized Schur energy decay remains Open. -/
theorem riemannHypothesis_of_normalizedEven_small_tail
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (b : OddTailIndex n → ℝ),
      (∑ j : OddTailIndex n, b j / ((j.val.val + 2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (parityTailCoefficients n (normalizedEvenTailCoefficients n b) b)‖^2 < ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_oddMoment_small_tail (oddMoment_small_tail_iff_normalizedEven.mpr h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
