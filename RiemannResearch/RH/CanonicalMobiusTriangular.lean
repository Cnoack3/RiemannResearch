/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCesaro
import RiemannResearch.RH.MobiusReciprocalNonvanishing

/-!
# Triangular canonical Möbius coordinates and finite affine exhaustion

Source: Section 11 of the user-provided Pareto capacity handoff, for the
proposed structural target. The proof uses adjacent residue differences,
finite head injectivity, and the verified finite reciprocal-sum nonvanishing.
Every finite legal exact-head vector is expressed by a canonical signed
window with coefficient sum one. No asymptotic energy bound is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- Adjacent legal atoms with their common linear head cancelled. -/
def consecutiveResidueHilbert (n : ℕ) : ThresholdHilbert :=
  ((n + 2 : ℕ) : ℝ) • normalizedResidueHilbert (n + 2) (by omega) -
    ((n + 1 : ℕ) : ℝ) • normalizedResidueHilbert (n + 1) (by omega)

theorem consecutiveResidueHilbert_sequence (n j : ℕ) :
    hilbertSequence (consecutiveResidueHilbert n) j =
      ((n + 2 : ℕ) : ℝ) * residueFraction (n + 2) j -
      ((n + 1 : ℕ) : ℝ) * residueFraction (n + 1) j := by
  change hilbertSequenceLinear (consecutiveResidueHilbert n) j = _
  simp only [consecutiveResidueHilbert, map_sub, map_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change ((n + 2 : ℕ) : ℝ) * hilbertSequence (normalizedResidueHilbert (n+2) _) j -
    ((n + 1 : ℕ) : ℝ) * hilbertSequence (normalizedResidueHilbert (n+1) _) j = _
  rw [normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]

theorem consecutiveResidueHilbert_head_zero (n j : ℕ) (hj : j ≤ n) :
    hilbertSequence (consecutiveResidueHilbert n) j = 0 := by
  rw [consecutiveResidueHilbert_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt (by omega : j < n+2),
    Nat.mod_eq_of_lt (by omega : j < n+1)]
  have h1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem consecutiveResidueHilbert_diagonal (n : ℕ) :
    hilbertSequence (consecutiveResidueHilbert n) (n+1) = ((n+1 : ℕ) : ℝ) := by
  rw [consecutiveResidueHilbert_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt (by omega : n+1 < n+2), Nat.mod_self,
    Nat.cast_zero, zero_div, mul_zero, sub_zero]
  have h2 : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem canonicalMobiusHilbert_zero : canonicalMobiusHilbert 0 = 0 := by
  apply hilbertSequence_injective
  funext j
  rw [canonicalMobiusHilbert_sequence]
  cases j <;> simp [canonicalMobiusHead, mobiusReciprocalSum, hilbertSequence]

theorem canonicalMobiusHilbert_succ_sub (n : ℕ) :
    canonicalMobiusHilbert (n+1) - canonicalMobiusHilbert n =
      mobiusReciprocalSum (n+1) • consecutiveResidueHilbert n := by
  apply hilbertSequence_injective
  funext j
  change hilbertSequenceLinear (_ - _) j = hilbertSequenceLinear (_ • _) j
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change hilbertSequence (canonicalMobiusHilbert (n+1)) j -
    hilbertSequence (canonicalMobiusHilbert n) j =
    mobiusReciprocalSum (n+1) * hilbertSequence (consecutiveResidueHilbert n) j
  rw [canonicalMobiusHilbert_sequence, canonicalMobiusHilbert_sequence,
    consecutiveResidueHilbert_sequence]
  simp only [canonicalMobiusHead, Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1),
    mobiusReciprocalSum_succ]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem canonicalMobiusHilbert_eq_sum_steps (N : ℕ) :
    canonicalMobiusHilbert N =
      ∑ n ∈ Finset.range N, mobiusReciprocalSum (n+1) • consecutiveResidueHilbert n := by
  induction N with
  | zero => simp [canonicalMobiusHilbert_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h := canonicalMobiusHilbert_succ_sub N
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative
namespace CoefficientStabilization

def canonicalMobiusSpan (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (fun i : Fin M => canonicalMobiusHilbert (i.val + 1)))

theorem canonicalMobiusHilbert_mem_canonicalMobiusSpan (M n : ℕ) (hn : n ≤ M) :
    canonicalMobiusHilbert n ∈ canonicalMobiusSpan M := by
  cases n with
  | zero =>
    rw [canonicalMobiusHilbert_zero]
    exact (canonicalMobiusSpan M).zero_mem
  | succ n =>
    apply Submodule.subset_span
    exact ⟨⟨n, by omega⟩, rfl⟩

theorem consecutiveResidueHilbert_mem_canonicalMobiusSpan
    (M n : ℕ) (hn : n < M) :
    consecutiveResidueHilbert n ∈ canonicalMobiusSpan M := by
  have hd := (canonicalMobiusSpan M).sub_mem
    (canonicalMobiusHilbert_mem_canonicalMobiusSpan M (n + 1) (by omega))
    (canonicalMobiusHilbert_mem_canonicalMobiusSpan M n (by omega))
  rw [canonicalMobiusHilbert_succ_sub] at hd
  have hi := (canonicalMobiusSpan M).smul_mem (mobiusReciprocalSum (n + 1))⁻¹ hd
  simpa only [smul_smul, inv_mul_cancel₀ (mobiusReciprocalSum_ne_zero (N := n + 1) (by omega)), one_smul] using hi

theorem residueAtom_mem_canonicalMobiusSpan
    (M n : ℕ) : n < M → residueAtom n ∈ canonicalMobiusSpan M := by
  induction n with
  | zero =>
    intro hn
    have hz : normalizedResidueHilbert 1 (by omega) = 0 := by
      apply hilbertSequence_injective
      rw [normalizedResidueHilbert_sequence]
      funext j
      cases j <;> simp [residueFraction, hilbertSequence, Nat.mod_one]
    have hd := consecutiveResidueHilbert_mem_canonicalMobiusSpan M 0 hn
    norm_num only [consecutiveResidueHilbert, Nat.reduceAdd, Nat.cast_ofNat, one_smul] at hd
    rw [hz, sub_zero] at hd
    change (2 : ℝ) • residueAtom 0 ∈ canonicalMobiusSpan M at hd
    have hi := (canonicalMobiusSpan M).smul_mem (1 / 2 : ℝ) hd
    norm_num [smul_smul] at hi
    exact hi
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hd := consecutiveResidueHilbert_mem_canonicalMobiusSpan M (n + 1) hn
    change (((n + 3 : ℕ) : ℝ) • residueAtom (n + 1) -
      ((n + 2 : ℕ) : ℝ) • residueAtom n) ∈ canonicalMobiusSpan M at hd
    have hs := (canonicalMobiusSpan M).add_mem hd
      ((canonicalMobiusSpan M).smul_mem ((n + 2 : ℕ) : ℝ) hprev)
    rw [sub_add_cancel] at hs
    have hi := (canonicalMobiusSpan M).smul_mem (((n + 3 : ℕ) : ℝ))⁻¹ hs
    have hc : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

/-- The canonical family is a complete finite change of legal generators.
No asymptotic norm estimate is assumed. -/
theorem canonicalMobiusSpan_eq_finiteSpace
    (M : ℕ) :
    canonicalMobiusSpan M = finiteSpace M := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
      (by omega : i.val + 1 ≤ M) (canonicalMobiusHilbert_mem_finiteSpace (i.val + 1))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact residueAtom_mem_canonicalMobiusSpan M i.val i.isLt

end CoefficientStabilization

namespace CoefficientStabilization

theorem finiteSpace_succ_step_decomposition (M : ℕ)
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace (M + 1)) :
    ∃ y ∈ finiteSpace M, ∃ c : ℝ, x = y + c • consecutiveResidueHilbert M := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : i.val < M
    · refine ⟨residueAtom i.val, ?_, 0, by simp⟩
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · have hie : i.val = M := by omega
      simp only [id_eq, hie]
      let b : ThresholdHilbert :=
        ((M + 1 : ℕ) : ℝ) • normalizedResidueHilbert (M + 1) (by omega)
      let c : ℝ := (((M + 2 : ℕ) : ℝ))⁻¹
      have hb : b ∈ finiteSpace M := by
        exact (finiteSpace M).smul_mem _
          (normalizedResidueHilbert_mem_finiteSpace M (M + 1) (by omega) le_rfl)
      have hc : ((M + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      have hstep : consecutiveResidueHilbert M + b =
          ((M + 2 : ℕ) : ℝ) • residueAtom M := by
        change (((M + 2 : ℕ) : ℝ) • residueAtom M - b) + b = _
        exact sub_add_cancel _ _
      refine ⟨c • b, (finiteSpace M).smul_mem c hb, c, ?_⟩
      calc
        residueAtom M = c • (((M + 2 : ℕ) : ℝ) • residueAtom M) := by
          simp only [c, smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c • (consecutiveResidueHilbert M + b) := congrArg (c • ·) hstep.symm
        _ = c • b + c • consecutiveResidueHilbert M := by rw [smul_add, add_comm]
  | zero => exact ⟨0, (finiteSpace M).zero_mem, 0, by simp⟩
  | add x z hx hz hix hiz =>
    obtain ⟨y, hy, c, rfl⟩ := hix
    obtain ⟨w, hw, d, rfl⟩ := hiz
    exact ⟨y + w, (finiteSpace M).add_mem hy hw, c + d, by module⟩
  | smul a x hx hi =>
    obtain ⟨y, hy, c, rfl⟩ := hi
    exact ⟨a • y, (finiteSpace M).smul_mem a hy, a * c, by module⟩

private theorem hilbertSequence_add_smul_aux (x y : ThresholdHilbert) (c : ℝ) (j : ℕ) :
    hilbertSequence (x + c • y) j = hilbertSequence x j + c * hilbertSequence y j := by
  change hilbertSequenceLinear (x + c • y) j = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

private theorem hilbertSequence_sub_aux (x y : ThresholdHilbert) (j : ℕ) :
    hilbertSequence (x - y) j = hilbertSequence x j - hilbertSequence y j := by
  change hilbertSequenceLinear (x - y) j = _
  simp only [map_sub, Pi.sub_apply]
  rfl

private theorem hilbertSequence_zero_aux (j : ℕ) : hilbertSequence 0 j = 0 := by
  change hilbertSequenceLinear 0 j = 0
  simp

/-- Evaluation at the first M physical coordinates is injective on the M-dimensional
legal space. This statement is purely finite and uses no Möbius nonvanishing. -/
theorem finiteSpace_eq_zero_of_head_zero (M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ finiteSpace M)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ M → hilbertSequence x j = 0) : x = 0 := by
  induction M generalizing x with
  | zero =>
    obtain ⟨a, ha⟩ := finiteSpace_expansion 0 x hx
    simpa using ha
  | succ M ih =>
    obtain ⟨y, hy, c, hxy⟩ := finiteSpace_succ_step_decomposition M x hx
    have hyhead : ∀ j : ℕ, 0 < j → j ≤ M → hilbertSequence y j = 0 := by
      intro j hj hjM
      have hh := hhead j hj (by omega)
      rw [hxy, hilbertSequence_add_smul_aux,
        consecutiveResidueHilbert_head_zero M j hjM, mul_zero, add_zero] at hh
      exact hh
    have hy0 := ih y hy hyhead
    have hh := hhead (M + 1) (by omega) le_rfl
    rw [hxy, hilbertSequence_add_smul_aux, hy0, hilbertSequence_zero_aux,
      zero_add, consecutiveResidueHilbert_diagonal] at hh
    have hc : c = 0 := (mul_eq_zero.mp hh).resolve_right (by positivity)
    rw [hxy, hy0, hc, zero_smul, add_zero]

def consecutiveTailSpan (N M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {v | ∃ k : ℕ, N ≤ k ∧ k < M ∧ consecutiveResidueHilbert k = v}

theorem consecutiveTailSpan_mono (N M K : ℕ) (hMK : M ≤ K) :
    consecutiveTailSpan N M ≤ consecutiveTailSpan N K := by
  apply Submodule.span_mono
  rintro v ⟨k, hNk, hkM, rfl⟩
  exact ⟨k, hNk, lt_of_lt_of_le hkM hMK, rfl⟩

theorem consecutiveResidueHilbert_mem_tailSpan (N M k : ℕ) (hNk : N ≤ k)
    (hkM : k < M) : consecutiveResidueHilbert k ∈ consecutiveTailSpan N M :=
  Submodule.subset_span ⟨k, hNk, hkM, rfl⟩

/-- Every vector in the legal space whose first N values vanish is a combination
of precisely the later triangular steps. -/
theorem mem_consecutiveTailSpan_of_head_zero (N M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ finiteSpace M)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 0) :
    x ∈ consecutiveTailSpan N M := by
  induction M generalizing x with
  | zero =>
    have hz : x = 0 := finiteSpace_eq_zero_of_head_zero 0 x hx (by intros; omega)
    rw [hz]
    exact (consecutiveTailSpan N 0).zero_mem
  | succ M ih =>
    by_cases hMN : M < N
    · have hz : x = 0 := finiteSpace_eq_zero_of_head_zero (M + 1) x hx
        (fun j hj hjM => hhead j hj (by omega))
      rw [hz]
      exact (consecutiveTailSpan N (M + 1)).zero_mem
    · have hNM : N ≤ M := by omega
      obtain ⟨y, hy, c, hxy⟩ := finiteSpace_succ_step_decomposition M x hx
      have hyhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence y j = 0 := by
        intro j hj hjN
        have hh := hhead j hj hjN
        rw [hxy, hilbertSequence_add_smul_aux,
          consecutiveResidueHilbert_head_zero M j (hjN.trans hNM), mul_zero, add_zero] at hh
        exact hh
      have hyspan := consecutiveTailSpan_mono N M (M + 1) (by omega) (ih y hy hyhead)
      rw [hxy]
      exact (consecutiveTailSpan N (M + 1)).add_mem hyspan
        ((consecutiveTailSpan N (M + 1)).smul_mem c
          (consecutiveResidueHilbert_mem_tailSpan N (M + 1) M hNM (by omega)))

/-- Direction space of the affine hull anchored at u_N. -/
def canonicalMobiusDifferenceSpan (N M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {v | ∃ k : ℕ, N ≤ k ∧ k ≤ M ∧
    canonicalMobiusHilbert k - canonicalMobiusHilbert N = v}

theorem consecutiveTailSpan_le_canonicalMobiusDifferenceSpan
    (N M : ℕ) :
    consecutiveTailSpan N M ≤ canonicalMobiusDifferenceSpan N M := by
  apply Submodule.span_le.mpr
  rintro v ⟨k, hNk, hkM, rfl⟩
  change consecutiveResidueHilbert k ∈ canonicalMobiusDifferenceSpan N M
  have ha : canonicalMobiusHilbert (k + 1) - canonicalMobiusHilbert N ∈
      canonicalMobiusDifferenceSpan N M :=
    Submodule.subset_span ⟨k + 1, by omega, by omega, rfl⟩
  have hb : canonicalMobiusHilbert k - canonicalMobiusHilbert N ∈
      canonicalMobiusDifferenceSpan N M :=
    Submodule.subset_span ⟨k, hNk, by omega, rfl⟩
  have hd : canonicalMobiusHilbert (k + 1) - canonicalMobiusHilbert k ∈
      canonicalMobiusDifferenceSpan N M := by
    convert (canonicalMobiusDifferenceSpan N M).sub_mem ha hb using 1
    module
  rw [canonicalMobiusHilbert_succ_sub] at hd
  have hi := (canonicalMobiusDifferenceSpan N M).smul_mem
    (mobiusReciprocalSum (k + 1))⁻¹ hd
  simpa only [smul_smul, inv_mul_cancel₀ (mobiusReciprocalSum_ne_zero (N := k+1) (by omega)), one_smul] using hi

/-- Every finite legal exact-head candidate is already in the affine family
generated by u_N,...,u_M. The family restriction therefore loses no candidates
at any fixed budget M. -/
theorem exact_head_sub_mem_canonicalMobiusDifferenceSpan
    (N M : ℕ) (hNM : N ≤ M) (x : ThresholdHilbert) (hx : x ∈ finiteSpace M)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) :
    x - canonicalMobiusHilbert N ∈ canonicalMobiusDifferenceSpan N M := by
  apply consecutiveTailSpan_le_canonicalMobiusDifferenceSpan N M
  apply mem_consecutiveTailSpan_of_head_zero N M
  · exact (finiteSpace M).sub_mem hx
      (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hNM
        (canonicalMobiusHilbert_mem_finiteSpace N))
  · intro j hj hjN
    rw [hilbertSequence_sub_aux, hhead j hj hjN,
      canonicalMobiusHilbert_exact N j hj hjN, sub_self]


/-- At the smallest conductor budget, the canonical vector is the only
legal vector with the prescribed head. -/
theorem exact_head_eq_canonical_at_diagonal (N : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ finiteSpace N)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) :
    x = canonicalMobiusHilbert N := by
  apply sub_eq_zero.mp
  apply finiteSpace_eq_zero_of_head_zero N (x - canonicalMobiusHilbert N)
    ((finiteSpace N).sub_mem hx (canonicalMobiusHilbert_mem_finiteSpace N))
  intro j hj hjN
  rw [hilbertSequence_sub_aux, hhead j hj hjN,
    canonicalMobiusHilbert_exact N j hj hjN, sub_self]


theorem canonicalMobiusDifferenceSpan_expansion (N M : ℕ)
    (x : ThresholdHilbert) (hx : x ∈ canonicalMobiusDifferenceSpan N M) :
    ∃ a : Fin (M - N + 1) → ℝ,
      x = ∑ i : Fin (M - N + 1),
        a i • (canonicalMobiusHilbert (N + i.val) - canonicalMobiusHilbert N) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hNk, hkM, rfl⟩ := hx
    let i : Fin (M - N + 1) := ⟨k - N, by omega⟩
    have hi : N + i.val = k := by dsimp [i]; omega
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    simp [ite_smul, hi]
  | zero => exact ⟨fun _ => 0, by simp⟩
  | add x y hx hy hix hiy =>
    obtain ⟨a, rfl⟩ := hix
    obtain ⟨b, rfl⟩ := hiy
    exact ⟨fun j => a j + b j, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul c x hx hi =>
    obtain ⟨a, rfl⟩ := hi
    exact ⟨fun j => c * a j, by simp [mul_smul, Finset.smul_sum]⟩

/-- Exact coefficients for the affine exhaustion: no extra conductor beyond M+1
and no nonlinear or infinite combination is needed. -/
theorem exists_canonicalMobius_affine_expansion_of_exact_head
    (N M : ℕ) (hNM : N ≤ M) (x : ThresholdHilbert) (hx : x ∈ finiteSpace M)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) :
    ∃ c : Fin (M - N + 1) → ℝ, (∑ i, c i) = 1 ∧
      x = ∑ i : Fin (M - N + 1), c i • canonicalMobiusHilbert (N + i.val) := by
  classical
  obtain ⟨a, ha⟩ := canonicalMobiusDifferenceSpan_expansion N M
    (x - canonicalMobiusHilbert N)
    (exact_head_sub_mem_canonicalMobiusDifferenceSpan N M hNM x hx hhead)
  let i0 : Fin (M - N + 1) := ⟨0, by omega⟩
  let A : ℝ := ∑ i, a i
  let c : Fin (M - N + 1) → ℝ := fun i => a i + if i = i0 then 1 - A else 0
  have hcsum : (∑ i, c i) = 1 := by
    simp only [c, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change A + (1 - A) = 1
    ring
  have hcomb :
      (∑ i : Fin (M - N + 1), c i • canonicalMobiusHilbert (N + i.val)) =
      (∑ i : Fin (M - N + 1), a i • canonicalMobiusHilbert (N + i.val)) +
        (1 - A) • canonicalMobiusHilbert N := by
    have hi (i : Fin (M - N + 1)) :
        (if i = i0 then 1 - A else 0) • canonicalMobiusHilbert (N + i.val) =
        if i = i0 then (1 - A) • canonicalMobiusHilbert N else 0 := by
      split_ifs with h
      · subst i
        simp [i0]
      · simp
    simp only [c, add_smul, hi, Finset.sum_add_distrib]
    simp
  refine ⟨c, hcsum, ?_⟩
  rw [hcomb]
  calc
    x = (x - canonicalMobiusHilbert N) + canonicalMobiusHilbert N :=
      (sub_add_cancel _ _).symm
    _ = (∑ i : Fin (M - N + 1),
        a i • (canonicalMobiusHilbert (N + i.val) - canonicalMobiusHilbert N)) +
          canonicalMobiusHilbert N := by rw [ha]
    _ = _ := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      change ((∑ i : Fin (M - N + 1), a i • canonicalMobiusHilbert (N + i.val)) -
        A • canonicalMobiusHilbert N) + canonicalMobiusHilbert N = _
      module

end CoefficientStabilization
end RiemannResearch.RH.Pareto
