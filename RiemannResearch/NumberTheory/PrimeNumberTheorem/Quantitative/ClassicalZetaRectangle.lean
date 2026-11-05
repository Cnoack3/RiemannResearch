/-
Copyright (c) the PrimeNumberTheoremAnd contributors. All rights reserved.
Released under the Apache License, Version 2.0.
-/
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ZetaBounds

/-!
# Classical zero-free region and holomorphy on rectangles

The statements and proofs below are adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/747e480362ef6a0a7341055a84372333d72fa62a/PrimeNumberTheoremAnd/ZetaBounds.lean
(Apache-2.0). The exponent is kept as a parameter so the same rectangle estimate applies to the classical strip.
-/

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics

set_option lang.lemmaCmd true

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalRegion

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

def ZetaZeroFreeGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ n) 1),
    ζ (σ + t * I) ≠ 0

lemma LogDerivZetaHolcSmallT' : ∃ (σ₂ : ℝ)
  (_ : σ₂ ∈ Ioo 0 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  refine ⟨σ₂, ⟨σ₂_pos, σ₂_lt_one⟩, holo2'.mono (fun s hs ↦ ?_)⟩
  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_reProdIm, mem_Icc,
    mem_singleton_iff] at hs ⊢
  refine ⟨?_, hs.2⟩
  refine ⟨?_, hs.1.2⟩
  rcases hs.1.1 with ⟨left, right⟩
  constructor
  · apply le_trans _ left
    apply min_le_min_right
    apply le_max_left
  · rw [max_eq_right (by linarith)] at right ⊢
    exact right

def LogDerivZetaHolcLargeTGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ n) 2)  ×ℂ (Icc (-T) T) ) \ {1})

lemma LogDerivZetaHolcLargeTGen {n : ℝ} (ZetaZeroFree : ZetaZeroFreeGenProp n) (n_pos : 0 < n) :
  LogDerivZetaHolcLargeTGenProp n := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ n)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ n := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1
  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ n := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ n := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ n)) / Real.log 3 ^ n := by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; simp

def LogDerivZetaBndUnifGenProp (n₁ n₂ : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2))
  (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ n₂

end RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalRegion
