import RiemannResearch.RH.ParetoMellinHeadObstruction
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.ArithmeticMellinResearchTargets
import RiemannResearch.RH.ArithmeticConductorCommonZeros
import RiemannResearch.RH.ArithmeticMellinSymbolZeros
import RiemannResearch.RH.ArithmeticMellinIdentity
import RiemannResearch.Analysis.BoundedInterpolation

/-!
# Single-seed obstruction and the precise remaining arithmetic providers

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. The analytic functional, continuity and interpolation lower
bound are supplied by proved declarations in the two Mellin modules.

The general finite-seed obstruction uses the actual half-plane arithmetic
identity and finite-symbol zero existence. Both are supplied by imported
theorems; no unresolved domain-specific provider is assumed here.
-/

namespace RiemannResearch.RH.Pareto
open Set
noncomputable section

def singleSeedDilationSet (ψ : ThresholdHilbert) : Set ThresholdHilbert :=
  {v | ∃ (m : ℕ) (hm : 0 < m), v = hilbertDilation m hm ψ}

/-- Only dilates of this one fixed vector are admitted; all positive integer
indices remain available. -/
def singleSeedDilationClosure (ψ : ThresholdHilbert) : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (singleSeedDilationSet ψ)).topologicalClosure

/-- A continuous Mellin functional annihilating every allowed dilation also
annihilates the entire Hilbert closure. -/
theorem paretoMellin_zero_on_singleSeedClosure (ψ : ThresholdHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hzero : ∀ (m : ℕ) (hm : 0 < m), paretoMellin (hilbertDilation m hm ψ) s = 0)
    {f : ThresholdHilbert} (hf : f ∈ singleSeedDilationClosure ψ) :
    paretoMellin f s = 0 := by
  let L := paretoMellinContinuous s hs
  have hspan : Submodule.span ℝ (singleSeedDilationSet ψ) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨m, hm, rfl⟩
    exact hzero m hm
  have hc := Submodule.topologicalClosure_mono hspan
  rw [L.isClosed_ker.submodule_topologicalClosure_eq] at hc
  exact hc hf

/-- Functional separation from one actual seed zero; covariance supplies
annihilation of all its positive integer dilates. -/
theorem hilbertOne_not_mem_singleSeedClosure_of_mellin (ψ : ThresholdHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hnull : paretoMellin ψ s = 0) :
    hilbertOne ∉ singleSeedDilationClosure ψ := by
  have hzero (m : ℕ) (hm : 0 < m) : paretoMellin (hilbertDilation m hm ψ) s = 0 := by
    rw [paretoMellin_dilation, hnull, mul_zero]
  intro hmem
  have h := paretoMellin_zero_on_singleSeedClosure ψ s hs hzero hmem
  rw [paretoMellin_one s hs] at h
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  exact (one_div_ne_zero hs0) h

/-- One Mellin zero gives a uniform positive lower bound on squared distance
from the target to every element of the closed dilation span. -/
theorem singleSeedClosure_distance_sq_lower_bound (ψ : ThresholdHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hnull : paretoMellin ψ s = 0)
    {f : ThresholdHilbert} (hf : f ∈ singleSeedDilationClosure ψ) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hzero (m : ℕ) (hm : 0 < m) : paretoMellin (hilbertDilation m hm ψ) s = 0 := by
    rw [paretoMellin_dilation, hnull, mul_zero]
  have hfzero := paretoMellin_zero_on_singleSeedClosure ψ s hs hzero hf
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have hb := paretoMellin_norm_sq_le (hilbertOne - f) s hs
  rw [heval, norm_div, norm_one, div_pow, one_pow] at hb
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hm := (le_div_iff₀ hd).mp hb
  have he : (1 / ‖s‖ ^ 2) * (2 * s.re - 1) = (2 * s.re - 1) / ‖s‖ ^ 2 := by ring
  rwa [he] at hm

/-- The complete interpolation lower bound applies even to members of the
closed single-seed span, whenever the actual annihilator is supplied. -/
theorem singleSeedClosure_exact_head_lower_bound (ψ : ThresholdHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hnull : paretoMellin ψ s = 0)
    {f : ThresholdHilbert} (hf : f ∈ singleSeedDilationClosure ψ) {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    (N : ℝ) / ((N : ℝ) + 1) +
      ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
        ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hzero (m : ℕ) (hm : 0 < m) : paretoMellin (hilbertDilation m hm ψ) s = 0 := by
    rw [paretoMellin_dilation, hnull, mul_zero]
  exact paretoMellin_exact_head_lower_bound hhead s hs
    (paretoMellin_zero_on_singleSeedClosure ψ s hs hzero hf)

/-- The exact entire arithmetic factor vanishes at the removable point.
This is finite algebra, not the existence of a nonreal zero. -/
theorem arithmeticMellinSymbol_one (c : ArithmeticCoefficients) :
    arithmeticMellinSymbol c 1 = 0 := by
  simp [arithmeticMellinSymbol]

/-- An actual nonreal Mellin annihilator exists for every finite legal seed. -/
theorem finite_legal_seed_has_mellin_zero
    (c : ArithmeticCoefficients) (hc : ArithmeticCoefficientsLegal c)
    (ψ : ThresholdHilbert) (hψ : hilbertSequence ψ = arithmeticCombination c) :
    ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ s.im ≠ 0 ∧ paretoMellin ψ s = 0 := by
  obtain ⟨s, hs, him, hsymbol⟩ := arithmeticMellinSymbol_exists_nonreal_zero c hc
  have hs1 : s ≠ 1 := by intro h; apply him; simp [h]
  have hnull : paretoMellin ψ s = 0 := by
    rw [arithmeticMellin_identity c hc ψ hψ s hs hs1, hsymbol, mul_zero]
  exact ⟨s, hs, him, hnull⟩

/-- No single fixed finite legal seed is cyclic for the target. Actual
continuity, dilation covariance, arithmetic identification and nonreal zero
existence are all supplied by theorem declarations. -/
theorem finite_legal_seed_not_cyclic
    (c : ArithmeticCoefficients) (hc : ArithmeticCoefficientsLegal c)
    (ψ : ThresholdHilbert) (hψ : hilbertSequence ψ = arithmeticCombination c) :
    hilbertOne ∉ singleSeedDilationClosure ψ := by
  obtain ⟨s, hs, _, hnull⟩ := finite_legal_seed_has_mellin_zero c hc ψ hψ
  exact hilbertOne_not_mem_singleSeedClosure_of_mellin ψ s hs hnull

/-- Every fixed finite legal seed has a positive squared-distance gap from
the target, uniformly over its entire closed dilation span. -/
theorem finite_legal_seed_positive_distance_gap
    (c : ArithmeticCoefficients) (hc : ArithmeticCoefficientsLegal c)
    (ψ : ThresholdHilbert) (hψ : hilbertSequence ψ = arithmeticCombination c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ singleSeedDilationClosure ψ,
      δ ≤ ‖hilbertOne - f‖ ^ 2 := by
  obtain ⟨s, hs, _, hnull⟩ := finite_legal_seed_has_mellin_zero c hc ψ hψ
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  refine ⟨(2 * s.re - 1) / ‖s‖ ^ 2, ?_, ?_⟩
  · exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hs0))
  · intro f hf
    exact singleSeedClosure_distance_sq_lower_bound ψ s hs hnull hf

private def seedHilbertEval (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  ({ toFun := fun f => f n
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : ThresholdHilbert →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by
      change ‖f n‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f n)

/-- For every proposed energy bound, some finite head already forces every
interpolant from this fixed seed's closed dilation span above that bound. -/
theorem finite_legal_seed_interpolation_unbounded
    (c : ArithmeticCoefficients) (hc : ArithmeticCoefficientsLegal c)
    (ψ : ThresholdHilbert) (hψ : hilbertSequence ψ = arithmeticCombination c)
    (C : ℝ) :
    ∃ N : ℕ, ∀ f ∈ singleSeedDilationClosure ψ,
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) → C < ‖f‖ ^ 2 := by
  by_contra hnone
  push_neg at hnone
  apply finite_legal_seed_not_cyclic c hc ψ hψ
  apply Analysis.BoundedInterpolation.mem_of_bounded_exact_interpolation
    (singleSeedDilationClosure ψ)
    (Submodule.span ℝ (singleSeedDilationSet ψ)).isClosed_topologicalClosure
    seedHilbertEval (by intro x y h; apply Subtype.ext; exact h) hilbertOne C
  intro N
  obtain ⟨f, hf, hhead, hbound⟩ := hnone (N + 1)
  refine ⟨f, hf, ?_, hbound⟩
  intro k hk
  change f k = hilbertOne k
  have he : hilbertSequence f (k + 1) = hilbertSequence hilbertOne (k + 1) := by
    calc
      hilbertSequence f (k + 1) = 1 :=
        hhead (k + 1) (Nat.succ_pos _) (Nat.succ_le_succ hk)
      _ = hilbertSequence hilbertOne (k + 1) := by
        rw [hilbertOne_sequence]
        simp [zeroAnchor]
  change f k / Real.sqrt (paretoWeight k) =
    hilbertOne k / Real.sqrt (paretoWeight k) at he
  exact (div_left_inj' (show Real.sqrt (paretoWeight k) ≠ 0 by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold paretoWeight
    positivity)).mp he

end
end RiemannResearch.RH.Pareto
