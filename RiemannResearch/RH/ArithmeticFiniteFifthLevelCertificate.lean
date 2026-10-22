import RiemannResearch.RH.ArithmeticFiniteFifthLevelIntervals
import RiemannResearch.RH.ArithmeticFiniteFifthLevelIntegerCertificate

/-!
# Fifth-level native arithmetic positivity

At R=1/16, m=5, N=2, J=5, the literal auxiliary, finite, and actual arithmetic
Haar forms dominate 10^-9 times the exact unnormalized coefficient norm.
The finite model retains the literal signed range-two prime-power sum, polar
correction, live linear coefficient comparison, and all five archimedean modes.

Source: user-provided FifthLevel_Paper_Recon_v47.md and the RH continuation
program support the certificate architecture and candidate rational data.
All identities and inequalities below are formally proved. These fixed-level
results do not establish all-level positivity, completed-Weil positivity, or RH.
-/


open scoped BigOperators
namespace RiemannResearch.RH
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

def fifthLevelOddGram : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 2)

theorem fifthLevelOddShiftedNumerator_eq (i j : Fin 16) :
    (fifthLevelOddShiftedLowerNumerator i j:ℚ)/1000000000000000000 =
      fifthLevelOddLower i j - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) ∧
    (fifthLevelOddShiftedUpperNumerator i j:ℚ)/1000000000000000000 =
      fifthLevelOddUpper i j - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem fifthLevelOddBlock_shifted_bounds (p : Fin 33 → ℝ)
    (hraw : ∀ i j, (fifthLevelOddLower i j : ℝ) ≤ fifthLevelOddBlock p i j ∧
      fifthLevelOddBlock p i j ≤ (fifthLevelOddUpper i j : ℝ)) (i j : Fin 16) :
    (fifthLevelOddShiftedLowerNumerator i j:ℝ)/1000000000000000000 ≤
      (fifthLevelOddBlock p - (1/1000000000:ℝ) • fifthLevelOddGram) i j ∧
    (fifthLevelOddBlock p - (1/1000000000:ℝ) • fifthLevelOddGram) i j ≤
      (fifthLevelOddShiftedUpperNumerator i j:ℝ)/1000000000000000000 := by
  have hl : (fifthLevelOddShiftedLowerNumerator i j:ℝ)/1000000000000000000 =
      (fifthLevelOddLower i j:ℝ) - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (fifthLevelOddShiftedNumerator_eq i j).1
    push_cast at h
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact h
  have hu : (fifthLevelOddShiftedUpperNumerator i j:ℝ)/1000000000000000000 =
      (fifthLevelOddUpper i j:ℝ) - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (fifthLevelOddShiftedNumerator_eq i j).2
    push_cast at h
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact h
  change _ ≤ fifthLevelOddBlock p i j - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) ∧
    fifthLevelOddBlock p i j - (1/1000000000)*(if i = j then (if i = 0 then 1 else 2) else 0) ≤ _
  rw [hl, hu]
  exact ⟨sub_le_sub_right (hraw i j).1 _, sub_le_sub_right (hraw i j).2 _⟩

def fifthLevelEvenGram : Matrix (Fin 15) (Fin 15) ℝ :=
  Matrix.diagonal (fun _ => 2)

theorem fifthLevelEvenShiftedNumerator_eq (i j : Fin 15) :
    (fifthLevelEvenShiftedLowerNumerator i j:ℚ)/1000000000000000000 =
      fifthLevelEvenLower i j - (1/1000000000)*(if i = j then (2) else 0) ∧
    (fifthLevelEvenShiftedUpperNumerator i j:ℚ)/1000000000000000000 =
      fifthLevelEvenUpper i j - (1/1000000000)*(if i = j then (2) else 0) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem fifthLevelEvenBlock_shifted_bounds (p : Fin 33 → ℝ)
    (hraw : ∀ i j, (fifthLevelEvenLower i j : ℝ) ≤ fifthLevelEvenBlock p i j ∧
      fifthLevelEvenBlock p i j ≤ (fifthLevelEvenUpper i j : ℝ)) (i j : Fin 15) :
    (fifthLevelEvenShiftedLowerNumerator i j:ℝ)/1000000000000000000 ≤
      (fifthLevelEvenBlock p - (1/1000000000:ℝ) • fifthLevelEvenGram) i j ∧
    (fifthLevelEvenBlock p - (1/1000000000:ℝ) • fifthLevelEvenGram) i j ≤
      (fifthLevelEvenShiftedUpperNumerator i j:ℝ)/1000000000000000000 := by
  have hl : (fifthLevelEvenShiftedLowerNumerator i j:ℝ)/1000000000000000000 =
      (fifthLevelEvenLower i j:ℝ) - (1/1000000000)*(if i = j then (2) else 0) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (fifthLevelEvenShiftedNumerator_eq i j).1
    push_cast at h
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact h
  have hu : (fifthLevelEvenShiftedUpperNumerator i j:ℝ)/1000000000000000000 =
      (fifthLevelEvenUpper i j:ℝ) - (1/1000000000)*(if i = j then (2) else 0) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (fifthLevelEvenShiftedNumerator_eq i j).2
    push_cast at h
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact h
  change _ ≤ fifthLevelEvenBlock p i j - (1/1000000000)*(if i = j then (2) else 0) ∧
    fifthLevelEvenBlock p i j - (1/1000000000)*(if i = j then (2) else 0) ≤ _
  rw [hl, hu]
  exact ⟨sub_le_sub_right (hraw i j).1 _, sub_le_sub_right (hraw i j).2 _⟩

end
end RiemannResearch.RH

open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.RH.PrimeGapCurvature
noncomputable section

theorem realMatrix_quadratic_reindex {n m : Type*} [Fintype n] [Fintype m]
    (e : m ≃ n) (M : Matrix n n ℝ) (c : n → ℝ) :
    dotProduct c (M.mulVec c) =
      dotProduct (fun i => c (e i)) (Matrix.mulVec (fun i j => M (e i) (e j)) (fun i => c (e i))) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← e.sum_comp (fun i => c i * ∑ j, M i j * c j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp (fun j => M (e i) j * c j)]

theorem fifthLevelOddGram_reindex :
    (fun i j => (Matrix.diagonal
      (fun k : Option (FiniteDyadicHaarIndex 4) => if k = none then (1:ℝ) else 2))
        (fifthLevelOddIndexEquiv i) (fifthLevelOddIndexEquiv j)) = fifthLevelOddGram := by
  ext i j
  simp only [fifthLevelOddGram, Matrix.diagonal_apply, fifthLevelOddIndexEquiv.injective.eq_iff]
  change (if i = j then (if fifthLevelOddIndex i = none then (1:ℝ) else 2) else 0) = _
  simp only [fifthLevelOddIndex_root]

theorem fifthLevelEvenGram_reindex :
    (fun i j => (Matrix.diagonal (fun _ : FiniteDyadicHaarIndex 4 => (2:ℝ)))
      (fourthLevelIndexEquiv i) (fourthLevelIndexEquiv j)) = fifthLevelEvenGram := by
  ext i j
  simp only [fifthLevelEvenGram, Matrix.diagonal_apply, fourthLevelIndexEquiv.injective.eq_iff]

theorem fifthLevelOddBlock_lower_of_raw (p : Fin 33 → ℝ)
    (hraw : ∀ i j, (fifthLevelOddLower i j : ℝ) ≤ fifthLevelOddBlock p i j ∧
      fifthLevelOddBlock p i j ≤ (fifthLevelOddUpper i j : ℝ)) (c : Fin 16 → ℝ) :
    (1/1000000000:ℝ) * dotProduct c (fifthLevelOddGram.mulVec c) ≤
      dotProduct c ((fifthLevelOddBlock p).mulVec c) := by
  apply realMatrix_lower_of_integer_interval_shear
    (fifthLevelOddBlock p) fifthLevelOddGram fifthLevelOddShearNumerator
    fifthLevelOddShiftedLowerNumerator fifthLevelOddShiftedUpperNumerator
    fifthLevelOddShearedLowerNumerator fifthLevelOddShearedUpperNumerator
    (1/1000000000) (fifthLevelOddBlock_isHermitian p)
    (Matrix.isHermitian_diagonal _) fifthLevelOddShearNumerator_unitUpper.1
    fifthLevelOddShearNumerator_unitUpper.2
    (fifthLevelOddBlock_shifted_bounds p hraw) fifthLevelOddIntegerIntervals
  intro i
  have h := fifthLevelOddIntegerMargin i
  omega

theorem fifthLevelEvenBlock_lower_of_raw (p : Fin 33 → ℝ)
    (hraw : ∀ i j, (fifthLevelEvenLower i j : ℝ) ≤ fifthLevelEvenBlock p i j ∧
      fifthLevelEvenBlock p i j ≤ (fifthLevelEvenUpper i j : ℝ)) (c : Fin 15 → ℝ) :
    (1/1000000000:ℝ) * dotProduct c (fifthLevelEvenGram.mulVec c) ≤
      dotProduct c ((fifthLevelEvenBlock p).mulVec c) := by
  apply realMatrix_lower_of_integer_interval_shear
    (fifthLevelEvenBlock p) fifthLevelEvenGram fifthLevelEvenShearNumerator
    fifthLevelEvenShiftedLowerNumerator fifthLevelEvenShiftedUpperNumerator
    fifthLevelEvenShearedLowerNumerator fifthLevelEvenShearedUpperNumerator
    (1/1000000000) (fifthLevelEvenBlock_isHermitian p)
    (Matrix.isHermitian_diagonal _) fifthLevelEvenShearNumerator_unitUpper.1
    fifthLevelEvenShearNumerator_unitUpper.2
    (fifthLevelEvenBlock_shifted_bounds p hraw) fifthLevelEvenIntegerIntervals
  intro i
  have h := fifthLevelEvenIntegerMargin i
  omega

theorem arithmeticFiniteHaarModel_fifthLevel_lower_of_raw
    (hodd : ∀ i j, (fifthLevelOddLower i j : ℝ) ≤ fifthLevelOddBlock fifthLevelSamples i j ∧
      fifthLevelOddBlock fifthLevelSamples i j ≤ (fifthLevelOddUpper i j : ℝ))
    (heven : ∀ i j, (fifthLevelEvenLower i j : ℝ) ≤ fifthLevelEvenBlock fifthLevelSamples i j ∧
      fifthLevelEvenBlock fifthLevelSamples i j ≤ (fifthLevelEvenUpper i j : ℝ))
    (c : FiniteDyadicHaarIndex 5 → ℝ) :
    (1/1000000000:ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticFiniteHaarModel (5373/2000) (1/16) 5 2 5).mulVec c) := by
  apply arithmeticFiniteHaarModel_fiveModes_lower_of_blocks (5373/2000) (1/16) (1/1000000000) 4
  · intro v
    rw [realMatrix_quadratic_reindex fifthLevelOddIndexEquiv,
      realMatrix_quadratic_reindex fifthLevelOddIndexEquiv, fifthLevelOddGram_reindex]
    have he : (fun i j => arithmeticFiniteOddBlock (5373/2000) (1/16) 4
        (fifthLevelOddIndexEquiv i) (fifthLevelOddIndexEquiv j)) =
        fifthLevelOddBlock fifthLevelSamples := by
      ext i j
      exact (fifthLevelOddBlock_eq_arithmetic i j).symm
    rw [he]
    exact fifthLevelOddBlock_lower_of_raw fifthLevelSamples hodd _
  · intro v
    rw [realMatrix_quadratic_reindex fourthLevelIndexEquiv,
      realMatrix_quadratic_reindex fourthLevelIndexEquiv, fifthLevelEvenGram_reindex]
    have he : (fun i j => arithmeticFiniteEvenBlock (5373/2000) (1/16) 4
        (fourthLevelIndexEquiv i) (fourthLevelIndexEquiv j)) =
        fifthLevelEvenBlock fifthLevelSamples := by
      ext i j
      exact (fifthLevelEvenBlock_eq_arithmetic i j).symm
    rw [he]
    exact fifthLevelEvenBlock_lower_of_raw fifthLevelSamples heven _

end
end RiemannResearch.RH

open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.RH.PrimeGapCurvature
noncomputable section

/-- The exact fifth-level auxiliary lower bound in the native coefficient norm. -/
theorem arithmeticFiniteHaarModel_sixteenth_level5_lower (c : FiniteDyadicHaarIndex 5 → ℝ) :
    (1/1000000000:ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticFiniteHaarModel (5373/2000) (1/16) 5 2 5).mulVec c) :=
  arithmeticFiniteHaarModel_fifthLevel_lower_of_raw
    (fifthLevelOddBlock_bounds fifthLevelSamples fifthLevelSamples_bounds)
    (fifthLevelEvenBlock_bounds fifthLevelSamples fifthLevelSamples_bounds) c

/-- Quantitative positivity of the literal signed finite arithmetic Haar matrix. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level5_lower (c : FiniteDyadicHaarIndex 5 → ℝ) :
    (1/1000000000:ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) 5 2 5).mulVec c) :=
  (arithmeticFiniteHaarModel_sixteenth_lower_transfer 5 5 (1/1000000000) (by norm_num)
    arithmeticFiniteHaarModel_sixteenth_level5_lower).1 c

theorem arithmeticScrewApproxHaarMatrix_sixteenth_level5_posSemidef :
    (arithmeticScrewApproxHaarMatrix (1/16) 5 2 5).PosSemidef :=
  (arithmeticFiniteHaarModel_sixteenth_lower_transfer 5 5 (1/1000000000) (by norm_num)
    arithmeticFiniteHaarModel_sixteenth_level5_lower).2.1

/-- The established admissible signed comparison transfers the bound to the actual matrix. -/
theorem arithmeticScrewHaarMatrix_sixteenth_level5_lower (c : FiniteDyadicHaarIndex 5 → ℝ) :
    (1/1000000000:ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewHaarMatrix (1/16) 5).mulVec c) :=
  (arithmeticFiniteHaarModel_sixteenth_lower_transfer 5 5 (1/1000000000) (by norm_num)
    arithmeticFiniteHaarModel_sixteenth_level5_lower).2.2.1 c

theorem arithmeticScrewHaarMatrix_sixteenth_level5_posSemidef :
    (arithmeticScrewHaarMatrix (1/16) 5).PosSemidef :=
  (arithmeticFiniteHaarModel_sixteenth_lower_transfer 5 5 (1/1000000000) (by norm_num)
    arithmeticFiniteHaarModel_sixteenth_level5_lower).2.2.2

end
end RiemannResearch.RH
