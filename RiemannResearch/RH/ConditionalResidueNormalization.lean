import RiemannResearch.RH.ConditionalFiniteMatrixMinimum

/-!
# Exact normalization of the finite arithmetic dictionary

Source: `ArithmeticVariationalProof.md`, Section 5.1. The manuscript uses
`g_d = R_d / d`, whereas the finite residue matrix development uses `R_d`.
The coefficient maps below are inverse diagonal rescalings. They preserve
the actual witness and therefore every constrained energy set. Entrywise
head and signed Gram rescaling are also recorded explicitly.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
open Probability.ConditionalIID

/-- The manuscript's normalized arithmetic generator. -/
def normalizedResidue (d n : ℕ) : ℝ := residue d n / (d : ℝ)

def normalizedSynthesis (D : ℕ) (c : Finset.Icc 2 D → ℝ) : ℕ → ℝ :=
  fun n => ∑ i : Finset.Icc 2 D, c i * normalizedResidue i.1 n

/-- Normalized coefficients become raw coefficients by division by the modulus. -/
def toRawCoefficients (D : ℕ) (c : Finset.Icc 2 D → ℝ) : Finset.Icc 2 D → ℝ :=
  fun i => c i / (i.1 : ℝ)

def toNormalizedCoefficients (D : ℕ) (a : Finset.Icc 2 D → ℝ) :
    Finset.Icc 2 D → ℝ := fun i => (i.1 : ℝ) * a i

theorem modulus_ne_zero (D : ℕ) (i : Finset.Icc 2 D) : (i.1 : ℝ) ≠ 0 := by
  have hi : 2 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
  exact_mod_cast (show i.1 ≠ 0 by omega)

theorem toRaw_toNormalized (D : ℕ) (a : Finset.Icc 2 D → ℝ) :
    toRawCoefficients D (toNormalizedCoefficients D a) = a := by
  funext i
  dsimp [toRawCoefficients, toNormalizedCoefficients]
  field_simp [modulus_ne_zero D i]

theorem toNormalized_toRaw (D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    toNormalizedCoefficients D (toRawCoefficients D c) = c := by
  funext i
  dsimp [toRawCoefficients, toNormalizedCoefficients]
  field_simp [modulus_ne_zero D i]

theorem synthesis_toRaw (D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    synthesis D (toRawCoefficients D c) = normalizedSynthesis D c := by
  funext n
  unfold synthesis normalizedSynthesis toRawCoefficients normalizedResidue
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalizedSynthesis_toNormalized (D : ℕ) (a : Finset.Icc 2 D → ℝ) :
    normalizedSynthesis D (toNormalizedCoefficients D a) = synthesis D a := by
  rw [← synthesis_toRaw, toRaw_toNormalized]

theorem normalizedResidue_cesaro (d t : ℕ) :
    cesaro (normalizedResidue d) t = cesaro (residue d) t / (d : ℝ) := by
  unfold cesaro normalizedResidue
  rw [← Finset.sum_div]
  ring

def normalizedHeadMatrix (N D : ℕ) : Matrix (Fin N) (Finset.Icc 2 D) ℝ :=
  fun t d => cesaro (normalizedResidue d.1) (t.1 + 1)

def normalizedTailMatrix (N D : ℕ) : Matrix (Finset.Icc 2 D) (Finset.Icc 2 D) ℝ :=
  fun i j => conditionalTailPairing N
    (cesaro (normalizedResidue i.1)) (cesaro (normalizedResidue j.1))

def normalizedGramMatrix (D : ℕ) := normalizedTailMatrix 0 D

/-- Column `d` of the normalized head matrix is raw column `d` divided by `d`. -/
theorem normalizedHeadMatrix_entry (N D : ℕ) (t : Fin N) (i : Finset.Icc 2 D) :
    normalizedHeadMatrix N D t i = A N D t i / (i.1 : ℝ) := by
  exact normalizedResidue_cesaro i.1 (t.1 + 1)

/-- Signed Gram entries have the exact factor `1 / (d * e)`. -/
theorem normalizedTailMatrix_entry (N D : ℕ) (i j : Finset.Icc 2 D) :
    normalizedTailMatrix N D i j = T N D i j / ((i.1 : ℝ) * (j.1 : ℝ)) := by
  have hi : cesaro (normalizedResidue i.1) =
      fun t => (i.1 : ℝ)⁻¹ * cesaro (residue i.1) t := by
    funext t
    rw [normalizedResidue_cesaro]
    ring
  have hj : cesaro (normalizedResidue j.1) =
      fun t => (j.1 : ℝ)⁻¹ * cesaro (residue j.1) t := by
    funext t
    rw [normalizedResidue_cesaro]
    ring
  change conditionalTailPairing N (cesaro (normalizedResidue i.1))
    (cesaro (normalizedResidue j.1)) = _
  rw [hi, hj, conditionalTailPairing_const_mul_left,
    conditionalTailPairing_const_mul_right]
  change (i.1 : ℝ)⁻¹ * ((j.1 : ℝ)⁻¹ * conditionalTailPairing N
      (cesaro (residue i.1)) (cesaro (residue j.1))) =
    conditionalTailPairing N (cesaro (residue i.1)) (cesaro (residue j.1)) /
      ((i.1 : ℝ) * (j.1 : ℝ))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalizedGramMatrix_entry (D : ℕ) (i j : Finset.Icc 2 D) :
    normalizedGramMatrix D i j = G D i j / ((i.1 : ℝ) * (j.1 : ℝ)) :=
  normalizedTailMatrix_entry 0 D i j

theorem normalizedHeadMatrix_mulVec (N D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    (normalizedHeadMatrix N D).mulVec c = (A N D).mulVec (toRawCoefficients D c) := by
  funext t
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizedHeadMatrix_entry]
  dsimp [toRawCoefficients]
  ring

theorem normalizedHeadMatrix_surjective (N D : ℕ) (hND : N + 1 ≤ D) :
    Function.Surjective (normalizedHeadMatrix N D).mulVec := by
  intro b
  obtain ⟨a, ha⟩ := A_surjective N D hND b
  refine ⟨toNormalizedCoefficients D a, ?_⟩
  rw [normalizedHeadMatrix_mulVec, toRaw_toNormalized]
  exact ha

/-- The dictionary change preserves the whole constrained energy set,
for any real functional of the actual arithmetic witness. -/
theorem normalized_constrained_energy_set_eq (N D : ℕ) (b : Fin N → ℝ)
    (energy : (ℕ → ℝ) → ℝ) :
    {E : ℝ | ∃ c : Finset.Icc 2 D → ℝ,
      (normalizedHeadMatrix N D).mulVec c = b ∧ energy (normalizedSynthesis D c) = E} =
    {E : ℝ | ∃ a : Finset.Icc 2 D → ℝ,
      (A N D).mulVec a = b ∧ energy (synthesis D a) = E} := by
  ext E
  constructor
  · rintro ⟨c, hc, hE⟩
    refine ⟨toRawCoefficients D c, ?_, ?_⟩
    · exact (normalizedHeadMatrix_mulVec N D c).symm.trans hc
    · rw [synthesis_toRaw]
      exact hE
  · rintro ⟨a, ha, hE⟩
    refine ⟨toNormalizedCoefficients D a, ?_, ?_⟩
    · rw [normalizedHeadMatrix_mulVec, toRaw_toNormalized]
      exact ha
    · rw [normalizedSynthesis_toNormalized]
      exact hE

/-- The attained raw inverse-Gram value is also the manuscript's normalized minimum. -/
theorem normalized_fullValue_isLeast (N D : ℕ) (hND : N + 1 ≤ D) :
    IsLeast {E : ℝ | ∃ c : Finset.Icc 2 D → ℝ,
      (normalizedHeadMatrix N D).mulVec c = (fun _ => 1) ∧
        conditionalMeanSquare (normalizedSynthesis D c) = E}
      (fullValue N D hND) := by
  rw [normalized_constrained_energy_set_eq]
  exact fullValue_isLeast N D hND

theorem normalized_tailValue_isLeast (N D : ℕ) (hND : N + 1 ≤ D) :
    IsLeast {E : ℝ | ∃ c : Finset.Icc 2 D → ℝ,
      (normalizedHeadMatrix N D).mulVec c = (fun _ => 1) ∧
        conditionalMeanTailSquare N (normalizedSynthesis D c) = E}
      (tailValue N D hND) := by
  rw [normalized_constrained_energy_set_eq]
  exact tailValue_isLeast N D hND

end RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
