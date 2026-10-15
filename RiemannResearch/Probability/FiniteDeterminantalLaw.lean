import RiemannResearch.LinearAlgebra.AccretiveDeterminant
import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Abel

/-!
# Finite determinantal probability laws

Source: Lyons, Determinantal Probability Measures, arXiv:math/0204325,
Sections 5 and 8 (statements and terminology of exact configuration laws).
The proof here uses determinant row multilinearity and the nonnegative
quadratic form of mixed occupied/vacant rows. Every positive contraction gives
an explicit PMF, with all correlation determinants verified.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.Probability.DPP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedRows (K : Matrix ι ι ℝ) (S : Finset ι) : Matrix ι ι ℝ :=
  Matrix.of (S.piecewise K.row ((1 : Matrix ι ι ℝ) - K).row)

def exactWeight (K : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  (mixedRows K S).det

/-- The candidate exact configuration masses always sum to one, algebraically. -/
theorem sum_exactWeight (K : Matrix ι ι ℝ) :
    (∑ S : Finset ι, exactWeight K S) = 1 := by
  have h := (Matrix.detRowAlternating (R := ℝ) (n := ι)).map_add_univ K.row ((1 : Matrix ι ι ℝ) - K).row
  change Matrix.det (K + ((1 : Matrix ι ι ℝ) - K)) =
    ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise K.row ((1 : Matrix ι ι ℝ) - K).row)) at h
  have hsum : K + ((1 : Matrix ι ι ℝ) - K) = 1 := by abel
  simpa only [hsum, Matrix.det_one, exactWeight, mixedRows] using h.symm

/-- Summing exact configuration masses over supersets gives each principal minor.
The determinant argument is valid even without symmetry or positivity of K. -/
theorem sum_exactWeight_supersets (K : Matrix ι ι ℝ) (T : Finset ι) :
    (∑ S : Finset ι, if T ⊆ S then exactWeight K S else 0) =
      (K.submatrix (fun i : T => (i : ι)) (fun i : T => (i : ι))).det := by
  let Z : Matrix ι ι ℝ := Matrix.of (T.piecewise (0 : Matrix ι ι ℝ).row ((1 : Matrix ι ι ℝ) - K).row)
  have hsum : K + Z = Matrix.of (T.piecewise K.row (1 : Matrix ι ι ℝ).row) := by
    ext i j
    by_cases hi : i ∈ T
    · simp [Z, Finset.piecewise, Matrix.add_apply, Matrix.sub_apply, hi]
    · simp [Z, Finset.piecewise, Matrix.add_apply, Matrix.sub_apply, hi]
  have hterm (S : Finset ι) :
      Matrix.det (Matrix.of (S.piecewise K.row Z.row)) =
        if T ⊆ S then exactWeight K S else 0 := by
    by_cases hTS : T ⊆ S
    · rw [if_pos hTS]
      apply congrArg Matrix.det
      ext i j
      by_cases hiS : i ∈ S
      · simp [exactWeight, mixedRows, Finset.piecewise, Matrix.add_apply, Matrix.sub_apply, hiS]
      · have hiT : i ∉ T := fun hiT => hiS (hTS hiT)
        simp [Z, exactWeight, mixedRows, Finset.piecewise, Matrix.add_apply, Matrix.sub_apply, hiS, hiT]
    · rw [if_neg hTS]
      obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Z, Finset.piecewise, Matrix.add_apply, Matrix.sub_apply, hiS, hiT]
  have h := (Matrix.detRowAlternating (R := ℝ) (n := ι)).map_add_univ K.row Z.row
  change Matrix.det (K + Z) =
    ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise K.row Z.row)) at h
  rw [hsum] at h
  calc
    _ = ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise K.row Z.row)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (hterm S).symm
    _ = Matrix.det (Matrix.of (T.piecewise K.row (1 : Matrix ι ι ℝ).row)) := h.symm
    _ = _ := Matrix.det_piecewise_one_eq_submatrix_det K T

end RiemannResearch.Probability.DPP


namespace RiemannResearch.Probability.DPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exactWeight_nonneg (K : Matrix ι ι ℝ)
    (hK : K.PosSemidef) (hI : (1 - K).PosSemidef) (S : Finset ι) :
    0 ≤ exactWeight K S := by
  apply Matrix.det_nonneg_of_quadratic_nonneg
  intro x
  let a : ι → ℝ := fun i => if i ∈ S then x i else 0
  let b : ι → ℝ := fun i => if i ∈ S then 0 else x i
  have hab : a + b = x := by
    funext i
    by_cases hi : i ∈ S <;> simp [a, b, hi]
  have hsym (i j : ι) : K i j = K j i := by
    simpa using congrArg (fun A : Matrix ι ι ℝ => A j i) hK.isHermitian
  have hcross : a ⬝ᵥ (K *ᵥ b) = b ⬝ᵥ (K *ᵥ a) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hba : b ⬝ᵥ a = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S <;> simp [a, b, hi]
  have hsplit : x ⬝ᵥ ((mixedRows K S) *ᵥ x) =
      a ⬝ᵥ (K *ᵥ x) + b ⬝ᵥ ((1 - K) *ᵥ x) := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;>
      simp [Matrix.mulVec, mixedRows, Finset.piecewise, a, b, hi]
  have ha : 0 ≤ a ⬝ᵥ (K *ᵥ a) := by
    simpa using hK.dotProduct_mulVec_nonneg a
  have hb : 0 ≤ b ⬝ᵥ ((1 - K) *ᵥ b) := by
    simpa using hI.dotProduct_mulVec_nonneg b
  rw [hsplit, ← hab]
  simp only [Matrix.mulVec_add, dotProduct_add]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hba]
  linarith
end RiemannResearch.Probability.DPP

namespace RiemannResearch.Probability.DPP

open MeasureTheory
open RiemannResearch.Probability.DPP
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_ofReal_exactWeight (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) :
    (∑ S : Finset ι, ENNReal.ofReal (exactWeight K S)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => hpos S),
    sum_exactWeight, ENNReal.ofReal_one]

/-- The only geometric input needed by this constructor is positivity of the
explicit exact configuration weights; their sum has already been proved. -/
def finiteLaw (K : Matrix ι ι ℝ) (hpos : ∀ S, 0 ≤ exactWeight K S) :
    PMF (Finset ι) :=
  PMF.ofFintype (fun S => ENNReal.ofReal (exactWeight K S))
    (sum_ofReal_exactWeight K hpos)

/-- The real mass of a finite configuration is its exact determinant weight. -/
@[simp] theorem finiteLaw_apply_toReal (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (S : Finset ι) :
    ((finiteLaw K hpos) S).toReal = exactWeight K S := by
  change (ENNReal.ofReal (exactWeight K S)).toReal = _
  exact ENNReal.toReal_ofReal (hpos S)

variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem finiteLaw_inclusion (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (T : Finset ι) :
    (finiteLaw K hpos).toMeasure.real {S | T ⊆ S} =
      (K.submatrix (fun i : T => (i : ι)) (fun i : T => (i : ι))).det := by
  let E : Set (Finset ι) := {S | T ⊆ S}
  have hmeas : MeasurableSet E := (Set.toFinite E).measurableSet
  have hfinite (S : Finset ι) :
      E.indicator (fun S => ENNReal.ofReal (exactWeight K S)) S ≠ ⊤ := by
    by_cases hS : S ∈ E <;> simp [hS]
  change ENNReal.toReal ((finiteLaw K hpos).toMeasure E) = _
  rw [finiteLaw, PMF.toMeasure_ofFintype_apply _ E hmeas, tsum_fintype,
    ENNReal.toReal_sum (fun S _ => hfinite S)]
  calc
    _ = ∑ S : Finset ι, if T ⊆ S then exactWeight K S else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hTS : T ⊆ S
      · simp [E, hTS, ENNReal.toReal_ofReal (hpos S)]
      · simp [E, hTS]
    _ = _ := sum_exactWeight_supersets K T

/-- This proves every finite correlation, including arbitrarily ordered
injective lists of sites, from the exact configuration law. -/
theorem finiteLaw_isDPP (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) :
    IsDPP (finiteLaw K hpos).toMeasure (fun S => (S : Set ι)) K := by
  constructor
  · intro i
    exact (Set.toFinite _).measurableSet
  · intro n e
    let T : Finset ι := Finset.univ.map e
    have hevent : {S : Finset ι | ∀ i, e i ∈ (S : Set ι)} =
        {S : Finset ι | T ⊆ S} := by
      ext S
      simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      constructor
      · intro h i hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
        simpa only [hji] using h j
      · intro h i
        exact h (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    rw [hevent, finiteLaw_inclusion]
    let f : Fin n → T := fun i =>
      ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        exact e.injective (congrArg Subtype.val hij)
      · intro x
        obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp x.property
        exact ⟨i, Subtype.ext hix⟩
    let q : Fin n ≃ T := Equiv.ofBijective f hf
    symm
    change Matrix.det ((K.submatrix (fun i : T => (i : ι))
      (fun i : T => (i : ι))).submatrix q q) = _
    exact Matrix.det_submatrix_equiv_self q _

end RiemannResearch.Probability.DPP
