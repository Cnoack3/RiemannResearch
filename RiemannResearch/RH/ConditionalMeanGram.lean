import RiemannResearch.RH.CesaroResidueMean
import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.Analysis.FiniteSignedQuadratic

/-!
# Actual conditional-mean finite Gram data
Source: user-provided Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md,
Section 11. The actual infinite weighted entries are used, with convergence
proved before splitting. No uniform bound is asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ConditionalMeanGram
open RiemannResearch.Analysis.FiniteSignedQuadratic
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ArithmeticCumulative.CesaroResidue

/-- D columns correspond exactly to conductors 2,...,D+1. -/
def column (d t : ℕ) : ℝ := cesaro (residueFraction (d + 2)) t

def headMatrix (Y D : ℕ) : Matrix (Fin Y) (Fin D) ℝ :=
  fun t d => column d.val (t.val + 1)

def gramMatrix (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  fun d e => ∑' k : ℕ, conditionalWeight k * column d.val (k + 1) * column e.val (k + 1)

def tailMatrix (Y D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  fun d e => ∑' k : ℕ, conditionalWeight (k + Y) *
    column d.val (k + Y + 1) * column e.val (k + Y + 1)

theorem entry_summable (d e : ℕ) :
    Summable (fun k : ℕ => conditionalWeight k * column d (k + 1) * column e (k + 1)) := by
  have hq : Summable conditionalWeight := hasSum_mixtureWeight.summable
  apply hq.of_norm_bounded
  intro k
  have hd0 := cesaro_residue_nonneg (d + 2) (k + 1)
  have he0 := cesaro_residue_nonneg (e + 2) (k + 1)
  have hd1 := cesaro_residue_le_half (d + 2) (k + 1) (by omega)
  have he1 := cesaro_residue_le_half (e + 2) (k + 1) (by omega)
  change ‖conditionalWeight k * cesaro (residueFraction (d + 2)) (k + 1) *
    cesaro (residueFraction (e + 2)) (k + 1)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (conditionalWeight_pos k).le hd0) he0)]
  have hprod : cesaro (residueFraction (d + 2)) (k + 1) *
      cesaro (residueFraction (e + 2)) (k + 1) ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hprod (conditionalWeight_pos k).le]

theorem tail_entry_summable (Y d e : ℕ) :
    Summable (fun k : ℕ => conditionalWeight (k + Y) *
      column d (k + Y + 1) * column e (k + Y + 1)) :=
  (entry_summable d e).comp_injective (fun _ _ h => Nat.add_right_cancel h)

/-- Entrywise form of (11.2), with the exact positive-index head weights. -/
theorem gram_head_tail (Y D : ℕ) (d e : Fin D) :
    gramMatrix D d e =
      (∑ k ∈ Finset.range Y, conditionalWeight k *
        column d.val (k + 1) * column e.val (k + 1)) + tailMatrix Y D d e :=
  ((entry_summable d.val e.val).sum_add_tsum_nat_add Y).symm

theorem gram_symmetric (D : ℕ) (d e : Fin D) :
    gramMatrix D d e = gramMatrix D e d := by
  unfold gramMatrix
  apply tsum_congr
  intro k
  ring

theorem tail_symmetric (Y D : ℕ) (d e : Fin D) :
    tailMatrix Y D d e = tailMatrix Y D e d := by
  unfold tailMatrix
  apply tsum_congr
  intro k
  ring




/-- No independence approximation: a concrete finite conductor target.
The coefficient array is deterministic and the same in every row. -/
def UniformFiniteTailTarget : Prop :=
  ∃ K : ℝ, ∀ Y : ℕ, 1 ≤ Y → ∃ D : ℕ, Y ≤ D ∧
    ∃ c : Fin D → ℝ,
      (∀ t : Fin Y, (headMatrix Y D).mulVec c t = 1) ∧
      quadratic (tailMatrix Y D) c ≤ K

/-- The exact inverse expression in (11.7). This definition asserts no bound.
N is required to parametrize the entire head-preserving kernel injectively.
The inverse identity is explicit until concrete positivity has been proved. -/
def UniformSignedSchurTarget : Prop :=
  ∃ K : ℝ, ∀ Y : ℕ, 1 ≤ Y →
    ∃ D : ℕ, Y ≤ D ∧ ∃ c₀ : Fin D → ℝ,
    ∃ r : ℕ, ∃ N : Matrix (Fin D) (Fin r) ℝ,
    ∃ B : Matrix (Fin r) (Fin r) ℝ,
      (∀ t : Fin Y, (headMatrix Y D).mulVec c₀ t = 1) ∧
      Function.Injective N.mulVec ∧
      (∀ c : Fin D → ℝ, (headMatrix Y D).mulVec c = 0 ↔ ∃ z, N.mulVec z = c) ∧
      B * correctionMatrix (tailMatrix Y D) N = 1 ∧
      correctionMatrix (tailMatrix Y D) N * B = 1 ∧
      quadratic (tailMatrix Y D) c₀ -
        (∑ i, correlation (tailMatrix Y D) N c₀ i *
          B.mulVec (correlation (tailMatrix Y D) N c₀) i) ≤ K



/-- Exact constrained square completion from the normal equation.
This is conditional on stationarity; it does not postulate an optimizer. -/
theorem constrained_completion {Y D : ℕ}
    (cStar c : Fin D → ℝ)
    (hnormal : ∑ i, ∑ j, (c i - cStar i) * tailMatrix Y D i j * cStar j = 0) :
    quadratic (tailMatrix Y D) c = quadratic (tailMatrix Y D) cStar +
      quadratic (tailMatrix Y D) (c - cStar) := by
  have h := quadratic_add (tailMatrix Y D) (tail_symmetric Y D) cStar (c - cStar)
  have he : cStar + (c - cStar) = c := by ext i; simp
  rw [he] at h
  simpa only [Pi.sub_apply, hnormal, mul_zero, add_zero] using h


/-- Actual tail quadratic as a sum of squares, including all cross terms. -/
theorem tail_quadratic_series (Y D : ℕ) (c : Fin D → ℝ) :
    quadratic (tailMatrix Y D) c =
      ∑' k : ℕ, conditionalWeight (k + Y) *
        (∑ d : Fin D, c d * column d.val (k + Y + 1)) ^ 2 := by
  have hs (d e : Fin D) : Summable (fun k : ℕ =>
      c d * (conditionalWeight (k + Y) * column d.val (k + Y + 1) *
        column e.val (k + Y + 1)) * c e) :=
    ((tail_entry_summable Y d.val e.val).mul_left (c d)).mul_right (c e)
  have hp (k : ℕ) : conditionalWeight (k + Y) *
      (∑ d : Fin D, c d * column d.val (k + Y + 1)) ^ 2 =
      ∑ d : Fin D, ∑ e : Fin D, c d * (conditionalWeight (k + Y) *
        column d.val (k + Y + 1) * column e.val (k + Y + 1)) * c e := by
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [show (fun k : ℕ => conditionalWeight (k + Y) *
      (∑ d : Fin D, c d * column d.val (k + Y + 1)) ^ 2) =
      (fun k => ∑ d : Fin D, ∑ e : Fin D, c d *
        (conditionalWeight (k + Y) * column d.val (k + Y + 1) *
          column e.val (k + Y + 1)) * c e) from funext hp]
  rw [Summable.tsum_finsetSum (fun d _ => summable_sum (fun e _ => hs d e))]
  unfold quadratic tailMatrix
  apply Finset.sum_congr rfl
  intro d _
  rw [Summable.tsum_finsetSum (fun e _ => hs d e)]
  apply Finset.sum_congr rfl
  intro e _
  rw [((tail_entry_summable Y d.val e.val).mul_left (c d)).tsum_mul_right,
    (tail_entry_summable Y d.val e.val).tsum_mul_left]

theorem tail_quadratic_nonneg (Y D : ℕ) (c : Fin D → ℝ) :
    0 ≤ quadratic (tailMatrix Y D) c := by
  rw [tail_quadratic_series]
  exact tsum_nonneg (fun k => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))

/-- A stationary feasible point minimizes over every supplied feasible direction.
No existence of a stationary point is asserted in this declaration. -/
theorem stationary_minimizes (Y D : ℕ) (cStar c : Fin D → ℝ)
    (hnormal : ∑ i, ∑ j, (c i - cStar i) * tailMatrix Y D i j * cStar j = 0) :
    quadratic (tailMatrix Y D) cStar ≤ quadratic (tailMatrix Y D) c := by
  rw [constrained_completion cStar c hnormal]
  exact le_add_of_nonneg_right (tail_quadratic_nonneg Y D (c - cStar))







theorem correction_symmetric (Y D r : ℕ) (N : Matrix (Fin D) (Fin r) ℝ) :
    ∀ i j, correctionMatrix (tailMatrix Y D) N i j =
      correctionMatrix (tailMatrix Y D) N j i := by
  have ht : (tailMatrix Y D).transpose = tailMatrix Y D := by
    ext i j
    exact tail_symmetric Y D j i
  have he : (correctionMatrix (tailMatrix Y D) N).transpose =
      correctionMatrix (tailMatrix Y D) N := by
    simp [correctionMatrix, Matrix.transpose_mul, ht, Matrix.mul_assoc]
  intro i j
  exact (congrFun (congrFun he j) i)

theorem correction_quadratic_nonneg (Y D r : ℕ)
    (N : Matrix (Fin D) (Fin r) ℝ) (z : Fin r → ℝ) :
    0 ≤ quadratic (correctionMatrix (tailMatrix Y D) N) z := by
  rw [← correction_quadratic]
  exact tail_quadratic_nonneg Y D _

/-- Concrete expansion with S=NᵀTN and h=NᵀTc₀, not abstract placeholders. -/
theorem tail_correction_expansion (Y D r : ℕ)
    (N : Matrix (Fin D) (Fin r) ℝ) (c₀ : Fin D → ℝ) (z : Fin r → ℝ) :
    quadratic (tailMatrix Y D) (c₀ + N.mulVec z) =
      quadratic (tailMatrix Y D) c₀ +
        2 * (∑ i, z i * correlation (tailMatrix Y D) N c₀ i) +
        quadratic (correctionMatrix (tailMatrix Y D) N) z := by
  rw [quadratic_add _ (tail_symmetric Y D), correction_quadratic]
  congr 2
  have he : (∑ i, ∑ j, N.mulVec z i * tailMatrix Y D i j * c₀ j) =
      ∑ i, N.mulVec z i * (tailMatrix Y D).mulVec c₀ i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [he, transpose_pairing]
  rfl

/-- Concrete (11.6) square completion. Invertibility is an explicit finite
algebra premise, not a proved property of the arithmetic tail matrix here. -/
theorem tail_schur_completion (Y D r : ℕ)
    (N : Matrix (Fin D) (Fin r) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (hSB : correctionMatrix (tailMatrix Y D) N * B = 1)
    (c₀ : Fin D → ℝ) (z : Fin r → ℝ) :
    quadratic (tailMatrix Y D) (c₀ + N.mulVec z) =
      quadratic (tailMatrix Y D) c₀ -
        (∑ i, B.mulVec (correlation (tailMatrix Y D) N c₀) i *
          correlation (tailMatrix Y D) N c₀ i) +
        quadratic (correctionMatrix (tailMatrix Y D) N)
          (z + B.mulVec (correlation (tailMatrix Y D) N c₀)) := by
  rw [tail_correction_expansion]
  exact schur_completion_of_inverse _ B (correction_symmetric Y D r N)
    hSB _ z _

theorem tail_schur_minimizes (Y D r : ℕ)
    (N : Matrix (Fin D) (Fin r) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (hSB : correctionMatrix (tailMatrix Y D) N * B = 1)
    (c₀ : Fin D → ℝ) (z : Fin r → ℝ) :
    quadratic (tailMatrix Y D)
      (c₀ + N.mulVec (-B.mulVec (correlation (tailMatrix Y D) N c₀))) ≤
      quadratic (tailMatrix Y D) (c₀ + N.mulVec z) := by
  rw [tail_schur_completion Y D r N B hSB c₀,
    tail_schur_completion Y D r N B hSB c₀]
  simp only [neg_add_cancel, quadratic, Pi.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  exact le_add_of_nonneg_right (correction_quadratic_nonneg Y D r N _)


/-- Attained minimum over the *actual* finite affine head constraint.
The exact kernel parametrization and inverse are exposed as premises;
their unconditional construction is a remaining formalization obligation. -/
theorem constrained_tail_isLeast (Y D r : ℕ)
    (N : Matrix (Fin D) (Fin r) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (hSB : correctionMatrix (tailMatrix Y D) N * B = 1)
    (c₀ : Fin D → ℝ) (hc₀ : (headMatrix Y D).mulVec c₀ = 1)
    (hker : ∀ c : Fin D → ℝ,
      (headMatrix Y D).mulVec c = 0 ↔ ∃ z, N.mulVec z = c) :
    IsLeast {E : ℝ | ∃ c : Fin D → ℝ,
      (headMatrix Y D).mulVec c = 1 ∧ quadratic (tailMatrix Y D) c = E}
      (quadratic (tailMatrix Y D) c₀ -
        ∑ i, B.mulVec (correlation (tailMatrix Y D) N c₀) i *
          correlation (tailMatrix Y D) N c₀ i) := by
  let zStar := -B.mulVec (correlation (tailMatrix Y D) N c₀)
  have hz : (headMatrix Y D).mulVec (N.mulVec zStar) = 0 :=
    (hker _).mpr ⟨zStar, rfl⟩
  have hv : quadratic (tailMatrix Y D) (c₀ + N.mulVec zStar) =
      quadratic (tailMatrix Y D) c₀ -
        ∑ i, B.mulVec (correlation (tailMatrix Y D) N c₀) i *
          correlation (tailMatrix Y D) N c₀ i := by
    rw [tail_schur_completion Y D r N B hSB]
    simp [zStar, quadratic]
  constructor
  · refine ⟨c₀ + N.mulVec zStar, ?_, hv⟩
    rw [Matrix.mulVec_add, hc₀, hz, add_zero]
  · rintro E ⟨c, hc, rfl⟩
    have hd : (headMatrix Y D).mulVec (c - c₀) = 0 := by
      rw [Matrix.mulVec_sub, hc, hc₀, sub_self]
    obtain ⟨z, hz⟩ := (hker _).mp hd
    have he : c₀ + N.mulVec z = c := by rw [hz]; abel
    rw [← hv, ← he]
    exact tail_schur_minimizes Y D r N B hSB c₀ z


/-- The named Schur target supplies actual finite feasible coefficient arrays.
This implication proves neither target. -/
theorem finiteTailTarget_of_signedSchurTarget
    (h : UniformSignedSchurTarget) : UniformFiniteTailTarget := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨D, hD, c₀, r, N, B, hc₀, hN, hker, hBS, hSB, hbound⟩ := hK Y hY
  have hc : (headMatrix Y D).mulVec c₀ = 1 := by ext t; exact hc₀ t
  have hm := constrained_tail_isLeast Y D r N B hSB c₀ hc hker
  obtain ⟨c, hc, he⟩ := hm.1
  refine ⟨D, hD, c, ?_, ?_⟩
  · intro t
    exact congrFun hc t
  · rw [he]
    convert hbound using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end RiemannResearch.RH.ConditionalMeanGram
