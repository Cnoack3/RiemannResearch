import RiemannResearch.RH.ConditionalMeanTailNonattainment
import RiemannResearch.RH.ParetoFiniteGram
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The actual complete signed conditional-mean residue Gram matrices

Source: `ArithmeticVariationalProof.md`, Sections 5--6, completing Section 11
of the user-provided conditional-iid handoff. Entries below are actual
summable conditional-mean products. Exact finite Gram expansion and strict
positive definiteness are proved for every finite set of distinct moduli
at least two. No matrix positivity premise or independent-row replacement
is used.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

theorem cesaro_finsetCombination {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → ℕ → ℝ) (t : ℕ) :
    cesaro (fun n => ∑ i ∈ s, c i * f i n) t = ∑ i ∈ s, c i * cesaro (f i) t := by
  unfold cesaro
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end RiemannResearch.Probability.ConditionalIID

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- The actual signed pairing on conditional-mean coordinates beyond `N`. -/
def conditionalTailPairing (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, conditionalWeight (k + N) * (u (k + N + 1) * v (k + N + 1))

theorem conditionalTailPairing_comm (N : ℕ) (u v : ℕ → ℝ) :
    conditionalTailPairing N u v = conditionalTailPairing N v u := by
  unfold conditionalTailPairing
  apply tsum_congr
  intro k
  ring

theorem conditionalTail_weighted_summable_of_bounded (N : ℕ) {u : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n, |u n| ≤ B) :
    Summable (fun k : ℕ => conditionalWeight (k + N) * u (k + N + 1)) := by
  have hq : Summable (fun k : ℕ => conditionalWeight (k + N)) :=
    hasSum_mixtureWeight.summable.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  apply (hq.mul_right B).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (conditionalWeight_pos _)]
  exact mul_le_mul_of_nonneg_left (hu _) (conditionalWeight_pos _).le

theorem conditionalTailPairing_finsetSum_left {ι : Type*} (N : ℕ) (s : Finset ι)
    {u : ι → ℕ → ℝ} {v : ℕ → ℝ} {B : ι → ℝ} {D : ℝ}
    (hu : ∀ i n, |u i n| ≤ B i) (hv : ∀ n, |v n| ≤ D) :
    conditionalTailPairing N (fun n => ∑ i ∈ s, u i n) v =
      ∑ i ∈ s, conditionalTailPairing N (u i) v := by
  unfold conditionalTailPairing
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ =>
    conditionalTail_weighted_summable_of_bounded N (bounded_product (hu i) hv))

theorem conditionalTailPairing_finsetSum_right {ι : Type*} (N : ℕ) (s : Finset ι)
    {u : ℕ → ℝ} {v : ι → ℕ → ℝ} {B : ℝ} {D : ι → ℝ}
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ i n, |v i n| ≤ D i) :
    conditionalTailPairing N u (fun n => ∑ i ∈ s, v i n) =
      ∑ i ∈ s, conditionalTailPairing N u (v i) := by
  rw [conditionalTailPairing_comm, conditionalTailPairing_finsetSum_left N s hv hu]
  exact Finset.sum_congr rfl (fun i _ => conditionalTailPairing_comm N (v i) u)

theorem conditionalTailPairing_const_mul_left (N : ℕ) (a : ℝ) (u v : ℕ → ℝ) :
    conditionalTailPairing N (fun n => a * u n) v = a * conditionalTailPairing N u v := by
  unfold conditionalTailPairing
  calc
    _ = ∑' k : ℕ, a * (conditionalWeight (k + N) *
        (u (k + N + 1) * v (k + N + 1))) := by
      apply tsum_congr
      intro k
      ring
    _ = _ := tsum_mul_left

theorem conditionalTailPairing_const_mul_right (N : ℕ) (a : ℝ) (u v : ℕ → ℝ) :
    conditionalTailPairing N u (fun n => a * v n) = a * conditionalTailPairing N u v := by
  rw [conditionalTailPairing_comm, conditionalTailPairing_const_mul_left,
    conditionalTailPairing_comm N v u]

/-- Every signed covariance is retained in the exact double Gram sum. -/
theorem conditionalTailPairing_finsetCombination {ι : Type*} (N : ℕ) (s : Finset ι)
    (c : ι → ℝ) {u : ι → ℕ → ℝ} {B : ι → ℝ}
    (hu : ∀ i n, |u i n| ≤ B i) :
    conditionalTailPairing N (fun n => ∑ i ∈ s, c i * u i n)
      (fun n => ∑ i ∈ s, c i * u i n) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * conditionalTailPairing N (u i) (u j) := by
  have hcu := fun i => bounded_const_mul (hu i) (c i)
  rw [conditionalTailPairing_finsetSum_left N s hcu (bounded_finsetCombination s c hu)]
  apply Finset.sum_congr rfl
  intro i _
  rw [conditionalTailPairing_finsetSum_right N s (hcu i) hcu]
  apply Finset.sum_congr rfl
  intro j _
  rw [conditionalTailPairing_const_mul_left, conditionalTailPairing_const_mul_right]
  ring

theorem residue_cesaro_abs_le (d : ℕ) (hd : 0 < d) (t : ℕ) :
    |cesaro (residue d) t| ≤ (d : ℝ) := by
  cases t with
  | zero => simp [cesaro]
  | succ t =>
    have h := mean_norm_le (fun n => (residue d n : ℂ)) (d : ℝ)
      (fun n _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        residue_abs_le d n hd) (t + 1) (Nat.succ_pos _)
    simpa only [mean_ofReal, Complex.norm_real, Real.norm_eq_abs] using h

/-- Complete signed tail matrix on the actual finite set of moduli. -/
def conditionalResidueTailMatrix (N : ℕ) (s : Finset ℕ) : Matrix s s ℝ :=
  fun i j => conditionalTailPairing N (cesaro (residue i.1)) (cesaro (residue j.1))

theorem conditionalResidueTailMatrix_entry_summable (N : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (i j : s) :
    Summable (fun k : ℕ => conditionalWeight (k + N) *
      (cesaro (residue i.1) (k + N + 1) * cesaro (residue j.1) (k + N + 1))) := by
  exact conditionalTail_weighted_summable_of_bounded N
    (bounded_product (residue_cesaro_abs_le i.1 (by have := hs i.1 i.2; omega))
      (residue_cesaro_abs_le j.1 (by have := hs j.1 j.2; omega)))

/-- The actual matrix quadratic form is precisely the complete arithmetic tail energy. -/
theorem conditionalResidueTailMatrix_quadratic (N : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (c : s → ℝ) :
    dotProduct c ((conditionalResidueTailMatrix N s).mulVec c) =
      conditionalMeanTailSquare N (fun n => ∑ i : s, c i * residue i.1 n) := by
  have hb (i : s) (n : ℕ) : |cesaro (residue i.1) n| ≤ (i.1 : ℝ) :=
    residue_cesaro_abs_le _ (by have := hs i.1 i.2; omega) n
  calc
    _ = ∑ i : s, ∑ j : s, c i * c j *
        conditionalTailPairing N (cesaro (residue i.1)) (cesaro (residue j.1)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, conditionalResidueTailMatrix]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = conditionalTailPairing N
        (fun n => ∑ i : s, c i * cesaro (residue i.1) n)
        (fun n => ∑ i : s, c i * cesaro (residue i.1) n) :=
      (conditionalTailPairing_finsetCombination N Finset.univ c hb).symm
    _ = _ := by
      unfold conditionalTailPairing conditionalMeanTailSquare
      apply tsum_congr
      intro k
      rw [cesaro_finsetCombination]
      ring

/-- Positive definiteness follows from actual arithmetic tail injectivity. -/
theorem conditionalResidueTailMatrix_posDef (N : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) : (conditionalResidueTailMatrix N s).PosDef := by
  classical
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    change star (conditionalTailPairing N (cesaro (residue j.1))
      (cesaro (residue i.1))) =
        conditionalTailPairing N (cesaro (residue i.1)) (cesaro (residue j.1))
    simpa only [star_trivial] using
      conditionalTailPairing_comm N (cesaro (residue j.1)) (cesaro (residue i.1))
  · intro x hx
    let c : ℕ → ℝ := fun d => if hd : d ∈ s then x ⟨d, hd⟩ else 0
    have hc : ∃ d ∈ s, c d ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hx
      funext i
      have h := hn i.1 i.2
      simpa only [c, dif_pos i.2, Pi.zero_apply] using h
    have he : (fun n => ∑ i : s, x i * residue i.1 n) =
        (fun n => ∑ d ∈ s, c d * residue d n) := by
      funext n
      rw [Finset.univ_eq_attach]
      calc
        _ = ∑ i ∈ s.attach, c i.1 * residue i.1 n := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [c, dif_pos i.2]
        _ = _ := Finset.sum_attach s (fun d => c d * residue d n)
    have hp := finite_residue_tail_energy_pos s c hs hc N
    rw [← he, ← conditionalResidueTailMatrix_quadratic N s hs x] at hp
    simpa only [star_trivial] using hp

/-- The full matrix is the zero-cutoff case, retaining every positive endpoint. -/
def conditionalResidueGramMatrix (s : Finset ℕ) : Matrix s s ℝ :=
  conditionalResidueTailMatrix 0 s

theorem conditionalResidueGramMatrix_posDef (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) : (conditionalResidueGramMatrix s).PosDef :=
  conditionalResidueTailMatrix_posDef 0 s hs

theorem conditionalResidueGramMatrix_quadratic (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (c : s → ℝ) :
    dotProduct c ((conditionalResidueGramMatrix s).mulVec c) =
      conditionalMeanSquare (fun n => ∑ i : s, c i * residue i.1 n) := by
  simpa only [conditionalResidueGramMatrix, conditionalMeanTailSquare,
    conditionalMeanSquare, Nat.add_zero] using conditionalResidueTailMatrix_quadratic 0 s hs c

end RiemannResearch.RH.Pareto
