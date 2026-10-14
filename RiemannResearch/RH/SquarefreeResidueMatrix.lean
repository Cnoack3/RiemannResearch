import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Real squarefree residue Gram matrices

Source: user-directed real-matrix and infinite-limit investigation, 14 October 2026.
The conductor feature realization retains the complete squarefree infinite sum.
Physical indices are positive integers; matrix index i represents i+1.
The raw matrix equals D M D for the previously Q-normalized matrix M.
This congruence changes eigenvalues. No zeta spectral identity is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.SquarefreeResidueMatrix
open ZetaTwoProbability ZetaTwoHilbert

def legalRemainder (n d : ℕ) : ℝ :=
  if 2 ≤ d ∧ Squarefree d then (n % d : ℕ) else 0

theorem legalRemainder_nonneg (n d : ℕ) : 0 ≤ legalRemainder n d := by
  unfold legalRemainder
  split_ifs <;> positivity

theorem legalRemainder_le (n d : ℕ) : legalRemainder n d ≤ n := by
  unfold legalRemainder
  split_ifs
  · exact_mod_cast Nat.mod_le n d
  · positivity

theorem legalRemainder_zero (n : ℕ) : legalRemainder n 0 = 0 := by
  simp [legalRemainder]

theorem legalRemainder_two (n : ℕ) : legalRemainder n 2 = (n % 2 : ℕ) := by
  have hs : Squarefree (2 : ℕ) := (Nat.prime_iff.mp Nat.prime_two).squarefree
  simp [legalRemainder, hs]

def siteFeature (n : ℕ) : QHilbert :=
  encodeQ (legalRemainder n) (boundedQ_square_summable _ n (by positivity)
    (fun d => by rw [abs_of_nonneg (legalRemainder_nonneg n d)]; exact legalRemainder_le n d))

@[simp] theorem qSequence_siteFeature (n : ℕ) :
    qSequence (siteFeature n) = legalRemainder n :=
  qSequence_encodeQ _ _ (legalRemainder_zero n)

def rawKernel (n m : ℕ) : ℝ := inner ℝ (siteFeature n) (siteFeature m)

theorem kernel_exact (n m : ℕ) :
    rawKernel n m =
      ∑' d : ℕ, positiveQWeight d * legalRemainder n d * legalRemainder m d := by
  simp only [rawKernel, qInner_weighted, qSequence_siteFeature]

theorem kernel_summable (n m : ℕ) :
    Summable (fun d : ℕ => positiveQWeight d * legalRemainder n d * legalRemainder m d) := by
  simpa only [qSequence_siteFeature] using
    qSequence_product_summable (siteFeature n) (siteFeature m)

theorem kernel_nonneg (n m : ℕ) : 0 ≤ rawKernel n m := by
  rw [kernel_exact]
  exact tsum_nonneg (fun d => mul_nonneg
    (mul_nonneg (positiveQWeight_nonneg d) (legalRemainder_nonneg n d))
    (legalRemainder_nonneg m d))

theorem kernel_symm (n m : ℕ) : rawKernel n m = rawKernel m n :=
  real_inner_comm _ _

theorem kernel_two_lower (n m : ℕ) :
    positiveQWeight 2 * (n % 2 : ℕ) * (m % 2 : ℕ) ≤ rawKernel n m := by
  have h := (kernel_summable n m).sum_le_tsum ({2} : Finset ℕ)
    (fun d _ => mul_nonneg
      (mul_nonneg (positiveQWeight_nonneg d) (legalRemainder_nonneg n d))
      (legalRemainder_nonneg m d))
  simpa only [Finset.sum_singleton, legalRemainder_two, kernel_exact] using h

theorem kernel_odd_lower (a b : ℕ) :
    positiveQWeight 2 ≤ rawKernel (2*a+1) (2*b+1) := by
  simpa [Nat.add_mod, Nat.mul_mod] using kernel_two_lower (2*a+1) (2*b+1)

def matrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => rawKernel (i.val+1) (j.val+1)

def oddMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => rawKernel (2*i.val+1) (2*j.val+1)

def quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ A.mulVec x

theorem kernel_quadratic {ι : Type*} [Fintype ι] (s : ι → ℕ) (x : ι → ℝ) :
    quadratic (fun i j => rawKernel (s i) (s j)) x =
      ‖∑ i, x i • siteFeature (s i)‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    quadratic, Matrix.mulVec, dotProduct, rawKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (siteFeature (s j)) (siteFeature (s i))]
  ring

theorem kernel_matrix_posSemidef {ι : Type*} [Finite ι] (s : ι → ℕ) :
    (show Matrix ι ι ℝ from fun i j => rawKernel (s i) (s j)).PosSemidef := by
  let := Fintype.ofFinite ι
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change rawKernel (s j) (s i) = rawKernel (s i) (s j)
    exact kernel_symm _ _
  · intro x
    simp only [star_trivial]
    change 0 ≤ quadratic (fun i j => rawKernel (s i) (s j)) x
    rw [kernel_quadratic]
    positivity

theorem matrix_posSemidef (N : ℕ) : (matrix N).PosSemidef :=
  kernel_matrix_posSemidef (fun i : Fin N => i.val+1)

theorem oddMatrix_posSemidef (N : ℕ) : (oddMatrix N).PosSemidef :=
  kernel_matrix_posSemidef (fun i : Fin N => 2*i.val+1)

theorem oddMatrix_principal (N : ℕ) (i j : Fin N) :
    oddMatrix N i j =
      matrix (2*N) ⟨2*i.val, by omega⟩ ⟨2*j.val, by omega⟩ := rfl

def conductorCutoff (R n m : ℕ) : ℝ :=
  ∑ d ∈ Finset.range R, positiveQWeight d * legalRemainder n d * legalRemainder m d

theorem conductorCutoff_tendsto (n m : ℕ) :
    Tendsto (fun R => conductorCutoff R n m) atTop (𝓝 (rawKernel n m)) := by
  simpa only [conductorCutoff, kernel_exact] using
    (kernel_summable n m).hasSum.tendsto_sum_nat

theorem matrix_fixed_entry (N M : ℕ) (i : Fin N) (j : Fin N)
    (hi : i.val < M) (hj : j.val < M) :
    matrix M ⟨i.val,hi⟩ ⟨j.val,hj⟩ = matrix N i j := rfl

theorem weight_two_pos : 0 < positiveQWeight 2 := by
  unfold positiveQWeight
  have h := zetaTwo_pos
  positivity


theorem weight_two_exact : positiveQWeight 2 = 1 / (4*zetaTwo) := by
  unfold positiveQWeight
  norm_num
  ring

theorem kernel_one_bounds : 0 < rawKernel 1 1 ∧ rawKernel 1 1 < 1 := by
  have hlo := kernel_two_lower 1 1
  norm_num at hlo
  have hw := weight_two_pos
  have hnonneg (d : ℕ) :
      0 ≤ positiveQWeight d -
        positiveQWeight d * legalRemainder 1 d * legalRemainder 1 d := by
    have h0 := legalRemainder_nonneg 1 d
    have h1 := legalRemainder_le 1 d
    norm_num at h1
    have hs : legalRemainder 1 d * legalRemainder 1 d ≤ 1 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg d)
    nlinarith
  have hs := positiveQWeight_summable.sub (kernel_summable 1 1)
  have hh := hs.sum_le_tsum ({1} : Finset ℕ) (fun d _ => hnonneg d)
  rw [positiveQWeight_summable.tsum_sub (kernel_summable 1 1),
    positiveQWeight_tsum, ← kernel_exact] at hh
  norm_num [legalRemainder] at hh
  have hwp : 0 < positiveQWeight 1 := by
    unfold positiveQWeight
    have hZ := zetaTwo_pos
    positivity
  constructor <;> linarith

theorem kernel_one_nonintegral : ¬ ∃ z : ℤ, (z : ℝ) = rawKernel 1 1 := by
  rintro ⟨z,hz⟩
  have hb := kernel_one_bounds
  have hz0 : (0 : ℤ) < z := by exact_mod_cast (show (0 : ℝ) < z by linarith)
  have hz1 : (1 : ℤ) ≤ z := by omega
  have hz1R : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  linarith


def normalizedMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => matrix N i j / (((i.val+1 : ℕ) : ℝ) * (j.val+1 : ℕ))

def siteDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => (i.val+1 : ℕ))

theorem normalization_entry (N : ℕ) (i j : Fin N) :
    matrix N i j =
      ((i.val+1 : ℕ) : ℝ) * normalizedMatrix N i j * (j.val+1 : ℕ) := by
  have hi : ((i.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj : ((j.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold normalizedMatrix
  field_simp [hi, hj]

theorem normalization_congruence (N : ℕ) :
    matrix N = siteDiagonal N * normalizedMatrix N * siteDiagonal N := by
  ext i j
  simp only [siteDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact normalization_entry N i j

theorem legalRemainder_four_relation (d : ℕ) :
    legalRemainder 1 d - legalRemainder 2 d -
      legalRemainder 3 d + legalRemainder 4 d = 0 := by
  by_cases h : 2 ≤ d ∧ Squarefree d
  · have hfour : d ≠ 4 := by
      intro hd
      subst d
      exact (show ¬ Squarefree (4 : ℕ) by decide) h.2
    by_cases hd : d ≤ 4
    · have hd' : d = 2 ∨ d = 3 := by omega
      rcases hd' with rfl | rfl <;> norm_num [legalRemainder, h.2]
    · have h1 : 1 < d := by omega
      have h2 : 2 < d := by omega
      have h3 : 3 < d := by omega
      have h4 : 4 < d := by omega
      norm_num [legalRemainder, h, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
        Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  · simp [legalRemainder, h]

theorem kernel_four_relation (m : ℕ) :
    rawKernel 1 m - rawKernel 2 m - rawKernel 3 m + rawKernel 4 m = 0 := by
  rw [kernel_exact, kernel_exact, kernel_exact, kernel_exact,
    ← (kernel_summable 1 m).tsum_sub (kernel_summable 2 m),
    ← ((kernel_summable 1 m).sub (kernel_summable 2 m)).tsum_sub
      (kernel_summable 3 m),
    ← (((kernel_summable 1 m).sub (kernel_summable 2 m)).sub
      (kernel_summable 3 m)).tsum_add (kernel_summable 4 m)]
  have he (d : ℕ) :
      positiveQWeight d * legalRemainder 1 d * legalRemainder m d -
      positiveQWeight d * legalRemainder 2 d * legalRemainder m d -
      positiveQWeight d * legalRemainder 3 d * legalRemainder m d +
      positiveQWeight d * legalRemainder 4 d * legalRemainder m d = 0 := by
    have hh := legalRemainder_four_relation d
    calc
      _ = positiveQWeight d * (legalRemainder 1 d - legalRemainder 2 d -
        legalRemainder 3 d + legalRemainder 4 d) * legalRemainder m d := by ring
      _ = 0 := by rw [hh]; ring
  simp only [he, tsum_zero]

end RiemannResearch.RH.SquarefreeResidueMatrix
