import RiemannResearch.LinearAlgebra.FiniteCumulativeSignedEnergy
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual Mobius weighted energy and its signed cancellation criterion

Source: user-provided `Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex`,
Sections 6-7 and agenda Step 1. The finite floor equation, the weighted energy,
and its signed cross terms use the actual Mobius function. No RH equivalence
or analytic continuation theorem is assumed or asserted in this module.

The classical RH/Mertens growth equivalence is discussed in K. Soundararajan,
*Partial sums of the Mobius function*, introduction, arXiv:0705.0723.
That reference supplies background, not an unchecked analytic Lean provider.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.MertensWeightedEnergy
open RiemannResearch.LinearAlgebra.CumulativeCellEnergy

/-- Zero-based coordinates represent the positive integers `n+1`. -/
def mobiusCoefficients (n : ℕ) : ℝ := ArithmeticFunction.moebius (n + 1)

def weight (ε : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-2 - 2 * ε)

/-- This is exactly M(N), including M(0)=0. -/
def mertensPrefix (N : ℕ) : ℝ := cumulative mobiusCoefficients N

def finiteEnergy (ε : ℝ) (N : ℕ) : ℝ :=
  weightedPrefixEnergy (weight ε) mobiusCoefficients N

def diagonal (ε : ℝ) (N : ℕ) : ℝ :=
  diagonalEnergy (weight ε) mobiusCoefficients N

def offDiagonal (ε : ℝ) (N : ℕ) : ℝ :=
  offDiagonalEnergy (weight ε) mobiusCoefficients N

/-- Use summability, not the totalized real `tsum`, to express finite energy. -/
def HasFiniteEnergy (ε : ℝ) : Prop :=
  Summable (fun n => weight ε n * mertensPrefix (n + 1) ^ 2)

theorem mobiusCoefficients_sq_le_one (n : ℕ) : mobiusCoefficients n ^ 2 ≤ 1 := by
  have h : |mobiusCoefficients n| ≤ 1 := by
    unfold mobiusCoefficients
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n + 1))
  have h' := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, sq_abs, one_pow] using h'

theorem weight_pos (ε : ℝ) (n : ℕ) : 0 < weight ε n := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem finiteEnergy_identity (ε : ℝ) (N : ℕ) :
    finiteEnergy ε N = diagonal ε N + offDiagonal ε N :=
  weightedPrefixEnergy_eq_diagonal_add_offDiagonal _ _ _

theorem offDiagonal_pair_sum (ε : ℝ) (N : ℕ) :
    offDiagonal ε N = 2 * ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j,
      mobiusCoefficients i * mobiusCoefficients j * tailWeight (weight ε) N j :=
  offDiagonalEnergy_eq_pair_sum _ _ _

theorem finiteEnergy_nonneg (ε : ℝ) (N : ℕ) : 0 ≤ finiteEnergy ε N :=
  weightedPrefixEnergy_nonneg _ _ _ (fun n => (weight_pos ε n).le)

theorem finiteEnergy_monotone (ε : ℝ) : Monotone (finiteEnergy ε) :=
  weightedPrefixEnergy_mono _ _ (fun n => (weight_pos ε n).le)

theorem diagonal_nonneg (ε : ℝ) (N : ℕ) : 0 ≤ diagonal ε N :=
  diagonalEnergy_nonneg _ _ (fun n => (weight_pos ε n).le) N

theorem weight_mul_index (ε : ℝ) (n : ℕ) :
    weight ε n * ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) ^ (-1 - 2 * ε) := by
  simp only [weight, Nat.cast_add, Nat.cast_one]
  calc
    _ = ((n : ℝ) + 1) ^ (-2 - 2 * ε) * ((n : ℝ) + 1) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

theorem diagonal_majorant_summable (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-1 - 2 * ε)) := by
  have h := Real.summable_nat_rpow.mpr (show -1 - 2 * ε < -1 by linarith)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h

/-- The diagonal bound is unconditional at every strictly positive damping. -/
theorem diagonal_le_pseries (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    diagonal ε N ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-1 - 2 * ε) := by
  calc
    diagonal ε N ≤ ∑ n ∈ Finset.range N, weight ε n * ((n + 1 : ℕ) : ℝ) :=
      diagonalEnergy_le_linear_weight _ _ (fun n => (weight_pos ε n).le)
        mobiusCoefficients_sq_le_one N
    _ = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-1 - 2 * ε) := by
      simp only [weight_mul_index]
    _ ≤ _ := Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (by positivity) _)
      (diagonal_majorant_summable ε hε)

/-- Exact signed cancellation target: finite weighted Mertens energy is
equivalent to an upper bound on the finite signed off-diagonal sums. -/
theorem hasFiniteEnergy_iff_bounded_offDiagonal (ε : ℝ) (hε : 0 < ε) :
    HasFiniteEnergy ε ↔ ∃ B : ℝ, ∀ N, offDiagonal ε N ≤ B :=
  summable_prefixEnergy_iff_bounded_offDiagonal _ _
    (fun n => (weight_pos ε n).le) _ (diagonal_le_pseries ε hε)

theorem hasFiniteEnergy_iff_bounded_finiteEnergy (ε : ℝ) :
    HasFiniteEnergy ε ↔ ∃ A : ℝ, ∀ N, finiteEnergy ε N ≤ A :=
  RiemannResearch.Analysis.NonnegativeEnergy.summable_iff_nonnegative_prefix_bound
    _ (fun n => mul_nonneg (weight_pos ε n).le (sq_nonneg _))

private theorem sum_fin_positive (f : ℕ → ℝ) (N : ℕ) :
    (∑ i : Fin N, f (i.val + 1)) = ∑ i ∈ Finset.Icc 1 N, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) N]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem mertensPrefix_eq_mobius_sum (N : ℕ) :
    mertensPrefix N = ∑ i ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius i : ℝ) := by
  rw [← sum_fin_positive,
    Fin.sum_univ_eq_sum_range (fun i => (ArithmeticFunction.moebius (i + 1) : ℝ)) N]
  rfl

/-- The paper's floor matrix, with positive physical indices. -/
def floorMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (((i.val + 1) / (j.val + 1) : ℕ) : ℝ)

def cumulativeMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ≤ i then 1 else 0

def weightMatrix (ε : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => weight ε i.val)

def gramMatrix (ε : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (cumulativeMatrix N).transpose * weightMatrix ε N * cumulativeMatrix N

theorem floorMatrix_det (N : ℕ) : (floorMatrix N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [floorMatrix, Nat.div_self (Nat.succ_pos _)]
  · intro i j hij
    have h : i.val + 1 < j.val + 1 := by exact Nat.succ_lt_succ hij
    simp [floorMatrix, Nat.div_eq_of_lt h]

/-- Exact floor inversion for the actual arithmetic vector. -/
theorem floorMatrix_mulVec_mobius (N : ℕ) :
    (floorMatrix N).mulVec (fun i => mobiusCoefficients i.val) = (fun _ => 1) := by
  funext i
  change (∑ d : Fin N, (((i.val + 1) / (d.val + 1) : ℕ) : ℝ) *
    (ArithmeticFunction.moebius (d.val + 1) : ℝ)) = 1
  rw [sum_fin_positive (fun d => (((i.val + 1) / d : ℕ) : ℝ) *
    (ArithmeticFunction.moebius d : ℝ)) N]
  simpa only [mul_comm] using Pareto.finite_mobius_floor_sum N (i.val + 1)
    (by omega) (by have := i.isLt; omega)

theorem floorMatrix_inv_one (N : ℕ) :
    ((floorMatrix N)⁻¹).mulVec (fun _ => 1) = (fun i => mobiusCoefficients i.val) := by
  have h := congrArg (((floorMatrix N)⁻¹).mulVec) (floorMatrix_mulVec_mobius N)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (by rw [floorMatrix_det]; exact isUnit_one), Matrix.one_mulVec] at h
  exact h.symm

theorem cumulativeMatrix_det (N : ℕ) : (cumulativeMatrix N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [cumulativeMatrix]
  · intro i j hij
    have hij' : i < j := hij
    exact if_neg (not_le.mpr hij')

theorem cumulativeMatrix_injective (N : ℕ) :
    Function.Injective (cumulativeMatrix N).mulVec := by
  intro a b hab
  have h := congrArg (((cumulativeMatrix N)⁻¹).mulVec) hab
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (cumulativeMatrix N)
    (by rw [cumulativeMatrix_det N]; exact isUnit_one), Matrix.one_mulVec] using h

/-- Positivity is finite linear algebra, valid even without an energy bound. -/
theorem gramMatrix_posDef (ε : ℝ) (N : ℕ) : (gramMatrix ε N).PosDef := by
  have hd : (weightMatrix ε N).PosDef :=
    Matrix.PosDef.diagonal (fun i => weight_pos ε i.val)
  have h := hd.conjTranspose_mul_mul_same (cumulativeMatrix_injective N)
  have ht : (cumulativeMatrix N).conjTranspose = (cumulativeMatrix N).transpose := by
    ext i j
    simp
  simpa only [gramMatrix, ht] using h

theorem cumulativeMatrix_mulVec (N : ℕ) (a : ℕ → ℝ) (i : Fin N) :
    (cumulativeMatrix N).mulVec (fun j => a j.val) i = cumulative a (i.val + 1) := by
  change (∑ j : Fin N, (if j ≤ i then (1 : ℝ) else 0) * a j.val) = _
  simp only [ite_mul, one_mul, zero_mul, Fin.le_def]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ i.val then a j else 0) N,
    ← Finset.sum_filter]
  have he : (Finset.range N).filter (fun j => j ≤ i.val) =
      Finset.range (i.val + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have := i.isLt
    omega
  rw [he]
  rfl

theorem gramMatrix_quadratic (ε : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    dotProduct x ((gramMatrix ε N).mulVec x) =
      ∑ i : Fin N, weight ε i.val * ((cumulativeMatrix N).mulVec x i) ^ 2 := by
  rw [gramMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [weightMatrix, Matrix.mulVec, Matrix.diagonal_apply, dotProduct]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact tail kernel K(i,j), with the full endpoint N retained. -/
theorem gramMatrix_entry (ε : ℝ) (N : ℕ) (i j : Fin N) :
    gramMatrix ε N i j = tailWeight (weight ε) N (max i.val j.val) := by
  rw [tailWeight_eq_sum_ite _ _ _ (max_le i.isLt.le j.isLt.le)]
  calc
    gramMatrix ε N i j =
        ∑ n : Fin N, if max i.val j.val ≤ n.val then weight ε n.val else 0 := by
      simp only [gramMatrix, weightMatrix, Matrix.mul_apply,
        Matrix.diagonal_apply, Matrix.transpose_apply]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [cumulativeMatrix, Fin.le_def, max_le_iff]
      split_ifs <;> simp_all
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun n => if max i.val j.val ≤ n then weight ε n else 0) N

theorem finiteEnergy_eq_mobius_gram (ε : ℝ) (N : ℕ) :
    finiteEnergy ε N = dotProduct (fun i : Fin N => mobiusCoefficients i.val)
      ((gramMatrix ε N).mulVec (fun i => mobiusCoefficients i.val)) := by
  rw [gramMatrix_quadratic]
  simp only [cumulativeMatrix_mulVec]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => weight ε i * cumulative mobiusCoefficients (i + 1) ^ 2) N]
  rfl

/-- The exact inverse-floor quadratic from the agenda, with both inverse factors. -/
theorem finiteEnergy_eq_inverse_floor_quadratic (ε : ℝ) (N : ℕ) :
    finiteEnergy ε N = dotProduct (fun _ : Fin N => (1 : ℝ))
      ((((floorMatrix N)⁻¹).transpose * gramMatrix ε N * (floorMatrix N)⁻¹).mulVec
        (fun _ => 1)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, floorMatrix_inv_one]
  exact finiteEnergy_eq_mobius_gram ε N

theorem mertensPrefix_abs_le (N : ℕ) : |mertensPrefix N| ≤ N := by
  unfold mertensPrefix RiemannResearch.LinearAlgebra.CumulativeCellEnergy.cumulative
  calc
    _ ≤ ∑ i ∈ Finset.range N, |mobiusCoefficients i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold mobiusCoefficients
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i + 1))
    _ = _ := by simp

theorem hasFiniteEnergy_mono {ε δ : ℝ} (hεδ : ε ≤ δ)
    (hE : HasFiniteEnergy ε) : HasFiniteEnergy δ := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_pos δ n).le (sq_nonneg _)) _ hE
  intro n
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (n : ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    (by linarith)

/-- Unconditional baseline from |M(n)| ≤ n; the critical small dampings
needed by the RH criterion are not supplied by this estimate. -/
theorem hasFiniteEnergy_of_half_lt {ε : ℝ} (hε : 1/2 < ε) : HasFiniteEnergy ε := by
  have hs : Summable (fun n : ℕ => ((n : ℝ)+1)^(-2*ε)) := by
    have hp := Real.summable_nat_rpow.mpr (show -2*ε < -1 by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_pos ε n).le (sq_nonneg _)) _ hs
  intro n
  have hx : 0 < (n : ℝ)+1 := by positivity
  have hb : mertensPrefix (n+1)^2 ≤ ((n : ℝ)+1)^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) (mertensPrefix_abs_le (n+1))
    simpa only [← pow_two, sq_abs, Nat.cast_add, Nat.cast_one] using hh
  calc
    weight ε n * mertensPrefix (n+1)^2 ≤ weight ε n * ((n : ℝ)+1)^2 :=
      mul_le_mul_of_nonneg_left hb (weight_pos ε n).le
    _ = _ := by
      rw [weight, ← Real.rpow_two, ← Real.rpow_add hx]
      congr 1
      ring

/-- Arbitrarily late bounded signed sums are enough: monotonicity applies
to total energy while the signed term is kept intact. -/
theorem hasFiniteEnergy_iff_frequently_bounded_offDiagonal (ε : ℝ) (hε : 0 < ε) :
    HasFiniteEnergy ε ↔
      ∃ B : ℝ, ∃ᶠ N : ℕ in atTop, offDiagonal ε N ≤ B := by
  constructor
  · intro hE
    obtain ⟨B, hB⟩ := (hasFiniteEnergy_iff_bounded_offDiagonal ε hε).mp hE
    exact ⟨B, (Eventually.of_forall hB).frequently⟩
  · rintro ⟨B, hB⟩
    apply (hasFiniteEnergy_iff_bounded_finiteEnergy ε).mpr
    let D : ℝ := ∑' n : ℕ, ((n : ℝ)+1)^(-1-2*ε)
    refine ⟨D+B, fun n => ?_⟩
    obtain ⟨N, hgood, hN⟩ := (hB.and_eventually (eventually_ge_atTop n)).exists
    have hdiag : diagonal ε N ≤ D := diagonal_le_pseries ε hε N
    calc
      finiteEnergy ε n ≤ finiteEnergy ε N := finiteEnergy_monotone ε hN
      _ = diagonal ε N + offDiagonal ε N := finiteEnergy_identity ε N
      _ ≤ D+B := add_le_add hdiag hgood

end RiemannResearch.RH.MertensWeightedEnergy
