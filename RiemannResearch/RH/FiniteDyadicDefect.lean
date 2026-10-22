import RiemannResearch.RH.OptimalProjectionDilationGaps
import RiemannResearch.RH.ResidualDyadicFactor
import RiemannResearch.RH.ReciprocalGramCorrection
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Exact dyadic balances for the actual optimal projections

Independent assembly of the existing exact dilation, finite projection, and
reciprocal Gram correction identities. No novelty claim is made.

The conductor cutoff doubles at each step: stage n becomes 2*n+1.
The failure of the finite residual to satisfy the limiting dyadic square
identity is a pairing of two successive projection increments. Its absolute
values have a finite telescoping budget. The primary finite equality retains
both normalized-dilation norm-square remainders, the signed Mobius sum, and
all boundary energies. The exact cumulative slope is also proved; zero slope
implies RH, but zero slope remains an explicit open hypothesis.

Source: equality-first refinement of the user-directed research argument,
2026-09-29, using polarization and Cesaro convergence. No novelty is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
set_option backward.isDefEq.respectTransparency false

def doubleStage (n : ℕ) : ℕ := 2 * n + 1

def dyadicStage (b : ℕ) : ℕ → ℕ
  | 0 => b
  | k + 1 => doubleStage (dyadicStage b k)

def finiteDyadicDefect (n : ℕ) : ℝ :=
  inner ℝ (projectionResidual n) (doubleDilation (projection n))

def finiteDyadicFactor (n : ℕ) : ThresholdHilbert :=
  projectionResidual n - (1 - Real.sqrt 2 / 2) •
    doubleDilation (projectionResidual n)

def finiteDyadicSquare (n : ℕ) : ℝ :=
  (1 + Real.sqrt 2 / 2) * ‖finiteDyadicFactor n‖ ^ 2

/-- Polarization for the normalized dyadic isometry, with its full remainder. -/
theorem doubleDilation_inner_eq_norm_remainder (x y : ThresholdHilbert) :
    inner ℝ x (doubleDilation y) = (Real.sqrt 2 / 2) *
      (‖x‖ ^ 2 + ‖y‖ ^ 2 -
        ‖x - (Real.sqrt 2 / 2) • doubleDilation y‖ ^ 2) := by
  have ha : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hd : ‖doubleDilation y‖ ^ 2 = 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner, real_inner_self_eq_norm_sq]
  have hn : ‖(Real.sqrt 2 / 2) • doubleDilation y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha, hd]
    ring
  have hp := norm_sub_sq_real x ((Real.sqrt 2 / 2) • doubleDilation y)
  rw [hn, inner_smul_right] at hp
  calc
    _ = (2 * (Real.sqrt 2 / 2) ^ 2) * inner ℝ x (doubleDilation y) := by
      rw [ha]
      ring
    _ = _ := by nlinarith [congrArg (fun t : ℝ => (Real.sqrt 2 / 2) * t) hp]

/-- The residual mismatch under the normalized dyadic isometry. -/
def finiteDyadicResidualRemainder (n : ℕ) : ℝ :=
  ‖projectionResidual n - (Real.sqrt 2 / 2) •
    doubleDilation (projectionResidual n)‖ ^ 2

/-- The complete mismatch between consecutive dyadic projection increments. -/
def finiteDyadicIncrementRemainder (m : ℕ) : ℝ :=
  ‖(projection (doubleStage (doubleStage m)) - projection (doubleStage m)) -
    (Real.sqrt 2 / 2) • doubleDilation (projection (doubleStage m) - projection m)‖ ^ 2

/-- Exact refinement of the previous energy lower bound: the square is retained. -/
theorem finiteDyadicSquare_eq_energy_add_remainder (n : ℕ) :
    finiteDyadicSquare n = (2 - Real.sqrt 2) * energy n +
      (Real.sqrt 2 / 2) * finiteDyadicResidualRemainder n := by
  have hs := dyadic_factor_energy (projectionResidual n)
  change finiteDyadicSquare n = 2 * energy n -
    inner ℝ (projectionResidual n) (doubleDilation (projectionResidual n)) at hs
  rw [hs, doubleDilation_inner_eq_norm_remainder]
  change 2 * energy n - (Real.sqrt 2 / 2) *
    (energy n + energy n - finiteDyadicResidualRemainder n) = _
  ring

theorem doubleDilation_mem_double {n : ℕ} {x : ThresholdHilbert}
    (hx : x ∈ finiteSpace n) :
    doubleDilation x ∈ finiteSpace (doubleStage n) := by
  classical
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n x hx
  rw [map_sum]
  apply (finiteSpace (doubleStage n)).sum_mem
  intro i hi
  rw [map_smul]
  apply (finiteSpace (doubleStage n)).smul_mem
  change hilbertDilation 2 (by decide) (residueAtom i.val) ∈ _
  rw [hilbertDilation_residueAtom]
  apply (finiteSpace (doubleStage n)).sub_mem
  · apply (finiteSpace (doubleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hiN : i.val + 2 ≤ n + 1 := by omega
    simp only [doubleStage]
    omega
  · apply (finiteSpace (doubleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    simp only [doubleStage]
    omega

theorem projectionResidual_inner_one (n : ℕ) :
    inner ℝ (projectionResidual n) hilbertOne = energy n := by
  have ho := projectionResidual_inner_mem n (projection n)
    ((finiteSpace n).starProjection_apply_mem _)
  have he : hilbertOne = projectionResidual n + projection n := by
    unfold projectionResidual
    abel
  rw [he, inner_add_right, ho, add_zero, real_inner_self_eq_norm_sq]
  rfl

theorem finite_firstCoordinate_dyadic_identity (n : ℕ) :
    hilbertSequence (projectionResidual n) 1 =
      2 * energy n - inner ℝ (projectionResidual n)
        (doubleDilation (projectionResidual n)) - finiteDyadicDefect n := by
  have h := congrArg (fun f => inner ℝ (projectionResidual n) f)
    firstPoint_eq_dilation_difference
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq, inner_sub_right,
    inner_smul_right, projectionResidual_inner_one] at h
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at h
  have he : hilbertOne = projectionResidual n + projection n := by
    unfold projectionResidual
    abel
  have hd : inner ℝ (projectionResidual n) (doubleDilation hilbertOne) =
      inner ℝ (projectionResidual n) (doubleDilation (projectionResidual n)) +
        finiteDyadicDefect n := by
    rw [he, map_add, inner_add_right]
    rfl
  change (1 / 2 : ℝ) * hilbertSequence (projectionResidual n) 1 =
    energy n - (1 / 2 : ℝ) *
      inner ℝ (projectionResidual n) (doubleDilation hilbertOne) at h
  rw [hd] at h
  linarith

theorem finite_firstCoordinate_eq_dyadicSquare_sub_defect (n : ℕ) :
    hilbertSequence (projectionResidual n) 1 =
      finiteDyadicSquare n - finiteDyadicDefect n := by
  have hs := dyadic_factor_energy (projectionResidual n)
  change finiteDyadicSquare n =
    2 * energy n - inner ℝ (projectionResidual n)
      (doubleDilation (projectionResidual n)) at hs
  rw [hs]
  exact finite_firstCoordinate_dyadic_identity n

/-- The defect at the middle scale pairs two consecutive projection gains. -/
theorem finiteDyadicDefect_two_gap (m : ℕ) :
    finiteDyadicDefect (doubleStage m) =
      inner ℝ (projection (doubleStage (doubleStage m)) - projection (doubleStage m))
        (doubleDilation (projection (doubleStage m) - projection m)) := by
  let n := doubleStage m
  let k := doubleStage n
  have hm : projection m ∈ finiteSpace m := (finiteSpace m).starProjection_apply_mem _
  have hn : projection n ∈ finiteSpace n := (finiteSpace n).starProjection_apply_mem _
  have hmn : m ≤ n := by dsimp [n, doubleStage]; omega
  have hv : doubleDilation (projection m) ∈ finiteSpace n :=
    doubleDilation_mem_double hm
  have h0 := projectionResidual_inner_mem n _ hv
  have hdiff : projection n - projection m ∈ finiteSpace n :=
    (finiteSpace n).sub_mem hn (walkSpan_mono residueAtom id hmn hm)
  have h1 := projectionResidual_inner_mem k _ (doubleDilation_mem_double hdiff)
  change inner ℝ (projectionResidual n) (doubleDilation (projection n)) =
    inner ℝ (projection k - projection n)
      (doubleDilation (projection n - projection m))
  have he : projectionResidual n =
      projectionResidual k + (projection k - projection n) := by
    unfold projectionResidual
    abel
  calc
    _ = inner ℝ (projectionResidual n)
        (doubleDilation (projection n - projection m)) := by
      rw [map_sub, inner_sub_right, h0, sub_zero]
    _ = _ := by rw [he, inner_add_left, h1, zero_add]

/-- The signed defect is an exact two-step energy drop minus a norm square. -/
theorem finiteDyadicDefect_eq_energy_drop_sub_remainder (m : ℕ) :
    finiteDyadicDefect (doubleStage m) = (Real.sqrt 2 / 2) *
      (energy m - energy (doubleStage (doubleStage m)) -
        finiteDyadicIncrementRemainder m) := by
  rw [finiteDyadicDefect_two_gap, doubleDilation_inner_eq_norm_remainder,
    projection_gap_sq (show doubleStage m ≤ doubleStage (doubleStage m) by
      unfold doubleStage; omega),
    projection_gap_sq (show m ≤ doubleStage m by unfold doubleStage; omega)]
  change (Real.sqrt 2 / 2) *
    ((energy (doubleStage m) - energy (doubleStage (doubleStage m))) +
      (energy m - energy (doubleStage m)) - finiteDyadicIncrementRemainder m) = _
  ring

/-- Exact finite telescope, retaining the signed defect sum, all boundary
energies, and the complete increment remainder sum. -/
theorem finiteDyadicDefect_sum_eq_boundary_sub_remainders (b K : ℕ) :
    (∑ k ∈ Finset.range K, finiteDyadicDefect (dyadicStage b (k + 1))) =
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1)) -
          ∑ k ∈ Finset.range K, finiteDyadicIncrementRemainder (dyadicStage b k)) := by
  induction K with
  | zero => simp [dyadicStage]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := finiteDyadicDefect_eq_energy_drop_sub_remainder (dyadicStage b K)
    change finiteDyadicDefect (dyadicStage b (K + 1)) = (Real.sqrt 2 / 2) *
      (energy (dyadicStage b K) - energy (dyadicStage b (K + 2)) -
        finiteDyadicIncrementRemainder (dyadicStage b K)) at h
    rw [h]
    ring

theorem finiteDyadicDefect_two_gap_sq (m : ℕ) :
    finiteDyadicDefect (doubleStage m) ^ 2 ≤
      2 * (energy m - energy (doubleStage m)) *
        (energy (doubleStage m) - energy (doubleStage (doubleStage m))) := by
  rw [finiteDyadicDefect_two_gap]
  let a := projection (doubleStage (doubleStage m)) - projection (doubleStage m)
  let b := projection (doubleStage m) - projection m
  have h := norm_inner_le_norm (𝕜 := ℝ) a (doubleDilation b)
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  rw [Real.norm_eq_abs] at hs
  have hd : ‖doubleDilation b‖ ^ 2 = 2 * ‖b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner, real_inner_self_eq_norm_sq]
  have ha : ‖a‖ ^ 2 =
      energy (doubleStage m) - energy (doubleStage (doubleStage m)) :=
    projection_gap_sq (by unfold doubleStage; omega)
  have hb : ‖b‖ ^ 2 = energy m - energy (doubleStage m) :=
    projection_gap_sq (by unfold doubleStage; omega)
  change (inner ℝ a (doubleDilation b)) ^ 2 ≤ _
  rw [← ha, ← hb]
  nlinarith [sq_abs (inner ℝ a (doubleDilation b))]

theorem finiteDyadicDefect_two_gap_abs (m : ℕ) :
    |finiteDyadicDefect (doubleStage m)| ≤
      (Real.sqrt 2 / 2) *
        (energy m - energy (doubleStage (doubleStage m))) := by
  let a := energy m - energy (doubleStage m)
  let b := energy (doubleStage m) - energy (doubleStage (doubleStage m))
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [← projection_gap_sq (show m ≤ doubleStage m by unfold doubleStage; omega)]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    rw [← projection_gap_sq (show doubleStage m ≤ doubleStage (doubleStage m) by
      unfold doubleStage; omega)]
    positivity
  have hs := finiteDyadicDefect_two_gap_sq m
  change finiteDyadicDefect (doubleStage m) ^ 2 ≤ 2 * a * b at hs
  have hy : 0 ≤ (Real.sqrt 2 / 2) * (a + b) := by positivity
  have hy2 : ((Real.sqrt 2 / 2) * (a + b)) ^ 2 = (1 / 2 : ℝ) * (a + b) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : |finiteDyadicDefect (doubleStage m)| ^ 2 ≤
      ((Real.sqrt 2 / 2) * (a + b)) ^ 2 := by
    rw [sq_abs, hy2]
    nlinarith [sq_nonneg (a - b)]
  have ht := (sq_le_sq₀ (abs_nonneg _) hy).mp hsq
  have hab : a + b = energy m - energy (doubleStage (doubleStage m)) := by
    dsimp [a, b]
    ring
  simpa only [hab] using ht

/-- Finite, explicit l1 budget, retaining both terminal energies. -/
theorem finiteDyadicDefect_sum_abs_le (b K : ℕ) :
    (∑ k ∈ Finset.range K, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  induction K with
  | zero => simp [dyadicStage]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h := finiteDyadicDefect_two_gap_abs (dyadicStage b K)
    change |finiteDyadicDefect (dyadicStage b (K + 1))| ≤
      (Real.sqrt 2 / 2) *
        (energy (dyadicStage b K) - energy (dyadicStage b (K + 2))) at h
    calc
      _ ≤ (Real.sqrt 2 / 2) *
          (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
            energy (dyadicStage b (K + 1))) +
          (Real.sqrt 2 / 2) *
            (energy (dyadicStage b K) - energy (dyadicStage b (K + 2))) :=
        add_le_add ih h
      _ = _ := by ring

theorem finiteDyadicSquare_lower (n : ℕ) :
    (2 - Real.sqrt 2) * energy n ≤ finiteDyadicSquare n := by
  have hs := dyadic_factor_energy (projectionResidual n)
  change finiteDyadicSquare n = 2 * energy n -
    inner ℝ (projectionResidual n) (doubleDilation (projectionResidual n)) at hs
  have h := norm_inner_le_norm (𝕜 := ℝ) (projectionResidual n)
    (hilbertDilation 2 (by decide) (projectionResidual n))
  rw [hilbertDilation_norm, Real.norm_eq_abs] at h
  have hb : |inner ℝ (projectionResidual n) (doubleDilation (projectionResidual n))| ≤
      Real.sqrt 2 * energy n := by
    calc
      _ ≤ ‖projectionResidual n‖ * (Real.sqrt 2 * ‖projectionResidual n‖) := h
      _ = Real.sqrt 2 * ‖projectionResidual n‖ ^ 2 := by ring
      _ = _ := rfl
  rw [hs]
  nlinarith [(abs_le.mp hb).2]

theorem finite_firstCoordinate_deficit_le (n : ℕ) :
    max 0 ((2 - Real.sqrt 2) * energy n -
      hilbertSequence (projectionResidual n) 1) ≤ |finiteDyadicDefect n| := by
  apply max_le (abs_nonneg _)
  have hl := finiteDyadicSquare_lower n
  rw [finite_firstCoordinate_eq_dyadicSquare_sub_defect]
  exact (by linarith : (2 - Real.sqrt 2) * energy n -
    (finiteDyadicSquare n - finiteDyadicDefect n) ≤ finiteDyadicDefect n).trans
      (le_abs_self _)

/-- The exact centered signed reciprocal Gram statistic has the same budget. -/
theorem reciprocalCorrection_add_dyadicSquare_sub_mobius (n : ℕ) :
    GramMobiusCorrection.reciprocalCorrection n + finiteDyadicSquare n -
      mobiusReciprocalSum (n + 1) = finiteDyadicDefect n := by
  have h := GramMobiusCorrection.reciprocalCorrection_eq_firstCoordinate n
  have he : hilbertSequence (projectionResidual n) 1 =
      1 - anchoredEvaluationCLM 1 (projection n) := by
    rw [← anchoredEvaluationCLM_apply]
    change anchoredEvaluationCLM 1 (hilbertOne - projection n) = _
    have hone : anchoredEvaluationCLM 1 hilbertOne = 1 := by
      rw [anchoredEvaluationCLM_apply, hilbertOne_sequence]
      norm_num [zeroAnchor]
    rw [map_sub, hone]
  have hs := finite_firstCoordinate_eq_dyadicSquare_sub_defect n
  rw [he] at hs
  linarith

/-- Full signed reciprocal-correction identity. No norm square, signed Mobius
summand, or boundary term is discarded. Valid also for K = 0. -/
theorem reciprocalCorrection_dyadic_sum_eq_full_remainders (b K : ℕ) :
    -(∑ k ∈ Finset.range K,
      GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) =
      (2 - Real.sqrt 2) * (∑ k ∈ Finset.range K, energy (dyadicStage b (k + 1))) +
      (Real.sqrt 2 / 2) * (∑ k ∈ Finset.range K,
        (finiteDyadicResidualRemainder (dyadicStage b (k + 1)) +
          finiteDyadicIncrementRemainder (dyadicStage b k))) -
      (∑ k ∈ Finset.range K, mobiusReciprocalSum (dyadicStage b (k + 1) + 1)) -
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  have hc := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range K) =>
    reciprocalCorrection_add_dyadicSquare_sub_mobius (dyadicStage b (k + 1)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hc
  have hj := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range K) =>
    finiteDyadicSquare_eq_energy_add_remainder (dyadicStage b (k + 1)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hj
  rw [finiteDyadicDefect_sum_eq_boundary_sub_remainders] at hc
  rw [Finset.sum_add_distrib]
  linarith

theorem reciprocalCorrection_dyadic_sum_abs_le (b K : ℕ) :
    (∑ k ∈ Finset.range K,
      |GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1)) +
          finiteDyadicSquare (dyadicStage b (k + 1)) -
            mobiusReciprocalSum (dyadicStage b (k + 1) + 1)|) ≤
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  simp_rw [reciprocalCorrection_add_dyadicSquare_sub_mobius]
  exact finiteDyadicDefect_sum_abs_le b K

/-- Finite cumulative signed drift. An arithmetic lower bound on the energy
can be inserted here without changing the actual inverse-Gram coefficients. -/
theorem reciprocalCorrection_dyadic_sum_le (b K : ℕ) :
    (∑ k ∈ Finset.range K,
      GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) ≤
      (∑ k ∈ Finset.range K, mobiusReciprocalSum (dyadicStage b (k + 1) + 1)) -
      (2 - Real.sqrt 2) * (∑ k ∈ Finset.range K, energy (dyadicStage b (k + 1))) +
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  have ht : (∑ k ∈ Finset.range K,
      GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) ≤
      ∑ k ∈ Finset.range K,
        (mobiusReciprocalSum (dyadicStage b (k + 1) + 1) -
          (2 - Real.sqrt 2) * energy (dyadicStage b (k + 1)) +
            |finiteDyadicDefect (dyadicStage b (k + 1))|) := by
    apply Finset.sum_le_sum
    intro k hk
    have he := reciprocalCorrection_add_dyadicSquare_sub_mobius
      (dyadicStage b (k + 1))
    have hl := finiteDyadicSquare_lower (dyadicStage b (k + 1))
    have hb := le_abs_self (finiteDyadicDefect (dyadicStage b (k + 1)))
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at ht
  have hb := finiteDyadicDefect_sum_abs_le b K
  linarith

theorem finiteDyadicDefect_sum_abs_uniform (b K : ℕ) :
    (∑ k ∈ Finset.range K, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) * (energy b + energy (doubleStage b)) := by
  apply (finiteDyadicDefect_sum_abs_le b K).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hK : 0 ≤ energy (dyadicStage b K) := sq_nonneg _
  have hK1 : 0 ≤ energy (dyadicStage b (K + 1)) := sq_nonneg _
  linarith

theorem finiteDyadicDefect_abs_summable (b : ℕ) :
    Summable (fun k => |finiteDyadicDefect (dyadicStage b (k + 1))|) := by
  exact summable_of_sum_range_le (fun _ => abs_nonneg _)
    (finiteDyadicDefect_sum_abs_uniform b)

theorem finiteDyadicDefect_summable (b : ℕ) :
    Summable (fun k => finiteDyadicDefect (dyadicStage b (k + 1))) :=
  (finiteDyadicDefect_abs_summable b).of_abs

theorem finiteDyadicDefect_tsum_abs_le (b : ℕ) :
    (∑' k, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) * (energy b + energy (doubleStage b)) :=
  Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _)
    (finiteDyadicDefect_sum_abs_uniform b)

theorem reciprocalCorrection_centered_dyadic_abs_summable (b : ℕ) :
    Summable (fun k =>
      |GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1)) +
          finiteDyadicSquare (dyadicStage b (k + 1)) -
            mobiusReciprocalSum (dyadicStage b (k + 1) + 1)|) := by
  simpa only [reciprocalCorrection_add_dyadicSquare_sub_mobius] using
    finiteDyadicDefect_abs_summable b

theorem finiteDyadicDefect_sum_abs_limit_bound (b K : ℕ) :
    (∑ k ∈ Finset.range K, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - 2 * limitEnergy) := by
  apply (finiteDyadicDefect_sum_abs_le b K).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hK := energy_eq_limit_add (dyadicStage b K)
  have hK1 := energy_eq_limit_add (dyadicStage b (K + 1))
  nlinarith [sq_nonneg ‖limitProjection - projection (dyadicStage b K)‖,
    sq_nonneg ‖limitProjection - projection (dyadicStage b (K + 1))‖]

theorem finiteDyadicDefect_tsum_abs_limit_bound (b : ℕ) :
    (∑' k, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - 2 * limitEnergy) :=
  Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _)
    (finiteDyadicDefect_sum_abs_limit_bound b)

theorem finiteDyadicDefect_tsum_abs_gap_bound (b : ℕ) :
    (∑' k, |finiteDyadicDefect (dyadicStage b (k + 1))|) ≤
      Real.sqrt 2 * (energy b - limitEnergy) := by
  apply (finiteDyadicDefect_tsum_abs_limit_bound b).trans
  have hm := energy_antitone (show b ≤ doubleStage b by unfold doubleStage; omega)
  have hs := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg 2)
  nlinarith

/-- Positive excursions of the actual reciprocal correction are paid for by
only the scalar Mobius sum and the summable two-gap defect. -/
theorem reciprocalCorrection_positive_part_le (n : ℕ) :
    max 0 (GramMobiusCorrection.reciprocalCorrection n) ≤
      |mobiusReciprocalSum (n + 1)| + |finiteDyadicDefect n| := by
  have he := reciprocalCorrection_add_dyadicSquare_sub_mobius n
  have hq : 0 ≤ finiteDyadicSquare n := by
    unfold finiteDyadicSquare
    positivity
  apply max_le (by positivity)
  linarith [le_abs_self (mobiusReciprocalSum (n + 1)),
    le_abs_self (finiteDyadicDefect n)]

/-- Unconditional finite positive-part budget for the genuine inverse-Gram
statistic, with the complete remaining scalar arithmetic contribution. -/
theorem reciprocalCorrection_dyadic_positive_sum_le (b K : ℕ) :
    (∑ k ∈ Finset.range K,
      max 0 (GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1)))) ≤
      (∑ k ∈ Finset.range K, |mobiusReciprocalSum (dyadicStage b (k + 1) + 1)|) +
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  have h := Finset.sum_le_sum (s := Finset.range K)
    (fun k _ => reciprocalCorrection_positive_part_le (dyadicStage b (k + 1)))
  rw [Finset.sum_add_distrib] at h
  exact h.trans (add_le_add (le_refl _) (finiteDyadicDefect_sum_abs_le b K))

/-- Exact limiting first-coordinate identity with the normalized-dilation
remainder retained. -/
theorem firstCoordinate_eq_energy_add_dyadicRemainder :
    hilbertSequence limitResidual 1 = (2 - Real.sqrt 2) * limitEnergy +
      (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2 := by
  have h := firstCoordinate_energy_identity
  change hilbertSequence limitResidual 1 / 2 = limitEnergy -
    inner ℝ limitResidual (doubleDilation limitResidual) / 2 at h
  rw [doubleDilation_inner_eq_norm_remainder] at h
  change hilbertSequence limitResidual 1 / 2 = limitEnergy -
    ((Real.sqrt 2 / 2) * (limitEnergy + limitEnergy -
      ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2)) / 2 at h
  linarith

theorem reciprocalCorrection_tendsto_full_remainder :
    Tendsto GramMobiusCorrection.reciprocalCorrection atTop
      (𝓝 (-((2 - Real.sqrt 2) * limitEnergy + (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2))) := by
  simpa only [firstCoordinate_eq_energy_add_dyadicRemainder] using
    GramMobiusCorrection.reciprocalCorrection_tendsto

theorem dyadicStage_tendsto (b : ℕ) : Tendsto (dyadicStage b) atTop atTop := by
  have hle : ∀ k, k ≤ dyadicStage b k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => simp only [dyadicStage, doubleStage]; omega
  exact tendsto_atTop_mono hle tendsto_id

/-- The cumulative signed correction has an exact linear slope. Both limiting
energy contributions remain explicit; their vanishing is not asserted. -/
theorem reciprocalCorrection_dyadic_average_tendsto (b : ℕ) :
    Tendsto (fun K : ℕ =>
      -(∑ k ∈ Finset.range K,
        GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) / (K : ℝ))
      atTop (𝓝 ((2 - Real.sqrt 2) * limitEnergy + (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2)) := by
  have h := (reciprocalCorrection_tendsto_full_remainder.comp
    ((dyadicStage_tendsto b).comp (tendsto_add_atTop_nat 1))).neg.cesaro
  simpa only [Function.comp_def, Finset.sum_neg_distrib, neg_neg,
    div_eq_mul_inv, mul_comm] using h

/-- Zero slope is exactly residual vanishing, with the arithmetic limit
condition kept explicit. -/
theorem reciprocalCorrection_dyadic_average_zero_iff_residual_zero (b : ℕ) :
    Tendsto (fun K : ℕ =>
      -(∑ k ∈ Finset.range K,
        GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) / (K : ℝ))
      atTop (𝓝 0) ↔ limitResidual = 0 := by
  have ht := reciprocalCorrection_dyadic_average_tendsto b
  rw [← firstCoordinate_eq_energy_add_dyadicRemainder] at ht
  constructor
  · intro h
    exact firstCoordinate_zero_iff_residual_zero.mp (tendsto_nhds_unique ht h)
  · intro h
    have hz := firstCoordinate_zero_iff_residual_zero.mpr h
    simpa only [hz] using ht

/-- Conditional RH reduction: establishing zero cumulative slope remains open. -/
theorem riemannHypothesis_of_reciprocalCorrection_dyadic_average_zero (b : ℕ)
    (h : Tendsto (fun K : ℕ =>
      -(∑ k ∈ Finset.range K,
        GramMobiusCorrection.reciprocalCorrection (dyadicStage b (k + 1))) / (K : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    ((reciprocalCorrection_dyadic_average_zero_iff_residual_zero b).mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
