/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Probability.DeterminantalBernoulliCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Poisson generating-function and vacancy limits for moving DPP windows

Source: elementary logarithmic estimate, applied to the already verified
finite spectral generating function. The dimensions may vary arbitrarily.
These theorems are conditional on convergence of the first and second
spectral sums; no arithmetic provider is assumed or asserted.
-/

noncomputable section
open Filter Matrix MeasureTheory
open scoped BigOperators Topology Classical

namespace RiemannResearch.Probability.DPP

/-- A quantitative scalar estimate, with its signed first-order remainder. -/
theorem log_one_sub_add_bounds {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    -2 * t ^ 2 ≤ Real.log (1 - t) + t ∧
      Real.log (1 - t) + t ≤ 0 := by
  have hpos : 0 < 1 - t := by linarith
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hl
  have hi : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp
    <;> ring
  rw [hi] at hl
  have hquad : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 2 * t by linarith)]
  constructor <;> linarith

/-- Exact product logarithm and the finite quadratic remainder budget. -/
theorem log_prod_one_sub_bounds {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1 / 2) :
    -2 * (∑ i, p i ^ 2) ≤
        Real.log (∏ i, (1 - p i)) + ∑ i, p i ∧
      Real.log (∏ i, (1 - p i)) + ∑ i, p i ≤ 0 := by
  rw [Real.log_prod (fun i _ => (show 0 < 1 - p i by linarith [hp' i]).ne')]
  rw [← Finset.sum_add_distrib]
  constructor
  · calc
      -2 * (∑ i, p i ^ 2) = ∑ i, (-2 * p i ^ 2) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (log_one_sub_add_bounds (hp i) (hp' i)).1)
  · exact (Finset.sum_le_sum (fun i _ => (log_one_sub_add_bounds (hp i) (hp' i)).2)).trans_eq
      (by simp)

/-- A vanishing sum of squares makes every entry of a moving finite vector
small, including when its dimension grows. -/
theorem eventually_le_half_of_sum_sq_tendsto_zero
    (d : ℕ → ℕ) (p : (N : ℕ) → Fin (d N) → ℝ)
    (hp : ∀ N i, 0 ≤ p N i)
    (h2 : Tendsto (fun N => ∑ i, p N i ^ 2) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, ∀ i, p N i ≤ 1 / 2 := by
  filter_upwards [h2.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))]
    with N hN i
  have hi : p N i ^ 2 ≤ ∑ j, p N j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (p N j)) (Finset.mem_univ i)
  nlinarith [hp N i]

/-- Law-of-small-numbers product limit. The first two spectral sums suffice;
an additional maximum-eigenvalue hypothesis is redundant. -/
theorem prod_one_sub_tendsto_exp_neg
    (d : ℕ → ℕ) (p : (N : ℕ) → Fin (d N) → ℝ) (rate : ℝ)
    (hp : ∀ N i, 0 ≤ p N i)
    (h1 : Tendsto (fun N => ∑ i, p N i) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, p N i ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ∏ i, (1 - p N i)) atTop (𝓝 (Real.exp (-rate))) := by
  have hsmall := eventually_le_half_of_sum_sq_tendsto_zero d p hp h2
  have hrem : Tendsto (fun N =>
      Real.log (∏ i, (1 - p N i)) + ∑ i, p N i) atTop (𝓝 0) := by
    have hn2 : Tendsto (fun N => -2 * (∑ i, p N i ^ 2)) atTop (𝓝 0) := by
      convert h2.const_mul (-2) using 1 <;> norm_num
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hn2 tendsto_const_nhds
    · filter_upwards [hsmall] with N hN
      exact (log_prod_one_sub_bounds (p N) (hp N) hN).1
    · filter_upwards [hsmall] with N hN
      exact (log_prod_one_sub_bounds (p N) (hp N) hN).2
  have hlog : Tendsto (fun N => Real.log (∏ i, (1 - p N i))) atTop (𝓝 (-rate)) := by
    simpa only [add_sub_cancel_right, zero_sub] using hrem.sub h1
  have he := Real.continuous_exp.continuousAt.tendsto.comp hlog
  apply he.congr'
  filter_upwards [hsmall] with N hN
  exact Real.exp_log (Finset.prod_pos (fun i _ => by linarith [hN i]))

/-- Conditional Poisson PGF limit, including `z = 0` (vacancy).
The parameter interval `[0,1]` is sufficient to characterize a count law. -/
theorem bernoulli_product_tendsto_poisson_pgf
    (d : ℕ → ℕ) (p : (N : ℕ) → Fin (d N) → ℝ) (rate z : ℝ)
    (hp : ∀ N i, 0 ≤ p N i)
    (h1 : Tendsto (fun N => ∑ i, p N i) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, p N i ^ 2) atTop (𝓝 0))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∏ i, (1 - p N i + z * p N i)) atTop
      (𝓝 (Real.exp ((z - 1) * rate))) := by
  have hq1 : Tendsto (fun N => ∑ i, (1 - z) * p N i) atTop (𝓝 ((1 - z) * rate)) := by
    simpa only [Finset.mul_sum] using h1.const_mul (1 - z)
  have hq2 : Tendsto (fun N => ∑ i, ((1 - z) * p N i) ^ 2) atTop (𝓝 0) := by
    simpa only [mul_pow, ← Finset.mul_sum, mul_zero] using h2.const_mul ((1 - z) ^ 2)
  have hh := prod_one_sub_tendsto_exp_neg d (fun N i => (1 - z) * p N i)
    ((1 - z) * rate) (fun N i => mul_nonneg (sub_nonneg.mpr hz.2) (hp N i)) hq1 hq2
  have hfun : (fun N => ∏ i, (1 - (1 - z) * p N i)) =
      (fun N => ∏ i, (1 - p N i + z * p N i)) := by
    funext N
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hfun] at hh
  have he : -((1 - z) * rate) = (z - 1) * rate := by ring
  simpa only [he] using hh

end RiemannResearch.Probability.DPP

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The squared spectral mass is exactly the squared-entry mass. -/
theorem IsHermitian.sum_sq_eigenvalues_eq_sum_sq_entries (hQ : Q.IsHermitian) :
    (∑ i, hQ.eigenvalues i ^ 2) = ∑ i, ∑ j, Q i j ^ 2 := by
  let U := hQ.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hQ' : Q = f (Matrix.diagonal hQ.eigenvalues) := by
    simpa [f, U, Function.comp_def] using hQ.spectral_theorem
  have htrace : (Q * Q).trace = ∑ i, hQ.eigenvalues i ^ 2 := by
    calc
      (Q * Q).trace =
          (f (Matrix.diagonal hQ.eigenvalues * Matrix.diagonal hQ.eigenvalues)).trace := by
        rw [map_mul, ← hQ']
      _ = (Matrix.diagonal hQ.eigenvalues * Matrix.diagonal hQ.eigenvalues).trace := by
        change (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U _).trace = _
        rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
          ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
      _ = ∑ i, hQ.eigenvalues i ^ 2 := by
        simp [Matrix.trace, Matrix.diagonal_mul, pow_two]
  rw [← htrace]
  simp only [Matrix.trace, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Q j i = Q i j := by simpa using hQ.apply i j
  change Q i j * Q j i = Q i j ^ 2
  rw [hs, pow_two]

end Matrix

namespace RiemannResearch.Probability.DPP

/-- Moving-dimensional determinant PGFs converge under the exact trace and
squared-entry criteria. The kernel need only be positive semidefinite here;
the probability interpretation additionally uses the positive contraction. -/
theorem moving_matrix_pgf_tendsto_poisson
    (d : ℕ → ℕ) (Q : (N : ℕ) → Matrix (Fin (d N)) (Fin (d N)) ℝ)
    (hQ : ∀ N, (Q N).PosSemidef) (rate z : ℝ)
    (h1 : Tendsto (fun N => (Q N).trace) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, ∑ j, Q N i j ^ 2) atTop (𝓝 0))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => (1 + (z - 1) • Q N).det) atTop
      (𝓝 (Real.exp ((z - 1) * rate))) := by
  have he1 : Tendsto (fun N => ∑ i, (hQ N).isHermitian.eigenvalues i)
      atTop (𝓝 rate) := by
    apply h1.congr
    intro N
    simpa using (hQ N).isHermitian.trace_eq_sum_eigenvalues
  have he2 : Tendsto (fun N => ∑ i, ((hQ N).isHermitian.eigenvalues i) ^ 2)
      atTop (𝓝 0) := by
    simpa only [Matrix.IsHermitian.sum_sq_eigenvalues_eq_sum_sq_entries] using h2
  have hh := bernoulli_product_tendsto_poisson_pgf d
    (fun N => (hQ N).isHermitian.eigenvalues) rate z
    (fun N i => (hQ N).eigenvalues_nonneg i) he1 he2 hz
  apply hh.congr
  intro N
  rw [(hQ N).isHermitian.det_one_add_smul_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Actual moving-window DPP PGFs satisfy the conditional Poisson limit. -/
theorem moving_window_count_pgf_tendsto_poisson
    {α Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ N, IsProbabilityMeasure (μ N)]
    (X : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (h : ∀ N, IsDPP (μ N) (X N) (K N))
    (d : ℕ → ℕ) (e : (N : ℕ) → Fin (d N) ↪ α)
    (hQ : ∀ N, (Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (hI : ∀ N, (1 - Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (rate z : ℝ)
    (h1 : Tendsto (fun N => ∑ i, K N (e N i) (e N i)) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, ∑ j, K N (e N i) (e N j) ^ 2) atTop (𝓝 0))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∫ ω, ∏ i : Fin (d N), if e N i ∈ X N ω then z else 1 ∂μ N)
      atTop (𝓝 (Real.exp ((z - 1) * rate))) := by
  have hh := moving_matrix_pgf_tendsto_poisson d
    (fun N => Matrix.of (fun i j => K N (e N i) (e N j))) hQ rate z h1 h2 hz
  apply hh.congr
  intro N
  symm
  exact (h N).window_count_generating (e N) (exactWeight_nonneg _ (hQ N) (hI N)) z

/-- Actual vacancy probabilities converge to the Poisson vacancy probability. -/
theorem moving_window_gap_tendsto_poisson
    {α Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ N, IsProbabilityMeasure (μ N)]
    (X : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (h : ∀ N, IsDPP (μ N) (X N) (K N))
    (d : ℕ → ℕ) (e : (N : ℕ) → Fin (d N) ↪ α)
    (hQ : ∀ N, (Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (hI : ∀ N, (1 - Matrix.of (fun i j => K N (e N i) (e N j))).PosSemidef)
    (rate : ℝ)
    (h1 : Tendsto (fun N => ∑ i, K N (e N i) (e N i)) atTop (𝓝 rate))
    (h2 : Tendsto (fun N => ∑ i, ∑ j, K N (e N i) (e N j) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => (μ N).real {ω | ∀ i, e N i ∉ X N ω})
      atTop (𝓝 (Real.exp (-rate))) := by
  have hh := moving_matrix_pgf_tendsto_poisson d
    (fun N => Matrix.of (fun i j => K N (e N i) (e N j))) hQ rate 0 h1 h2 (by norm_num)
  have hmat (N : ℕ) :
      (1 : Matrix (Fin (d N)) (Fin (d N)) ℝ) + (0 - 1 : ℝ) •
        Matrix.of (fun i j => K N (e N i) (e N j)) =
      1 - Matrix.of (fun i j => K N (e N i) (e N j)) := by
    ext i j
    simp <;> ring
  have hexp : Real.exp ((0 - 1) * rate) = Real.exp (-rate) := by congr 1; ring
  simp only [hmat, hexp] at hh
  apply hh.congr
  intro N
  symm
  exact (h N).finite_gap (e N) (exactWeight_nonneg _ (hQ N) (hI N))

end RiemannResearch.Probability.DPP


/-!
# Exact diagonal decomposition of the Poisson squared-mass condition

Source: elementary finite sums. A bound on every diagonal occupation,
vanishing with the stage, and the off-diagonal squared-mass bound discharge
the full squared-mass premise in the conditional Poisson limit.
-/

noncomputable section
open Filter Matrix
open scoped BigOperators Topology

namespace RiemannResearch.Probability.DPP

/-- The complete squared kernel mass splits exactly into its diagonal and
off-diagonal parts. -/
theorem sum_sq_entries_eq_diag_add_offdiag {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) :
    (∑ i, ∑ j, Q i j ^ 2) = (∑ i, Q i i ^ 2) +
      ∑ i, ∑ j, if i = j then 0 else Q i j ^ 2 := by
  have he (i : ι) : (∑ j, Q i j ^ 2) = Q i i ^ 2 +
      ∑ j, if i = j then 0 else Q i j ^ 2 := by
    calc
      (∑ j, Q i j ^ 2) =
          ∑ j, ((if i = j then Q i i ^ 2 else 0) +
            (if i = j then 0 else Q i j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j; simp
        · simp [hij]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  simp_rw [he]
  exact Finset.sum_add_distrib

/-- The maximum diagonal occupation and the off-diagonal Hilbert--Schmidt
budget together imply the exact full squared-mass criterion. -/
theorem moving_full_sq_tendsto_zero_of_offdiag
    (d : ℕ → ℕ) (Q : (N : ℕ) → Matrix (Fin (d N)) (Fin (d N)) ℝ)
    (b : ℕ → ℝ) (rate : ℝ)
    (hdiag : ∀ N i, 0 ≤ Q N i i ∧ Q N i i ≤ b N)
    (hmean : Tendsto (fun N => (Q N).trace) atTop (𝓝 rate))
    (hb : Tendsto b atTop (𝓝 0))
    (hoff : Tendsto (fun N => ∑ i, ∑ j,
      if i = j then 0 else Q N i j ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ i, ∑ j, Q N i j ^ 2) atTop (𝓝 0) := by
  have hd : Tendsto (fun N => ∑ i, Q N i i ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_mul] using hb.mul hmean)
    · intro N
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (Q N i i))
    · intro N
      change (∑ i, Q N i i ^ 2) ≤ b N * ∑ i, Q N i i
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_nonneg (hdiag N i).1 (sub_nonneg.mpr (hdiag N i).2)]
  have hh := hd.add hoff
  simpa only [sum_sq_entries_eq_diag_add_offdiag, zero_add] using hh

end RiemannResearch.Probability.DPP
