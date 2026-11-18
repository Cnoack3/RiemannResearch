/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DirichletMeanSquare
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.RH.WeilExplicitFormula.PrimeSideB.PPKernel
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Mean squares of absolutely convergent Dirichlet tails

For arbitrary complex coefficients of norm at most one, the tail after X on
any line sigma > 1 has a translated-interval second-moment bound with explicit
dependence on sigma, X, and the interval length. The proof starts with the
complete signed finite mean-value identity, uses the repository's checked
Montgomery--Vaughan estimate, and passes to the ordinary infinite sum by
dominated convergence. Continuity is supplied by the uniform majorant.

Source for the mean-value strategy: H. L. Montgomery and R. C. Vaughan,
"Hilbert's inequality", J. London Math. Soc. (2) 8 (1974), 73--82.
The concrete consumer is the actual moving right-line Ingham error moment.
No zero-density or zeta-moment provider is assumed.
-/

noncomputable section
open MeasureTheory Complex Filter Set
open scoped BigOperators
namespace RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.ZeroOrdinate

def tailCoefficient (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * Complex.exp (-(σ : ℂ) * (Real.log n : ℂ))

def tailTerm (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  tailCoefficient a σ n * phase (-Real.log n) t

def tailPartial (a : ℕ → ℂ) (σ : ℝ) (X N : ℕ) (t : ℝ) : ℂ :=
  ∑ i : Fin N, tailTerm a σ (i.val + X + 1) t

def dirichletTail (a : ℕ → ℂ) (σ : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, tailTerm a σ (k + X + 1) t

theorem tailPartial_eq_sum_range (a : ℕ → ℂ) (σ : ℝ) (X N : ℕ) (t : ℝ) :
    tailPartial a σ X N t = ∑ k ∈ Finset.range N, tailTerm a σ (k + X + 1) t :=
  Fin.sum_univ_eq_sum_range (fun k => tailTerm a σ (k + X + 1) t) N

theorem tailCoefficient_norm (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖tailCoefficient a σ n‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [tailCoefficient, norm_mul, Complex.norm_exp]
  congr 1
  rw [Real.rpow_def_of_pos hn']
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  ring

theorem tailTerm_norm (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖tailTerm a σ n t‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
  rw [tailTerm, norm_mul, phase_norm, mul_one, tailCoefficient_norm a σ hn]

theorem summable_tail_rpow {p : ℝ} (hp : 1 < p) (X : ℕ) :
    Summable (fun k : ℕ => ((k + X + 1 : ℕ) : ℝ) ^ (-p)) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (X + 1)).mpr (Real.summable_nat_rpow.mpr (by linarith : -p < -1))

theorem tailCoefficient_norm_sq_le {a : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1)
    (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖tailCoefficient a σ n‖ ^ 2 ≤ (n : ℝ) ^ (-(2 * σ)) := by
  have h := ha n hn
  rw [tailCoefficient_norm a σ hn, mul_pow]
  have he : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
    ring
  rw [he]
  calc
    _ ≤ 1 ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h 2) (by positivity)
    _ = _ := by ring

/-- The exact finite tail identity retains the full signed off-diagonal. -/
theorem tailPartial_mean_square_identity (a : ℕ → ℂ) (σ : ℝ)
    (X N : ℕ) (H T : ℝ) :
    ((∫ t in H..T, ‖tailPartial a σ X N t‖ ^ 2 : ℝ) : ℂ) =
      (((T - H) * ∑ i : Fin N, ‖tailCoefficient a σ (i.val + X + 1)‖ ^ 2 : ℝ) : ℂ) +
        offDiagonal (fun i : Fin N => tailCoefficient a σ (i.val + X + 1))
          (fun i : Fin N => -Real.log (i.val + X + 1 : ℕ)) H T :=
  integral_norm_sq_eq_diagonal_add _ _ H T

theorem tailPartial_mean_square_le {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) (N : ℕ) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖tailPartial a σ X N t‖ ^ 2) ≤
      (T - H) * ((X : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) +
        52 * ((X : ℝ) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
  let n : Fin N → ℕ := fun i => i.val + X + 1
  let c : Fin N → ℂ := fun i => tailCoefficient a σ (n i)
  let ω : Fin N → ℝ := fun i => -Real.log (n i)
  have hnpos (i : Fin N) : 1 ≤ n i := by dsimp [n]; omega
  have hinj : Function.Injective n := by intro i j hij; dsimp [n] at hij; ext; omega
  have hω : Function.Injective ω := by
    intro i j hij
    apply hinj
    have hlog : Real.log (n i : ℝ) = Real.log (n j : ℝ) := neg_injective hij
    exact_mod_cast Real.log_injOn_pos
      (show (n i : ℝ) ∈ Ioi 0 from by
        change 0 < (n i : ℝ)
        exact_mod_cast hnpos i)
      (show (n j : ℝ) ∈ Ioi 0 from by
        change 0 < (n j : ℝ)
        exact_mod_cast hnpos j) hlog
  have hsep (i j : Fin N) (hij : i ≠ j) :
      1 / (2 * (n i : ℝ)) ≤ |ω i - ω j| := by
    simpa only [ω, neg_sub_neg, abs_sub_comm] using
      Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub (hnpos i) (hnpos j)
        (fun he => hij (hinj he))
  have hmv := abs_integral_norm_sq_sub_le c ω (fun i => 1 / (2 * (n i : ℝ)))
    hω (fun i => by
      have hi : 0 < (n i : ℝ) := by exact_mod_cast hnpos i
      positivity)
    hsep H T
  have heq : polynomial c ω = tailPartial a σ X N := rfl
  rw [heq] at hmv
  have henergy : (∑ i : Fin N, ‖c i‖ ^ 2) ≤
      (X : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) := by
    calc
      _ ≤ ∑ i : Fin N, (n i : ℝ) ^ (-(2 * σ)) :=
        Finset.sum_le_sum (fun i _ => tailCoefficient_norm_sq_le ha σ (hnpos i))
      _ = ∑ k ∈ Finset.range N, ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ)) := by
        exact Fin.sum_univ_eq_sum_range
          (fun k => ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ))) N
      _ ≤ ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ)) :=
        (summable_tail_rpow (by linarith : 1 < 2 * σ) X).sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ _ := Real.tsum_nat_rpow_tail_le (by linarith) hX
  have hweighted : (∑ i : Fin N, ‖c i‖ ^ 2 / (1 / (2 * (n i : ℝ)))) ≤
      2 * ((X : ℝ) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
    simp only [div_div_eq_mul_div, div_one]
    have hterm (i : Fin N) : ‖c i‖ ^ 2 * (2 * (n i : ℝ)) ≤
        2 * (n i : ℝ) ^ (-(2 * σ - 1)) := by
      calc
        _ ≤ (n i : ℝ) ^ (-(2 * σ)) * (2 * (n i : ℝ)) :=
          mul_le_mul_of_nonneg_right (tailCoefficient_norm_sq_le ha σ (hnpos i)) (by positivity)
        _ = _ := by
          have hi : 0 < (n i : ℝ) := by exact_mod_cast hnpos i
          calc
            _ = 2 * ((n i : ℝ) ^ (-(2 * σ)) * (n i : ℝ) ^ (1 : ℝ)) := by
              rw [Real.rpow_one]; ring
            _ = _ := by rw [← Real.rpow_add hi]; congr 2; ring
    calc
      _ ≤ ∑ i : Fin N, 2 * (n i : ℝ) ^ (-(2 * σ - 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = 2 * ∑ k ∈ Finset.range N, ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ - 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fin.sum_univ_eq_sum_range
          (fun k => ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ - 1))) N
      _ ≤ 2 * ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) ^ (-(2 * σ - 1)) :=
        mul_le_mul_of_nonneg_left
          ((summable_tail_rpow (by linarith : 1 < 2 * σ - 1) X).sum_le_tsum _
            (fun _ _ => by positivity)) (by norm_num)
      _ ≤ _ := by
        have h := Real.tsum_nat_rpow_tail_le (by linarith : 1 < 2 * σ - 1) hX
        simpa only [show 1 - (2 * σ - 1) = 2 - 2 * σ by ring,
          show (2 * σ - 1) - 1 = 2 * σ - 2 by ring] using
          mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  have hh := (abs_le.mp hmv).2
  have hd := mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr hHT)
  linarith

theorem continuous_tailPartial (a : ℕ → ℂ) (σ : ℝ) (X N : ℕ) :
    Continuous (tailPartial a σ X N) := by
  unfold tailPartial tailTerm phase
  fun_prop

theorem tailPartial_norm_le {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) (N : ℕ) (t : ℝ) :
    ‖tailPartial a σ X N t‖ ≤ (X : ℝ) ^ (1 - σ) / (σ - 1) := by
  calc
    _ ≤ ∑ i : Fin N, ‖tailTerm a σ (i.val + X + 1) t‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ((i.val + X + 1 : ℕ) : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [tailTerm_norm a σ (by omega)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (ha (i.val + X + 1) (by omega))
        (Real.rpow_nonneg (Nat.cast_nonneg _) (-σ))
    _ = ∑ k ∈ Finset.range N, ((k + X + 1 : ℕ) : ℝ) ^ (-σ) :=
      Fin.sum_univ_eq_sum_range (fun k => ((k + X + 1 : ℕ) : ℝ) ^ (-σ)) N
    _ ≤ ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) ^ (-σ) :=
      (summable_tail_rpow hσ X).sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ _ := Real.tsum_nat_rpow_tail_le hσ hX

theorem summable_tailTerm {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    (X : ℕ) (t : ℝ) : Summable (fun k : ℕ => tailTerm a σ (k + X + 1) t) := by
  apply (summable_tail_rpow hσ X).of_norm_bounded
  intro k
  rw [tailTerm_norm a σ (by omega)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha (k + X + 1) (by omega))
    (Real.rpow_nonneg (Nat.cast_nonneg _) (-σ))

theorem tailPartial_tendsto {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    (X : ℕ) (t : ℝ) :
    Tendsto (fun N => tailPartial a σ X N t) atTop (nhds (dirichletTail a σ X t)) := by
  simpa only [tailPartial_eq_sum_range, dirichletTail] using
    (summable_tailTerm ha hσ X t).hasSum.tendsto_sum_nat

theorem continuous_dirichletTail {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) (X : ℕ) :
    Continuous (dirichletTail a σ X) := by
  apply continuous_tsum (u := fun k : ℕ => ((k + X + 1 : ℕ) : ℝ) ^ (-σ))
  · intro k
    unfold tailTerm phase
    fun_prop
  · exact summable_tail_rpow hσ X
  · intro k t
    rw [tailTerm_norm a σ (by omega)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha (k + X + 1) (by omega))
      (Real.rpow_nonneg (Nat.cast_nonneg _) (-σ))

/-- The infinite tail estimate follows by dominated convergence from the
complete finite mean-value formula. -/
theorem dirichletTail_mean_square_le {a : ℕ → ℂ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖dirichletTail a σ X t‖ ^ 2) ≤
      (T - H) * ((X : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) +
        52 * ((X : ℝ) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
  let B : ℝ := (X : ℝ) ^ (1 - σ) / (σ - 1)
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc H T))
    (F := fun N t => ‖tailPartial a σ X N t‖ ^ 2)
    (f := fun t => ‖dirichletTail a σ X t‖ ^ 2) (fun _ : ℝ => B ^ 2)
    (fun N => ((continuous_tailPartial a σ X N).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (tailPartial_norm_le ha hσ hX N t) 2))
    (Filter.Eventually.of_forall (fun t => (tailPartial_tendsto ha hσ X t).norm.pow 2))
  rw [intervalIntegral.integral_of_le hHT]
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun N => by
    simpa only [Pi.pow_apply, intervalIntegral.integral_of_le hHT] using
      tailPartial_mean_square_le ha hσ hX N hHT)

end RiemannResearch.Analysis.DirichletMeanSquare
