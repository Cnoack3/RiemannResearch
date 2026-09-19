import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite covariance signal-to-noise identity

Source: user-provided `signal_to_noise_RH_program (2)(1).pdf`, Theorem 4.2.
This finite algebraic theorem assumes a symmetric positive definite covariance
matrix and an actual solution of C v = lambda. It does not assert that a specified
arithmetic covariance meets the hypotheses, nor an asymptotic RH estimate.

-/

open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteSignalNoise
noncomputable section
variable {ι : Type*} [Fintype ι]

def form (C : Matrix ι ι ℝ) (a b : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * C i j * b j

def signal (lambda a : ι → ℝ) : ℝ := ∑ i, lambda i * a i

def error (C : Matrix ι ι ℝ) (lambda a : ι → ℝ) : ℝ :=
  (1 - signal lambda a) ^ 2 + form C a a

def optimal (lambda v : ι → ℝ) : ι → ℝ :=
  fun i => (1 + signal lambda v)⁻¹ * v i

def PositiveDefinite (C : Matrix ι ι ℝ) : Prop :=
  ∀ a : ι → ℝ, a ≠ 0 → 0 < form C a a

theorem form_zero (C : Matrix ι ι ℝ) : form C 0 0 = 0 := by
  simp [form]

theorem form_nonneg (C : Matrix ι ι ℝ) (hC : PositiveDefinite C)
    (a : ι → ℝ) : 0 ≤ form C a a := by
  by_cases ha : a = 0
  · rw [ha, form_zero]
  · exact le_of_lt (hC a ha)

theorem form_symm (C : Matrix ι ι ℝ)
    (hC : ∀ i j, C i j = C j i) (a b : ι → ℝ) :
    form C a b = form C b a := by
  unfold form
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hC j i]
  ring

theorem form_sub_left (C : Matrix ι ι ℝ) (a b c : ι → ℝ) :
    form C (a - b) c = form C a c - form C b c := by
  simp only [form, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem form_sub_right (C : Matrix ι ι ℝ) (a b c : ι → ℝ) :
    form C a (b - c) = form C a b - form C a c := by
  simp only [form, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem form_scale_left (C : Matrix ι ι ℝ) (t : ℝ) (a b : ι → ℝ) :
    form C (fun i => t * a i) b = t * form C a b := by
  simp only [form, mul_assoc, Finset.mul_sum]

theorem form_scale_right (C : Matrix ι ι ℝ) (t : ℝ) (a b : ι → ℝ) :
    form C a (fun i => t * b i) = t * form C a b := by
  unfold form
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem signal_sub (lambda a b : ι → ℝ) :
    signal lambda (a - b) = signal lambda a - signal lambda b := by
  simp only [signal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem signal_scale (lambda a : ι → ℝ) (t : ℝ) :
    signal lambda (fun i => t * a i) = t * signal lambda a := by
  unfold signal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem form_solution_right (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hv : C.mulVec v = lambda) : form C a v = signal lambda a := by
  have hrow (i : ι) : (∑ j, C i j * v j) = lambda i := congrFun hv i
  unfold form signal
  simp_rw [mul_assoc, ← Finset.mul_sum, hrow]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem signal_solution_nonneg (C : Matrix ι ι ℝ) (lambda v : ι → ℝ)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    0 ≤ signal lambda v := by
  rw [← form_solution_right C lambda v v hv]
  exact form_nonneg C hC v

/-- Exact finite completion: d² = 1/(1+R), with both nonnegative remainders. -/
theorem error_completion (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    error C lambda a = 1 / (1 + signal lambda v) +
      form C (a - optimal lambda v) (a - optimal lambda v) +
      (signal lambda (a - optimal lambda v)) ^ 2 := by
  have hnonneg := signal_solution_nonneg C lambda v hC hv
  have hd : 1 + signal lambda v ≠ 0 := ne_of_gt (by linarith)
  have hav := form_solution_right C lambda v a hv
  have hva : form C v a = signal lambda a :=
    (form_symm C hsymm v a).trans hav
  have hvv := form_solution_right C lambda v v hv
  unfold error optimal
  rw [form_sub_left, form_sub_right, form_sub_right,
    form_scale_right, form_scale_left, form_scale_left, form_scale_right,
    signal_sub, signal_scale, hav, hva, hvv]
  field_simp [hd]
  ring

theorem error_at_optimal (C : Matrix ι ι ℝ) (lambda v : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    error C lambda (optimal lambda v) = 1 / (1 + signal lambda v) := by
  rw [error_completion C lambda v (optimal lambda v) hsymm hC hv]
  simp [form, signal]

theorem optimal_minimizes (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    1 / (1 + signal lambda v) ≤ error C lambda a := by
  rw [error_completion C lambda v a hsymm hC hv]
  have hform := form_nonneg C hC (a - optimal lambda v)
  have hsquare := sq_nonneg (signal lambda (a - optimal lambda v))
  linarith

theorem optimal_unique (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    error C lambda a = 1 / (1 + signal lambda v) ↔ a = optimal lambda v := by
  constructor
  · intro he
    have hc := error_completion C lambda v a hsymm hC hv
    have hsquare := sq_nonneg (signal lambda (a - optimal lambda v))
    have hzero : a - optimal lambda v = 0 := by
      by_contra hne
      have hp := hC (a - optimal lambda v) hne
      linarith
    exact sub_eq_zero.mp hzero
  · rintro rfl
    exact error_at_optimal C lambda v hsymm hC hv

/-- The Rayleigh inequality, preserving exactly the requested signal direction. -/
theorem signal_sq_le_form_mul_snr (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) :
    (signal lambda a) ^ 2 ≤ form C a a * signal lambda v := by
  have hR := signal_solution_nonneg C lambda v hC hv
  have hav := form_solution_right C lambda v a hv
  have hva : form C v a = signal lambda a :=
    (form_symm C hsymm v a).trans hav
  have hvv := form_solution_right C lambda v v hv
  rcases eq_or_lt_of_le hR with hzero | hpos
  · have hvzero : v = 0 := by
      by_contra hn
      have hh := hC v hn
      rw [hvv, ← hzero] at hh
      exact (lt_irrefl 0) hh
    have hlam : lambda = 0 := by simpa [hvzero] using hv.symm
    simp [hlam, signal]
  · have hform := form_nonneg C hC
      ((fun i => signal lambda v * a i) - (fun i => signal lambda a * v i))
    simp only [form_sub_left, form_sub_right, form_scale_left, form_scale_right,
      hav, hva, hvv] at hform
    have hmul : 0 ≤ signal lambda v *
        (form C a a * signal lambda v - (signal lambda a)^2) := by
      nlinarith only [hform]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp hmul)

/-- Every nonzero coefficient vector has Rayleigh quotient at most the SNR. -/
theorem rayleigh_le_snr (C : Matrix ι ι ℝ) (lambda v a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) (ha : a ≠ 0) :
    (signal lambda a)^2 / form C a a ≤ signal lambda v := by
  apply (div_le_iff₀ (hC a ha)).mpr
  simpa only [mul_comm] using signal_sq_le_form_mul_snr C lambda v a hsymm hC hv

/-- C^{-1}lambda attains the Rayleigh bound when the signal is nonzero. -/
theorem rayleigh_at_solution (C : Matrix ι ι ℝ) (lambda v : ι → ℝ)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) (hlam : lambda ≠ 0) :
    v ≠ 0 ∧ (signal lambda v)^2 / form C v v = signal lambda v := by
  have hvzero : v ≠ 0 := by
    intro he
    apply hlam
    simpa [he] using hv.symm
  refine ⟨hvzero, ?_⟩
  have hh := hC v hvzero
  rw [form_solution_right C lambda v v hv] at hh ⊢
  field_simp [ne_of_gt hh]

/-- Matrix part of PDF Theorem 6.1, without any asymptotic assumption. -/
theorem scalar_signal_lower_bound (C : Matrix ι ι ℝ) (lambda v : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : PositiveDefinite C) (hv : C.mulVec v = lambda) (hlam : lambda ≠ 0) :
    (signal lambda lambda)^2 / form C lambda lambda ≤ signal lambda v :=
  rayleigh_le_snr C lambda v lambda hsymm hC hv hlam

end
end RiemannResearch.LinearAlgebra.FiniteSignalNoise
