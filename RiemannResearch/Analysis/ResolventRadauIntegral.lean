import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannResearch.Analysis.FiniteResolventRadau

/-!
# Integral Radau certificates for arbitrary spectral measures

Source: user-provided exact optimizer cancellation argument, 2026-10-08.
These are actual Bochner integral identities, not finite quadrature assertions.
The base measure may have infinite support. A nonnegative density `w` with
`∫ w = 1` gives the probability law; `w = 1` specializes directly to an actual
probability spectral measure. All polynomial and reciprocal integrability
needed to split signed integrals is explicit. Every square remainder is kept.
-/

noncomputable section

open MeasureTheory

namespace RiemannResearch.Analysis.ResolventRadauIntegral

variable {α : Type*} [MeasurableSpace α]

def moment (μ : Measure α) (w x : α → ℝ) (n : ℕ) : ℝ :=
  ∫ i, w i * x i ^ n ∂μ

def resolvent (μ : Measure α) (w x : α → ℝ) : ℝ :=
  ∫ i, w i / (1 + x i) ∂μ

def polynomial (c₀ c₁ t : ℝ) : ℝ := c₀ + c₁ * t

def variationalValue (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ) : ℝ :=
  2 * (∫ i, w i * polynomial c₀ c₁ (x i) ∂μ) -
    ∫ i, w i * (1 + x i) * polynomial c₀ c₁ (x i) ^ 2 ∂μ

def squareRemainder (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ) : ℝ :=
  ∫ i, w i * (1 - (1 + x i) * polynomial c₀ c₁ (x i)) ^ 2 / (1 + x i) ∂μ

def NormalEquations (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ) : Prop :=
  (moment μ w x 0 + moment μ w x 1) * c₀ +
      (moment μ w x 1 + moment μ w x 2) * c₁ = moment μ w x 0 ∧
    (moment μ w x 1 + moment μ w x 2) * c₀ +
      (moment μ w x 2 + moment μ w x 3) * c₁ = moment μ w x 1

theorem integrable_linear (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (h₀ : Integrable (fun i => w i * x i ^ 0) μ)
    (h₁ : Integrable (fun i => w i * x i ^ 1) μ) :
    Integrable (fun i => w i * polynomial c₀ c₁ (x i)) μ := by
  have he : (fun i => w i * polynomial c₀ c₁ (x i)) =
      (fun i => c₀ * (w i * x i ^ 0) + c₁ * (w i * x i ^ 1)) := by
    funext i
    unfold polynomial
    simp only [pow_zero, pow_one]
    ring
  rw [he]
  exact (h₀.const_mul c₀).add (h₁.const_mul c₁)

theorem linear_integral_eq (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (h₀ : Integrable (fun i => w i * x i ^ 0) μ)
    (h₁ : Integrable (fun i => w i * x i ^ 1) μ) :
    (∫ i, w i * polynomial c₀ c₁ (x i) ∂μ) =
      c₀ * moment μ w x 0 + c₁ * moment μ w x 1 := by
  have he : (fun i => w i * polynomial c₀ c₁ (x i)) =
      (fun i => c₀ * (w i * x i ^ 0) + c₁ * (w i * x i ^ 1)) := by
    funext i
    unfold polynomial
    simp only [pow_zero, pow_one]
    ring
  rw [he]
  simpa only [Pi.add_apply, integral_const_mul, moment] using
    integral_add (h₀.const_mul c₀) (h₁.const_mul c₁)

theorem quadratic_function_eq (w x : α → ℝ) (c₀ c₁ : ℝ) :
    (fun i => w i * (1 + x i) * polynomial c₀ c₁ (x i) ^ 2) =
      (fun i => c₀ ^ 2 * (w i * x i ^ 0) +
        (c₀ ^ 2 + 2 * c₀ * c₁) * (w i * x i ^ 1) +
        (2 * c₀ * c₁ + c₁ ^ 2) * (w i * x i ^ 2) +
        c₁ ^ 2 * (w i * x i ^ 3)) := by
  funext i
  unfold polynomial
  simp only [pow_zero, pow_one]
  ring

theorem integrable_quadratic (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (hm : ∀ n ≤ 3, Integrable (fun i => w i * x i ^ n) μ) :
    Integrable (fun i => w i * (1 + x i) * polynomial c₀ c₁ (x i) ^ 2) μ := by
  rw [quadratic_function_eq]
  have h₀ := (hm 0 (by decide)).const_mul (c₀ ^ 2)
  have h₁ := (hm 1 (by decide)).const_mul (c₀ ^ 2 + 2 * c₀ * c₁)
  have h₂ := (hm 2 (by decide)).const_mul (2 * c₀ * c₁ + c₁ ^ 2)
  have h₃ := (hm 3 (by decide)).const_mul (c₁ ^ 2)
  exact ((h₀.add h₁).add h₂).add h₃

theorem quadratic_integral_eq (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (hm : ∀ n ≤ 3, Integrable (fun i => w i * x i ^ n) μ) :
    (∫ i, w i * (1 + x i) * polynomial c₀ c₁ (x i) ^ 2 ∂μ) =
      c₀ ^ 2 * (moment μ w x 0 + moment μ w x 1) +
      2 * c₀ * c₁ * (moment μ w x 1 + moment μ w x 2) +
      c₁ ^ 2 * (moment μ w x 2 + moment μ w x 3) := by
  have h₀ := (hm 0 (by decide)).const_mul (c₀ ^ 2)
  have h₁ := (hm 1 (by decide)).const_mul (c₀ ^ 2 + 2 * c₀ * c₁)
  have h₂ := (hm 2 (by decide)).const_mul (2 * c₀ * c₁ + c₁ ^ 2)
  have h₃ := (hm 3 (by decide)).const_mul (c₁ ^ 2)
  have h₀₁ := integral_add h₀ h₁
  have h₀₁₂ := integral_add (h₀.add h₁) h₂
  have h₀₁₂₃ := integral_add ((h₀.add h₁).add h₂) h₃
  simp only [Pi.add_apply] at h₀₁ h₀₁₂ h₀₁₂₃
  rw [quadratic_function_eq, h₀₁₂₃, h₀₁₂, h₀₁]
  simp only [integral_const_mul, moment]
  ring

theorem integrable_squareRemainder (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (hx : ∀ᵐ i ∂μ, 0 ≤ x i)
    (hr : Integrable (fun i => w i / (1 + x i)) μ)
    (hm : ∀ n ≤ 3, Integrable (fun i => w i * x i ^ n) μ) :
    Integrable (fun i =>
      w i * (1 - (1 + x i) * polynomial c₀ c₁ (x i)) ^ 2 / (1 + x i)) μ := by
  have hl := integrable_linear μ w x c₀ c₁ (hm 0 (by decide)) (hm 1 (by decide))
  have hq := integrable_quadratic μ w x c₀ c₁ hm
  apply (hr.sub ((hl.const_mul 2).sub hq)).congr
  filter_upwards [hx] with i hi
  exact FiniteResolventRadau.scalar_complete_square _ _ _ (by linarith)

/-- Actual integral completion of the square. The base reciprocal and signed
polynomial terms are integrable, as is the whole square remainder. -/
theorem complete_square (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (hx : ∀ᵐ i ∂μ, 0 ≤ x i)
    (hr : Integrable (fun i => w i / (1 + x i)) μ)
    (hm : ∀ n ≤ 3, Integrable (fun i => w i * x i ^ n) μ) :
    resolvent μ w x - variationalValue μ w x c₀ c₁ =
      squareRemainder μ w x c₀ c₁ := by
  have hl := integrable_linear μ w x c₀ c₁ (hm 0 (by decide)) (hm 1 (by decide))
  have hq := integrable_quadratic μ w x c₀ c₁ hm
  have he : (fun i => w i / (1 + x i) -
      (2 * (w i * polynomial c₀ c₁ (x i)) -
        w i * (1 + x i) * polynomial c₀ c₁ (x i) ^ 2)) =ᵐ[μ]
      (fun i => w i * (1 - (1 + x i) * polynomial c₀ c₁ (x i)) ^ 2 / (1 + x i)) := by
    filter_upwards [hx] with i hi
    exact FiniteResolventRadau.scalar_complete_square _ _ _ (by linarith)
  have h := integral_congr_ae he
  have hsub₁ := integral_sub hr ((hl.const_mul 2).sub hq)
  have hsub₂ := integral_sub (hl.const_mul 2) hq
  simp only [Pi.sub_apply] at hsub₁ hsub₂
  rw [hsub₁, hsub₂, integral_const_mul] at h
  exact h

theorem squareRemainder_nonneg (μ : Measure α) (w x : α → ℝ) (c₀ c₁ : ℝ)
    (hw : ∀ᵐ i ∂μ, 0 ≤ w i) (hx : ∀ᵐ i ∂μ, 0 ≤ x i) :
    0 ≤ squareRemainder μ w x c₀ c₁ := by
  apply integral_nonneg_of_ae
  filter_upwards [hw, hx] with i hi hi'
  exact div_nonneg (mul_nonneg hi (sq_nonneg _)) (by linarith)

theorem variationalValue_eq_of_normal_equations (μ : Measure α) (w x : α → ℝ)
    (c₀ c₁ : ℝ) (hm : ∀ n ≤ 3, Integrable (fun i => w i * x i ^ n) μ)
    (hn : NormalEquations μ w x c₀ c₁) :
    variationalValue μ w x c₀ c₁ = c₀ * moment μ w x 0 + c₁ * moment μ w x 1 := by
  unfold variationalValue
  rw [linear_integral_eq μ w x c₀ c₁ (hm 0 (by decide)) (hm 1 (by decide)),
    quadratic_integral_eq μ w x c₀ c₁ hm]
  have e₀ := congrArg (fun z : ℝ => c₀ * z) hn.1
  have e₁ := congrArg (fun z : ℝ => c₁ * z) hn.2
  nlinarith only [e₀, e₁]

theorem moment_mul_node (μ : Measure α) (w x : α → ℝ) (n : ℕ) :
    moment μ (fun i => x i * w i) x n = moment μ w x (n + 1) := by
  apply integral_congr_ae
  filter_upwards [] with i
  rw [pow_succ]
  ring

theorem integrable_moment_mul_node (μ : Measure α) (w x : α → ℝ)
    (hm : ∀ n ≤ 4, Integrable (fun i => w i * x i ^ n) μ) :
    ∀ n ≤ 3, Integrable (fun i => (x i * w i) * x i ^ n) μ := by
  intro n hn
  have he : (fun i => (x i * w i) * x i ^ n) =
      (fun i => w i * x i ^ (n + 1)) := by
    funext i
    rw [pow_succ]
    ring
  rw [he]
  exact hm (n + 1) (Nat.succ_le_succ hn)

theorem moment_endpoint_weight (μ : Measure α) (w x : α → ℝ) (q : ℝ) (n : ℕ)
    (hn : Integrable (fun i => w i * x i ^ n) μ)
    (hn₁ : Integrable (fun i => w i * x i ^ (n + 1)) μ) :
    moment μ (fun i => (q - x i) * w i) x n =
      q * moment μ w x n - moment μ w x (n + 1) := by
  have he : (fun i => ((q - x i) * w i) * x i ^ n) =
      (fun i => q * (w i * x i ^ n) - w i * x i ^ (n + 1)) := by
    funext i
    rw [pow_succ]
    ring
  unfold moment
  rw [he]
  simpa only [Pi.sub_apply, integral_const_mul] using
    integral_sub (hn.const_mul q) hn₁

theorem integrable_moment_endpoint_weight (μ : Measure α) (w x : α → ℝ) (q : ℝ)
    (hm : ∀ n ≤ 4, Integrable (fun i => w i * x i ^ n) μ) :
    ∀ n ≤ 3, Integrable (fun i => ((q - x i) * w i) * x i ^ n) μ := by
  intro n hn
  have he : (fun i => ((q - x i) * w i) * x i ^ n) =
      (fun i => q * (w i * x i ^ n) - w i * x i ^ (n + 1)) := by
    funext i
    rw [pow_succ]
    ring
  rw [he]
  exact ((hm n (Nat.le_trans hn (by decide))).const_mul q).sub (hm (n + 1) (Nat.succ_le_succ hn))

theorem reciprocal_mul_node_ae (μ : Measure α) (w x : α → ℝ)
    (hx : ∀ᵐ i ∂μ, 0 ≤ x i) :
    (fun i => (x i * w i) / (1 + x i)) =ᵐ[μ]
      (fun i => w i - w i / (1 + x i)) := by
  filter_upwards [hx] with i hi
  have h : 1 + x i ≠ 0 := by linarith
  field_simp [h]
  ring

theorem reciprocal_endpoint_weight_ae (μ : Measure α) (w x : α → ℝ) (q : ℝ)
    (hx : ∀ᵐ i ∂μ, 0 ≤ x i) :
    (fun i => ((q - x i) * w i) / (1 + x i)) =ᵐ[μ]
      (fun i => (1 + q) * (w i / (1 + x i)) - w i) := by
  filter_upwards [hx] with i hi
  have h : 1 + x i ≠ 0 := by linarith
  field_simp [h]
  ring

theorem radau_remainders (μ : Measure α) (w x : α → ℝ) (q u₀ u₁ l₀ l₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∫ i, w i ∂μ) = 1)
    (hx : ∀ᵐ i ∂μ, 0 ≤ x i)
    (hr : Integrable (fun i => w i / (1 + x i)) μ)
    (hm : ∀ n ≤ 4, Integrable (fun i => w i * x i ^ n) μ) :
    1 - variationalValue μ (fun i => x i * w i) x u₀ u₁ - resolvent μ w x =
        squareRemainder μ (fun i => x i * w i) x u₀ u₁ ∧
      resolvent μ w x -
          (1 + variationalValue μ (fun i => (q - x i) * w i) x l₀ l₁) / (1 + q) =
        squareRemainder μ (fun i => (q - x i) * w i) x l₀ l₁ / (1 + q) := by
  have hwI : Integrable w μ := by simpa only [pow_zero, mul_one] using hm 0 (by decide)
  have heU := reciprocal_mul_node_ae μ w x hx
  have heL := reciprocal_endpoint_weight_ae μ w x q hx
  have hrU : Integrable (fun i => (x i * w i) / (1 + x i)) μ :=
    (hwI.sub hr).congr heU.symm
  have hrL : Integrable (fun i => ((q - x i) * w i) / (1 + x i)) μ :=
    ((hr.const_mul (1 + q)).sub hwI).congr heL.symm
  have hRU : resolvent μ (fun i => x i * w i) x = 1 - resolvent μ w x := by
    have hsub := integral_sub hwI hr
    unfold resolvent
    rw [integral_congr_ae heU, hsub, hnorm]
  have hRL : resolvent μ (fun i => (q - x i) * w i) x =
      (1 + q) * resolvent μ w x - 1 := by
    have hsub := integral_sub (hr.const_mul (1 + q)) hwI
    unfold resolvent
    rw [integral_congr_ae heL, hsub, integral_const_mul, hnorm]
  have hU := complete_square μ (fun i => x i * w i) x u₀ u₁ hx hrU
    (integrable_moment_mul_node μ w x hm)
  have hL := complete_square μ (fun i => (q - x i) * w i) x l₀ l₁ hx hrL
    (integrable_moment_endpoint_weight μ w x q hm)
  rw [hRU] at hU
  rw [hRL] at hL
  constructor
  · linarith
  · have hq' : 1 + q ≠ 0 := by linarith
    calc
      _ = ((1 + q) * resolvent μ w x - 1 -
        variationalValue μ (fun i => (q - x i) * w i) x l₀ l₁) / (1 + q) := by
          field_simp [hq']
          ring
      _ = _ := by rw [hL]

theorem radau_bounds (μ : Measure α) (w x : α → ℝ) (q u₀ u₁ l₀ l₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∫ i, w i ∂μ) = 1)
    (hw : ∀ᵐ i ∂μ, 0 ≤ w i) (hx : ∀ᵐ i ∂μ, 0 ≤ x i)
    (hxq : ∀ᵐ i ∂μ, x i ≤ q)
    (hr : Integrable (fun i => w i / (1 + x i)) μ)
    (hm : ∀ n ≤ 4, Integrable (fun i => w i * x i ^ n) μ) :
    (1 + variationalValue μ (fun i => (q - x i) * w i) x l₀ l₁) / (1 + q) ≤
        resolvent μ w x ∧
      resolvent μ w x ≤ 1 - variationalValue μ (fun i => x i * w i) x u₀ u₁ := by
  have he := radau_remainders μ w x q u₀ u₁ l₀ l₁ hq hnorm hx hr hm
  have hwU : ∀ᵐ i ∂μ, 0 ≤ x i * w i := by
    filter_upwards [hx, hw] with i hi hi'
    exact mul_nonneg hi hi'
  have hwL : ∀ᵐ i ∂μ, 0 ≤ (q - x i) * w i := by
    filter_upwards [hxq, hw] with i hi hi'
    exact mul_nonneg (sub_nonneg.mpr hi) hi'
  have hU := squareRemainder_nonneg μ (fun i => x i * w i) x u₀ u₁ hwU hx
  have hL := squareRemainder_nonneg μ (fun i => (q - x i) * w i) x l₀ l₁ hwL hx
  have hd : 0 ≤ squareRemainder μ (fun i => (q - x i) * w i) x l₀ l₁ / (1 + q) :=
    div_nonneg hL (by linarith)
  constructor <;> linarith [he.1, he.2]

/-- The four actual integral moments give the Radau interval after solving the
two displayed two-by-two systems. All analytic integrability is ordinary. -/
theorem radau_four_moment_certificate (μ : Measure α) (w x : α → ℝ)
    (q u₀ u₁ l₀ l₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∫ i, w i ∂μ) = 1)
    (hw : ∀ᵐ i ∂μ, 0 ≤ w i) (hx : ∀ᵐ i ∂μ, 0 ≤ x i)
    (hxq : ∀ᵐ i ∂μ, x i ≤ q)
    (hr : Integrable (fun i => w i / (1 + x i)) μ)
    (hm : ∀ n ≤ 4, Integrable (fun i => w i * x i ^ n) μ)
    (hu : NormalEquations μ (fun i => x i * w i) x u₀ u₁)
    (hl : NormalEquations μ (fun i => (q - x i) * w i) x l₀ l₁) :
    (1 + (l₀ * (q * moment μ w x 0 - moment μ w x 1) +
        l₁ * (q * moment μ w x 1 - moment μ w x 2))) / (1 + q) ≤
        resolvent μ w x ∧
      resolvent μ w x ≤ 1 - (u₀ * moment μ w x 1 + u₁ * moment μ w x 2) := by
  have hU := variationalValue_eq_of_normal_equations μ (fun i => x i * w i) x u₀ u₁
    (integrable_moment_mul_node μ w x hm) hu
  simp only [moment_mul_node] at hU
  have hL := variationalValue_eq_of_normal_equations μ (fun i => (q - x i) * w i) x l₀ l₁
    (integrable_moment_endpoint_weight μ w x q hm) hl
  rw [moment_endpoint_weight μ w x q 0 (hm 0 (by decide)) (hm 1 (by decide)),
    moment_endpoint_weight μ w x q 1 (hm 1 (by decide)) (hm 2 (by decide))] at hL
  have he := radau_bounds μ w x q u₀ u₁ l₀ l₁ hq hnorm hw hx hxq hr hm
  rw [hU, hL] at he
  exact he

end RiemannResearch.Analysis.ResolventRadauIntegral
