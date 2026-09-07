import RiemannResearch.RH.LogarithmicSchwartzTransport
import RiemannResearch.RH.ArithmeticReturnDerivatives
import RiemannResearch.Analysis.SuperexponentialDecay
import Mathlib.Tactic.GCongr

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Superexponential decay of the actual arithmetic conductor return

Source: Theorem 4.1, equations (4.5)--(4.6), of the user-provided Nyman--Weil
note. The actual compact input is transformed into an actual Schwartz kernel,
Poisson summation removes the zero frequency, and Schwartz seminorms provide
an arbitrary-order bound. No rapid-decay assumption is made on the output.
-/

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- Concrete constant supplied by the Fourier Schwartz seminorm. -/
def returnDecayConstant (g : SchwartzMap ℝ ℂ) (n A : ℕ) : ℝ :=
  (SchwartzMap.seminorm ℂ A 0 (𝓕 g)) *
    (∑' k : ℤ, |(k : ℝ)| ^ (-(A : ℝ))) * (1 + (n : ℝ) ^ A) / n

theorem returnDecayConstant_nonneg (g : SchwartzMap ℝ ℂ) (n A : ℕ) :
    0 ≤ returnDecayConstant g n A := by
  unfold returnDecayConstant
  positivity

/-- Explicit all-window exponential bound from genuine nonzero Poisson modes. -/
theorem nymanFullReturn_norm_le_exp {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (n : ℕ) [NeZero n] (A : ℕ) (hA : 1 < A) (y : ℝ) :
    ‖nymanFullReturn n u y‖ ≤
      returnDecayConstant (logarithmicSchwartzKernel hu ha hb) n A *
        Real.exp (-((A : ℝ) - 1 / 2) * y) := by
  let g := logarithmicSchwartzKernel hu ha hb
  let C := SchwartzMap.seminorm ℂ A 0 (𝓕 g)
  let S := ∑' k : ℤ, |(k : ℝ)| ^ (-(A : ℝ))
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn0 : (n : ℝ) ≠ 0 := hn.ne'
  have hey : 0 < Real.exp y := Real.exp_pos _
  have hemy : 0 < Real.exp (-y) := Real.exp_pos _
  have H1 : ‖∑' k : ℤ, if k = 0 then 0 else
      (𝓕 g) ((k : ℝ) / Real.exp (-y))‖ ≤ C / (Real.exp y) ^ A * S := by
    simpa [C, S, Real.exp_neg, div_eq_mul_inv, mul_comm] using
      norm_nonzero_schwartz_modes_le (𝓕 g) A hA hey
  have H2 : ‖∑' k : ℤ, if k = 0 then 0 else
      (𝓕 g) ((k : ℝ) / ((n : ℝ) * Real.exp (-y)))‖ ≤
        C / (Real.exp y / n) ^ A * S := by
    simpa [C, S, Real.exp_neg, div_eq_mul_inv, mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using
      norm_nonzero_schwartz_modes_le (𝓕 g) A hA (div_pos hey hn)
  rw [nymanFullReturn_eq_actual_poisson_kernel hu ha hb,
    conductorLatticeDiscrepancy_nonzero_modes g hn hemy]
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-y / 2)), abs_of_pos (inv_pos.mpr (mul_pos hn hemy))]
  have hAexp : (Real.exp y) ^ A = Real.exp ((A : ℝ) * y) :=
    (Real.exp_nat_mul y A).symm
  have he : Real.exp (-y / 2) * Real.exp y / (Real.exp y) ^ A =
      Real.exp (-((A : ℝ) - 1 / 2) * y) := by
    rw [hAexp, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-y / 2) * ((n : ℝ) * Real.exp (-y))⁻¹ *
        (C / (Real.exp y) ^ A * S + C / (Real.exp y / n) ^ A * S) := by
      rw [← mul_assoc]
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add H1 H2)
    _ = (C * S * (1 + (n : ℝ) ^ A) / n) *
        (Real.exp (-y / 2) * Real.exp y / (Real.exp y) ^ A) := by
      rw [Real.exp_neg]
      simp only [div_pow]
      field_simp
    _ = _ := by rw [he]; rfl

/-- Membership in the actual rapid exponential-decay class is supplied for
all compact smooth inputs, using exact arithmetic and Poisson identities. -/
theorem superexponentialDecay_nymanFullReturn {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (n : ℕ) [NeZero n] : SuperexponentialDecay (nymanFullReturn n u) := by
  intro d hd
  obtain ⟨A, hAd⟩ := exists_nat_gt (d + 1)
  have hA : 1 < A := by exact_mod_cast (by linarith : (1 : ℝ) < A)
  let B : ℝ := (A : ℝ) - 1 / 2
  let K := returnDecayConstant (logarithmicSchwartzKernel hu ha hb) n A
  have hB : 0 < B := by dsimp [B]; linarith
  have hdB : d ≤ B := by dsimp [B]; linarith
  have hK : 0 ≤ K := returnDecayConstant_nonneg _ _ _
  refine ⟨(K + 1) * Real.exp (2 * B * |a|), by positivity, ?_⟩
  intro y
  by_cases hy : y < a
  · have hz : nymanFullReturn n u y = 0 :=
      arithmeticReturn_zero_below _ ha hy
    rw [hz, norm_zero]
    positivity
  · have hay : a ≤ y := le_of_not_gt hy
    have habs : |y| ≤ y + 2 * |a| := by
      apply abs_le.mpr
      constructor <;> nlinarith [neg_abs_le a, abs_nonneg a]
    calc
      ‖nymanFullReturn n u y‖ ≤ K * Real.exp (-B * y) :=
        nymanFullReturn_norm_le_exp hu ha hb n A hA y
      _ ≤ (K + 1) * Real.exp (-B * y) := by gcongr; linarith
      _ ≤ (K + 1) * Real.exp (2 * B * |a| - B * |y|) := by
        gcongr
        nlinarith
      _ ≤ (K + 1) * Real.exp (2 * B * |a| - d * |y|) := by
        gcongr
      _ = _ := by
        rw [show 2 * B * |a| - d * |y| = 2 * B * |a| + (-d * |y|) by ring,
          Real.exp_add]
        ring

end RiemannResearch.RH

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- Every actual derivative of a full return has arbitrary exponential decay.
The derivative-support and arithmetic commutation providers discharge all
extra hypotheses when the base theorem is applied to the differentiated seed. -/
theorem superexponentialDecay_iteratedDeriv_nymanFullReturn
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (n : ℕ) [NeZero n] (j : ℕ) :
    SuperexponentialDecay (iteratedDeriv j (nymanFullReturn n u)) := by
  rw [nymanFullReturn_iteratedDeriv n hu ha j]
  have hdu : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv j hu
  exact superexponentialDecay_nymanFullReturn hdu
    (iteratedDeriv_zero_below_of_zero_below ha j)
    (iteratedDeriv_zero_above_of_zero_above hb j) n

/-- Full smooth admissibility of the actual arithmetic return, including every
order of derivative in the note's space E. -/
theorem nymanFullReturn_smooth_and_all_derivatives_decay
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (n : ℕ) [NeZero n] :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanFullReturn n u) ∧
      ∀ j : ℕ, SuperexponentialDecay (iteratedDeriv j (nymanFullReturn n u)) :=
  ⟨arithmeticReturn_contDiff _ hu ha,
    superexponentialDecay_iteratedDeriv_nymanFullReturn hu ha hb n⟩

end RiemannResearch.RH
