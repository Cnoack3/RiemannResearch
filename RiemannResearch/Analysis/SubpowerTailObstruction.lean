import RiemannResearch.Analysis.RemoteLaplaceTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Subpower tails cannot retain a nonzero transform signature
Source: user-provided RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md,
sections 1–2. All L², support, integral and growth hypotheses are explicit.
-/
open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory.RemoteLaplaceTail

/-- A fixed nonzero transform signature is incompatible with subpower energy
of any actual L² tail family beyond the specified logarithmic support gap. -/
theorem signature_eq_zero_of_supported_subpower_tail
    {τ : ℕ → ℝ → ℂ} {a : ℝ} {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (hLp : ∀ M, MemLp (τ M) 2 volume)
    (hsupport : ∀ M y, y < a + Real.log (M + 1 : ℕ) → τ M y = 0)
    (A : ℂ)
    (hsignature : ∀ M, (∫ y, τ M y * kernel (ρ - 1 / 2) y) = -A)
    (hgrowth : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun M : ℕ => Real.exp (-ε * Real.log (M + 1 : ℕ)) * energy (τ M))
      atTop (𝓝 0)) : A = 0 := by
  let c : ℝ := 2 * ρ.re - 1
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound (M : ℕ) : c * Real.exp (c * a) * ‖A‖ ^ 2 ≤
      Real.exp (-c * Real.log (M + 1 : ℕ)) * energy (τ M) := by
    let L : ℝ := Real.log (M + 1 : ℕ)
    have h := supported_signature_energy_lower_bound (τ M) ρ hρ
      (a + Real.log (M + 1 : ℕ)) (hLp M) (hsupport M) A (hsignature M)
    have he : Real.exp (-c * L) * (c * Real.exp (c * (a + L)) * ‖A‖ ^ 2) =
        c * Real.exp (c * a) * ‖A‖ ^ 2 := by
      rw [show c * (a + L) = c * a + c * L by ring, Real.exp_add,
        show -c * L = -(c * L) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    rw [← he]
    exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  have hle : c * Real.exp (c * a) * ‖A‖ ^ 2 ≤ 0 :=
    ge_of_tendsto (hgrowth c hc) (Eventually.of_forall hbound)
  by_contra hA
  have hp : 0 < c * Real.exp (c * a) * ‖A‖ ^ 2 :=
    mul_pos (mul_pos hc (Real.exp_pos _)) (pow_pos (norm_pos_iff.mpr hA) 2)
  exact (not_le_of_gt hp) hle

/-- A power upper bound below the precise transform exponent forces the
fixed signature to vanish. The eventual upper bound is a hypothesis, not a
proved arithmetic estimate. Source: candid assessment, section 1. -/
theorem signature_eq_zero_of_supported_power_bound
    {τ : ℕ → ℝ → ℂ} {a b C : ℝ} {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (hLp : ∀ M, MemLp (τ M) 2 volume)
    (hsupport : ∀ M y, y < a + Real.log (M + 1 : ℕ) → τ M y = 0)
    (A : ℂ)
    (hsignature : ∀ M, (∫ y, τ M y * kernel (ρ - 1 / 2) y) = -A)
    (hgap : b < 2 * ρ.re - 1)
    (hupper : ∀ᶠ M : ℕ in atTop, energy (τ M) ≤
      C * Real.exp (b * Real.log (M + 1 : ℕ))) : A = 0 := by
  let c : ℝ := 2 * ρ.re - 1
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : ∀ᶠ M : ℕ in atTop,
      c * Real.exp (c * a) * ‖A‖ ^ 2 ≤
        C * Real.exp ((b - c) * Real.log (M + 1 : ℕ)) := by
    filter_upwards [hupper] with M hM
    let L : ℝ := Real.log (M + 1 : ℕ)
    have hlow := supported_signature_energy_lower_bound (τ M) ρ hρ
      (a + Real.log (M + 1 : ℕ)) (hLp M) (hsupport M) A (hsignature M)
    have h := mul_le_mul_of_nonneg_left (hlow.trans hM)
      (Real.exp_nonneg (-c * L))
    have hleft : Real.exp (-c * L) *
        (c * Real.exp (c * (a + L)) * ‖A‖ ^ 2) =
        c * Real.exp (c * a) * ‖A‖ ^ 2 := by
      rw [show c * (a + L) = c * a + c * L by ring, Real.exp_add,
        show -c * L = -(c * L) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    have hright : Real.exp (-c * L) * (C * Real.exp (b * L)) =
        C * Real.exp ((b - c) * L) := by
      calc
        _ = C * (Real.exp (-c * L) * Real.exp (b * L)) := by ring
        _ = C * Real.exp (-c * L + b * L) := by rw [Real.exp_add]
        _ = _ := by congr 2; ring
    change Real.exp (-c * L) * (c * Real.exp (c * (a + L)) * ‖A‖ ^ 2) ≤
      Real.exp (-c * L) * (C * Real.exp (b * L)) at h
    rw [hleft, hright] at h
    exact h
  have hnat : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    obtain ⟨N, hN⟩ := exists_nat_gt r
    filter_upwards [eventually_ge_atTop N] with M hM
    have hcast : (N : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (hM.trans (Nat.le_succ M))
    exact (hN.trans_le hcast).le
  have hlog : Tendsto (fun M : ℕ => Real.log (M + 1 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hneg : b - c < 0 := by dsimp [c]; linarith
  have hlim : Tendsto (fun M : ℕ =>
      C * Real.exp ((b - c) * Real.log (M + 1 : ℕ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg hneg hlog)).const_mul C
  have hle : c * Real.exp (c * a) * ‖A‖ ^ 2 ≤ 0 := ge_of_tendsto hlim hbound
  by_contra hA
  have hp : 0 < c * Real.exp (c * a) * ‖A‖ ^ 2 :=
    mul_pos (mul_pos hc (Real.exp_pos _)) (pow_pos (norm_pos_iff.mpr hA) 2)
  exact (not_le_of_gt hp) hle

end MeasureTheory.RemoteLaplaceTail
