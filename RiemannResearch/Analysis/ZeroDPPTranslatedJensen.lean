import RiemannResearch.Analysis.OrdinateWindowVariance
import Mathlib.Tactic

/-! The restored-second-moment Jensen inequality on physical translated
windows, using their existing Lebesgue integrals over the whole real line. -/
noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.DPPLargeWidth
open OrdinateWindowVariance

theorem translated_count_restored_loss_ge
    {T m : ℝ} (hT : 0 ≤ T) (Z X : ℝ → ℝ) (hiZ : Integrable Z) (hiX : Integrable X)
    (hz : Integrable (fun t => Z t ^ 2)) (hx : Integrable (fun t => X t ^ 2))
    (hZsup : ∀ t, Z t * pulse 0 T t = Z t)
    (hXsup : ∀ t, X t * pulse 0 T t = X t)
    (hthin : ∀ t, 0 ≤ X t ∧ X t ≤ Z t)
    (hmean : (∫ t, Z t - X t) = T*m) :
    T*(m^2-m) ≤ (∫ t, Z t^2) - ((∫ t, X t^2) + (∫ t, Z t-X t)) := by
  have hiH : Integrable (fun t => Z t - X t) := hiZ.sub hiX
  have h1 := hiH.const_mul (2*m)
  have h2 := (pulse_integrable 0 T).const_mul (m^2)
  have hlow :
      (∫ t, (2*m)*(Z t-X t) - m^2 * pulse 0 T t) ≤
      (∫ t, Z t^2 - X t^2) := by
    apply integral_mono (h1.sub h2) (hz.sub hx)
    intro t
    change (2*m)*(Z t-X t) - m^2 * pulse 0 T t ≤ Z t^2 - X t^2
    by_cases ht : t ∈ Ioc 0 T
    · rw [show pulse 0 T t = 1 by simp [pulse, ht]]
      have h := hthin t
      nlinarith only [sq_nonneg (Z t - X t - m), mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    · have hp : pulse 0 T t = 0 := by simp [pulse, ht]
      have hZ := hZsup t
      have hX := hXsup t
      simp only [hp,mul_zero] at hZ hX
      simp [← hZ, ← hX, hp]
  rw [integral_sub h1 h2, integral_const_mul, integral_const_mul, integral_pulse,
    sub_zero, max_eq_left hT, hmean, integral_sub hz hx] at hlow
  rw [hmean]
  nlinarith only [hlow]

/-- Finite full and thinned configurations may have different index types.
The geometric input is just pointwise inclusion of the thinned counts. -/
theorem finite_window_restored_loss_ge {ι κ : Type*} (s : Finset ι) (u : Finset κ)
    (x : ι → ℝ) (y : κ → ℝ) {T h m : ℝ} (hT : 0 ≤ T)
    (hthin : ∀ t, windowCount u y T h t ≤ windowCount s x T h t)
    (hmean : (∫ t, windowCount s x T h t - windowCount u y T h t) = T*m) :
    T*(m^2-m) ≤ (∫ t, windowCount s x T h t ^ 2) -
      ((∫ t, windowCount u y T h t ^ 2) +
        (∫ t, windowCount s x T h t - windowCount u y T h t)) := by
  apply translated_count_restored_loss_ge hT (windowCount s x T h) (windowCount u y T h)
    (windowCount_integrable ..) (windowCount_integrable ..)
    (windowCount_sq_integrable ..) (windowCount_sq_integrable ..)
    (windowCount_mul_support s x T h) (windowCount_mul_support u y T h) _ hmean
  intro t
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), hthin t⟩
  unfold windowPulse pulse
  by_cases ht : t ∈ Ioc (max 0 (y i-h)) (min T (y i)) <;> simp [ht]

/--
info: 'RiemannResearch.Analysis.DPPLargeWidth.finite_window_restored_loss_ge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_window_restored_loss_ge

end RiemannResearch.Analysis.DPPLargeWidth
