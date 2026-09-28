import RiemannResearch.RH.CriticalLineZeros
import RiemannResearch.RH.ParetoShapeCapacity

/-!
# Uniform subcritical-shape obstruction and moving-shape necessity

The imported critical-zero theorem supplies one fixed Mellin certificate.
Its exact tail Cauchy bound gives one constant valid for every positive
shape below one, every dictionary size, and every complex coefficient vector.
The bound degenerates at most as `1 / (α * (1 - α))`.

Consequently normalized trials of vanishing complete tail energy, at shapes
bounded away from zero, must approach shape one. This is an unconditional
necessary condition. It supplies neither such trials nor endpoint density.

Source: assembly of the repository's proved Mellin capacity bounds with the
pinned Zeta23 critical-zero provider; the moving-shape argument is elementary.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity
open RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- One strictly positive constant controls every finite dictionary and all
positive subcritical shapes. No zeta-zero premise remains. -/
theorem exists_uniform_subcritical_shape_coercivity :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∀ (n : ℕ) (c : Fin n → ℂ),
        (α * (1 - α)) * ‖complexReciprocalSource n c‖ ^ 2 ≤
          C * shapeLegalTailEnergy α n c := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have hs0 : s ≠ 0 := by intro h; simp [h] at hspos
  have hs1 : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have hhead : 1 - (2 : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have he : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos
        (show (0 : ℝ) < 2 by norm_num) (-s)
    have hl : (2 : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [he, norm_one] at hn
    linarith
  have hA : 0 < ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hhead) 2
  have hS : 0 < ‖s‖ ^ 2 := pow_pos (norm_pos_iff.mpr hs0) 2
  refine ⟨‖s‖ ^ 2 / ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2, div_pos hS hA, ?_⟩
  intro α hα hα1 n c
  have hden : 0 < α * (1 - α) := mul_pos hα (sub_pos.mpr hα1)
  have hE := shapeLegalTailEnergy_nonneg α hα n c
  have hcs : ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 *
      ‖complexReciprocalSource n c‖ ^ 2 ≤
      (‖s‖ ^ 2 * (2 : ℝ) ^ (α - 1) / (α * (1 - α))) *
        shapeLegalTailEnergy α n c := by
    simpa only [hs, show 2 * (1 / 2 : ℝ) = 1 by norm_num] using
      zero_shapeLegal_tail_cauchy α s hα (by rw [hs]; linarith) hs1 hz n c
  have hscaled : (α * (1 - α)) * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 *
      ‖complexReciprocalSource n c‖ ^ 2 ≤
      (‖s‖ ^ 2 * (2 : ℝ) ^ (α - 1)) * shapeLegalTailEnergy α n c := by
    calc
      _ = (‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 *
          ‖complexReciprocalSource n c‖ ^ 2) * (α * (1 - α)) := by ring
      _ ≤ ((‖s‖ ^ 2 * (2 : ℝ) ^ (α - 1) / (α * (1 - α))) *
          shapeLegalTailEnergy α n c) * (α * (1 - α)) :=
        mul_le_mul_of_nonneg_right hcs hden.le
      _ = _ := by field_simp [hα.ne', (sub_pos.mpr hα1).ne']
  have hp : (2 : ℝ) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hmajor : (‖s‖ ^ 2 * (2 : ℝ) ^ (α - 1)) * shapeLegalTailEnergy α n c ≤
      ‖s‖ ^ 2 * shapeLegalTailEnergy α n c := by
    calc
      _ = (2 : ℝ) ^ (α - 1) * (‖s‖ ^ 2 * shapeLegalTailEnergy α n c) := by ring
      _ ≤ 1 * (‖s‖ ^ 2 * shapeLegalTailEnergy α n c) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg hS.le hE)
      _ = _ := one_mul _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hA).2
  nlinarith only [hscaled.trans hmajor]

/-- A single constant bounds every subcritical capacity with an explicit
shape dependence; the supremum is over all complex coefficient vectors. -/
theorem exists_subcritical_shape_capacity_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ n : ℕ,
      shapeFiniteCapacity α n ≤ C / (α * (1 - α)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_subcritical_shape_coercivity
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 n
  have hden : 0 < α * (1 - α) := mul_pos hα (sub_pos.mpr hα1)
  unfold shapeFiniteCapacity
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  dsimp only
  by_cases he : shapeLegalTailEnergy α n c = 0
  · rw [he, div_zero]
    exact (div_pos hC hden).le
  · have hE : 0 < shapeLegalTailEnergy α n c :=
      lt_of_le_of_ne (shapeLegalTailEnergy_nonneg α hα n c) (Ne.symm he)
    apply (div_le_iff₀ hE).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith only [hb α hα hα1 n c]

/-- Every fixed shape below one has a positive complete tail-energy gap
for all head-normalized legal finite combinations. -/
theorem exists_subcritical_shape_normalized_tail_gap
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (c : Fin n → ℂ),
      complexReciprocalSource n c = 1 → δ ≤ shapeLegalTailEnergy α n c := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_subcritical_shape_coercivity
  refine ⟨α * (1 - α) / C, div_pos (mul_pos hα (sub_pos.mpr hα1)) hC, ?_⟩
  intro n c hc
  have h := hb α hα hα1 n c
  rw [hc, norm_one, one_pow, mul_one] at h
  exact (div_le_iff₀ hC).2 (by nlinarith only [h])

/-- If normalized complete tail energies tend to zero while the shapes
remain bounded away from zero, their shapes must tend to one. This necessary
condition is unconditional and quantitatively follows from the uniform gap. -/
theorem subcritical_normalized_small_tail_shapes_tendsto_one
    (α : ℕ → ℝ) (n : ℕ → ℕ) (c : ∀ j : ℕ, Fin (n j) → ℂ)
    {a : ℝ} (ha : 0 < a) (haα : ∀ j, a ≤ α j) (hα1 : ∀ j, α j < 1)
    (hc : ∀ j, complexReciprocalSource (n j) (c j) = 1)
    (hE : Tendsto (fun j => shapeLegalTailEnergy (α j) (n j) (c j))
      atTop (𝓝 0)) :
    Tendsto α atTop (𝓝 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_subcritical_shape_coercivity
  have hgap (j : ℕ) : 1 - α j ≤
      (C / a) * shapeLegalTailEnergy (α j) (n j) (c j) := by
    have hα : 0 < α j := ha.trans_le (haα j)
    have h := hb (α j) hα (hα1 j) (n j) (c j)
    rw [hc j, norm_one, one_pow, mul_one] at h
    have hg : 0 ≤ 1 - α j := (sub_pos.mpr (hα1 j)).le
    have hlow := mul_le_mul_of_nonneg_right (haα j) hg
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).2
    nlinarith only [hlow, h]
  have hlim : Tendsto (fun j => 1 - α j) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => (sub_pos.mpr (hα1 j)).le) hgap
    simpa only [mul_zero] using hE.const_mul (C / a)
  have hlim' : Tendsto (fun j => (1 : ℝ) - (1 - α j)) atTop (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hlim
  simpa only [sub_sub_cancel, sub_zero] using hlim'

/-- For normalized trials, the complete energy is at least a fixed multiple
of the distance to shape one, uniformly over all dictionaries. -/
theorem exists_subcritical_shape_normalized_gap_rate
    (a : ℝ) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℝ, a ≤ α → α < 1 →
      ∀ (n : ℕ) (c : Fin n → ℂ), complexReciprocalSource n c = 1 →
        δ * (1 - α) ≤ shapeLegalTailEnergy α n c := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_subcritical_shape_coercivity
  refine ⟨a / C, div_pos ha hC, ?_⟩
  intro α haα hα1 n c hc
  have h := hb α (ha.trans_le haα) hα1 n c
  rw [hc, norm_one, one_pow, mul_one] at h
  have hlo := mul_le_mul_of_nonneg_right haα (sub_pos.mpr hα1).le
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).2
  nlinarith only [hlo, h]

/-- Even for moving shapes, normalized complete energy cannot be little-o
of the distance to the endpoint. The statement uses the literal quotient. -/
theorem not_subcritical_normalized_energy_ratio_tendsto_zero
    (α : ℕ → ℝ) (n : ℕ → ℕ) (c : ∀ j : ℕ, Fin (n j) → ℂ)
    {a : ℝ} (ha : 0 < a) (haα : ∀ j, a ≤ α j) (hα1 : ∀ j, α j < 1)
    (hc : ∀ j, complexReciprocalSource (n j) (c j) = 1) :
    ¬ Tendsto (fun j => shapeLegalTailEnergy (α j) (n j) (c j) / (1 - α j))
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hb⟩ := exists_subcritical_shape_normalized_gap_rate a ha
  intro hlim
  obtain ⟨j, hj⟩ := (hlim.eventually_lt_const hδ).exists
  have hlow := (le_div_iff₀ (sub_pos.mpr (hα1 j))).2
    (hb (α j) (haα j) (hα1 j) (n j) (c j) (hc j))
  exact (not_lt_of_ge hlow) hj

end RiemannResearch.RH.Pareto.ShapeCapacity
