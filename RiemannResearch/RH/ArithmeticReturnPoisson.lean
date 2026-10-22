import RiemannResearch.RH.ArithmeticReturnSupport
import RiemannResearch.Analysis.NymanPoissonCancellation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual arithmetic returns and their Poisson kernel

Source: equation (4.5) of the user-provided Nyman--Weil note. This module
uses the actual arithmetic return and the actual logarithmic half-density
input associated with a Schwartz test supported on the positive half-line.
No Poisson identity, transform identity, or arithmetic return equality is
assumed. `LogarithmicSchwartzTransport` supplies the compact-u to
compact-positive-g equivalence used with this exact synthesis identity.
-/

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- The inverse logarithmic half-density substitution. -/
def logarithmicHalfDensity (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  Real.exp (-y / 2) • g (Real.exp (-y))

private theorem logarithmicHalfDensity_return_term (c : ArithmeticFunction ℝ)
    (g : ℝ → ℂ) (y : ℝ) (k : ℕ) :
    (c k / Real.sqrt k : ℝ) • logarithmicHalfDensity g (y - Real.log k) =
      Real.exp (-y / 2) • (c k • g (Real.exp (-y) * (k : ℝ))) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hsqrt : Real.sqrt (k : ℝ) = Real.exp (Real.log k / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hkR]
    congr 1
    ring
  have he : Real.exp (-(y - Real.log k) / 2) =
      Real.exp (-y / 2) * Real.sqrt k := by
    rw [hsqrt, ← Real.exp_add]
    congr 1
    ring
  have hx : Real.exp (-(y - Real.log k)) = Real.exp (-y) * (k : ℝ) := by
    rw [show -(y - Real.log k) = -y + Real.log k by ring,
      Real.exp_add, Real.exp_log hkR]
  simp only [logarithmicHalfDensity, he, hx, smul_smul]
  congr 1
  have hsq : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hkR).ne'
  field_simp

/-- The beta-weighted sum separates into the constant and divisibility sectors,
retaining both infinite sums exactly. -/
theorem tsum_nyman_beta_smul (n : ℕ) [NeZero n] {h : ℕ → ℂ}
    (hh : Summable h) (hzero : h 0 = 0) :
    (∑' k : ℕ, nymanConductorBeta n k • h k) =
      (1 / (n : ℝ)) • (∑' k : ℕ, h k) - ∑' k : ℕ, h (n * k) := by
  classical
  let d : ℕ → ℂ := fun k => if n ∣ k then h k else 0
  have hd : Summable d := hh.norm.of_norm_bounded (fun k => by
    by_cases hnk : n ∣ k <;> simp [d, hnk])
  have hi : Function.Injective (fun k : ℕ => n * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) hab
  have hs : Function.support d ⊆ Set.range (fun k : ℕ => n * k) := by
    intro k hk
    have hnk : n ∣ k := by
      by_contra he
      exact hk (by simp [d, he])
    obtain ⟨m, hm⟩ := hnk
    exact ⟨m, hm.symm⟩
  have hdsum : (∑' k : ℕ, d k) = ∑' k : ℕ, h (n * k) := by
    rw [← hi.tsum_eq hs]
    simp [d]
  calc
    (∑' k : ℕ, nymanConductorBeta n k • h k) =
        ∑' k : ℕ, ((1 / (n : ℝ)) • h k - d k) := by
      apply tsum_congr
      intro k
      by_cases hk : k = 0
      · simp [hk, hzero, d]
      · by_cases hnk : n ∣ k <;>
          simp [nymanConductorBeta_apply hk, d, hnk, sub_smul]
    _ = (1 / (n : ℝ)) • (∑' k : ℕ, h k) - ∑' k : ℕ, d k := by
      rw [(hh.const_smul (1 / (n : ℝ))).tsum_sub hd, tsum_const_smul'']
    _ = _ := by rw [hdsum]

private theorem nat_samples_eq_int_samples (g : ℝ → ℂ)
    (hg : ∀ x ≤ 0, g x = 0) {a : ℝ} (ha : 0 < a) :
    (∑' k : ℕ, g (a * k)) = ∑' k : ℤ, g (a * k) := by
  have hs : Function.support (fun k : ℤ => g (a * k)) ⊆
      Set.range (fun k : ℕ => (k : ℤ)) := by
    intro k hk
    have hk0 : 0 ≤ k := by
      by_contra h
      have hkR : (k : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      exact hk (hg _ (mul_nonpos_of_nonneg_of_nonpos ha.le hkR.le))
    exact ⟨k.toNat, Int.toNat_of_nonneg hk0⟩
  have hi : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    intro j k hjk
    change (j : ℤ) = (k : ℤ) at hjk
    exact_mod_cast hjk
  simpa using (hi.tsum_eq hs)

private theorem summable_schwartz_nat_mul (g : SchwartzMap ℝ ℂ)
    {a : ℝ} (ha : 0 < a) : Summable (fun k : ℕ => g (a * k)) := by
  have h := summable_schwartz_int (schwartzScale g a ha.ne')
  have hi : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    intro j k hjk
    change (j : ℤ) = (k : ℤ) at hjk
    exact_mod_cast hjk
  simpa [Function.comp_def, Int.cast_natCast] using h.comp_injective hi

/-- Exact identification of the actual arithmetic return with the Poisson lattice
kernel. The square-root weight is essential to the factor `exp(-y/2)`. -/
theorem nymanFullReturn_logarithmicHalfDensity (g : SchwartzMap ℝ ℂ)
    (hg : ∀ x ≤ 0, g x = 0) (n : ℕ) [NeZero n] (y : ℝ) :
    nymanFullReturn n (logarithmicHalfDensity g) y =
      Real.exp (-y / 2) •
        conductorLatticeDiscrepancy g (n : ℝ) (Real.exp (-y)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have ha : 0 < Real.exp (-y) := Real.exp_pos _
  unfold nymanFullReturn arithmeticReturn
  simp_rw [logarithmicHalfDensity_return_term]
  rw [tsum_const_smul'',
    tsum_nyman_beta_smul n (summable_schwartz_nat_mul g ha)
      (by simpa using hg 0 le_rfl)]
  congr 1
  rw [nat_samples_eq_int_samples g hg ha]
  have heq : (fun k : ℕ => g (Real.exp (-y) * (n * k : ℕ))) =
      (fun k : ℕ => g (((n : ℝ) * Real.exp (-y)) * k)) := by
    funext k
    simp only [Nat.cast_mul]
    congr 1
    ring
  rw [heq, nat_samples_eq_int_samples g hg (mul_pos hn ha)]
  simp [conductorLatticeDiscrepancy, one_div]

end RiemannResearch.RH
