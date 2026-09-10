import RiemannResearch.RH.DyadicRegularizedNorm
import RiemannResearch.RH.DampedMobiusCoefficientEnergy
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary uniform bounds for the actual regularization normalization

Source: Section 7 of `FourierBridgeUniformSignedEnergy20260910.md`.
The Laurent-series argument there can be replaced by real integral comparison.
No analytic continuation or zero-free region is needed for these bounds.
-/

open scoped BigOperators
open Filter

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Integral comparison for the actual positive-damping zeta series. -/
theorem regularizationZetaSeries_integral_bounds {ε : ℝ} (hε : 0 < ε) :
    1 / ε ≤ regularizationZetaSeries ε ∧
      regularizationZetaSeries ε ≤ 1 + 1 / ε := by
  let f : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-(1 + ε))
  let I : ℕ → ℝ := fun M => (1 - (1 + (M : ℝ)) ^ (-ε)) / ε
  have hs : Summable f := regularizationZetaSeries_summable hε
  have hs' : Summable (fun n => f (n + 1)) := hs.comp_injective Nat.succ_injective
  have hmono (M : ℕ) :
      AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Set.Icc 1 (1 + (M : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint (M : ℕ) :
      (∫ x : ℝ in (1 : ℝ)..1 + (M : ℝ), x ^ (-(1 + ε))) = I M := by
    rw [integral_rpow (Or.inr ⟨by linarith,
      Set.notMem_uIcc_of_lt (by norm_num : (0 : ℝ) < 1) (by positivity)⟩)]
    rw [show -(1 + ε) + 1 = -ε by ring, Real.one_rpow]
    dsimp [I]
    field_simp [hε.ne']
    ring
  have hlo (M : ℕ) : I M ≤ ∑ n ∈ Finset.range M, f n := by
    have h := (hmono M).integral_le_sum
    rw [hint M] at h
    simpa [f, add_comm] using h
  have hhi (M : ℕ) : (∑ n ∈ Finset.range M, f (n + 1)) ≤ I M := by
    have h := (hmono M).sum_le_integral
    rw [hint M] at h
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h
  have htop : Tendsto (fun M : ℕ => 1 + (M : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun M => by linarith) tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_neg_atTop hε).comp htop
  have hI : Tendsto I atTop (nhds (1 / ε)) := by
    simpa [I] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hpow).div_const ε
  have hleft : 1 / ε ≤ ∑' n, f n :=
    le_of_tendsto_of_tendsto hI hs.hasSum.tendsto_sum_nat (Eventually.of_forall hlo)
  have hright : (∑' n, f (n + 1)) ≤ 1 / ε :=
    le_of_tendsto_of_tendsto hs'.hasSum.tendsto_sum_nat hI (Eventually.of_forall hhi)
  have hsplit := hs.tsum_eq_zero_add
  have hf0 : f 0 = 1 := by simp [f]
  rw [hf0] at hsplit
  change (1 / ε ≤ ∑' n, f n) ∧ (∑' n, f n) ≤ 1 + 1 / ε
  exact ⟨hleft, by linarith⟩

/-- The normalization error is first order, directly from real integral comparison. -/
theorem dyadicRegularizationNormalization_elementary_bounds {ε : ℝ} (hε : 0 < ε) :
    1 - ε * Real.log 3 ≤ dyadicRegularizationNormalization ε ∧
      dyadicRegularizationNormalization ε ≤ 1 + ε := by
  let Z := regularizationZetaSeries ε
  let q := triadicDampingRatio ε
  let L := Real.log 3
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hq : 0 ≤ q := (triadicDampingRatio_pos ε).le
  have hZ : 0 ≤ Z := le_trans (by norm_num) (one_le_regularizationZetaSeries hε)
  have hZbounds := regularizationZetaSeries_integral_bounds hε
  have hZlo : 1 ≤ ε * Z := by
    have h := (div_le_iff₀ hε).mp hZbounds.1
    simpa [Z, mul_comm] using h
  have hZhi : ε * Z ≤ 1 + ε := by
    calc
      _ ≤ ε * (1 + 1 / ε) := mul_le_mul_of_nonneg_left hZbounds.2 hε.le
      _ = _ := by field_simp [hε.ne']; ring
  have hqexp : q = Real.exp (-ε * L) := by
    dsimp only [q]
    rw [triadicDampingRatio, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hsmall : 1 - q ≤ ε * L := by
    have h := Real.add_one_le_exp (-ε * L)
    rw [← hqexp] at h
    linarith
  have hlarge : ε * L * q ≤ 1 - q := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (ε * L)) hq
    have hexp : Real.exp (ε * L) * q = 1 := by
      rw [hqexp, ← Real.exp_add]
      simp
    rw [hexp] at h
    nlinarith
  have hNlo : q ≤ dyadicRegularizationNormalization ε := by
    rw [dyadicRegularizationNormalization, le_div_iff₀ hL]
    change q * L ≤ Z * (1 - q)
    calc
      _ ≤ (ε * Z) * (q * L) := by
        simpa using mul_le_mul_of_nonneg_right hZlo (mul_nonneg hq hL.le)
      _ = Z * (ε * L * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge hZ
  have hNhi : dyadicRegularizationNormalization ε ≤ 1 + ε := by
    rw [dyadicRegularizationNormalization, div_le_iff₀ hL]
    change Z * (1 - q) ≤ (1 + ε) * L
    calc
      _ ≤ Z * (ε * L) := mul_le_mul_of_nonneg_left hsmall hZ
      _ = (ε * Z) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hZhi hL.le
  exact ⟨(by dsimp [L] at hsmall; linarith), hNhi⟩

/-- Actual scalar normalization bounds sufficient for the weighted energy theorem. -/
theorem dyadicRegularizationNormalization_uniform_control {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    |dyadicRegularizationNormalization ε| ≤ (3 / 2 : ℝ) ∧
      |dyadicRegularizationNormalization ε - 1| ≤ (1 + Real.log 3) * ε := by
  have hN := dyadicRegularizationNormalization_elementary_bounds hε
  have hpos := dyadicRegularizationNormalization_pos hε
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  constructor
  · rw [abs_of_pos hpos]
    linarith
  · apply abs_le.mpr
    constructor <;> nlinarith

/-- The actual normalization discharges both scalar hypotheses in the genuine
signed coefficient energy estimate. This is an unconditional coefficient
estimate; it does not assert the final compensated boundary-shell estimate. -/
theorem dyadic_normalizedSignedCoefficient_weighted_energy
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) :
    Summable (fun n : ℕ =>
      normalizedSignedCoefficient ε (dyadicRegularizationNormalization ε) n ^ 2 /
        (n : ℝ) ^ 2) ∧
      (∑' n : ℕ,
        normalizedSignedCoefficient ε (dyadicRegularizationNormalization ε) n ^ 2 /
          (n : ℝ) ^ 2) ≤
        (((1 + Real.log 3) ^ 2 + 16 * (3 / 2 : ℝ) ^ 2) *
          (∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ))) * ε ^ 2 := by
  obtain ⟨hN, hK⟩ := dyadicRegularizationNormalization_uniform_control hε hhalf
  exact normalizedSignedCoefficient_weighted_energy hε.le hN hK

end
end RiemannResearch.RH.Pareto
