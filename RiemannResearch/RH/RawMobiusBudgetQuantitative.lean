import RiemannResearch.RH.RawMobiusBudgetSublinear
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy

/-!
# Exact norm comparison and a quantitative raw Mobius budget

The full physical tail is retained in an exact harmonic-number identity.
The unconditional arithmetic provider combines the existing quantitative PNT
estimate for the canonical approximants with reciprocal-Mobius square-log decay.
It supplies a logarithmic saving, not the open cofinal subpower estimate.

Source: continuation of the user's NymanBeurlingSubpowerAudit20260924.md,
September 24, 2026. The arithmetic inputs and their provenance are in
CanonicalMobiusQuantitativeEnergy and MobiusQuantitativeRate; all comparisons
here are direct consequences of the existing finite-window identities.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Explicit ceiling for the normalized actual signed arithmetic budget. -/
def rawMobiusBudgetCeiling (C : ℝ) (N : ℕ) : ℝ :=
  16/(N : ℝ) + (25+8*(2+4*C)^2)*canonicalMobiusEnergyRate N +
    16*(2+4*C)^2*(canonicalMobiusEnergyRate N)^2

theorem rawMobiusBudgetCeiling_tendsto_zero (C : ℝ) :
    Tendsto (rawMobiusBudgetCeiling C) atTop (𝓝 0) := by
  have hi := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 16
  have hx := canonicalMobiusEnergyRate_tendsto_zero
  have hh := (hi.add (hx.const_mul (25+8*(2+4*C)^2))).add
    ((hx.pow 2).const_mul (16*(2+4*C)^2))
  simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at hh
  convert hh using 1
  ext N
  simp only [rawMobiusBudgetCeiling]
  ring

/-- Unconditional quantitative PNT provider; no arithmetic premise is assumed. -/
theorem rawMobiusSquareBudget_eventual_explicit_ceiling :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N/(N : ℝ) ≤ rawMobiusBudgetCeiling C N := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  have hm := mobiusReciprocalSum_sq_mul_log_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, hm, eventually_ge_atTop (2 : ℕ)] with N hEN hmN hN
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hm' : (mobiusReciprocalSum N)^2 ≤ 1/Real.log (N : ℝ) :=
    (le_div_iff₀ hL).mpr hmN.le
  have hQ : 1 ≤ 1+Real.log (Real.log (N : ℝ)+3) := by
    have := Real.log_nonneg (show 1 ≤ Real.log (N : ℝ)+3 by linarith)
    linarith
  have hx : 1/Real.log (N : ℝ) ≤ canonicalMobiusEnergyRate N :=
    div_le_div_of_nonneg_right hQ hL.le
  have he : ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤
      canonicalMobiusEnergyCeiling C N := hEN
  have hb := rawMobiusSquareBudget_div_le N (by omega)
  have hmsq := hm'.trans hx
  unfold rawMobiusBudgetCeiling canonicalMobiusEnergyCeiling at *
  simp only [div_eq_mul_inv] at he hb ⊢
  nlinarith only [he, hb, hmsq]


/-- Exact equality between the finite budget and the full physical norm. -/
theorem rawMobiusSquareBudget_add_far_eq (N : ℕ) :
    rawMobiusSquareBudget N + rawMobiusFarEnergy N (N^2) =
      ‖hilbertOne-rawMobiusHilbert N‖^2 +
        (mobiusReciprocalSum N)^2*((harmonic (N+1) : ℝ)-1) := by
  have hH : (harmonic (N+1) : ℝ) =
      ∑ k ∈ Finset.range (N+1), 1/((k : ℝ)+1) := by
    simp [harmonic, one_div]
  have hsum : (∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1)) +
      (harmonic (N+1) : ℝ) = (N : ℝ)+1 := by
    rw [hH, ← Finset.sum_add_distrib]
    calc
      _ = ∑ k ∈ Finset.range (N+1), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        field_simp
      _ = _ := by simp
  rw [rawMobius_energy_three_regions N (N^2) (by nlinarith)]
  unfold rawMobiusSquareBudget
  nlinarith [congrArg (fun x : ℝ => (mobiusReciprocalSum N)^2*x) hsum]

/-- Together with the square-window bound, the full norm and finite budget
control each other with universal constants. -/
theorem rawMobiusSquareBudget_le_two_raw_norm_sq (N : ℕ) :
    rawMobiusSquareBudget N ≤ 2*‖hilbertOne-rawMobiusHilbert N‖^2 := by
  have hsum : (N : ℝ)/2 ≤
      ∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_div, add_zero]
    calc
      _ = ∑ k ∈ Finset.range N, (1/2 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        apply (le_div_iff₀ (by positivity)).mpr
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
  have he := rawMobius_energy_three_regions N (N^2) (by nlinarith)
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (mobiusReciprocalSum N))
  have hm := rawMobiusMiddleEnergy_nonneg N (N^2)
  have hf := rawMobiusFarEnergy_nonneg N (N^2)
  unfold rawMobiusSquareBudget
  nlinarith


end RiemannResearch.RH.Pareto
