import RiemannResearch.RH.ParetoUniformLaw
import RiemannResearch.RH.ParetoNymanPointwise
import RiemannResearch.RH.ParetoSequenceCertificates

/-!
# Exact Nyman--Pareto norm identification

Source: the user-provided Pareto--Nyman argument, September 2026.
The actual uniform measure and its pushforward are constructed in
`ParetoUniformLaw`; the pointwise fractional-part identity is proved in
`ParetoNymanPointwise`. No density theorem is assumed.
-/

namespace RiemannResearch.RH.Pareto

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The complete Nyman square error is exactly the complete discrete Pareto
square error. This retains all residues and every cross term. -/
theorem nyman_finite_lintegral_error (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫⁻ u : ℝ in Ioc 0 1,
      ENNReal.ofReal ((1 - ∑ n ∈ s, a n *
        (Int.fract (1 / ((n : ℝ) * u)) -
          (1 / (n : ℝ)) * Int.fract (1 / u))) ^ 2)) =
    ∑' k : ℕ, ENNReal.ofReal
      ((1 / ((k : ℝ) * ((k : ℝ) + 1))) *
        (1 - ∑ n ∈ s, a n * (((k % n : ℕ) : ℝ) / (n : ℝ))) ^ 2) := by
  calc
    _ = ∫⁻ u : ℝ, ENNReal.ofReal
        ((1 - ∑ n ∈ s, a n *
          (((reciprocalFloor u % n : ℕ) : ℝ) / (n : ℝ))) ^ 2) ∂uniformUnit := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hsum : (∑ n ∈ s, a n *
          (Int.fract (1 / ((n : ℝ) * u)) -
            (1 / (n : ℝ)) * Int.fract (1 / u))) =
          ∑ n ∈ s, a n *
            (((reciprocalFloor u % n : ℕ) : ℝ) / (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [pareto_nyman_pointwise u hu.1 n (hs n hn)]
        rfl
      rw [hsum]
    _ = _ := uniformUnit_lintegral_square
      (fun k => 1 - ∑ n ∈ s, a n * (((k % n : ℕ) : ℝ) / (n : ℝ)))

/-- Every finite legal combination has a finite genuine squared norm, with an
explicit bound depending only on the absolute coefficient sum. -/
theorem nyman_finite_lintegral_error_le (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫⁻ u : ℝ in Ioc 0 1,
      ENNReal.ofReal ((1 - ∑ n ∈ s, a n *
        (Int.fract (1 / ((n : ℝ) * u)) -
          (1 / (n : ℝ)) * Int.fract (1 / u))) ^ 2)) ≤
    ENNReal.ofReal ((1 + ∑ n ∈ s, |a n|) ^ 2) := by
  have hres (n k : ℕ) (hn : 0 < n) :
      |((k % n : ℕ) : ℝ) / (n : ℝ)| ≤ 1 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k % n : ℕ) : ℝ) / (n : ℝ))]
    apply (div_le_iff₀ hnR).mpr
    simpa only [one_mul] using
      (show ((k % n : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast (Nat.mod_lt k hn).le)
  have hcomb (k : ℕ) :
      |∑ n ∈ s, a n * (((k % n : ℕ) : ℝ) / (n : ℝ))| ≤ ∑ n ∈ s, |a n| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hres n k (hs n hn)) (abs_nonneg (a n))
  rw [nyman_finite_lintegral_error s a hs,
    ← uniformUnit_lintegral_square
      (fun k => 1 - ∑ n ∈ s, a n * (((k % n : ℕ) : ℝ) / (n : ℝ)))]
  calc
    _ ≤ ∫⁻ _u : ℝ, ENNReal.ofReal ((1 + ∑ n ∈ s, |a n|) ^ 2) ∂uniformUnit := by
      apply lintegral_mono
      intro u
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (error_square_bounded hcomb (reciprocalFloor u))
    _ = _ := by simp

theorem nyman_finite_lintegral_error_lt_top (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫⁻ u : ℝ in Ioc 0 1,
      ENNReal.ofReal ((1 - ∑ n ∈ s, a n *
        (Int.fract (1 / ((n : ℝ) * u)) -
          (1 / (n : ℝ)) * Int.fract (1 / u))) ^ 2)) < ⊤ :=
  lt_of_le_of_lt (nyman_finite_lintegral_error_le s a hs) ENNReal.ofReal_lt_top

end RiemannResearch.RH.Pareto
