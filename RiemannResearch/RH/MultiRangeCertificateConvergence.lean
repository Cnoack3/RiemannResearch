import RiemannResearch.RH.MultiRangeEnergyCertificates
import RiemannResearch.RH.ConditionalMeanFiniteCutoff

/-!
# Convergent certificates for the actual infinite conditional-mean energy

Source: `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`, Section 7.
The fixed-candidate convergence theorem is unconditional for a legal candidate
with a supplied uniform mean bound. The optimization sandwich below explicitly
requires minimizers; it neither asserts their existence nor hides a uniform
bound on coefficients as the divisor family varies.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

/-- An upper certificate includes the complete, rigorously bounded infinite tail. -/
def conditionalMeanUpperCertificate (F : ℕ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  conditionalMeanPrefix F N + 2 / ((N : ℝ)+2) * L^2

theorem conditionalMeanPrefix_monotone (F : ℕ → ℝ) :
    Monotone (conditionalMeanPrefix F) := by
  apply monotone_nat_of_le_succ
  intro N
  simp only [conditionalMeanPrefix, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))

theorem conditionalMeanPrefix_tendsto (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    Tendsto (conditionalMeanPrefix F) atTop (𝓝 (conditionalMeanSquare F)) :=
  (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hF).hasSum.tendsto_sum_nat

/-- Explicit certificate accuracy; no unproved rate in a growing family is used. -/
theorem conditionalMean_certificate_accuracy (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, |cesaro F t| ≤ L) (ε : ℝ) (hε : 0 < ε)
    (N : ℕ) (hN : 2 * L^2 / ε < (N : ℝ)) :
    0 ≤ conditionalMeanSquare F - conditionalMeanPrefix F N ∧
    conditionalMeanSquare F - conditionalMeanPrefix F N < ε ∧
    0 ≤ conditionalMeanUpperCertificate F L N - conditionalMeanSquare F ∧
    conditionalMeanUpperCertificate F L N - conditionalMeanSquare F < ε := by
  obtain ⟨hlo, hhi⟩ := conditionalMeanSquare_finite_certificate F hF N L hL
    (fun t _ => hb t)
  change conditionalMeanPrefix F N ≤ conditionalMeanSquare F at hlo
  change conditionalMeanSquare F ≤ conditionalMeanUpperCertificate F L N at hhi
  have hwidth : 2 / ((N : ℝ)+2) * L^2 < ε := by
    have hprod := (div_lt_iff₀ hε).mp hN
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)+2)).2
    nlinarith
  dsimp [conditionalMeanUpperCertificate] at hhi ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem conditionalMeanUpperCertificate_tendsto (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, |cesaro F t| ≤ L) :
    Tendsto (conditionalMeanUpperCertificate F L) atTop (𝓝 (conditionalMeanSquare F)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * L^2 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc := conditionalMean_certificate_accuracy F hF L hL hb ε hε n (hN.trans_le hn')
  simpa only [Real.dist_eq, abs_of_nonneg hc.2.2.1] using hc.2.2.2

/-- A finite objective minimizer and a full objective minimizer give the exact
certificate sandwich. Their existence is a separate finite-dimensional result. -/
theorem conditionalMean_optimizer_certificate {ι : Type*}
    (F : ι → ℕ → ℝ) (hF : ∀ x, F x ∈ legalSeedSpan (Set.Ici 1))
    (xstar xN : ι) (N : ℕ)
    (hstar : ∀ x, conditionalMeanSquare (F xstar) ≤ conditionalMeanSquare (F x))
    (hmin : ∀ x, conditionalMeanPrefix (F xN) N ≤ conditionalMeanPrefix (F x) N)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ t, N < t → |cesaro (F xN) t| ≤ L) :
    conditionalMeanPrefix (F xN) N ≤ conditionalMeanSquare (F xstar) ∧
    conditionalMeanSquare (F xstar) ≤ conditionalMeanSquare (F xN) ∧
    conditionalMeanSquare (F xN) ≤ conditionalMeanUpperCertificate (F xN) L N := by
  have hlo := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) (hF xstar)).sum_le_tsum (Finset.range N)
      (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))
  exact ⟨(hmin xstar).trans hlo, hstar xN,
    (conditionalMeanSquare_finite_certificate (F xN) (hF xN) N L hL hb).2⟩

/-- Pointwise increasing truncated objectives have increasing minimum values. -/
theorem conditionalMean_truncated_minima_monotone {ι : Type*}
    (F : ι → ℕ → ℝ) (x : ℕ → ι)
    (hmin : ∀ N y, conditionalMeanPrefix (F (x N)) N ≤ conditionalMeanPrefix (F y) N) :
    Monotone (fun N => conditionalMeanPrefix (F (x N)) N) := by
  intro N M hNM
  exact (hmin N (x M)).trans (conditionalMeanPrefix_monotone (F (x M)) hNM)

/-- Uniform control of the candidate means suffices for convergence of optimized
certificates. This explicit hypothesis is not claimed uniformly in growing
families, and is not a replacement for proving bounded coefficients in a fixed
finite family. -/
theorem conditionalMean_optimizer_certificates_tendsto {ι : Type*}
    (F : ι → ℕ → ℝ) (hF : ∀ x, F x ∈ legalSeedSpan (Set.Ici 1))
    (xstar : ι) (x : ℕ → ι)
    (hstar : ∀ y, conditionalMeanSquare (F xstar) ≤ conditionalMeanSquare (F y))
    (hmin : ∀ N y, conditionalMeanPrefix (F (x N)) N ≤ conditionalMeanPrefix (F y) N)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ N t, |cesaro (F (x N)) t| ≤ L) :
    Tendsto (fun N => conditionalMeanPrefix (F (x N)) N) atTop
      (𝓝 (conditionalMeanSquare (F xstar))) ∧
    Tendsto (fun N => conditionalMeanUpperCertificate (F (x N)) L N) atTop
      (𝓝 (conditionalMeanSquare (F xstar))) := by
  have haccuracy (ε : ℝ) (hε : 0 < ε) (N : ℕ)
      (hN : 2 * L^2 / ε < (N : ℝ)) :
      |conditionalMeanPrefix (F (x N)) N - conditionalMeanSquare (F xstar)| < ε ∧
      |conditionalMeanUpperCertificate (F (x N)) L N -
        conditionalMeanSquare (F xstar)| < ε := by
    obtain ⟨hlo, hmid, hhi⟩ := conditionalMean_optimizer_certificate F hF xstar (x N)
      N hstar (hmin N) L hL (fun t _ => hb N t)
    have hwidth : 2 / ((N : ℝ)+2) * L^2 < ε := by
      have hprod := (div_lt_iff₀ hε).mp hN
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)+2)).2
      nlinarith
    have hupper : 0 ≤ conditionalMeanUpperCertificate (F (x N)) L N -
        conditionalMeanSquare (F xstar) := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonneg hupper]
    dsimp [conditionalMeanUpperCertificate] at hhi ⊢
    constructor <;> linarith
  constructor
  · apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * L^2 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa only [Real.dist_eq] using (haccuracy ε hε n (hN.trans_le hn')).1
  · apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * L^2 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa only [Real.dist_eq] using (haccuracy ε hε n (hN.trans_le hn')).2

end RiemannResearch.RH.Pareto
