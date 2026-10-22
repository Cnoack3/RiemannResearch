import RiemannResearch.Analysis.OrdinateCollisionSharpRemainder
import Mathlib.Order.Fin.Basic

/-!
# The sharp collision remainder from consecutive ordinate gaps

Consecutive gaps of at least `δ` imply the rank-separation hypothesis used
in `rankWeightedSincEnergy_sharp_remainder`. The proof applies monotonicity
to the corrected ordinate sequence `τᵢ - δ i`.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

theorem rank_separation_of_consecutive_spacing {N : ℕ}
    (ordinate : Fin (N + 1) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ i : Fin N, δ ≤ ordinate i.succ - ordinate i.castSucc) :
    ∀ i j, δ * |(i.val : ℝ) - (j.val : ℝ)| ≤ |ordinate i - ordinate j| := by
  have hmono : Monotone (fun i : Fin (N + 1) => ordinate i - δ * (i.val : ℝ)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hs := hstep i
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    nlinarith
  intro i j
  rcases le_total i j with hij | hji
  · have hv : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hij
    have hs := hmono hij
    have ho : ordinate i ≤ ordinate j := by
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hv)]
    rw [abs_of_nonpos (sub_nonpos.mpr hv), abs_of_nonpos (sub_nonpos.mpr ho)]
    nlinarith
  · have hv : (j.val : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hji
    have hs := hmono hji
    have ho : ordinate j ≤ ordinate i := by
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hv)]
    rw [abs_of_nonneg (sub_nonneg.mpr hv), abs_of_nonneg (sub_nonneg.mpr ho)]
    nlinarith

theorem rankWeightedSincEnergy_sharp_remainder_of_consecutive_spacing {N : ℕ}
    (ordinate : Fin (N + 1) → ℝ) (M : Fin (N + 1) → ℕ) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hstep : ∀ i : Fin N, δ ≤ ordinate i.succ - ordinate i.castSucc) :
    0 ≤ rankWeightedSincEnergy ordinate M R - rankCollisionMass M ∧
    rankWeightedSincEnergy ordinate M R - rankCollisionMass M ≤
      4 * Real.pi ^ 2 * rankCollisionMass M / (3 * R ^ 2 * δ ^ 2) :=
  rankWeightedSincEnergy_sharp_remainder ordinate M hR hδ
    (rank_separation_of_consecutive_spacing ordinate hδ.le hstep)

end RiemannResearch.Analysis.OrdinateCollisionCertificate
