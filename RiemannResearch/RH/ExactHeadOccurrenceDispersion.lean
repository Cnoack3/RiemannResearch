import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.Analysis.FiniteAtomDispersion
import RiemannResearch.Analysis.DiscretePrefixHardy
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Tactic

/-!
# Certified atom-reuse bound from optimal return dispersion

Source: Christian Noack, `sdf_modified.pdf`, (127) and (143). We supply
a rational universal constant five using finite Hardy duality and the
actual infinite progression weights. The atom coefficients are explicit
fiber means; their complete squared dispersion has an exact pairwise
formula. No decay of that arithmetic statistic is assumed here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.DiscretePrefixHardy
open RiemannResearch.Analysis.FiniteAtomDispersion
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer

/-- The actual periodized Pareto prefixSum energy has norm at most sqrt(5).
The first progression is controlled by Hardy; all later returns cost at most one. -/
theorem progression_prefix_energy_le_five (P : ℕ) (hP : 0 < P) (a : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (prefixSum a) ≤
      5 * ∑ n ∈ Finset.Icc 1 (P - 1), a n ^ 2 := by
  let D : ℝ := ∑ n ∈ Finset.Icc 1 (P - 1), a n ^ 2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hpoint (r : ℕ) (hr : r ∈ Finset.Icc 1 (P - 1)) :
      progressionWeight P r * prefixSum a r ^ 2 ≤
        (prefixSum a r / r) ^ 2 + D / P := by
    obtain ⟨hr1,hrP⟩ := Finset.mem_Icc.mp hr
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr1
    have hcs : prefixSum a r ^ 2 ≤ (r : ℝ) * D := by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 r) (fun _ => (1 : ℝ)) a
      have hc : (∑ n ∈ Finset.Icc 1 r, (1 : ℝ) ^ 2) = r := by simp
      rw [hc] at hh
      have hsub : (∑ n ∈ Finset.Icc 1 r, a n ^ 2) ≤ D :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hrP)
          (fun n hn _ => sq_nonneg _)
      calc
        _ ≤ (r : ℝ) * ∑ n ∈ Finset.Icc 1 r, a n ^ 2 := by simpa [prefixSum] using hh
        _ ≤ _ := mul_le_mul_of_nonneg_left hsub hrr.le
    have hhead : positiveWeight r * prefixSum a r ^ 2 ≤ (prefixSum a r / r) ^ 2 := by
      have hw : positiveWeight r ≤ 1 / (r : ℝ) ^ 2 := by
        unfold positiveWeight
        apply one_div_le_one_div_of_le (sq_pos_of_pos hrr)
        push_cast
        nlinarith
      calc
        _ ≤ (1 / (r : ℝ) ^ 2) * prefixSum a r ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = _ := by ring
    have htail : (1 / ((P : ℝ) * ((r : ℝ) + 1))) * prefixSum a r ^ 2 ≤ D / P := by
      have hh := hcs.trans (show (r : ℝ) * D ≤ ((r : ℝ) + 1) * D by nlinarith)
      have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      have hdivide : prefixSum a r ^ 2 / ((r : ℝ) + 1) ≤ D :=
        (div_le_iff₀ hrp).mpr (by simpa [mul_comm] using hh)
      calc
        _ = (prefixSum a r ^ 2 / ((r : ℝ) + 1)) / P := by
          simp only [div_eq_mul_inv, mul_inv, one_mul]
          ring
        _ ≤ D / P := div_le_div_of_nonneg_right hdivide hPr.le
    have hw := mul_le_mul_of_nonneg_right (progressionWeight_upper_one P r hP)
      (sq_nonneg (prefixSum a r))
    nlinarith
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (P - 1), ((prefixSum a r / r) ^ 2 + D / P) :=
      Finset.sum_le_sum hpoint
    _ = (∑ r ∈ Finset.Icc 1 (P - 1), (prefixSum a r / r) ^ 2) +
        ((P - 1 : ℕ) : ℝ) * (D / P) := by simp [Finset.sum_add_distrib]
    _ ≤ 4 * D + D := by
      apply add_le_add (finite_hardy_sq a (P - 1))
      have hle : ((P - 1 : ℕ) : ℝ) ≤ P := by exact_mod_cast Nat.sub_le P 1
      calc
        _ ≤ (P : ℝ) * (D / P) := mul_le_mul_of_nonneg_right hle (div_nonneg hD hPr.le)
        _ = D := mul_div_cancel₀ D hPr.ne'
    _ = _ := by ring

theorem fit_eq_supported_prefix (P x : ℕ) (c : ℕ → ℝ) (r : ℕ) (hr : r < P) :
    fit P x c r = prefixSum (fun n => if n ∈ freePositions P x then c n else 0) r := by
  classical
  unfold fit prefixSum
  simp_rw [step, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, freePositions, Finset.mem_Icc]
  omega

theorem fit_energy_le_five (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (fit P x c) ≤
      5 * ∑ n ∈ freePositions P x, c n ^ 2 := by
  classical
  let a : ℕ → ℝ := fun n => if n ∈ freePositions P x then c n else 0
  have he : energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (fit P x c) =
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (prefixSum a) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [fit_eq_supported_prefix P x c r (by have := Finset.mem_Icc.mp hr; omega)]
  have hs : (∑ n ∈ Finset.Icc 1 (P - 1), a n ^ 2) =
      ∑ n ∈ freePositions P x, c n ^ 2 := by
    simp only [a, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, freePositions, Finset.mem_Icc]
    omega
  rw [he]
  exact (progression_prefix_energy_le_five P hP a).trans_eq (by rw [hs])

/-- A finite and unconditional version of the stronger dispersion target. -/
theorem reuseEnergy_le_five_loss (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    reuseEnergy P x ≤ 5 * loss (freePositions P x) (fun n => Nat.gcd n P)
      (occurrenceCoefficients P x) u := by
  have ht := reuseEnergy_le_trial P x u
  have he : energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) =
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (fit P x (fun n => occurrenceCoefficients P x n - u (Nat.gcd n P))) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Pi.sub_apply]
    rw [← lift_synthesis P x u r (by have := Finset.mem_Icc.mp hr; omega)]
    simp [fit, sub_mul, Finset.sum_sub_distrib]
  rw [he] at ht
  exact ht.trans (fit_energy_le_five P x hP _)

def returnDispersion (P x : ℕ) : ℝ :=
  pooledDispersion (freePositions P x) (fun n => Nat.gcd n P) (occurrenceCoefficients P x)

/-- The trial values are explicit, shared across all shells, and globally optimal
for the coefficient L2 loss. They are not asserted to minimize Green energy. -/
theorem reuseEnergy_le_five_returnDispersion (P x : ℕ) (hP : 0 < P) :
    reuseEnergy P x ≤ 5 * returnDispersion P x := by
  have h := reuseEnergy_le_five_loss P x hP
    (atomMean (freePositions P x) (fun n => Nat.gcd n P) (occurrenceCoefficients P x))
  rw [(atomMean_minimizes (freePositions P x) (fun n => Nat.gcd n P)
    (occurrenceCoefficients P x) (fun _ => 0)).1] at h
  exact h

theorem atomEnergy_le_occurrence_add_dispersion (P x : ℕ) (hP : 0 < P) :
    atomEnergy P x ≤ occurrenceEnergy P x + 5 * returnDispersion P x := by
  rw [atomEnergy_eq_occurrence_add_reuse]
  exact add_le_add le_rfl (reuseEnergy_le_five_returnDispersion P x hP)

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
