import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The inverse-square probability law on positive integers

Source: user-provided inverse-square reindexing argument. The normalizing
constant is identified with Mathlib's Riemann zeta function at two.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RiemannResearch.RH.ZetaTwoProbability

def zetaTwo : ℝ := ∑' k : ℕ+, 1 / (k : ℝ) ^ 2

theorem inverseSquare_summable : Summable (fun k : ℕ+ => 1 / (k : ℝ) ^ 2) := by
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).subtype _

theorem zetaTwo_pos : 0 < zetaTwo := by
  exact inverseSquare_summable.tsum_pos (fun _ => by positivity) 1 (by norm_num)

theorem zetaTwo_eq_nat_sum : zetaTwo = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
  unfold zetaTwo
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / (n : ℝ)^2)]
  have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  simpa using h.tsum_eq_zero_add.symm

theorem zetaTwo_eq_riemannZeta : (zetaTwo : ℂ) = riemannZeta 2 := by
  rw [zetaTwo_eq_nat_sum, Complex.ofReal_tsum]
  have hz := zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < (2 : ℕ))
  norm_num only [Nat.cast_ofNat] at hz
  rw [hz]
  congr 1
  funext n
  push_cast
  rfl

private theorem weight_tsum :
    (∑' k : ℕ+, ENNReal.ofReal (1 / (k : ℝ) ^ 2)) = ENNReal.ofReal zetaTwo :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) inverseSquare_summable).symm

def pmf : PMF ℕ+ := PMF.normalize (fun k => ENNReal.ofReal (1 / (k : ℝ)^2))
  (by rw [weight_tsum]; exact ne_of_gt (ENNReal.ofReal_pos.mpr zetaTwo_pos))
  (by rw [weight_tsum]; exact ENNReal.ofReal_ne_top)

instance instMeasurableSpacePNat : MeasurableSpace ℕ+ := ⊤

instance instMeasurableSingletonClassPNat : MeasurableSingletonClass ℕ+ := ⟨fun _ => trivial⟩

def Q : Measure ℕ+ := pmf.toMeasure

instance : IsProbabilityMeasure Q := PMF.toMeasure.isProbabilityMeasure pmf

theorem pmf_apply (k : ℕ+) : pmf k = ENNReal.ofReal (1 / (zetaTwo * (k : ℝ)^2)) := by
  simp only [pmf, PMF.normalize_apply, weight_tsum]
  rw [← ENNReal.ofReal_inv_of_pos zetaTwo_pos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem measure_singleton (k : ℕ+) :
    Q {k} = ENNReal.ofReal (1 / (zetaTwo * (k : ℝ)^2)) := by
  rw [Q, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pmf_apply]

private def mulPositive (m : ℕ) (hm : 0 < m) (k : ℕ+) : ℕ+ :=
  ⟨m * k, Nat.mul_pos hm k.pos⟩

private theorem pmf_mul (m : ℕ) (hm : 0 < m) (k : ℕ+) :
    pmf (mulPositive m hm k) = ENNReal.ofReal (1 / (m : ℝ)^2) * pmf k := by
  rw [pmf_apply, pmf_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [mulPositive, PNat.mk_coe, Nat.cast_mul, mul_pow, one_div, mul_inv]
  ring

theorem measure_dvd (m : ℕ) (hm : 0 < m) :
    Q {k : ℕ+ | m ∣ (k : ℕ)} = ENNReal.ofReal (1 / (m : ℝ)^2) := by
  classical
  rw [Q, PMF.toMeasure_apply_eq_tsum]
  have hreindex :
      (∑' k : ℕ+, ({k : ℕ+ | m ∣ (k : ℕ)} : Set ℕ+).indicator pmf k) =
      ∑' k : ℕ+, pmf (mulPositive m hm k) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun k : Function.support (fun k : ℕ+ => pmf (mulPositive m hm k)) =>
        mulPositive m hm k.val)
    · intro a b hab
      apply Subtype.ext
      apply PNat.coe_injective
      exact Nat.eq_of_mul_eq_mul_left hm (congrArg (fun x : ℕ+ => (x : ℕ)) hab)
    · intro k hk
      change ({k : ℕ+ | m ∣ (k : ℕ)} : Set ℕ+).indicator (fun j => pmf j) k ≠ 0 at hk
      have hd : m ∣ (k : ℕ) := by
        by_contra h
        apply hk
        exact Set.indicator_of_notMem (s := {j : ℕ+ | m ∣ (j : ℕ)}) h (fun j => pmf j)
      obtain ⟨a, ha⟩ := hd
      have ha0 : 0 < a := by
        by_contra h
        have : a = 0 := Nat.eq_zero_of_not_pos h
        simp [this] at ha
      let a' : ℕ+ := ⟨a, ha0⟩
      have heq : mulPositive m hm a' = k := PNat.coe_injective ha.symm
      refine ⟨⟨a', ?_⟩, heq⟩
      change pmf (mulPositive m hm a') ≠ 0
      rw [heq]
      simpa only [Set.indicator_of_mem (show k ∈ {j : ℕ+ | m ∣ (j : ℕ)} from ⟨a, ha⟩)] using hk
    · intro k
      apply Set.indicator_of_mem
      exact dvd_mul_right m (k.val : ℕ)
  rw [hreindex]
  simp_rw [pmf_mul m hm]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

end RiemannResearch.RH.ZetaTwoProbability
