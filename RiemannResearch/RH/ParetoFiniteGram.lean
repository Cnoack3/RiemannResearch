import RiemannResearch.RH.ParetoCovariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact finite Pareto Gram matrices and a valid coefficient bound

Source: repair of the covariance suggestion in the user-provided
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §8.
All identities use the full infinite Pareto inner product. The coefficient
bound below is the ordinary finite Cauchy--Schwarz bound, with the total
diagonal energy outside the coefficient sum. It does not assert the false
uniform bound by the sum of coefficient-weighted diagonal energies.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem bounded_finsetCombination {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {f : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ i k, |f i k| ≤ B i) :
    ∀ k, |∑ i ∈ s, a i * f i k| ≤ ∑ i ∈ s, |a i| * B i := by
  intro k
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact bounded_const_mul (hf i) (a i) k

theorem paretoInner_finsetSum_left {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → ℝ} {g : ℕ → ℝ} {B : ι → ℝ} {D : ℝ}
    (hf : ∀ i k, |f i k| ≤ B i) (hg : ∀ k, |g k| ≤ D) :
    paretoInner (fun k => ∑ i ∈ s, f i k) g =
      ∑ i ∈ s, paretoInner (f i) g := by
  unfold paretoInner
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ =>
    weighted_summable_of_bounded (bounded_product (hf i) hg))

theorem paretoInner_finsetSum_right {ι : Type*} (s : Finset ι)
    {f : ℕ → ℝ} {g : ι → ℕ → ℝ} {B : ℝ} {D : ι → ℝ}
    (hf : ∀ k, |f k| ≤ B) (hg : ∀ i k, |g i k| ≤ D i) :
    paretoInner f (fun k => ∑ i ∈ s, g i k) =
      ∑ i ∈ s, paretoInner f (g i) := by
  rw [paretoInner_comm, paretoInner_finsetSum_left s hg hf]
  exact Finset.sum_congr rfl (fun i _ => paretoInner_comm (g i) f)

/-- Every signed cross term is retained exactly. -/
theorem paretoInner_finsetCombination {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) {f : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ i k, |f i k| ≤ B i) :
    paretoInner (fun k => ∑ i ∈ s, a i * f i k)
      (fun k => ∑ i ∈ s, a i * f i k) =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * paretoInner (f i) (f j) := by
  have hfa := fun i => bounded_const_mul (hf i) (a i)
  rw [paretoInner_finsetSum_left s hfa (bounded_finsetCombination s a hf)]
  apply Finset.sum_congr rfl
  intro i _
  rw [paretoInner_finsetSum_right s (hfa i) hfa]
  apply Finset.sum_congr rfl
  intro j _
  rw [paretoInner_const_mul_left (hf i) (hfa j),
    paretoInner_const_mul_right (hf i) (hf j)]
  ring

/-- Orthogonality gives an equality with constant one, for the transformed
directions and their transformed coefficients. -/
theorem paretoInner_finsetCombination_of_orthogonal {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) {f : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ i k, |f i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (f i) (f j) = 0) :
    paretoInner (fun k => ∑ i ∈ s, a i * f i k)
      (fun k => ∑ i ∈ s, a i * f i k) =
      ∑ i ∈ s, (a i)^2 * paretoInner (f i) (f i) := by
  classical
  rw [paretoInner_finsetCombination s a hf]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · ring
  · intro j hj hji
    rw [ho i hi j hj (Ne.symm hji), mul_zero]
  · exact fun h => (h hi).elim

/-- A valid coefficient estimate: the total diagonal energy multiplies the
unweighted coefficient square sum. Cross covariances are bounded only after
the exact Gram identity has been established. -/
theorem paretoInner_finsetCombination_le_total_energy {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) {f : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ i k, |f i k| ≤ B i) :
    paretoInner (fun k => ∑ i ∈ s, a i * f i k)
      (fun k => ∑ i ∈ s, a i * f i k) ≤
      (∑ i ∈ s, (a i)^2) * ∑ i ∈ s, paretoInner (f i) (f i) := by
  have hs := weighted_summable_of_bounded
    (bounded_product (bounded_finsetCombination s a hf)
      (bounded_finsetCombination s a hf))
  have ht : Summable (fun k => ∑ i ∈ s,
      positiveWeight k * (f i k * f i k)) := by
    classical
    clear hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (weighted_summable_of_bounded (bounded_product (hf i) (hf i))).add ih
  calc
    _ ≤ ∑' k, (∑ i ∈ s, (a i)^2) *
        (∑ i ∈ s, positiveWeight k * (f i k * f i k)) := by
      apply Summable.tsum_le_tsum _ hs (ht.mul_left _)
      intro k
      have h := mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sq_le_sq_mul_sq s a (fun i => f i k))
        (positiveWeight_nonneg k)
      simpa only [pow_two, Finset.mul_sum, mul_left_comm] using h
    _ = _ := by
      rw [ht.tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum (fun i _ =>
        weighted_summable_of_bounded (bounded_product (hf i) (hf i)))

/-- Summable diagonal energies provide a single constant for square-summable
coefficients. This is not the refuted normalized Bessel statement. -/
theorem paretoInner_finsetCombination_le_tsum_energy {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) {f : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ i k, |f i k| ≤ B i)
    (he : Summable (fun i => paretoInner (f i) (f i))) :
    paretoInner (fun k => ∑ i ∈ s, a i * f i k)
      (fun k => ∑ i ∈ s, a i * f i k) ≤
      (∑ i ∈ s, (a i)^2) * ∑' i, paretoInner (f i) (f i) := by
  apply (paretoInner_finsetCombination_le_total_energy s a hf).trans
  exact mul_le_mul_of_nonneg_left
    (he.sum_le_tsum s (fun i _ => paretoInner_self_nonneg (f i)))
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))

end
end RiemannResearch.RH.Pareto
