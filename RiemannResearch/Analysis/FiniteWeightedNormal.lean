import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

/-!
# Finite weighted least-squares normal solutions without rank assumptions
This transports the repository's feasible Hilbert Gram theorem to arbitrary
finite nonnegative weighted data. Zero weights and dependent columns are
permitted. Intended provider: exact-head upper-divisor floor regression.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedNormal

theorem exists_normal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : κ → ι → ℝ) (y : ι → ℝ) :
    ∃ c : κ → ℝ, ∀ j,
      (∑ i, w i * a j i * (y i - ∑ k, c k * a k i)) = 0 := by
  let e (f : ι → ℝ) : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => Real.sqrt (w i) * f i)
  have hp (f g : ι → ℝ) :
      inner ℝ (e f) (e g) = ∑ i, w i * f i * g i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change (Real.sqrt (w i) * g i) * (Real.sqrt (w i) * f i) = _
    calc
      _ = (Real.sqrt (w i)) ^ 2 * f i * g i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]
  obtain ⟨c,hc⟩ := FiniteFeasibleGramRepair.exists_normal_of_feasible
    (fun j => e (a j)) (fun j => inner ℝ (e (a j)) (e y)) (e y) (fun _ => rfl)
  refine ⟨c,?_⟩
  intro j
  have hs : inner ℝ (e (a j))
      (Fintype.linearCombination ℝ (fun k => e (a k)) c) =
      ∑ i, w i * a j i * (∑ k, c k * a k i) := by
    rw [Fintype.linearCombination_apply, inner_sum]
    simp_rw [inner_smul_right, hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hj := hc j
  rw [hs,hp] at hj
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hj.symm

theorem exists_normal_finset {ι κ : Type*}
    (s : Finset ι) (D : Finset κ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (a : κ → ι → ℝ) (y : ι → ℝ) :
    ∃ c : κ → ℝ, (∀ k, k ∉ D → c k = 0) ∧
      ∀ j ∈ D, (∑ i ∈ s, w i * a j i * (y i - ∑ k ∈ D, c k * a k i)) = 0 := by
  classical
  obtain ⟨u,hu⟩ := exists_normal (fun i : s => w i) (fun i => hw i i.property)
    (fun k : D => fun i : s => a k i) (fun i : s => y i)
  let c : κ → ℝ := fun k => if hk : k ∈ D then u ⟨k,hk⟩ else 0
  have hc (k : D) : c k = u k := by simp [c,k.property]
  have hsum (i : ι) : (∑ k ∈ D, c k * a k i) = ∑ k : D, u k * a k i := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hc]
  refine ⟨c,?_,?_⟩
  · intro k hk
    simp [c,hk]
  · intro j hj
    have h := hu ⟨j,hj⟩
    simp_rw [← hsum] at h
    exact (Finset.sum_coe_sort s (fun i =>
      w i * a j i * (y i - ∑ k ∈ D, c k * a k i))).symm.trans h

end RiemannResearch.Analysis.FiniteWeightedNormal
