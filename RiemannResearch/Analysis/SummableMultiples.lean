import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
/-!
# Inversion of absolutely summable sums over multiples

Source: user-provided RH_Two_Seed_Tail_Rigidity_Continuation_20260911,
Section 2.1. The proof uses finite exclusion by divisibility and dominated
convergence, avoiding rearrangement of a conditionally convergent Mobius series.
The dyadic and grouped-equation corollaries are used by Pareto signed tails.
-/
open scoped BigOperators
open Filter
namespace RiemannResearch.Analysis
noncomputable section
private def sieve (b : ℕ → ℝ) (s : Finset ℕ) (d n : ℕ) : ℝ :=
  if d ∣ n ∧ ∀ k ∈ s, ¬ k ∣ n then b n else 0

private theorem sieve_summable {b : ℕ → ℝ} (hb : Summable b)
    (s : Finset ℕ) (d : ℕ) : Summable (sieve b s d) := by
  apply hb.abs.of_norm_bounded
  intro n
  simp only [sieve, Real.norm_eq_abs]
  split_ifs <;> simp

private theorem sieve_sum_zero {b : ℕ → ℝ} (hb : Summable b)
    (hz : ∀ d : ℕ, (∑' n, if d ∣ n then b n else 0) = 0)
    (s : Finset ℕ) (d : ℕ) : (∑' n, sieve b s d n) = 0 := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa [sieve] using hz d
  | @insert k s hk ih =>
    have he : sieve b (insert k s) d =
        fun n => sieve b s d n - sieve b s (Nat.lcm d k) n := by
      funext n
      simp only [sieve, Finset.mem_insert, forall_eq_or_imp, Nat.lcm_dvd_iff]
      by_cases hd : d ∣ n <;> by_cases hkn : k ∣ n <;>
        by_cases hs : ∀ x ∈ s, ¬ x ∣ n <;> simp [hd, hkn, hs]
    rw [he, (sieve_summable hb s d).tsum_sub (sieve_summable hb s (Nat.lcm d k)),
      ih d, ih (Nat.lcm d k), sub_self]

/-- Absolutely summable sequences are determined by their sums over multiples. -/
theorem eq_zero_of_summable_multiples {b : ℕ → ℝ} (hb : Summable b)
    (hz : ∀ d : ℕ, (∑' n, if d ∣ n then b n else 0) = 0) :
    b = 0 := by
  classical
  funext m
  by_cases hm : m = 0
  · subst m
    simpa using hz 0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let s : ℕ → Finset ℕ := fun N => (Finset.range N).filter (m < ·)
  have hp : ∀ n, Tendsto (fun N => sieve b (s N) m n) atTop
      (nhds (if n = m then b m else 0)) := by
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max (m+2) (n+1))] with N hN
    by_cases hn : n = m
    · subst n
      have hs : ∀ k ∈ s N, ¬ k ∣ m := by
        intro k hk hd
        have hk' : m < k := (Finset.mem_filter.mp hk).2
        exact (not_le_of_gt hk') (Nat.le_of_dvd hmpos hd)
      simp only [sieve, dvd_refl, true_and, if_pos hs, ite_true]
    · have hfalse : ¬ (m ∣ n ∧ ∀ k ∈ s N, ¬ k ∣ n) := by
        rintro ⟨hd, hs⟩
        by_cases hn0 : n = 0
        · subst n
          have hk : m+1 ∈ s N := by
            simp only [s, Finset.mem_filter, Finset.mem_range]
            omega
          exact hs (m+1) hk (dvd_zero _)
        · have hmn : m < n := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd)
            (Ne.symm hn)
          have hk : n ∈ s N := by
            simp only [s, Finset.mem_filter, Finset.mem_range]
            omega
          exact hs n hk (dvd_refl n)
      simp [sieve, hfalse, hn]
  have hdom : ∀ᶠ N in atTop, ∀ n, ‖sieve b (s N) m n‖ ≤ |b n| := by
    apply Eventually.of_forall
    intro N n
    simp only [sieve, Real.norm_eq_abs]
    split_ifs <;> simp
  have ht := tendsto_tsum_of_dominated_convergence hb.abs hp hdom
  have hzero : (fun N => ∑' n, sieve b (s N) m n) = fun _ : ℕ => (0 : ℝ) :=
    funext (fun N => sieve_sum_zero hb hz (s N) m)
  rw [hzero] at ht
  have he := tendsto_nhds_unique tendsto_const_nhds ht
  simpa using he.symm
end
end RiemannResearch.Analysis

namespace RiemannResearch.Analysis
noncomputable section
theorem tsum_multiples_eq {A : ℕ → ℝ} {d : ℕ} (hd : 0 < d) :
    (∑' n, if d ∣ n then A n else 0) = ∑' j, A (d*j) := by
  have hi : Function.Injective (fun j : ℕ => d*j) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hd hij
  have he := hi.tsum_eq (f := fun n => if d ∣ n then A n else 0) (by
    intro n hn
    have hdv : d ∣ n := by
      by_contra h
      simp [Function.mem_support, h] at hn
    obtain ⟨j, hj⟩ := hdv
    exact ⟨j, hj.symm⟩)
  simpa only [dvd_mul_right, ite_true] using he.symm

theorem dyadic_scaling_of_summable_multiples_equations
    {A : ℕ → ℝ} (hA : Summable A) (hzero : A 0 = 0)
    (hQ : ∀ m : ℕ, 0 < m →
      (∑' j, A (m*j)) = 2 * ∑' j, A ((2*m)*j)) :
    ∀ n : ℕ, A (2*n) = A n / 2 := by
  have hi : Function.Injective (fun n : ℕ => 2*n) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hij
  have hs2 : Summable (fun n => A (2*n)) := hA.comp_injective hi
  have hB : Summable (fun n => A n - 2*A (2*n)) := hA.sub (hs2.mul_left 2)
  have hz : ∀ d : ℕ,
      (∑' n, if d ∣ n then A n - 2*A (2*n) else 0) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst d
      simp [hzero]
    have hdpos := Nat.pos_of_ne_zero hd
    rw [tsum_multiples_eq hdpos]
    have hid : Function.Injective (fun j : ℕ => d*j) := by
      intro i j hij
      exact Nat.eq_of_mul_eq_mul_left hdpos hij
    have hs : Summable (fun j => A (d*j)) := hA.comp_injective hid
    have hs' : Summable (fun j => 2*A (2*(d*j))) := (hs2.mul_left 2).comp_injective hid
    rw [hs.tsum_sub hs', tsum_mul_left]
    simp only [← Nat.mul_assoc]
    linarith [hQ d hdpos]
  have he := eq_zero_of_summable_multiples hB hz
  intro n
  have hn := congrFun he n
  change A n - 2*A (2*n) = 0 at hn
  linarith
end
end RiemannResearch.Analysis

namespace RiemannResearch.Analysis
noncomputable section
/-- The grouped binary tail equation is the multiples equation when the tail
is absolutely summable. No separation of a conditionally convergent sum is used. -/
theorem multiples_equation_of_summable_binary_grouped
    {A : ℕ → ℝ} (hA : Summable A) (hzero : A 0 = 0)
    (hQ : ∀ m : ℕ, 0 < m →
      (∑' j, (A (m*(2*j+1)) - A (m*(2*(j+1))))) = 0) :
    ∀ m : ℕ, 0 < m →
      (∑' j, A (m*j)) = 2 * ∑' j, A ((2*m)*j) := by
  intro m hm
  have hi : Function.Injective (fun j : ℕ => m*j) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hm hij
  have hs : Summable (fun j => A (m*j)) := hA.comp_injective hi
  have heven : Summable (fun j => A (m*(2*j))) :=
    hs.comp_injective (by intro i j hij; change 2*i=2*j at hij; omega)
  have hodd : Summable (fun j => A (m*(2*j+1))) :=
    hs.comp_injective (by intro i j hij; change 2*i+1=2*j+1 at hij; omega)
  have hshift : Summable (fun j => A (m*(2*(j+1)))) :=
    (summable_nat_add_iff 1).mpr heven
  have heq := heven.tsum_eq_zero_add
  simp only [Nat.mul_zero, hzero, zero_add] at heq
  have hq := hQ m hm
  rw [hodd.tsum_sub hshift, ← heq] at hq
  have hp := tsum_even_add_odd (f := fun j => A (m*j)) heven hodd
  have hre : (∑' j, A (m*(2*j))) = ∑' j, A ((2*m)*j) := by
    apply tsum_congr
    intro j
    congr 1
    ring
  rw [hre] at hp hq
  linarith

theorem dyadic_scaling_of_summable_binary_grouped
    {A : ℕ → ℝ} (hA : Summable A) (hzero : A 0 = 0)
    (hQ : ∀ m : ℕ, 0 < m →
      (∑' j, (A (m*(2*j+1)) - A (m*(2*(j+1))))) = 0) :
    ∀ n, A (2*n) = A n/2 :=
  dyadic_scaling_of_summable_multiples_equations hA hzero
    (multiples_equation_of_summable_binary_grouped hA hzero hQ)
end
end RiemannResearch.Analysis

/-! Finite divisor masks and signed blocks. These exact finite identities
support grouped Pareto tail equations without splitting divergent channels. -/
namespace RiemannResearch.Analysis
lemma sum_divisibility_mask_range (A : ℕ → ℝ) {m : ℕ} (hm : 0 < m) (N : ℕ) :
  (∑ n ∈ Finset.range (m*N+1), if m ∣ n then A n else 0) =
    ∑ j ∈ Finset.range (N+1), A (m*j) := by
  classical
  have hf : (Finset.range (m*N+1)).filter (fun n => m ∣ n) =
      (Finset.range (N+1)).image (fun j => m*j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, ⟨j, rfl⟩⟩
      refine ⟨j, ?_, rfl⟩
      by_contra hj
      have hj' : N+1 ≤ j := by omega
      have hp := Nat.mul_le_mul_left m hj'
      nlinarith
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, dvd_mul_right m j⟩
      have hp := Nat.mul_le_mul_left m (show j ≤ N by omega)
      omega
  rw [← Finset.sum_filter, hf, Finset.sum_image]
  intro i hi j hj hij
  exact Nat.eq_of_mul_eq_mul_left hm hij

lemma binary_block_sum (f : ℕ → ℝ) (hzero : f 0 = 0) (K : ℕ) :
    (∑ n ∈ Finset.range (2*K+1), f n) -
      2*(∑ j ∈ Finset.range (K+1), f (2*j)) =
    ∑ j ∈ Finset.range K, (f (2*j+1)-f (2*j+2)) := by
  induction K with
  | zero => simp [hzero]
  | succ K ih =>
    have h₁ := Finset.sum_range_succ f (2*K+2)
    have h₂ := Finset.sum_range_succ f (2*K+1)
    have h₃ := Finset.sum_range_succ (fun j => f (2*j)) (K+1)
    have h₄ := Finset.sum_range_succ (fun j => f (2*j+1)-f (2*j+2)) K
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] at *
    linarith

lemma triadic_block_sum (f : ℕ → ℝ) (hzero : f 0 = 0) (K : ℕ) :
    (∑ n ∈ Finset.range (3*K+1), f n) -
      3*(∑ j ∈ Finset.range (K+1), f (3*j)) =
    ∑ j ∈ Finset.range K, (f (3*j+1)+f (3*j+2)-2*f (3*j+3)) := by
  induction K with
  | zero => simp [hzero]
  | succ K ih =>
    have h₁ := Finset.sum_range_succ f (3*K+3)
    have h₂ := Finset.sum_range_succ f (3*K+2)
    have h₃ := Finset.sum_range_succ f (3*K+1)
    have h₄ := Finset.sum_range_succ (fun j => f (3*j)) (K+1)
    have h₅ := Finset.sum_range_succ
      (fun j => f (3*j+1)+f (3*j+2)-2*f (3*j+3)) K
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] at *
    linarith

lemma finite_signed_divisibility_sum (A : ℕ → ℝ) {m a : ℕ}
    (hm : 0 < m) (ha : 0 < a) (K : ℕ) :
    (∑ n ∈ Finset.range ((m*a)*K+1), A n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*a ∣ n then ((m*a : ℕ) : ℝ) else 0))) =
    (m : ℝ) * ((∑ j ∈ Finset.range (a*K+1), A (m*j)) -
      (a : ℝ)*(∑ j ∈ Finset.range (K+1), A (m*(a*j)))) := by
  have he : ∀ n, A n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*a ∣ n then ((m*a : ℕ) : ℝ) else 0)) =
      (m : ℝ) * ((if m ∣ n then A n else 0) -
        (a : ℝ)*(if m*a ∣ n then A n else 0)) := by
    intro n
    split_ifs <;> push_cast <;> ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 := sum_divisibility_mask_range A hm (a*K)
  have h2 := sum_divisibility_mask_range A (Nat.mul_pos hm ha) K
  simp only [← Nat.mul_assoc] at h1 ⊢
  rw [h1, h2]
end RiemannResearch.Analysis
