import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Elementary bounds for Dirichlet exponentials

Source: the user-provided Pareto argument, conversation of 2026-11-13.
The proof strategy combines the odd-integer Euler-product estimate, a
local-to-global finite Euler-product criterion, and factorial norm bounds.
-/

open scoped BigOperators
open Filter

namespace RiemannResearch.NumberTheory.DirichletExponential

/-- A product over odd integers that majorizes the factors from all odd primes. -/
noncomputable def oddEulerProduct (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 2)

theorem oddEulerProduct_nonneg (r : ℕ) : 0 ≤ oddEulerProduct r := by
  exact Finset.prod_nonneg fun j _ => by positivity

/-- The elementary Wallis-type bound needed here; no estimate for the
distribution of the primes is required. -/
theorem oddEulerProduct_sq_le (r : ℕ) :
    oddEulerProduct r ^ 2 ≤ 2 * (r : ℝ) + 1 := by
  induction r with
  | zero => norm_num [oddEulerProduct]
  | succ r ih =>
      rw [oddEulerProduct, Finset.prod_range_succ, mul_pow]
      change oddEulerProduct r ^ 2 *
        ((2 * (r : ℝ) + 3) / (2 * (r : ℝ) + 2)) ^ 2 ≤ _
      calc
        oddEulerProduct r ^ 2 *
            ((2 * (r : ℝ) + 3) / (2 * (r : ℝ) + 2)) ^ 2
            ≤ (2 * (r : ℝ) + 1) *
              ((2 * (r : ℝ) + 3) / (2 * (r : ℝ) + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right ih (sq_nonneg _)
        _ ≤ 2 * ((r + 1 : ℕ) : ℝ) + 1 := by
          have hden : 0 < (2 * (r : ℝ) + 2) ^ 2 := by positivity
          rw [div_pow, ← mul_div_assoc]
          apply (div_le_iff₀ hden).2
          push_cast
          nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]

/-- A finite family of primes at most `2*r` has an elementary product bound.
The harmless factor `12` keeps the statement free of natural subtraction. -/
theorem small_prime_euler_product_sq_le (r : ℕ) (hr : 1 ≤ r) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ 2 * r) :
    (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 12 * (r : ℝ) := by
  classical
  let t : Finset ℕ := insert 2 ((Finset.range r).image (fun j => 2 * j + 3))
  have hsubset : s ⊆ t := by
    intro p hp
    obtain ⟨hpp, hpr⟩ := hs p hp
    rcases hpp.eq_two_or_odd with h2 | hodd
    · simp [t, h2]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨p / 2 - 1, Finset.mem_range.mpr ?_, ?_⟩ <;>
        have := hpp.two_le <;> omega
  have ht : ∀ p ∈ t, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · omega
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      omega
  have hnonneg : ∀ p ∈ s, 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).1.two_le
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmajor : (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤
      ∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsubset hnonneg
    intro p hp _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast ht p hp
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2
    linarith
  have hprod : (∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1)) =
      2 * oddEulerProduct r := by
    dsimp only [t]
    rw [Finset.prod_insert (by
      intro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      omega)]
    rw [Finset.prod_image (by
      intro a _ b _ hab
      dsimp only at hab
      omega)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    push_cast
    congr 1 <;> ring
  rw [hprod] at hmajor
  have hP : 0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_nonneg hnonneg
  have hsq := mul_self_le_mul_self hP hmajor
  have hodd := oddEulerProduct_sq_le r
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- Bounded finite Euler products give an unconditional summability criterion.
Only the prime-power series, rather than the global series, are assumed summable. -/
theorem summable_and_tsum_le_of_finite_euler_bound
    {f : ℕ → ℝ} {C : ℝ}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun a : ℕ => ‖f (p ^ a)‖))
    (hbound : ∀ N : ℕ,
      (∏ p ∈ N.primesBelow, ∑' a : ℕ, f (p ^ a)) ≤ C) :
    Summable f ∧ (∑' n : ℕ, f n) ≤ C := by
  classical
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ C := by
    intro N
    have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
    have hind : HasSum (N.smoothNumbers.indicator f)
        (∏ p ∈ N.primesBelow, ∑' a : ℕ, f (p ^ a)) :=
      hasSum_subtype_iff_indicator.mp heuler.2
    calc
      ∑ n ∈ Finset.range N, f n =
          ∑ n ∈ Finset.range N, N.smoothNumbers.indicator f n := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0, Set.indicator, hf0]
        · exact (Set.indicator_of_mem
            (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
              (Finset.mem_range.mp hn)) f).symm
      _ ≤ ∏ p ∈ N.primesBelow, ∑' a : ℕ, f (p ^ a) :=
        sum_le_hasSum _ (fun n _ => by
          by_cases hn : n ∈ N.smoothNumbers <;>
            simp [Set.indicator, hn, hf_nonneg]) hind
      _ ≤ C := hbound N
  exact ⟨summable_of_sum_range_le hf_nonneg hpartial,
    Real.tsum_le_of_sum_range_le hf_nonneg hpartial⟩

/-- A square root of an exponential-series term still forms a summable series. -/
theorem summable_sqrt_pow_div_factorial (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun n : ℕ => Real.sqrt (x ^ n / (n.factorial : ℝ))) := by
  have hden : (0 : ℝ) < (⌊x⌋₊ : ℝ) + 1 := by positivity
  have hratio : x / ((⌊x⌋₊ : ℝ) + 1) < 1 :=
    (div_lt_one hden).2 (Nat.lt_floor_add_one x)
  have hsqrt_ratio : Real.sqrt (x / ((⌊x⌋₊ : ℝ) + 1)) < 1 := by
    simpa using Real.sqrt_lt_sqrt (div_nonneg hx hden.le) hratio
  refine summable_of_ratio_norm_eventually_le hsqrt_ratio ?_
  filter_upwards [eventually_ge_atTop ⌊x⌋₊] with n hn
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (x ^ (n + 1) / ((n + 1).factorial : ℝ)) =
        Real.sqrt (x / ((n : ℝ) + 1)) *
          Real.sqrt (x ^ n / (n.factorial : ℝ)) := by
      rw [pow_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
        ← div_mul_div_comm, Real.sqrt_mul (div_nonneg hx (by positivity))]
    _ ≤ Real.sqrt (x / ((⌊x⌋₊ : ℝ) + 1)) *
        Real.sqrt (x ^ n / (n.factorial : ℝ)) := by
      gcongr

/-- A factorial squared-norm estimate gives absolute norm convergence of the
exponential series. Completeness of the vector space is not needed here. -/
theorem summable_norm_exp_terms_of_norm_sq_le_factorial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ n : ℕ, ‖u n‖ ^ 2 ≤ A ^ n * (n.factorial : ℝ)) :
    Summable (fun n : ℕ => ‖(1 / (n.factorial : ℝ)) • u n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    (summable_sqrt_pow_div_factorial A hA)
  intro n
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (n.factorial : ℝ))]
  apply Real.le_sqrt_of_sq_le
  calc
    (1 / (n.factorial : ℝ) * ‖u n‖) ^ 2 =
        ‖u n‖ ^ 2 / (n.factorial : ℝ) ^ 2 := by ring
    _ ≤ (A ^ n * (n.factorial : ℝ)) / (n.factorial : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hbound n) (sq_nonneg _)
    _ = A ^ n / (n.factorial : ℝ) := by field_simp

/-- A factorial squared-norm estimate gives an exponential sum in any complete
real normed space. This follows from the proved absolute norm convergence. -/
theorem summable_exp_terms_of_norm_sq_le_factorial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ n : ℕ, ‖u n‖ ^ 2 ≤ A ^ n * (n.factorial : ℝ)) :
    Summable (fun n : ℕ => (1 / (n.factorial : ℝ)) • u n) :=
  Summable.of_norm (summable_norm_exp_terms_of_norm_sq_le_factorial u hA hbound)

end RiemannResearch.NumberTheory.DirichletExponential
