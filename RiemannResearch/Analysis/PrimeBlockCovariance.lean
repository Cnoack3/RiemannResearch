import RiemannResearch.Analysis.FiniteWeightedSchurPairing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform geometric prime-block covariance bound

Source: user-provided `V_vector_space_RH.pdf`, Section 4. For `r = p^(-1/2)`
this is the off-diagonal Poisson/Toeplitz block before multiplication by
`-log p / (2*pi)`. The bound is independent of the number of powers retained.
This finite quadratic theorem has no zero-equidistribution hypothesis and
does not exchange support and zero-height limits.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PrimeBlockCovariance
open RiemannResearch.Fourier

theorem positive_geometric_sum_le (s : Finset ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : ∀ n ∈ s, 0 < n) :
    (∑ n ∈ s, r ^ n) ≤ r / (1-r) := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have hsum : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hn
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a-1=b-1 → a=b := by
    intro a ha b hb hab
    have := hs a ha
    have := hs b hb
    omega
  calc
    _ = ∑ n ∈ s, r ^ ((n-1)+1) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      have := hs n hn
      omega
    _ = ∑ k ∈ s.image (fun n => n-1), r ^ (k+1) := by
      rw [Finset.sum_image hinj]
    _ = r * ∑ k ∈ s.image (fun n => n-1), r ^ k := by
      simp only [pow_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ r * ∑' k : ℕ, r ^ k := by
      apply mul_le_mul_of_nonneg_left _ hr
      exact Summable.sum_le_tsum _ (fun k _ => pow_nonneg hr k) hsum
    _ = r / (1-r) := by
      rw [tsum_geometric_of_norm_lt_one hn]
      ring

theorem injective_positive_geometric_sum_le {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hpos : ∀ i ∈ s, 0 < f i)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j) :
    (∑ i ∈ s, r ^ f i) ≤ r / (1-r) := by
  classical
  rw [← Finset.sum_image hinj]
  apply positive_geometric_sum_le _ r hr hr1
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  exact hpos i hi

/-- The zero-diagonal real Toeplitz kernel; the exponent is the natural distance. -/
def entry (r : ℝ) (i j : ℕ) : ℝ :=
  if i = j then 0 else r ^ ((i-j)+(j-i))

theorem entry_nonneg (r : ℝ) (hr : 0 ≤ r) (i j : ℕ) : 0 ≤ entry r i j := by
  unfold entry
  split <;> positivity

theorem entry_symm (r : ℝ) (i j : ℕ) : entry r i j = entry r j i := by
  simp [entry, eq_comm, Nat.add_comm]

theorem entry_split (r : ℝ) (i j : ℕ) :
    entry r i j = (if j < i then r^(i-j) else 0) +
      (if i < j then r^(j-i) else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · simp [entry, ne_of_lt h, not_lt_of_ge h.le, h, Nat.sub_eq_zero_of_le h.le]
  · subst j
    simp [entry]
  · simp [entry, (ne_of_lt h).symm, not_lt_of_ge h.le, h, Nat.sub_eq_zero_of_le h.le]

theorem row_sum_le (s : Finset ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (i : ℕ) :
    (∑ j ∈ s, entry r i j) ≤ 2*r/(1-r) := by
  have hleft : (∑ j ∈ s.filter (fun j => j < i), r^(i-j)) ≤ r/(1-r) := by
    apply injective_positive_geometric_sum_le _ (fun j => i-j) r hr hr1
    · intro j hj
      have := (Finset.mem_filter.mp hj).2
      omega
    · intro j hj k hk he
      have := (Finset.mem_filter.mp hj).2
      have := (Finset.mem_filter.mp hk).2
      omega
  have hright : (∑ j ∈ s.filter (fun j => i < j), r^(j-i)) ≤ r/(1-r) := by
    apply injective_positive_geometric_sum_le _ (fun j => j-i) r hr hr1
    · intro j hj
      have := (Finset.mem_filter.mp hj).2
      omega
    · intro j hj k hk he
      have := (Finset.mem_filter.mp hj).2
      have := (Finset.mem_filter.mp hk).2
      omega
  simp_rw [entry_split, Finset.sum_add_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  calc
    _ ≤ r/(1-r) + r/(1-r) := add_le_add hleft hright
    _ = _ := by ring

/-- Support-independent bound for the complete signed complex prime block. -/
theorem quadratic_bound (s : Finset ℕ) (a : ℕ → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖finiteGramErrorPairing s a (fun i j => (entry r i j : ℂ))‖ ≤
      (2*r/(1-r)) * ∑ i ∈ s, ‖a i‖^2 := by
  apply finiteGramErrorPairing_norm_le_weighted_schur s a
    (fun i j => (entry r i j : ℂ)) (fun _ => 1) (2*r/(1-r))
  · intro i hi
    norm_num
  · intro i hi j hj
    rw [entry_symm r i j]
  · intro i hi
    simpa only [mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (entry_nonneg r hr i _)] using row_sum_le s r hr hr1 i

theorem scalar_pairing (s : Finset ℕ) (a : ℕ → ℂ) (r : ℝ) (c : ℂ) :
    finiteGramErrorPairing s a (fun i j => c * (entry r i j : ℂ)) =
      c * finiteGramErrorPairing s a (fun i j => (entry r i j : ℂ)) := by
  unfold finiteGramErrorPairing
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact per-prime constant, retaining the negative arithmetic sign. -/
theorem prime_block_bound (s : Finset ℕ) (a : ℕ → ℂ)
    (p : ℝ) (hp : 1 < p) :
    ‖finiteGramErrorPairing s a (fun i j =>
      ((-Real.log p / (2*Real.pi) : ℝ) : ℂ) *
        (entry (1 / Real.sqrt p) i j : ℂ))‖ ≤
      (Real.log p / (Real.pi * (Real.sqrt p - 1))) *
        ∑ i ∈ s, ‖a i‖^2 := by
  have hp0 : 0 ≤ p := by linarith
  have hsq := Real.sq_sqrt hp0
  have hs0 := Real.sqrt_nonneg p
  have hs1 : 1 < Real.sqrt p := by nlinarith
  have hs : 0 < Real.sqrt p := by linarith
  have hr : 0 ≤ 1 / Real.sqrt p := by positivity
  have hr1 : 1 / Real.sqrt p < 1 := (div_lt_one hs).mpr hs1
  have hc : ‖((-Real.log p / (2*Real.pi) : ℝ) : ℂ)‖ =
      Real.log p / (2*Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_nonneg (Real.log_nonneg hp.le), abs_of_pos (by positivity : 0 < 2*Real.pi)]
  have hconst :
      (Real.log p / (2*Real.pi)) * (2*(1/Real.sqrt p)/(1-1/Real.sqrt p)) =
      Real.log p / (Real.pi * (Real.sqrt p-1)) := by
    field_simp [hs.ne', Real.pi_ne_zero, (sub_pos.mpr hs1).ne',
      (sub_pos.mpr hr1).ne']
  rw [scalar_pairing, norm_mul, hc]
  calc
    _ ≤ (Real.log p / (2*Real.pi)) *
        ((2*(1/Real.sqrt p)/(1-1/Real.sqrt p)) * ∑ i ∈ s, ‖a i‖^2) :=
      mul_le_mul_of_nonneg_left (quadratic_bound s a _ hr hr1)
        (div_nonneg (Real.log_nonneg hp.le) (by positivity))
    _ = _ := by rw [← mul_assoc, hconst]

/-- The logarithmic secant slope decreases on the positive half-line after 1.
The proof uses the elementary bound log x ≤ x-1, twice. -/
theorem log_div_sub_one_antitone (a t : ℝ) (ha : 1 < a) (hat : a ≤ t) :
    Real.log t / (t-1) ≤ Real.log a / (a-1) := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have ha1 : 0 < a-1 := by linarith
  have ht1 : 0 < t-1 := by linarith
  have h1 : (Real.log t - Real.log a) * a ≤ t-a := by
    have hh := Real.log_le_sub_one_of_pos (div_pos ht0 ha0)
    rw [Real.log_div ht0.ne' ha0.ne'] at hh
    have hh := mul_le_mul_of_nonneg_right hh ha0.le
    have hid : (t/a-1)*a = t-a := by field_simp
    rwa [hid] at hh
  have h2 : a-1 ≤ Real.log a * a := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr ha0)
    rw [Real.log_inv] at hh
    have hh := mul_le_mul_of_nonneg_right hh ha0.le
    have hid : (a⁻¹-1)*a = 1-a := by
      rw [sub_mul, inv_mul_cancel₀ ha0.ne', one_mul]
    rw [hid] at hh
    nlinarith
  apply (div_le_div_iff₀ ht1 ha1).mpr
  apply (mul_le_mul_iff_right₀ ha0).mp
  nlinarith [mul_le_mul_of_nonneg_right h1 ha1.le,
    mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hat)]

theorem prime_constant_le_two (p : ℝ) (hp : 2 ≤ p) :
    Real.log p / (Real.pi * (Real.sqrt p-1)) ≤
      Real.log 2 / (Real.pi * (Real.sqrt 2-1)) := by
  have hp0 : 0 ≤ p := by linarith
  have h2 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have ht : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
  have hp1 : 1 < Real.sqrt p := lt_of_lt_of_le h2 ht
  have hlogp : Real.log p = 2*Real.log (Real.sqrt p) := by
    conv_lhs => rw [← Real.sq_sqrt hp0]
    rw [Real.log_pow]
    norm_num
  have hlog2 : Real.log 2 = 2*Real.log (Real.sqrt 2) := by
    conv_lhs => rw [← Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.log_pow]
    norm_num
  have h := mul_le_mul_of_nonneg_left
    (log_div_sub_one_antitone (Real.sqrt 2) (Real.sqrt p) h2 ht)
    (by positivity : 0 ≤ 2/Real.pi)
  rw [hlogp, hlog2]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using h

/-- The paper's universal constant, valid for every finite exponent subset. -/
theorem prime_block_uniform_bound (s : Finset ℕ) (a : ℕ → ℂ)
    (p : ℝ) (hp : 2 ≤ p) :
    ‖finiteGramErrorPairing s a (fun i j =>
      ((-Real.log p / (2*Real.pi) : ℝ) : ℂ) *
        (entry (1 / Real.sqrt p) i j : ℂ))‖ ≤
      (Real.log 2 / (Real.pi * (Real.sqrt 2 - 1))) *
        ∑ i ∈ s, ‖a i‖^2 :=
  (prime_block_bound s a p (by linarith)).trans
    (mul_le_mul_of_nonneg_right (prime_constant_le_two p hp)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Complete signed finite prime-sector form, with every intra-prime cross term
and one uniform constant independent of all support sizes. -/
theorem finite_prime_blocks_bound (P : Finset ℕ) (s : ℕ → Finset ℕ)
    (a : ℕ → ℕ → ℂ) (hp : ∀ p ∈ P, Nat.Prime p) :
    ‖∑ p ∈ P, finiteGramErrorPairing (s p) (a p) (fun i j =>
      ((-Real.log (p:ℝ) / (2*Real.pi) : ℝ) : ℂ) *
        (entry (1 / Real.sqrt (p:ℝ)) i j : ℂ))‖ ≤
      (Real.log 2 / (Real.pi * (Real.sqrt 2 - 1))) *
        ∑ p ∈ P, ∑ i ∈ s p, ‖a p i‖^2 := by
  calc
    _ ≤ ∑ p ∈ P, ‖finiteGramErrorPairing (s p) (a p) (fun i j =>
      ((-Real.log (p:ℝ) / (2*Real.pi) : ℝ) : ℂ) *
        (entry (1 / Real.sqrt (p:ℝ)) i j : ℂ))‖ := norm_sum_le P _
    _ ≤ ∑ p ∈ P, (Real.log 2 / (Real.pi * (Real.sqrt 2 - 1))) *
        ∑ i ∈ s p, ‖a p i‖^2 := by
      apply Finset.sum_le_sum
      intro p hpm
      apply prime_block_uniform_bound
      exact_mod_cast (hp p hpm).two_le
    _ = _ := by rw [Finset.mul_sum]

/-- The finite form is Hermitian, so its diagonal value is real. -/
theorem pairing_selfAdjoint (s : Finset ℕ) (a : ℕ → ℂ) (r : ℝ) :
    star (finiteGramErrorPairing s a (fun i j => (entry r i j : ℂ))) =
      finiteGramErrorPairing s a (fun i j => (entry r i j : ℂ)) := by
  unfold finiteGramErrorPairing
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [entry_symm r j i]
  simp [mul_comm, mul_left_comm, mul_assoc]

end RiemannResearch.Analysis.PrimeBlockCovariance
