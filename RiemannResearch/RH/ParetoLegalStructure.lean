/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdDilationAlgebra

/-!
# Periodic reflection structure of finite legal Pareto witnesses

Source: Christian Noack, September 11, 2026, conversation on the structure of
the two-seed family and its weighted CRT residue representation.

Every finite legal combination of positive seeds has a positive common period.
At every multiple of that period its reflection sum is constant. This gives an
unconditional obstruction to closure under pointwise multiplication, even if all
positive seeds are admitted. These finite identities make no assertion about
continuity of reflection in the Pareto Hilbert norm or about RH.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A complementary pair of residues immediately before a multiple of the modulus. -/
theorem residue_reflection_sum {a Q n : ℕ} (ha : 0 < a) (hQ : a ∣ Q)
    (hn : n < Q) :
    residue a n + residue a (Q - 1 - n) = ((a - 1 : ℕ) : ℝ) := by
  have hs : n + (Q - 1 - n) + 1 = Q := by omega
  have hd : a ∣ n % a + (Q - 1 - n) % a + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    calc
      (n % a + (Q - 1 - n) % a + 1) % a =
          (n + (Q - 1 - n) + 1) % a := by simp [Nat.add_mod]
      _ = 0 := by rw [hs, Nat.mod_eq_zero_of_dvd hQ]
  have hr := Nat.mod_lt n ha
  have ht := Nat.mod_lt (Q - 1 - n) ha
  obtain ⟨k, hk⟩ := hd
  have hklt : k < 2 := by
    apply (Nat.mul_lt_mul_left ha).mp
    rw [← hk]
    omega
  have hkne : k ≠ 0 := by
    intro he
    simp [he] at hk
  have hke : k = 1 := by omega
  have hsum : n % a + (Q - 1 - n) % a + 1 = a := by
    simpa [hke] using hk
  have he : n % a + (Q - 1 - n) % a = a - 1 := by omega
  simpa only [residue, Nat.cast_add] using congrArg (fun k : ℕ => (k : ℝ)) he

/-- Residue reflection stated using the terminal value of the period. -/
theorem residue_reflection {a Q n : ℕ} (ha : 0 < a) (hQ : a ∣ Q)
    (hn : n < Q) :
    residue a n + residue a (Q - 1 - n) = residue a (Q - 1) := by
  have hzero := residue_reflection_sum ha hQ (show 0 < Q by omega)
  have hpair := residue_reflection_sum ha hQ hn
  simpa [residue] using hpair.trans (by simpa [residue] using hzero.symm)

/-- Every multiple of the modulus is a period of its residue function. -/
theorem residue_period_of_dvd {a Q : ℕ} (hQ : a ∣ Q) (n : ℕ) :
    residue a (n + Q) = residue a n := by
  simp [residue, Nat.add_mod, Nat.mod_eq_zero_of_dvd hQ]

/-- A positive common period, together with reflection at all its multiples. -/
def HasLegalReflectionPeriod (f : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ Q : ℕ, d ∣ Q →
    (∀ n : ℕ, f (n + Q) = f n) ∧
    (∀ n : ℕ, n < Q → f n + f (Q - 1 - n) = f (Q - 1))

/-- The exact generator reflection follows from the residue cocycle. -/
theorem dilation_residue_hasLegalReflectionPeriod {a m : ℕ}
    (ha : 0 < a) (hm : 0 < m) :
    HasLegalReflectionPeriod (dilation m (residue a)) := by
  refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
  intro Q hQ
  have hmQ : m ∣ Q := dvd_trans (dvd_mul_right m a) hQ
  constructor
  · intro n
    rw [residue_mul_floor, residue_mul_floor,
      residue_period_of_dvd hQ, residue_period_of_dvd hmQ]
  · intro n hn
    rw [residue_mul_floor, residue_mul_floor, residue_mul_floor]
    have hma := residue_reflection (Nat.mul_pos hm ha) hQ hn
    have hmr := residue_reflection hm hmQ hn
    linarith

/-- The reflection invariant is closed under addition, using a common multiple. -/
theorem HasLegalReflectionPeriod.add {f g : ℕ → ℝ}
    (hf : HasLegalReflectionPeriod f) (hg : HasLegalReflectionPeriod g) :
    HasLegalReflectionPeriod (f + g) := by
  obtain ⟨d, hd, hf⟩ := hf
  obtain ⟨e, he, hg⟩ := hg
  refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
  intro Q hQ
  obtain ⟨hfp, hfr⟩ := hf Q (dvd_trans (dvd_mul_right d e) hQ)
  obtain ⟨hgp, hgr⟩ := hg Q (dvd_trans (dvd_mul_left e d) hQ)
  constructor
  · intro n
    simp only [Pi.add_apply, hfp, hgp]
  · intro n hn
    simp only [Pi.add_apply]
    linarith [hfr n hn, hgr n hn]

/-- The reflection invariant is closed under scalar multiplication. -/
theorem HasLegalReflectionPeriod.smul {f : ℕ → ℝ}
    (hf : HasLegalReflectionPeriod f) (c : ℝ) :
    HasLegalReflectionPeriod (c • f) := by
  obtain ⟨d, hd, hf⟩ := hf
  refine ⟨d, hd, ?_⟩
  intro Q hQ
  obtain ⟨hp, hr⟩ := hf Q hQ
  constructor
  · intro n
    simp only [Pi.smul_apply, hp]
  · intro n hn
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_add, hr n hn]

/-- Every legal finite combination of positive seeds has the reflection invariant. -/
theorem legalSeedSpan_hasLegalReflectionPeriod (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    HasLegalReflectionPeriod f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, m, hm, rfl⟩ := hf
    exact dilation_residue_hasLegalReflectionPeriod (hA a ha) hm
  | zero =>
    exact ⟨1, by norm_num, by intros; constructor <;> intros <;> simp⟩
  | add f g hf hg ihf ihg => exact ihf.add ihg
  | smul c f hf ih => exact ih.smul c

/-- There is an actual positive integer zero of every finite legal witness. -/
theorem legalSeedSpan_exists_positive_zero (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    ∃ Q : ℕ, 0 < Q ∧ f Q = 0 := by
  obtain ⟨d, hd, hperiod⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA hf
  refine ⟨d, hd, ?_⟩
  have hp := (hperiod d (dvd_refl d)).1 0
  simpa [legalSeedSpan_zero_value A hf] using hp

/-- The literal constant sequence is excluded already by the zero coordinate. -/
theorem one_not_mem_legalSeedSpan (A : Set ℕ) :
    (1 : ℕ → ℝ) ∉ legalSeedSpan A := by
  intro h
  have hz := legalSeedSpan_zero_value A h
  norm_num at hz

/-- The positive-index constant is excluded by a positive zero, independently of anchoring. -/
theorem legalSeedSpan_not_one_on_positive (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    ¬ ∀ n : ℕ, 0 < n → f n = 1 := by
  obtain ⟨Q, hQ, hz⟩ := legalSeedSpan_exists_positive_zero A hA hf
  intro hone
  have := hone Q hQ
  linarith

/-- Squaring the third residue violates reflection, even with every positive seed available. -/
theorem residue_three_sq_not_mem_legalSeedSpan (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    (fun n : ℕ => (residue 3 n) ^ 2) ∉ legalSeedSpan A := by
  intro h
  obtain ⟨d, hd, href⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA h
  have hr := (href (3 * d) (dvd_mul_left d 3)).2 1 (by omega)
  have hlast : (3 * d - 1) % 3 = 2 := by omega
  have hprev : (3 * d - 1 - 1) % 3 = 1 := by omega
  norm_num [residue, hlast, hprev] at hr

/-- The seed used in the explicit counterexample is itself legal. -/
theorem residue_three_mem_twoSeedSpan :
    residue 3 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  have h := dilation_generator_mem ({2, 3} : Set ℕ)
    (a := 3) (m := 1) (by simp) (by norm_num)
  simpa [dilation_one] using h

/-- The two-seed vector space is not closed under pointwise multiplication. -/
theorem twoSeedSpan_not_mul_closed :
    ¬ ∀ f ∈ legalSeedSpan ({2, 3} : Set ℕ),
      ∀ g ∈ legalSeedSpan ({2, 3} : Set ℕ),
        f * g ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  intro h
  have hs := h (residue 3) residue_three_mem_twoSeedSpan
    (residue 3) residue_three_mem_twoSeedSpan
  have hpos : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> norm_num
  apply residue_three_sq_not_mem_legalSeedSpan ({2, 3} : Set ℕ) hpos
  have he : (residue 3 * residue 3 : ℕ → ℝ) =
      (fun n : ℕ => (residue 3 n) ^ 2) := by
    funext n
    simp [pow_two]
  rw [he] at hs
  exact hs



/-- A sequence with period d is determined by its representatives modulo d. -/
theorem legalPeriodic_eq_mod {f : ℕ → ℝ} {d : ℕ}
    (hp : ∀ n : ℕ, f (n + d) = f n) (n : ℕ) : f n = f (n % d) := by
  have hmul (k : ℕ) : f (n % d + d * k) = f (n % d) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]
  calc
    f n = f (n % d + d * (n / d)) := by rw [Nat.mod_add_div]
    _ = f (n % d) := hmul (n / d)

/-- Squaring preserves legality exactly for witnesses with binary range {0,c}. -/
theorem legalSeedSpan_square_mem_iff_binary_range (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    (fun n : ℕ => (f n) ^ 2) ∈ legalSeedSpan A ↔
      ∃ c : ℝ, ∀ n : ℕ, f n = 0 ∨ f n = c := by
  constructor
  · intro hs
    obtain ⟨d, hd, hfd⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA hf
    obtain ⟨e, he, hse⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA hs
    let Q := d * e
    have hQ : 0 < Q := Nat.mul_pos hd he
    obtain ⟨hp, hr⟩ := hfd Q (dvd_mul_right d e)
    have hsq := (hse Q (dvd_mul_left e d)).2
    refine ⟨f (Q - 1), ?_⟩
    intro n
    rw [legalPeriodic_eq_mod hp n]
    have hn : n % Q < Q := Nat.mod_lt n hQ
    have hrn := hr (n % Q) hn
    have hsn := hsq (n % Q) hn
    change (f (n % Q)) ^ 2 + (f (Q - 1 - n % Q)) ^ 2 =
      (f (Q - 1)) ^ 2 at hsn
    have hy : f (Q - 1 - n % Q) = f (Q - 1) - f (n % Q) := by
      linarith
    rw [hy] at hsn
    have hz : f (n % Q) * (f (n % Q) - f (Q - 1)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hz with hzero | heq
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp heq)
  · rintro ⟨c, hc⟩
    have heq : (fun n : ℕ => (f n) ^ 2) = c • f := by
      funext n
      rcases hc n with hn | hn <;> simp [Pi.smul_apply, smul_eq_mul, hn, pow_two]
    rw [heq]
    exact (legalSeedSpan A).smul_mem c hf


end
end RiemannResearch.RH.Pareto
