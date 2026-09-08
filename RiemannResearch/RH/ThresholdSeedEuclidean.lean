import RiemannResearch.RH.ThresholdDilationAlgebra

/-!
# Exact Euclidean reduction of power seeds

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 4, finite-seed classification. This module gives an elementary
Euclidean proof of the algebraic common-base reduction, avoiding a polynomial
Bézout argument. Every positive integer dilation remains legal.

The module does not assert the analytic two-independent-seed density theorem
or any Riemann-hypothesis criterion. The existence of a common integer base
for a multiplicatively dependent family is a separate arithmetic statement.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A seed itself is a legal generator with dilation parameter one. -/
theorem residue_mem_legalSeedSpan (A : Set ℕ) {a : ℕ} (ha : a ∈ A) :
    residue a ∈ legalSeedSpan A := by
  simpa only [dilation_one] using dilation_generator_mem A ha Nat.zero_lt_one

/-- Synthesizing the seeds suffices to synthesize all their integer dilations. -/
theorem legalSeedSpan_le_of_residue_mem {A B : Set ℕ}
    (h : ∀ a ∈ A, residue a ∈ legalSeedSpan B) :
    legalSeedSpan A ≤ legalSeedSpan B := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, ha, m, hm, rfl⟩
  exact legalSeedSpan_dilation B (h a ha) m hm

/-- Power telescoping applies to any synthesized seed, not only an original one. -/
theorem residue_power_mem_of_mem (A : Set ℕ) {b : ℕ} (hb : 0 < b)
    (h : residue b ∈ legalSeedSpan A) (e : ℕ) :
    residue (b ^ e) ∈ legalSeedSpan A := by
  have he : residue (b ^ e) =
      ∑ j ∈ Finset.range e, dilation (b ^ j) (residue b) := by
    funext k
    simpa using residue_pow_telescope b e k
  rw [he]
  apply (legalSeedSpan A).sum_mem
  intro j hj
  exact legalSeedSpan_dilation A h (b ^ j) (pow_pos hb j)

/-- Exact subtraction of exponent seeds; no division of operators occurs. -/
theorem residue_power_sub_identity (c u v : ℕ) (huv : u ≤ v) :
    residue (c ^ (v - u)) =
      residue (c ^ v) - dilation (c ^ (v - u)) (residue (c ^ u)) := by
  funext k
  simp only [Pi.sub_apply, residue_mul_floor, ← pow_add, Nat.sub_add_cancel huv]
  ring

theorem residue_power_sub_mem (A : Set ℕ) {c u v : ℕ} (hc : 0 < c)
    (hu : residue (c ^ u) ∈ legalSeedSpan A)
    (hv : residue (c ^ v) ∈ legalSeedSpan A) (huv : u ≤ v) :
    residue (c ^ (v - u)) ∈ legalSeedSpan A := by
  rw [residue_power_sub_identity c u v huv]
  exact (legalSeedSpan A).sub_mem hv
    (legalSeedSpan_dilation A hu (c ^ (v - u)) (pow_pos hc _))

/-- The full Euclidean remainder step, still an exact finite legal synthesis. -/
theorem residue_power_mod_mem (A : Set ℕ) {c u v : ℕ} (hc : 0 < c)
    (hu : residue (c ^ u) ∈ legalSeedSpan A)
    (hv : residue (c ^ v) ∈ legalSeedSpan A) :
    residue (c ^ (v % u)) ∈ legalSeedSpan A := by
  have hquot : residue (c ^ (u * (v / u))) ∈ legalSeedSpan A := by
    simpa only [pow_mul] using
      residue_power_mem_of_mem A (pow_pos hc u) hu (v / u)
  have he : residue (c ^ (v % u)) =
      residue (c ^ v) - dilation (c ^ (v % u)) (residue (c ^ (u * (v / u)))) := by
    funext k
    simp only [Pi.sub_apply, residue_mul_floor, ← pow_add, Nat.mod_add_div]
    ring
  rw [he]
  exact (legalSeedSpan A).sub_mem hv
    (legalSeedSpan_dilation A hquot (c ^ (v % u)) (pow_pos hc _))

/-- Two known power seeds synthesize the seed with gcd exponent. -/
theorem residue_power_gcd_mem (A : Set ℕ) {c : ℕ} (hc : 0 < c)
    (u v : ℕ) (hu : residue (c ^ u) ∈ legalSeedSpan A)
    (hv : residue (c ^ v) ∈ legalSeedSpan A) :
    residue (c ^ Nat.gcd u v) ∈ legalSeedSpan A := by
  induction u using Nat.strong_induction_on generalizing v with
  | h u ih =>
    by_cases hu0 : u = 0
    · subst u
      simpa using hv
    · rw [Nat.gcd_rec]
      exact ih (v % u) (Nat.mod_lt v (Nat.pos_of_ne_zero hu0)) u
        (residue_power_mod_mem A hc hu hv) hu

/-- Exact algebraic classification of a pair of common-base power seeds. -/
theorem legalSeedSpan_power_pair (c u v : ℕ) (hc : 0 < c) :
    legalSeedSpan {c ^ u, c ^ v} = legalSeedSpan {c ^ Nat.gcd u v} := by
  apply le_antisymm
  · apply legalSeedSpan_le_of_residue_mem
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · obtain ⟨q, hq⟩ := Nat.gcd_dvd_left u v
      have hp : residue (c ^ u) = residue ((c ^ Nat.gcd u v) ^ q) := by
        rw [← pow_mul, ← hq]
      rw [hp]
      exact power_seed_mem_legalSeedSpan _ (by simp) (pow_pos hc _) q
    · have ha' : a = c ^ v := Set.mem_singleton_iff.mp ha
      subst a
      obtain ⟨q, hq⟩ := Nat.gcd_dvd_right u v
      have hp : residue (c ^ v) = residue ((c ^ Nat.gcd u v) ^ q) := by
        rw [← pow_mul, ← hq]
      rw [hp]
      exact power_seed_mem_legalSeedSpan _ (by simp) (pow_pos hc _) q
  · apply legalSeedSpan_le_of_residue_mem
    intro a ha
    have ha' : a = c ^ Nat.gcd u v := Set.mem_singleton_iff.mp ha
    subst a
    exact residue_power_gcd_mem _ hc u v
      (residue_mem_legalSeedSpan _ (by simp))
      (residue_mem_legalSeedSpan _ (by simp))

/-- In particular, coprime exponents recover the original base seed exactly. -/
theorem legalSeedSpan_coprime_powers (c u v : ℕ) (hc : 0 < c)
    (huv : Nat.Coprime u v) :
    legalSeedSpan {c ^ u, c ^ v} = legalSeedSpan {c} := by
  simpa only [huv.gcd_eq_one, pow_one] using legalSeedSpan_power_pair c u v hc

private theorem list_gcd_dvd_of_mem (es : List ℕ) {e : ℕ} (he : e ∈ es) :
    es.foldr Nat.gcd 0 ∣ e := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp he with rfl | he
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (ih he)

/-- Finite Euclidean synthesis uses every exponent, including families with
no coprime pair but collective gcd one, such as 6, 10, and 15. -/
theorem residue_power_list_gcd_mem (A : Set ℕ) {c : ℕ} (hc : 0 < c)
    (es : List ℕ) (h : ∀ e ∈ es, residue (c ^ e) ∈ legalSeedSpan A) :
    residue (c ^ es.foldr Nat.gcd 0) ∈ legalSeedSpan A := by
  induction es with
  | nil =>
    have hz : residue (c ^ (List.nil.foldr Nat.gcd 0)) = 0 := by
      funext k
      simp [residue, Nat.mod_one]
    rw [hz]
    exact (legalSeedSpan A).zero_mem
  | cons a es ih =>
    simp only [List.foldr_cons]
    apply residue_power_gcd_mem A hc
    · exact h a (by simp)
    · exact ih (fun e he => h e (List.mem_cons_of_mem a he))

/-- Complete finite common-base classification before any Hilbert-space closure. -/
theorem legalSeedSpan_power_list (c : ℕ) (hc : 0 < c) (es : List ℕ) :
    legalSeedSpan {a | ∃ e ∈ es, a = c ^ e} =
      legalSeedSpan {c ^ es.foldr Nat.gcd 0} := by
  apply le_antisymm
  · apply legalSeedSpan_le_of_residue_mem
    rintro a ⟨e, he, rfl⟩
    obtain ⟨q, hq⟩ := list_gcd_dvd_of_mem es he
    have hp : residue (c ^ e) = residue ((c ^ es.foldr Nat.gcd 0) ^ q) := by
      rw [← pow_mul, ← hq]
    rw [hp]
    exact power_seed_mem_legalSeedSpan _ (by simp) (pow_pos hc _) q
  · apply legalSeedSpan_le_of_residue_mem
    intro a ha
    have ha' : a = c ^ es.foldr Nat.gcd 0 := Set.mem_singleton_iff.mp ha
    subst a
    apply residue_power_list_gcd_mem _ hc es
    intro e he
    exact residue_mem_legalSeedSpan _ ⟨e, he, rfl⟩

/-- Collective gcd one, not the existence of a coprime pair, is the criterion
for recovery of a fixed common base by finite algebraic synthesis. -/
theorem legalSeedSpan_list_gcd_one (c : ℕ) (hc : 0 < c) (es : List ℕ)
    (he : es.foldr Nat.gcd 0 = 1) :
    legalSeedSpan {a | ∃ e ∈ es, a = c ^ e} = legalSeedSpan {c} := by
  simpa only [he, pow_one] using legalSeedSpan_power_list c hc es

end
end RiemannResearch.RH.Pareto
