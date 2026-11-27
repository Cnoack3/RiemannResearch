/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ThreePrimeGapParseval
import Mathlib.Topology.Algebra.Order.Archimedean

/-! # Arbitrarily fine real-frequency meshes from three fixed primes

Source: the three-prime construction in §4 of the Mellin–Montgomery handoff.
Integer combinations of the two ratio steps form a dense subgroup of the
real frequency axis. A single positive step in this subgroup then rounds
every real frequency with the same uniform error bound.
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open CompactCharacter CompactGaugeOrbitLaw

/-- The group of all two-step frequencies for a fixed prime triple is dense. -/
theorem threePrimeWordFrequency_dense {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    DenseRange (fun s : ℤ × ℤ =>
      wordFrequency (ratioWord p q s.1 ++ ratioWord q r s.2)) := by
  let b := logPrimeStep p q
  let c := logPrimeStep q r
  let F : ℤ × ℤ →+ ℝ := {
    toFun := fun s => (s.1 : ℝ) * b + (s.2 : ℝ) * c
    map_zero' := by simp
    map_add' := by intro s t; simp [add_mul]; ring }
  have hF (s : ℤ × ℤ) :
      wordFrequency (ratioWord p q s.1 ++ ratioWord q r s.2) = F s := by
    simp [wordFrequency_append, ratioWord_frequency, F, b, c]
  have hinj : Function.Injective F := by
    intro s t h
    exact two_prime_steps_injective hpq hqr ((hF s).trans (h.trans (hF t).symm))
  have hd : Dense (F.range : Set ℝ) := by
    apply F.range.dense_or_cyclic.resolve_right
    rintro ⟨u, hu⟩
    have h₁ : b ∈ F.range := ⟨(1, 0), by simp [F]⟩
    have h₂ : c ∈ F.range := ⟨(0, 1), by simp [F]⟩
    rw [hu, ← AddSubgroup.zmultiples_eq_closure] at h₁ h₂
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₂
    change m • u = b at hm
    change n • u = c at hn
    rw [zsmul_eq_mul] at hm hn
    have hz : F (n, -m) = F (0, 0) := by
      simp [F, ← hm, ← hn]; ring
    have ez := hinj hz
    have em : m = 0 := by
      have e := congrArg Prod.snd ez
      change -m = 0 at e
      omega
    have hb : b = 0 := by simpa [em] using hm.symm
    have e := hinj (show F (1, 0) = F (0, 0) by simp [F, hb])
    have e₁ := congrArg Prod.fst e
    change (1 : ℤ) = 0 at e₁
    omega
  apply hd.mono
  rintro x ⟨s, rfl⟩
  exact ⟨s, hF s⟩

/-- Multiplying both integer orders scales the physical frequency exactly. -/
theorem threePrimeWordFrequency_mul (p q r : Nat.Primes) (k a b : ℤ) :
    wordFrequency (ratioWord p q (k * a) ++ ratioWord q r (k * b)) =
      (k : ℝ) * wordFrequency (ratioWord p q a ++ ratioWord q r b) := by
  simp only [wordFrequency_append, ratioWord_frequency, Int.cast_mul]
  ring

/-- At every ordinate the mesh word evaluates to the exact rounded phase. -/
theorem threePrimeMesh_character_phasePoint (p q r : Nat.Primes) (k a b : ℤ) (t : ℝ) :
    character (ratioWord p q (k * a) ++ ratioWord q r (k * b)) (phasePoint t) =
      ZeroOrdinate.phase ((k : ℝ) * wordFrequency (ratioWord p q a ++ ratioWord q r b)) t := by
  rw [character_phasePoint, threePrimeWordFrequency_mul]

/-- Every positive tolerance admits a single positive step, made from the two
prime-ratio words, whose integer multiples round every real target frequency. -/
theorem exists_threePrimeWordFrequency_mesh {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, let h := wordFrequency (ratioWord p q a ++ ratioWord q r b)
      0 < h ∧ h < ε ∧ ∀ x : ℝ,
        let k := roundedOrder h x
        |wordFrequency (ratioWord p q (k * a) ++ ratioWord q r (k * b)) - x| ≤ h / 2 := by
  obtain ⟨⟨a, b⟩, hpos, hlt⟩ :=
    (threePrimeWordFrequency_dense hpq hqr).exists_mem_open isOpen_Ioo
      (Set.nonempty_Ioo.mpr hε)
  refine ⟨a, b, hpos, hlt, ?_⟩
  intro x
  let h := wordFrequency (ratioWord p q a ++ ratioWord q r b)
  let k := roundedOrder h x
  change |wordFrequency (ratioWord p q (k * a) ++ ratioWord q r (k * b)) - x| ≤ h / 2
  rw [threePrimeWordFrequency_mul]
  exact roundedOrder_error hpos x

/-- A positive frequency of a rational prime word cannot be smaller than
the reciprocal of its numerator. A step below `1 / T ^ 3` forces its
numerator above `T ^ 3`. -/
theorem inv_wordNumerator_le_wordFrequency (w : PrimeWord) (hpos : 0 < wordFrequency w) :
    (wordNumerator w : ℝ)⁻¹ ≤ wordFrequency w := by
  let n := wordNumerator w
  let m := wordDenominator w
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from wordNumerator_one_le w)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from wordDenominator_one_le w)
  have hlog : Real.log ((n : ℝ) / m) = wordFrequency w := by
    apply (PrimePhaseTorus.prime_log_ratio_eq_frequency _ _ (wordPrimes_prime w)).trans
    exact (wordFrequency_eq_sum w _ (fun a ha =>
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩))).symm
  have hlogpos : 0 < Real.log ((n : ℝ) / m) := by simpa only [hlog] using hpos
  have hmnr : (m : ℝ) < n :=
    (one_lt_div hm).mp ((Real.log_pos_iff (div_pos hn hm).le).mp hlogpos)
  have hmn : m < n := by exact_mod_cast hmnr
  have hsucc : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hmn)
  change (n : ℝ)⁻¹ ≤ wordFrequency w
  rw [← hlog]
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos (div_pos hn hm))
  rw [inv_div, ← one_div, show 1 - (m : ℝ) / n = ((n : ℝ) - m) / n by
    field_simp [hn.ne']]
  exact (div_le_div_iff_of_pos_right hn).2 (by linarith only [hsucc])

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
