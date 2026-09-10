import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Packing separated real points in an interval

Source: user-provided argument, §3 of
`Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`.
The finite packing estimate is the geometric ingredient for the rotation
prefix bound. Removing the minimum replaces the lower interval endpoint by
that minimum plus the separation, so no sorting algorithm is required.
-/

namespace Finset

/-- A finite collection of points separated by at least `η` occupies the
corresponding amount of interval length. -/
theorem card_mul_spacing_le_length_add
    (s : Finset ℝ) (η a b : ℝ) (hη : 0 ≤ η) (hab : a ≤ b)
    (hmem : ∀ x ∈ s, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → η ≤ |x - y|) :
    (s.card : ℝ) * η ≤ b - a + η := by
  classical
  induction s using Finset.strongInductionOn generalizing a b
  rename_i s ih
  by_cases hs : s.Nonempty
  · let x := s.min' hs
    have hx : x ∈ s := Finset.min'_mem s hs
    have hcard : ((s.erase x).card : ℝ) + 1 = s.card := by
      exact_mod_cast Finset.card_erase_add_one hx
    have hbounds : ∀ y ∈ s.erase x, x + η ≤ y ∧ y ≤ b := by
      intro y hy
      have hyS : y ∈ s := Finset.mem_of_mem_erase hy
      have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
      have hxle : x ≤ y := Finset.min'_le s y hyS
      have h := hsep y hyS x hx hyne
      rw [abs_of_nonneg (sub_nonneg.mpr hxle)] at h
      exact ⟨by linarith, (hmem y hyS).2⟩
    by_cases ht : (s.erase x).Nonempty
    · obtain ⟨y, hy⟩ := ht
      have hab' : x + η ≤ b := le_trans (hbounds y hy).1 (hbounds y hy).2
      have hsmall := ih (s.erase x) (Finset.erase_ssubset hx)
        (x + η) b hab' hbounds (by
          intro u hu v hv hne
          exact hsep u (Finset.mem_of_mem_erase hu)
            v (Finset.mem_of_mem_erase hv) hne)
      have hax := (hmem x hx).1
      nlinarith
    · have ht0 : s.erase x = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      simp only [ht0, Finset.card_empty, Nat.cast_zero, zero_add] at hcard
      nlinarith
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hs0, Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith

/-- Apply interval packing to arbitrary distinctly indexed points inside the
centered interval `[-d,d]`. This directly gives the rank lower bound once the
index set consists of the first `i` points in distance order. -/
theorem card_sub_one_mul_spacing_le_two_mul_radius
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (η d : ℝ)
    (hη : 0 < η) (hd : 0 ≤ d)
    (hbound : ∀ i ∈ s, |f i| ≤ d)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → η ≤ |f i - f j|) :
    ((s.card : ℝ) - 1) * η ≤ 2 * d := by
  classical
  have hinj : Set.InjOn f s := by
    intro i hi j hj he
    by_contra hne
    have h := hsep i hi j hj hne
    rw [he, sub_self, abs_zero] at h
    linarith
  have himage : (s.image f).card = s.card := Finset.card_image_iff.mpr hinj
  have hpack := card_mul_spacing_le_length_add (s.image f) η (-d) d
    (le_of_lt hη) (by linarith) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact abs_le.mp (hbound i hi)) (by
      intro x hx y hy hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact hsep i hi j hj (fun he => hne (congrArg f he)))
  rw [himage] at hpack
  nlinarith

end Finset
