/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Exact CRT tensor orthogonality for prime-block divisibility patterns

The proof works for arbitrary positive pairwise coprime moduli, not only primes.
The uniform CRT counting form is kept separate from the Pareto energy form.
-/

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open scoped BigOperators

/-- Centered divisibility coordinate on a finite residue ring. -/
def localEta (m : ℕ) (x : ZMod m) : ℝ :=
  1 - (m : ℝ) * (if x = 0 then 1 else 0)

theorem localEta_sum (m : ℕ) [NeZero m] :
    (∑ x : ZMod m, localEta m x) = 0 := by
  simp [localEta, Finset.sum_sub_distrib, ← Finset.mul_sum, ZMod.card]

theorem localEta_square_sum (m : ℕ) [NeZero m] :
    (∑ x : ZMod m, (localEta m x)^2) = (m : ℝ) * ((m : ℝ) - 1) := by
  have he (x : ZMod m) : (localEta m x)^2 =
      1 + ((m : ℝ)^2 - 2 * m) * (if x = 0 then 1 else 0) := by
    by_cases h : x = 0 <;> simp [localEta, h] <;> ring
  simp_rw [he]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ZMod.card]
  ring

theorem localEta_natCast (m n : ℕ) :
    localEta m (n : ZMod m) = 1 - (m : ℝ) * (if m ∣ n then 1 else 0) := by
  simp [localEta, ZMod.natCast_eq_zero_iff]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor product, with an inactive coordinate equal to one. -/
def tensorPacket (m : ι → ℕ) (S : Finset ι) (x : (i : ι) → ZMod (m i)) : ℝ :=
  ∏ i, if i ∈ S then localEta (m i) (x i) else 1

theorem tensorPacket_inner_factorization (m : ι → ℕ) [∀ i, NeZero (m i)]
    (S T : Finset ι) :
    (∑ x : (i : ι) → ZMod (m i), tensorPacket m S x * tensorPacket m T x) =
      ∏ i, if i ∈ S then
        (if i ∈ T then (m i : ℝ) * ((m i : ℝ) - 1) else 0)
        else (if i ∈ T then 0 else (m i : ℝ)) := by
  unfold tensorPacket
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (z : ZMod (m i)) =>
    (if i ∈ S then localEta (m i) z else 1) *
      (if i ∈ T then localEta (m i) z else 1))]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · simpa [hS, hT, ← pow_two] using localEta_square_sum (m i)
  · simpa [hS, hT] using localEta_sum (m i)
  · simpa [hS, hT] using localEta_sum (m i)
  · simp [hS, hT, ZMod.card]

theorem tensorPacket_orthogonal (m : ι → ℕ) [∀ i, NeZero (m i)]
    (S T : Finset ι) (hST : S ≠ T) :
    (∑ x : (i : ι) → ZMod (m i), tensorPacket m S x * tensorPacket m T x) = 0 := by
  rw [tensorPacket_inner_factorization]
  have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
    by_contra h
    apply hST
    ext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

theorem tensorPacket_norm_sq (m : ι → ℕ) [∀ i, NeZero (m i)] (S : Finset ι) :
    (∑ x : (i : ι) → ZMod (m i), (tensorPacket m S x)^2) =
      (∏ i, (m i : ℝ)) * ∏ i ∈ S, ((m i : ℝ) - 1) := by
  have h := tensorPacket_inner_factorization m S S
  rw [show (fun i => if i ∈ S then
      (if i ∈ S then (m i : ℝ) * ((m i : ℝ) - 1) else 0)
      else (if i ∈ S then 0 else (m i : ℝ))) =
      (fun i => (m i : ℝ) * (if i ∈ S then (m i : ℝ) - 1 else 1)) by
        funext i; by_cases hi : i ∈ S <;> simp [hi]] at h
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem] at h
  simp only [Finset.univ_inter] at h
  simpa only [pow_two] using h

/-- CRT realizes the tensor packet on one common residue ring. -/
def crtPacket (m : ι → ℕ) (hc : Pairwise (Function.onFun Nat.Coprime m))
    (S : Finset ι) (x : ZMod (∏ i, m i)) : ℝ :=
  tensorPacket m S ((ZMod.prodEquivPi m hc) x)

theorem crtPacket_orthogonal (m : ι → ℕ) [∀ i, NeZero (m i)]
    [NeZero (∏ i, m i)] (hc : Pairwise (Function.onFun Nat.Coprime m))
    (S T : Finset ι) (hST : S ≠ T) :
    (∑ x : ZMod (∏ i, m i), crtPacket m hc S x * crtPacket m hc T x) = 0 := by
  unfold crtPacket
  convert ((ZMod.prodEquivPi m hc).toEquiv.sum_comp
    (fun x => tensorPacket m S x * tensorPacket m T x)).trans
    (tensorPacket_orthogonal m S T hST) using 1 <;> rfl

theorem crtPacket_norm_sq (m : ι → ℕ) [∀ i, NeZero (m i)]
    [NeZero (∏ i, m i)] (hc : Pairwise (Function.onFun Nat.Coprime m))
    (S : Finset ι) :
    (∑ x : ZMod (∏ i, m i), (crtPacket m hc S x)^2) =
      (∏ i, (m i : ℝ)) * ∏ i ∈ S, ((m i : ℝ) - 1) := by
  unfold crtPacket
  convert ((ZMod.prodEquivPi m hc).toEquiv.sum_comp
    (fun x => (tensorPacket m S x)^2)).trans
    (tensorPacket_norm_sq m S) using 1 <;> rfl

theorem crtPacket_uniform_inner (m : ι → ℕ) [∀ i, NeZero (m i)]
    [NeZero (∏ i, m i)] (hc : Pairwise (Function.onFun Nat.Coprime m))
    (S T : Finset ι) :
    (∑ x : ZMod (∏ i, m i), crtPacket m hc S x * crtPacket m hc T x) /
        (∏ i, (m i : ℝ)) =
      if S = T then ∏ i ∈ S, ((m i : ℝ) - 1) else 0 := by
  by_cases h : S = T
  · subst T
    simp only [ite_true, ← pow_two]
    rw [crtPacket_norm_sq]
    have hp : (∏ i, (m i : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact_mod_cast (NeZero.ne (m i))
    field_simp
  · simp [h, crtPacket_orthogonal m hc S T h]

theorem crtPacket_natCast (m : ι → ℕ)
    (hc : Pairwise (Function.onFun Nat.Coprime m)) (S : Finset ι) (n : ℕ) :
    crtPacket m hc S (n : ZMod (∏ i, m i)) =
      ∏ i ∈ S, (1 - (m i : ℝ) * (if m i ∣ n then 1 else 0)) := by
  unfold crtPacket tensorPacket
  simp only [ZMod.prodEquivPi_apply, map_natCast, localEta_natCast]
  simp [Finset.prod_ite_mem]

end
end RiemannResearch.RH.CRTBlock
