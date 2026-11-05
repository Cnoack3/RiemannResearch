/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.TreeConeTopology
import Mathlib.Logic.Denumerable
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Nat.PrimeFin

/-! # Density, self-similarity and physical probes of the prime support tree

Source: Prime Trees, Carries and Zeta Zeros (5 November 2026), §7.2.
The fixed coordinates of a cone include all skipped primes below its last
prime. The homeomorphism retains precisely the complementary coordinates.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.PrimeTreeTopology

private theorem mem_coordinatesThrough_iff (K : ℕ) (p : Nat.Primes) :
    p ∈ coordinatesThrough K ↔ p.val ≤ K := by
  classical
  constructor
  · intro h
    obtain ⟨j, hj, h'⟩ := Finset.mem_biUnion.mp h
    simp only [Finset.mem_range] at hj
    split_ifs at h' with hp
    · have he := Finset.mem_singleton.mp h'
      have hv : p.val = j := congrArg Subtype.val he
      omega
    · simp at h'
  · intro h
    apply Finset.mem_biUnion.mpr
    exact ⟨p.val, Finset.mem_range.mpr (by omega), by
      rw [dif_pos p.property]
      exact Finset.mem_singleton.mpr (Subtype.ext rfl)⟩

private theorem prime_dvd_product_iff (s : Finset Nat.Primes) (p : Nat.Primes) :
    p.val ∣ (∏ q ∈ s, q.val) ↔ p ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [p.property.not_dvd_one]
  | @insert q s hq ih =>
    have h : p.val ∣ q.val ↔ p = q := by
      constructor
      · intro hd
        exact Subtype.ext (((Nat.dvd_prime q.property).mp hd).resolve_left p.property.ne_one)
      · rintro rfl; exact dvd_rfl
    rw [Finset.prod_insert hq, p.property.dvd_mul, h, ih, Finset.mem_insert]

private theorem product_squarefree (s : Finset Nat.Primes) :
    Squarefree (∏ q ∈ s, q.val) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    have hc : q.val.Coprime (∏ p ∈ s, p.val) :=
      q.property.coprime_iff_not_dvd.mpr (fun hd => hq ((prime_dvd_product_iff s q).mp hd))
    rw [Finset.prod_insert hq, Nat.squarefree_mul hc]
    exact ⟨q.property.prime.squarefree, ih⟩

/-- Every prime mask is the limit of physical squarefree vertices. -/
theorem dense_squarefree_vertices :
    Dense (Set.range fun r : {m : ℕ // Squarefree m} => vertex r.val) := by
  classical
  intro x
  let S (K : ℕ) : Finset Nat.Primes := (coordinatesThrough K).filter (fun p => x p = 1)
  let F (K : ℕ) : {m : ℕ // Squarefree m} :=
    ⟨∏ q ∈ S K, q.val, product_squarefree (S K)⟩
  apply mem_closure_of_tendsto (f := fun K => vertex (F K).val) (b := atTop)
  · apply tendsto_pi_nhds.mpr
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop p.val] with K hK
    have hp := (mem_coordinatesThrough_iff K p).mpr hK
    change x p = (if p.val ∣ (∏ q ∈ S K, q.val) then 1 else 0)
    have hbit : p.val ∣ (∏ q ∈ S K, q.val) ↔ x p = 1 :=
      (prime_dvd_product_iff (S K) p).trans (by simp only [S, Finset.mem_filter, hp, true_and])
    by_cases hd : p.val ∣ (∏ q ∈ S K, q.val)
    · rw [if_pos hd]
      exact hbit.mp hd
    · rw [if_neg hd]
      have hbits : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
      exact (hbits (x p)).resolve_right (fun h => hd (hbit.mpr h))
  · exact Eventually.of_forall fun K => Set.mem_range_self (F K)

/-- An arbitrary cylinder is the product of its free prime coordinates. -/
def cylinderTailHomeomorph (s : Finset Nat.Primes) (x : PrimeMask) :
    cylinder s x ≃ₜ ({p : Nat.Primes // p ∉ s} → Bit) := by
  classical
  refine {
    toFun := fun y p => y.val p.val
    invFun := fun z => ⟨fun p => if hp : p ∈ s then x p else z ⟨p,hp⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro p hp
    simp [hp]
  · intro y
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ s
    · simp [hp, y.property p hp]
    · simp [hp]
  · intro z
    funext p
    simp [p.property]
  · exact continuous_pi fun p => (continuous_apply p.val).comp continuous_subtype_val
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    by_cases hp : p ∈ s
    · simpa only [dif_pos hp] using
        (continuous_const : Continuous (fun _ : {p : Nat.Primes // p ∉ s} → Bit => x p))
    · simpa only [dif_neg hp] using (continuous_apply (⟨p,hp⟩ : {p : Nat.Primes // p ∉ s}))

/-- Every prefix cone is homeomorphic to the full compact prime support space. -/
def prefixConeHomeomorph (r : ℕ) : prefixCone r ≃ₜ PrimeMask := by
  classical
  let s := coordinatesThrough (r.primeFactors.sup id)
  letI : Infinite {p : Nat.Primes // p ∉ s} := s.finite_toSet.infinite_compl.to_subtype
  let e : {p : Nat.Primes // p ∉ s} ≃ Nat.Primes := nonempty_equiv_of_countable.some
  exact (cylinderTailHomeomorph s (vertex r)).trans (Homeomorph.piCongrLeft (Y := fun _ => Bit) e)

/-- A physical remainder cannot be read continuously at any finite positive
squarefree stopping point, even if continuity is imposed only at that point. -/
theorem no_continuousAt_own_remainder {r : ℕ} (hr : 0 < r) (hs : Squarefree r) :
    ¬ ∃ u : PrimeMask → ℕ, ContinuousAt u (vertex r) ∧
      ∀ m : ℕ, Squarefree m → u (vertex m) = r % m := by
  rintro ⟨u, hu, hv⟩
  let q (j : ℕ) := Classical.choose (Nat.exists_infinite_primes (j + r + 1))
  have hs' (j : ℕ) : j+r+1 ≤ q j ∧ (q j).Prime :=
    Classical.choose_spec (Nat.exists_infinite_primes (j+r+1))
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop a] with j hj
    have hh := (hs' j).1
    omega
  have hlim := hu.tendsto.comp (vertex_mul_prime_tendsto r q (fun j => (hs' j).2) hq)
  have hsame : (fun j : ℕ => u (vertex (r*q j))) = fun _ : ℕ => r := by
    funext j
    have hqr : r < q j := by have h := (hs' j).1; omega
    have hcop : (q j).Coprime r := (hs' j).2.coprime_iff_not_dvd.mpr
      (fun hd => (Nat.not_le_of_lt hqr) (Nat.le_of_dvd hr hd))
    have hsf := (Nat.squarefree_mul hcop.symm).mpr ⟨hs, (hs' j).2.prime.squarefree⟩
    have hbig : r < r*q j := by
      calc
        r = r*1 := (Nat.mul_one r).symm
        _ < r*q j := Nat.mul_lt_mul_of_pos_left (hs' j).2.one_lt hr
    rw [hv _ hsf, Nat.mod_eq_of_lt hbig]
  change Tendsto (fun j : ℕ => u (vertex (r*q j))) atTop (𝓝 (u (vertex r))) at hlim
  rw [hsame, hv r hs, Nat.mod_self] at hlim
  have hconst : Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := tendsto_const_nhds
  exact (Nat.ne_of_gt hr) (tendsto_nhds_unique hconst hlim)

end RiemannResearch.RH.PrimeTreeTopology
