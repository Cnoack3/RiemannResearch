import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-!
# Chinese remainder theorem for arbitrary finite integer congruences

The moduli may overlap or repeat. The compatibility test is congruence
modulo each pairwise gcd, and the solution class is modulo the finite lcm.
This is the generalized integer CRT, using Bézout for the two-modulus step.
For the statement, see the Complete finite generalized Chinese remainder
theorem at https://bnaskrecki.faculty.wmi.amu.edu.pl/proofs/generalized-crt/.
-/

namespace RiemannResearch.NumberTheory.GeneralizedCRT

private theorem gcd_lcm_distrib (a b c : ℕ) :
    a.gcd (b.lcm c) = (a.gcd b).lcm (a.gcd c) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · subst b
    simp [Nat.lcm_eq_left (Nat.gcd_dvd_left a c)]
  by_cases hc : c = 0
  · subst c
    simp [Nat.lcm_eq_right (Nat.gcd_dvd_left a b)]
  have hl : b.lcm c ≠ 0 := Nat.ne_of_gt
    (Nat.lcm_pos (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc))
  have hab : a.gcd b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha))
  have hac : a.gcd c ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero ha))
  apply Nat.eq_of_factorization_eq'
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)))
    (Nat.ne_of_gt (Nat.lcm_pos (Nat.pos_of_ne_zero hab) (Nat.pos_of_ne_zero hac)))
  rw [Nat.factorization_gcd ha hl, Nat.factorization_lcm hb hc,
    Nat.factorization_lcm hab hac, Nat.factorization_gcd ha hb, Nat.factorization_gcd ha hc]
  ext p
  change a.factorization p ⊓ (b.factorization p ⊔ c.factorization p) =
    (a.factorization p ⊓ b.factorization p) ⊔ (a.factorization p ⊓ c.factorization p)
  exact inf_sup_left _ _ _

private theorem gcd_finset_lcm {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ℕ) :
    a.gcd (s.lcm m) = s.lcm (fun i => a.gcd (m i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.lcm_insert, Finset.lcm_insert, lcm_eq_nat_lcm, lcm_eq_nat_lcm,
      gcd_lcm_distrib, ih]

private theorem exists_pair {m n : ℕ} {a b : ℤ}
    (h : Int.ModEq (m.gcd n : ℤ) a b) :
    ∃ x : ℤ, Int.ModEq m x a ∧ Int.ModEq n x b := by
  obtain ⟨t, ht⟩ := h.dvd
  refine ⟨a + (m : ℤ) * m.gcdA n * t, Int.modEq_of_dvd ⟨-(m.gcdA n * t), by ring⟩, ?_⟩
  apply Int.modEq_of_dvd
  refine ⟨m.gcdB n * t, ?_⟩
  calc
    b - (a + (m : ℤ) * m.gcdA n * t) = (b - a) - (m : ℤ) * m.gcdA n * t := by ring
    _ = (n : ℤ) * (m.gcdB n * t) := by rw [ht, Nat.gcd_eq_gcd_ab]; ring

/-- Equality of all finite residues is congruence modulo their least common multiple. -/
theorem int_modEq_lcm_iff {ι : Type*} (s : Finset ι) (m : ι → ℕ) (x y : ℤ) :
    Int.ModEq ↑(s.lcm m : ℕ) x y ↔ ∀ i ∈ s, Int.ModEq (m i : ℤ) x y := by
  have hmod (k : ℕ) : Int.ModEq k x y ↔ k ∣ (y - x).natAbs :=
    Int.modEq_iff_dvd.trans (Int.dvd_natAbs.symm.trans Int.natCast_dvd_natCast)
  simp only [hmod, Finset.lcm_dvd_iff]

/-- Simultaneous congruences are solvable exactly when the residues agree
modulo each pairwise gcd. Modulus zero is allowed and denotes equality. -/
theorem exists_int_modEq_iff_pairwise {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) (a : ι → ℤ) :
    (∃ x : ℤ, ∀ i ∈ s, Int.ModEq (m i : ℤ) x (a i)) ↔
      ∀ i ∈ s, ∀ j ∈ s, Int.ModEq ((m i).gcd (m j) : ℤ) (a i) (a j) := by
  classical
  constructor
  · rintro ⟨x, hx⟩ i hi j hj
    exact ((hx i hi).symm.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))).trans
      ((hx j hj).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)))
  · induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert i s hi ih =>
      intro h
      obtain ⟨x, hx⟩ := ih (fun j hj k hk =>
        h j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      have hg : Int.ModEq ((s.lcm m).gcd (m i) : ℤ) x (a i) := by
        rw [Nat.gcd_comm (s.lcm m), gcd_finset_lcm, int_modEq_lcm_iff]
        intro j hj
        have hjg : Int.ModEq ((m i).gcd (m j) : ℤ) x (a j) :=
          (hx j hj).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _))
        exact hjg.trans (h i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)).symm
      obtain ⟨y, hyx, hyi⟩ := exists_pair hg
      refine ⟨y, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hyi
      · exact ((int_modEq_lcm_iff s m y x).mp hyx j hj).trans (hx j hj)

/-- Any given solution generates exactly one congruence class modulo the lcm. -/
theorem int_solution_class {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) (a : ι → ℤ) {x : ℤ}
    (hx : ∀ i ∈ s, Int.ModEq (m i : ℤ) x (a i)) (y : ℤ) :
    (∀ i ∈ s, Int.ModEq (m i : ℤ) y (a i)) ↔ Int.ModEq ↑(s.lcm m : ℕ) y x := by
  rw [int_modEq_lcm_iff]
  exact ⟨fun h i hi => (h i hi).trans (hx i hi).symm,
    fun h i hi => (h i hi).trans (hx i hi)⟩

/-- For positive moduli, every compatible system has a unique representative
in the standard interval from zero to the lcm, excluding the upper endpoint. -/
theorem existsUnique_int_modEq_of_pairwise {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) (a : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (ha : ∀ i ∈ s, ∀ j ∈ s, Int.ModEq ((m i).gcd (m j) : ℤ) (a i) (a j)) :
    ∃! x : ℤ, 0 ≤ x ∧ x < ↑(s.lcm m : ℕ) ∧ ∀ i ∈ s, Int.ModEq (m i : ℤ) x (a i) := by
  obtain ⟨x, hx⟩ := (exists_int_modEq_iff_pairwise s m a).mpr ha
  have hL : (0 : ℤ) < ↑(s.lcm m : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr hm : s.lcm m ≠ 0)
  let z := x % ↑(s.lcm m : ℕ)
  have hz0 : 0 ≤ z := Int.emod_nonneg _ hL.ne'
  have hzL : z < ↑(s.lcm m : ℕ) := Int.emod_lt_of_pos _ hL
  have hz := (int_solution_class s m a hx z).mpr (Int.mod_modEq _ _)
  refine ⟨z, ⟨hz0, hzL, hz⟩, ?_⟩
  rintro y ⟨hy0, hyL, hy⟩
  have h := (int_solution_class s m a hz y).mp hy
  change y % ↑(s.lcm m : ℕ) = z % ↑(s.lcm m : ℕ) at h
  rwa [Int.emod_eq_of_lt hy0 hyL, Int.emod_eq_of_lt hz0 hzL] at h

end RiemannResearch.NumberTheory.GeneralizedCRT
