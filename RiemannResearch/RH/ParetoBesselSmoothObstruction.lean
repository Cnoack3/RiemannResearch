import RiemannResearch.Analysis.SmoothScaleReciprocal
import RiemannResearch.RH.PrimeReciprocalTail
import RiemannResearch.RH.ParetoBesselClusters
import RiemannResearch.RH.Smooth35Choice

/-!
# Smooth-scale binary repairs cannot satisfy the proposed Bessel bound

The report explicitly warned that its suggested all-coefficient normalized
Bessel estimate might fail through common-scale clustering. This module proves
that failure for every scale assignment which, at all sufficiently large
primes, is a `3,5`-smooth integer strictly above p and at most 2p.

The proof retains the actual full Pareto covariance through the cluster
certificate. Its counting step uses convergence of a double geometric series
and Euler's divergence of prime reciprocals. No RH input, prime number theorem,
or smooth-gap rate theorem is assumed.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The common-scale obstruction contradicts the suggested normalized Bessel
bound for all eventually comparable `3,5`-smooth scale assignments. -/
theorem not_repairBesselBound_of_eventual_smooth35
    (scale : ℕ → ℕ) (N : ℕ) (hN : 7 ≤ N)
    (hlegal : ∀ p, p.Prime → N ≤ p →
      p < scale p ∧ scale p ≤ 2*p ∧ ∃ a b : ℕ, scale p = 3^a * 5^b) :
    ¬ ResearchTargets.RepairBesselBound scale := by
  classical
  rintro ⟨C, hC, hb⟩
  let I := {p : ℕ // p.Prime ∧ N ≤ p}
  have hrepr : ∀ p : I, ∃ a b : ℕ, scale p.val = 3^a * 5^b := by
    intro p
    exact (hlegal p.val p.property.1 p.property.2).2.2
  choose a b hab using hrepr
  let D : ℝ := 1 + 108 * C * Real.log 2
  have hD : 0 ≤ D := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [D]
    positivity
  have hs : Summable (fun p : I => 1 / (p.val : ℝ)) := by
    apply RiemannResearch.Analysis.SmoothScale.reciprocal_summable_of_smooth_cluster_bound
      (fun p : I => (p.val : ℝ)) a b D hD
    · intro p
      refine ⟨by exact_mod_cast p.property.1.pos, ?_⟩
      have he := congrArg (fun n : ℕ => (n : ℝ)) (hab p)
      push_cast at he
      rw [← he]
      exact_mod_cast (hlegal p.val p.property.1 p.property.2).2.1
    · intro Q j hQ
      let S : Finset ℕ := Q.image Subtype.val
      let M : ℕ := 3^j.1 * 5^j.2
      have hS : ∀ p ∈ S,
          p.Prime ∧ 7 ≤ p ∧ scale p = M ∧ p < M ∧ M ≤ 2*p := by
        intro n hn
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
        have ha := congrArg Prod.fst (hQ p hp)
        have hb' := congrArg Prod.snd (hQ p hp)
        have heq : scale p.val = M := by
          rw [hab p]
          simp only [Prod.fst, Prod.snd] at ha hb'
          simp only [ha, hb', M]
        have hpLegal := hlegal p.val p.property.1 p.property.2
        exact ⟨p.property.1, hN.trans p.property.2, heq,
          heq ▸ hpLegal.1, heq ▸ hpLegal.2.1⟩
      have hc := repairBessel_commonScale_card_sq_le scale C hC hb S M hS
      have hcard : S.card = Q.card :=
        Finset.card_image_of_injective Q Subtype.val_injective
      rw [hcard] at hc
      simpa only [D, M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
  exact not_summable_prime_reciprocal_tail N hs

/-- The actual least-smooth scale choice in the report fails the proposed
normalized Bessel bound, without any unproved gap estimate. -/
theorem not_repairBesselBound_leastSmooth35Above :
    ¬ ResearchTargets.RepairBesselBound leastSmooth35Above := by
  apply not_repairBesselBound_of_eventual_smooth35 leastSmooth35Above 7 (by norm_num)
  intro p hp hp7
  exact ⟨(leastSmooth35Above_spec p).1,
    leastSmooth35Above_le_twice p (by omega), (leastSmooth35Above_spec p).2⟩

end
end RiemannResearch.RH.Pareto
