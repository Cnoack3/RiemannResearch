import RiemannResearch.Analysis.DyadicInvariantEnergy
import RiemannResearch.Analysis.DyadicBlockRecovery
import RiemannResearch.Analysis.PositiveScalingRigidity

/-!
# Two-scale rigidity for sequences with square-summable increments

Source: user-provided `RH_Iff_Two_Seed_Approximation_20260914.md`, Section 4.
The proof here constructs continuous prefix primitives from the actual
discrete data, uses their exact two homogeneity identities, and recovers
every positive-index value by the complete increment tail estimate.
No completeness or RH assumption occurs in the statement.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter
noncomputable section

/-- Two multiplicatively independent integer scales and finite squared
increment energy force constancy at every positive integer. Index zero is
deliberately excluded from the conclusion. -/
theorem multiplicativeSequence_rigidity (a : ℕ → ℝ)
    (h2 : ∀ n, 0 < n → a (2*n) = a n)
    (h3 : ∀ n, 0 < n → a (3*n) = a n)
    (hs : Summable (fun n => (a (n+1)-a n)^2)) :
    ∀ n : ℕ, 0 < n → a n = a 1 := by
  have ha2 : ∀ n, a (2*n) = a n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · exact h2 n (Nat.pos_of_ne_zero hn)
  have ha3 : ∀ n, a (3*n) = a n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · exact h3 n (Nat.pos_of_ne_zero hn)
  obtain ⟨C, hC0, hC⟩ := dyadicInvariant_prefix_energy_bound a ha2 hs
  have hs' : Summable (fun n => sequenceIncrement a n^2) := hs
  have hcontinuous : ContinuousOn (prefixPrimitiveLimit a) (Set.Ioi 0) :=
    continuousOn_Ioi_of_sq_increment_le (prefixPrimitiveLimit a) hC0
      (fun x y hx hxy => prefixPrimitiveLimit_holder a ha2 hs' hC0 hC hx hxy)
  have hlinear {x : ℝ} (hx : 0 < x) :
      prefixPrimitiveLimit a x = x * prefixPrimitiveLimit a 1 :=
    continuousOn_two_three_homogeneous (prefixPrimitiveLimit a) hcontinuous
      (fun x hx => prefixPrimitiveLimit_double a ha2 hs' hC0 hC hx.le)
      (fun x hx => prefixPrimitiveLimit_triple a ha2 ha3 hs' hC0 hC hx.le) hx
  have hzero : prefixPrimitiveLimit a 0 = 0 := by
    have ht := dyadicPrefixPrimitive_tendsto a ha2 hs' hC0 hC (le_refl (0 : ℝ))
    have he : (fun j => dyadicPrefixPrimitive a j 0) = (fun _ : ℕ => (0 : ℝ)) := by
      funext j
      simp [dyadicPrefixPrimitive, sequencePrefix]
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hlinNat (n : ℕ) : prefixPrimitiveLimit a n =
      (n : ℝ)*prefixPrimitiveLimit a 1 := by
    by_cases hn : n = 0
    · simp [hn, hzero]
    · exact hlinear (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have havg (n : ℕ) : Tendsto (fun j => dyadicBlockAverage a j n)
      atTop (nhds (prefixPrimitiveLimit a 1)) := by
    have hu := dyadicPrefixPrimitive_tendsto a ha2 hs' hC0 hC
      (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)
    have hl := dyadicPrefixPrimitive_tendsto a ha2 hs' hC0 hC
      (show (0 : ℝ) ≤ (n : ℝ) by positivity)
    have h := hu.sub hl
    rw [hlinNat (n+1), hlinNat n] at h
    have he : ((n+1 : ℕ) : ℝ)*prefixPrimitiveLimit a 1 -
        (n : ℝ)*prefixPrimitiveLimit a 1 = prefixPrimitiveLimit a 1 := by
      push_cast
      ring
    rw [he] at h
    simpa only [dyadicBlockAverage_eq_primitive, Nat.cast_add, Nat.cast_one] using h
  have hconst := sequence_constant_of_linear_prefix_limit a ha2 hs'
    (prefixPrimitiveLimit a 1) havg
  intro n hn
  exact (hconst n hn).trans (hconst 1 (by norm_num)).symm

end
end RiemannResearch.Analysis
