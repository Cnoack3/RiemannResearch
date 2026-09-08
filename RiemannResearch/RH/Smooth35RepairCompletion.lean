import RiemannResearch.RH.ParetoRepairSummability
import RiemannResearch.RH.Smooth35Choice
import RiemannResearch.RH.ParetoNoiseResearchTargets

/-!
# Exact remaining arithmetic input for summable smooth-prime repairs

The named research target is proved below from a single explicit quantitative
gap bound for the actual least `{3,5}`-smooth integer above each prime. The
gap bound is a hypothesis, not an axiom or a claimed formalization of the
published linear-forms-in-logarithms theorem. All analytic implications,
the actual scale choice, and both changes of index are proved here.
-/

namespace RiemannResearch.RH.Pareto
open Filter
noncomputable section

/-- Cofinite prime indexing is precisely the usual natural-number filter
restricted to primes, so no ordering convention for the prime subtype is needed. -/
theorem prime_cofinite_map_eq :
    Filter.map (fun p : Nat.Primes => p.val) Filter.cofinite =
      Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime} := by
  have hi : Function.Injective (fun p : Nat.Primes => p.val) :=
    fun _ _ he => Subtype.ext he
  have hrange : Set.range (fun p : Nat.Primes => p.val) = {p : ℕ | p.Prime} := by
    ext n
    constructor
    · rintro ⟨p, rfl⟩
      exact p.property
    · intro hn
      exact ⟨⟨n, hn⟩, rfl⟩
  calc
    _ = Filter.map (fun p : Nat.Primes => p.val)
        (Filter.comap (fun p : Nat.Primes => p.val) Filter.cofinite) := by
      rw [hi.comap_cofinite_eq]
    _ = Filter.cofinite ⊓ Filter.principal (Set.range (fun p : Nat.Primes => p.val)) :=
      Filter.map_comap _ _
    _ = _ := by rw [Nat.cofinite_eq_atTop, hrange]

/-- The exact target from §5 follows once the missing published quantitative
smooth-gap bound is supplied. No estimate about repair variances, no ratio
limit, and no summability statement is assumed. -/
theorem summablePrimeRepairs_of_leastSmooth35_log_gap
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hgap : ∀ᶠ p : ℕ in Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime},
      ((leastSmooth35Above p - p : ℕ) : ℝ) / p ≤
        C / (Real.log (p : ℝ))^η) :
    ResearchTargets.SummablePrimeRepairs := by
  let h : Nat.Primes → ℕ := fun p => leastSmooth35Above p.val - p.val
  have heq (p : Nat.Primes) : p.val + h p = leastSmooth35Above p.val := by
    dsimp [h]
    have he := (leastSmooth35Above_spec p.val).1
    omega
  have hpos (p : Nat.Primes) : 0 < h p := by
    dsimp [h]
    have he := (leastSmooth35Above_spec p.val).1
    omega
  have hgap' : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      0 < h p ∧ (h p : ℝ) / p.val ≤ C / (Real.log (p.val : ℝ))^η := by
    rw [← prime_cofinite_map_eq] at hgap
    have hg := Filter.eventually_map.mp hgap
    filter_upwards [hg] with p hp
    exact ⟨hpos p, hp⟩
  have hmain := prime_repairs_limit_and_summable_of_log_gap h C η hC hη hgap'
  refine ⟨leastSmooth35Above, ?_, ?_, ?_⟩
  · intro p _ _
    exact leastSmooth35Above_spec p
  · rw [← prime_cofinite_map_eq, Filter.tendsto_map'_iff]
    change Filter.Tendsto
      (fun p : Nat.Primes => (leastSmooth35Above p.val : ℝ) / (p.val : ℝ))
      Filter.cofinite (nhds 1)
    simpa only [heq] using hmain.1
  · have hs : Summable (fun p : Nat.Primes =>
        paretoVariance (arithmeticRepair 2 p.val (leastSmooth35Above p.val))) := by
      simpa only [heq] using hmain.2
    let inc : {p : ℕ // p.Prime ∧ 7 ≤ p} → Nat.Primes :=
      fun p => ⟨p.val, p.property.1⟩
    have hi : Function.Injective inc := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun p : Nat.Primes => p.val) hab
    convert hs.comp_injective hi using 1 <;> rfl

end
end RiemannResearch.RH.Pareto
