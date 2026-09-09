import RiemannResearch.RH.PrimePhaseCRT
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.NumberTheory.Real.Irrational

/-!
# Dense-period rigidity for prime logarithms

Source: the two-seed adjoint-rigidity route in Christian Noack,
`RH_Two_Seed_Threshold.tex` (8 September 2026), together with Mathlib's
`dense_addSubgroupClosure_pair_iff`.  The project theorem
`PrimePhaseCRT.intPrimeLogRelation` supplies the arithmetic independence.

We prove that the logarithms of distinct primes have irrational ratio and
that a continuous profile with both prime-log periods is constant.  In
particular this discharges the continuous `log 2`/`log 3` period-rigidity
step.  It does not construct the continuous profile from an adjoint-fixed
Hilbert vector; the local-L2 limit and quantitative coordinate recovery
remain separate analytic obligations.
-/

namespace RiemannResearch.Analysis

open Set

/-- A continuous function with two periods whose ratio is irrational is
constant.  The proof closes the algebraic period group and then uses its
density together with continuity. -/
theorem continuous_eq_const_of_two_irrational_periods
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (hf : Continuous f)
    {a b : ℝ} (ha : Function.Periodic f a)
    (hb : Function.Periodic f b)
    (hirr : Irrational (a / b)) :
    ∀ x, f x = f 0 := by
  let P : AddSubgroup ℝ :=
    { carrier := {t | Function.Periodic f t}
      zero_mem' := by
        intro x
        simp
      add_mem' := by
        intro x y hx hy
        exact hx.add_period hy
      neg_mem' := by
        intro x hx
        exact hx.neg }
  have hgen : AddSubgroup.closure ({a, b} : Set ℝ) ≤ P := by
    apply (AddSubgroup.closure_le P).2
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with h | h
    · subst t
      exact ha
    · subst t
      exact hb
  have hdense : Dense (P : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff.mpr hirr).mono hgen
  intro x
  exact hdense.induction
    (fun t ht => by
      change Function.Periodic f t at ht
      simpa using ht 0)
    (isClosed_eq hf continuous_const) x

end RiemannResearch.Analysis

namespace RiemannResearch.RH.PrimePhaseCRT

/-- The logarithms of two distinct primes have irrational ratio. -/
theorem primeLogRatio_irrational {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log (p : ℝ) / Real.log (q : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq.one_lt
  have hlogq : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hq1)
  have hbR : (b : ℝ) ≠ 0 := by
    exact_mod_cast hb
  have hcross :
      Real.log (p : ℝ) * (b : ℝ) =
        (a : ℝ) * Real.log (q : ℝ) :=
    (div_eq_div_iff hlogq hbR).mp hab
  have hrel :
      (a : ℝ) * Real.log (q : ℝ) =
        (b : ℝ) * Real.log (p : ℝ) := by
    simpa [mul_comm] using hcross.symm
  have hz := intPrimeLogRelation hp hq hpq hrel
  exact hb hz.2

/-- A continuous profile invariant under the logarithmic periods of two
distinct primes is constant. -/
theorem continuous_primeLog_periods_constant
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (f : ℝ → Y) (hf : Continuous f)
    (hpPeriod : Function.Periodic f (Real.log (p : ℝ)))
    (hqPeriod : Function.Periodic f (Real.log (q : ℝ))) :
    ∀ x, f x = f 0 :=
  RiemannResearch.Analysis.continuous_eq_const_of_two_irrational_periods
    f hf hpPeriod hqPeriod (primeLogRatio_irrational hp hq hpq)

/-- The continuous `log 2`/`log 3` rigidity specialization used by the
two-seed program. -/
theorem continuous_twoSeed_log_periods_constant
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (hf : Continuous f)
    (h2 : Function.Periodic f (Real.log (2 : ℝ)))
    (h3 : Function.Periodic f (Real.log (3 : ℝ))) :
    ∀ x, f x = f 0 :=
  continuous_primeLog_periods_constant
    (by decide) (by decide) (by norm_num) f hf h2 h3

end RiemannResearch.RH.PrimePhaseCRT
