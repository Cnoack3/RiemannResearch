import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.RH.QParetoEquivalence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full-conductor density after reciprocal damping

Source: the user's reciprocal-density argument, strengthened by the finite
factorial Möbius sieve already formalized in QPrimeSieve and
Analysis.NoorLogarithmDensity. The latter supports the elementary sieve proof
strategy; this module applies it to cumulative residue atoms.

Every full conductor is retained. The exact sieve is a nonnegative coprime
count divided by the physical index, bounded by 1/m; its pointwise limit is
the reciprocal tail at m. Dominated convergence gives the actual complete
Q norm limit. Differences of successive tails isolate every point vector.
The final density theorem transfers to the identical physical family in P.
The correctly damped constant D1 also belongs to the squarefree D-closure.
These statements do not bound the unsmoothed legal preimages.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QReciprocalFullDensity
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric ArithmeticCumulative QPrimeSieve

def floorAtom (m : ℕ) : QHilbert := (1 / (m : ℝ)) • qOne - D (qResidue m)

theorem floorAtom_sequence (m : ℕ) (hm : 0 < m) (n : ℕ) :
    qSequence (floorAtom m) n = ((n / m : ℕ) : ℝ) / (n : ℝ) := by
  change qSequenceLinear ((1 / (m : ℝ)) • qOne - D (qResidue m)) n = _
  rw [map_sub, map_smul]
  change (1 / (m : ℝ)) * qSequence qOne n - qSequence (D (qResidue m)) n = _
  rw [qSequence_D, qSequence_qResidue, qSequence_qOne]
  by_cases hn : n = 0
  · simp [hn, qOneSequence, residueFraction]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have he : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n m
  simp only [qOneSequence, if_neg hn, mul_one, residueFraction]
  field_simp
  nlinarith

theorem finite_floor_sieve (L r : ℕ) (hL : L ≠ 0) :
    (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
      ((r / d : ℕ) : ℝ)) = coprimeCount L r := by
  calc
    _ = ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        cumulative (divisorIndicator d) r := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [cumulative_divisorIndicator d r (Nat.pos_of_mem_divisors hd)]
    _ = cumulative (fun k => ∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d k) r := by
      simp only [cumulative, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = coprimeCount L r := by simp only [divisor_sift L _ hL, coprimeCount]

def factorialSieve (N m : ℕ) : QHilbert :=
  ∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) • floorAtom (m * d)

theorem factorialSieve_sequence (N m : ℕ) (hm : 0 < m) (n : ℕ) :
    qSequence (factorialSieve N m) n = coprimeCount N.factorial (n / m) / (n : ℝ) := by
  calc
    _ = ∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((n / m / d : ℕ) : ℝ) / (n : ℝ)) := by
      change qSequenceLinear (∑ d ∈ N.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) • floorAtom (m * d)) n = _
      rw [map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      change (ArithmeticFunction.moebius d : ℝ) * qSequence (floorAtom (m*d)) n = _
      rw [floorAtom_sequence (m * d) (Nat.mul_pos hm (Nat.pos_of_mem_divisors hd))]
      rw [Nat.div_div_eq_div_mul]
    _ = (∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((n / m / d : ℕ) : ℝ)) / (n : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [finite_floor_sieve _ _ (Nat.factorial_ne_zero N)]

theorem coprimeCount_bounds (L r : ℕ) :
    0 ≤ coprimeCount L r ∧ coprimeCount L r ≤ (r : ℝ) := by
  unfold coprimeCount cumulative
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    dsimp only
    split_ifs <;> norm_num
  · calc
      _ ≤ ∑ _k ∈ Finset.range r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        dsimp only
        split_ifs <;> norm_num
      _ = _ := by simp

theorem factorialSieve_bounds (N m : ℕ) (hm : 0 < m) (n : ℕ) :
    0 ≤ qSequence (factorialSieve N m) n ∧
      qSequence (factorialSieve N m) n ≤ 1 / (m : ℝ) := by
  rw [factorialSieve_sequence N m hm n]
  have hc := coprimeCount_bounds N.factorial (n / m)
  constructor
  · exact div_nonneg hc.1 (Nat.cast_nonneg n)
  · by_cases hn : n = 0
    · simp [hn]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    apply (div_le_iff₀ hnR).mpr
    have hdiv : ((n / m : ℕ) : ℝ) * (m : ℝ) ≤ n := by
      exact_mod_cast Nat.div_mul_le_self n m
    have hb : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m :=
      (le_div_iff₀ hmR).mpr hdiv
    calc
      coprimeCount N.factorial (n / m) ≤ (n : ℝ) / m := hc.2.trans hb
      _ = 1 / (m : ℝ) * (n : ℝ) := by ring

def tailSequence (m n : ℕ) : ℝ := if m ≤ n then 1 / (n : ℝ) else 0

theorem tailSequence_bounds (m n : ℕ) :
    0 ≤ tailSequence m n ∧ tailSequence m n ≤ 1 := by
  unfold tailSequence
  split_ifs
  · by_cases hn : n = 0
    · simp [hn]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact ⟨by positivity, (div_le_one hnR).mpr hn1⟩
  · norm_num

def tailVector (m : ℕ) : QHilbert :=
  encodeQ (tailSequence m) (boundedQ_square_summable _ 1 zero_le_one (by
    intro n
    rw [abs_of_nonneg (tailSequence_bounds m n).1]
    exact (tailSequence_bounds m n).2))

theorem tailVector_sequence (m n : ℕ) :
    qSequence (tailVector m) n = tailSequence m n := by
  exact congrFun (qSequence_encodeQ _ _ (by simp [tailSequence])) n

theorem factorialSieve_eventually (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      qSequence (factorialSieve N m) n = qSequence (tailVector m) n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [factorialSieve_sequence N m hm n, tailVector_sequence]
  by_cases hmn : m ≤ n
  · have hr : 0 < n / m := Nat.div_pos hmn hm
    rw [coprimeCount_head N.factorial N (n / m) hr
      ((Nat.div_le_self n m).trans hN) (factorial_covers_head N)]
    simp [tailSequence, hmn]
  · have hr : n / m = 0 := Nat.div_eq_of_lt (by omega)
    simp [hr, coprimeCount, cumulative, tailSequence, hmn]

theorem factorialSieve_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N => factorialSieve N m) atTop (𝓝 (tailVector m)) := by
  let e : ℕ → ℕ → ℝ := fun N n =>
    positiveQWeight n * (qSequence (factorialSieve N m - tailVector m) n)^2
  have hseq (N n : ℕ) :
      qSequence (factorialSieve N m - tailVector m) n =
        qSequence (factorialSieve N m) n - qSequence (tailVector m) n := by
    change qSequenceLinear (_ - _) n = _
    rw [map_sub]
    rfl
  have hpoint (n : ℕ) : Tendsto (fun N => e N n) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [factorialSieve_eventually m hm n] with N hN
    simp only [e, hseq, hN, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ n, ‖e N n‖ ≤ positiveQWeight n := by
    apply Eventually.of_forall
    intro N n
    have hb := factorialSieve_bounds N m hm n
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hb1 : qSequence (factorialSieve N m) n ≤ 1 :=
      hb.2.trans ((div_le_one hmR).mpr hm1)
    have ht := tailSequence_bounds m n
    rw [← tailVector_sequence m n] at ht
    have ha : |qSequence (factorialSieve N m) n - qSequence (tailVector m) n| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hb.1, ht.2], by linarith [ht.1, hb1]⟩
    have hs : (qSequence (factorialSieve N m - tailVector m) n)^2 ≤ 1 := by
      rw [hseq]
      have hh := mul_le_mul ha ha (abs_nonneg _) zero_le_one
      simpa only [← pow_two, sq_abs, one_pow] using hh
    change |positiveQWeight n * _| ≤ _
    rw [abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))]
    exact mul_le_of_le_one_right (positiveQWeight_nonneg n) hs
  have ht := tendsto_tsum_of_dominated_convergence
    (g := fun _ : ℕ => (0 : ℝ)) positiveQWeight_summable hpoint hbound
  have hs : Tendsto (fun N => ‖factorialSieve N m - tailVector m‖^2) atTop (𝓝 0) := by
    simpa only [e, ← qNorm_weighted_sq, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

theorem floorAtom_mem (K : Submodule ℝ QHilbert) (h1 : qOne ∈ K)
    (hg : ∀ k, 2 ≤ k → D (qResidue k) ∈ K) (m : ℕ) (hm : 0 < m) :
    floorAtom m ∈ K := by
  have hg1 : qResidue 1 = 0 := by simp
  apply K.sub_mem (K.smul_mem _ h1)
  by_cases h : m = 1
  · simp [h, hg1]
  · exact hg m (by omega)

theorem tailVector_mem (K : Submodule ℝ QHilbert) (hK : IsClosed (K : Set QHilbert))
    (h1 : qOne ∈ K) (hg : ∀ k, 2 ≤ k → D (qResidue k) ∈ K)
    (m : ℕ) (hm : 0 < m) : tailVector m ∈ K := by
  apply hK.mem_of_tendsto (factorialSieve_tendsto m hm)
  apply Eventually.of_forall
  intro N
  apply K.sum_mem
  intro d hd
  exact K.smul_mem _ (floorAtom_mem K h1 hg (m*d)
    (Nat.mul_pos hm (Nat.pos_of_mem_divisors hd)))

theorem qPoint_eq_tail_difference (k : ℕ) :
    qPoint k = ((k+1 : ℕ) : ℝ) • (tailVector (k+1) - tailVector (k+2)) := by
  apply qSequence_injective
  funext n
  change qSequence (qPoint k) n = qSequenceLinear (_ • (_ - _)) n
  rw [map_smul, map_sub]
  change qSequence (qPoint k) n = ((k+1 : ℕ) : ℝ) *
    (qSequence (tailVector (k+1)) n - qSequence (tailVector (k+2)) n)
  rw [qSequence_qPoint, tailVector_sequence, tailVector_sequence]
  by_cases hnk : n = k+1
  · subst n
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    simp [qPointSequence, tailSequence, hk]
  · by_cases hsmall : n < k+1
    · simp [qPointSequence, tailSequence, hnk, show ¬ k+1 ≤ n by omega,
        show ¬ k+2 ≤ n by omega]
    · simp [qPointSequence, tailSequence, hnk, show k+1 ≤ n by omega,
        show k+2 ≤ n by omega]

theorem closed_eq_top_of_reciprocal_residues
    (K : Submodule ℝ QHilbert) (hK : IsClosed (K : Set QHilbert))
    (h1 : qOne ∈ K) (hg : ∀ k, 2 ≤ k → D (qResidue k) ∈ K) : K = ⊤ := by
  have hpoints : Submodule.span ℝ (Set.range qPoint) ≤ K := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, rfl⟩
    rw [qPoint_eq_tail_difference k]
    exact K.smul_mem _ (K.sub_mem (tailVector_mem K hK h1 hg (k+1) (by omega))
      (tailVector_mem K hK h1 hg (k+2) (by omega)))
  have hc := (Submodule.span ℝ (Set.range qPoint)).topologicalClosure_minimal hpoints hK
  rw [QExactHeadAverages.qPoint_span_dense] at hc
  exact top_unique hc

theorem tailVector_one_eq_D_one : tailVector 1 = D qOne := by
  apply qSequence_injective
  funext n
  rw [tailVector_sequence, qSequence_D, qSequence_qOne]
  cases n with
  | zero => simp [tailSequence, qOneSequence]
  | succ n => simp [tailSequence, qOneSequence]

/-- The correctly damped constant target is approximable even using squarefree atoms. -/
theorem D_one_mem_of_squarefree_residues
    (K : Submodule ℝ QHilbert) (hK : IsClosed (K : Set QHilbert))
    (h1 : qOne ∈ K)
    (hg : ∀ k, 2 ≤ k → Squarefree k → D (qResidue k) ∈ K) : D qOne ∈ K := by
  rw [← tailVector_one_eq_D_one]
  apply hK.mem_of_tendsto (factorialSieve_tendsto 1 (by omega))
  apply Eventually.of_forall
  intro N
  apply K.sum_mem
  intro d hd
  by_cases hs : Squarefree d
  · apply K.smul_mem
    rw [one_mul]
    apply K.sub_mem (K.smul_mem _ h1)
    by_cases h : d = 1
    · simp [h]
    · exact hg d (by have := Nat.pos_of_mem_divisors hd; omega) hs
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

/-- Unconditional totality of the reciprocally damped full conductor dictionary. -/
theorem fullReciprocalClosure_eq_top :
    (Submodule.span ℝ {f : QHilbert | ∃ k : ℕ, 2 ≤ k ∧
      f = D (qResidue k)}).topologicalClosure = ⊤ := by
  let K : Submodule ℝ QHilbert :=
    (Submodule.span ℝ {f : QHilbert | ∃ k : ℕ, 2 ≤ k ∧
      f = D (qResidue k)}).topologicalClosure
  have hK : IsClosed (K : Set QHilbert) := Submodule.isClosed_topologicalClosure _
  have hg (k : ℕ) (hk : 2 ≤ k) : D (qResidue k) ∈ K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  apply closed_eq_top_of_reciprocal_residues K hK ?_ hg
  apply hK.mem_of_tendsto QDensityMetric.approximation_tendsto
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact K.smul_mem (k : ℝ) (hg k hk)

open Pareto ZetaTwoParetoTransfer QParetoEquivalence

/-- Identical physical generators are total also in the Pareto norm. -/
theorem pareto_fullReciprocalClosure_eq_top :
    ((Submodule.span ℝ {f : QHilbert | ∃ k : ℕ, 2 ≤ k ∧
      f = D (qResidue k)}).map paretoEquiv.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  intro f hf
  have hh : toQ f ∈ (Submodule.span ℝ {g : QHilbert | ∃ k : ℕ, 2 ≤ k ∧
      g = D (qResidue k)}).topologicalClosure := by
    rw [fullReciprocalClosure_eq_top]
    trivial
  have hp := (mem_closure_map_iff _ (toQ f)).mpr hh
  simpa only [toPareto_toQ] using hp

end RiemannResearch.RH.QReciprocalFullDensity
