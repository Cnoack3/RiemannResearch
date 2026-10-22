import RiemannResearch.RH.PrimeValuationIndependence
import RiemannResearch.RH.FinitePrimeDivisibilityMoments
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.CRTGCDGram
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual-prime likelihood, squarefree moments, and CRT identification

The finite Boolean product law is transported to integrals for the actual
inverse-square probability measure. Squarefree conductors are products of
*distinct actual primes*. Every differentiated residue identity retains its
full cross term. These finite identities assert no approximation or RH result.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace RiemannResearch.RH.ZetaTwoProbability
open FinitePrimeLikelihood

section FinitePrimes
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

/-- The natural-number squarefree conductor indexed by a finite set of primes. -/
def conductor (A : Finset ι) : ℕ := ∏ i ∈ A, p i

/-- The actual Boolean divisibility configuration of a positive integer. -/
def primeConfiguration (k : ℕ+) : ι → Bool := fun i => divisibilityBool (p i) k

/-- Every finite-configuration observable belongs to every Lᵣ space, including
L² and L∞. No independence or primality is needed for this boundedness fact. -/
theorem memLp_primeConfiguration (f : (ι → Bool) → ℝ) (r : ℝ≥0∞) :
    MemLp (fun k : ℕ+ => f (primeConfiguration p k)) r Q := by
  apply MemLp.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable
    (∑ b : ι → Bool, ‖f b‖)
  apply Filter.Eventually.of_forall
  intro k
  exact Finset.single_le_sum (fun b _ => norm_nonneg (f b))
    (Finset.mem_univ (primeConfiguration p k))

theorem integrable_primeConfiguration (f : (ι → Bool) → ℝ) :
    Integrable (fun k : ℕ+ => f (primeConfiguration p k)) Q :=
  memLp_one_iff_integrable.mp (memLp_primeConfiguration p f 1)

include hp hinj

/-- Every function of a finite actual prime configuration has the finite
Boolean expectation already used by the likelihood and moment modules. -/
theorem integral_primeConfiguration (f : (ι → Bool) → ℝ) :
    (∫ k : ℕ+, f (primeConfiguration p k) ∂Q) =
      tensorExpectation (fun i => primeParameter (p i : ℝ)) f := by
  let X : ℕ+ → (ι → Bool) := primeConfiguration p
  have hX : Measurable X := measurable_of_countable X
  calc
    (∫ k : ℕ+, f (primeConfiguration p k) ∂Q) =
        ∫ b, f b ∂Measure.map X Q :=
      (integral_map_of_stronglyMeasurable hX StronglyMeasurable.of_discrete).symm
    _ = ∑ b, (Measure.map X Q).real {b} * f b := by
      simpa only [smul_eq_mul] using
        (integral_fintype (μ := Measure.map X Q) (f := f) Integrable.of_finite)
    _ = tensorExpectation (fun i => primeParameter (p i : ℝ)) f := by
      apply Finset.sum_congr rfl
      intro b _
      rw [measureReal_def, Measure.map_apply hX (measurableSet_singleton b)]
      change (Q {k | (fun i => divisibilityBool (p i) k) = b}).toReal * f b = _
      rw [measure_boolean_configuration p hp hinj b]
      rw [ENNReal.toReal_ofReal (productMass_nonneg _
        (fun i => (primeParameter_mem_unitInterval
          (by exact_mod_cast (hp i).one_le)).1)
        (fun i => (primeParameter_mem_unitInterval
          (by exact_mod_cast (hp i).one_le)).2) b)]

omit hinj [Fintype ι] [DecidableEq ι] in
private theorem prime_cast_ne_zero (i : ι) : (p i : ℝ) ≠ 0 := by
  exact_mod_cast (hp i).ne_zero

omit hp hinj [Fintype ι] [DecidableEq ι] in
private theorem prime_cast_add_one_ne_zero (i : ι) : (p i : ℝ) + 1 ≠ 0 := by
  positivity

/-- The actual likelihood has expectation one. -/
theorem integral_finiteLikelihood :
    (∫ k : ℕ+, finiteLikelihood (fun i => (p i : ℝ)) (primeConfiguration p k) ∂Q) = 1 := by
  rw [integral_primeConfiguration p hp hinj (finiteLikelihood (fun i => (p i : ℝ)))]
  exact expect_finiteLikelihood _ (prime_cast_ne_zero p hp) (prime_cast_add_one_ne_zero p)

/-- Its exact second moment retains its dimension dependence. -/
theorem integral_finiteLikelihood_sq :
    (∫ k : ℕ+, finiteLikelihood (fun i => (p i : ℝ)) (primeConfiguration p k) ^ 2 ∂Q) =
      2 ^ Fintype.card ι * baseRatio (fun i => (p i : ℝ)) := by
  rw [integral_primeConfiguration p hp hinj (fun b => finiteLikelihood (fun i => (p i : ℝ)) b ^ 2)]
  exact expect_finiteLikelihood_sq _ (prime_cast_ne_zero p hp) (prime_cast_add_one_ne_zero p)

/-- The actual change of law from success probability p⁻² to p⁻¹. -/
theorem integral_finiteLikelihood_tilt (f : (ι → Bool) → ℝ) :
    (∫ k : ℕ+, finiteLikelihood (fun i => (p i : ℝ)) (primeConfiguration p k) *
      f (primeConfiguration p k) ∂Q) =
      tensorExpectation (fun i => 1 / (p i : ℝ)) f := by
  rw [integral_primeConfiguration p hp hinj (fun b => finiteLikelihood (fun i => (p i : ℝ)) b * f b)]
  exact tensorExpectation_tilt _ (prime_cast_ne_zero p hp) (prime_cast_add_one_ne_zero p) f

omit hp hinj [Fintype ι] [DecidableEq ι] in
/-- The real product in the finite algebra is the cast of the actual conductor. -/
theorem subsetProduct_eq_conductor (A : Finset ι) :
    subsetProduct (fun i => (p i : ℝ)) A = (conductor p A : ℝ) := by
  simp [subsetProduct, conductor]

omit [Fintype ι] [DecidableEq ι] in
private theorem prime_pairwise_coprime (A : Finset ι) :
    Set.Pairwise (A : Set ι) (fun i j => Nat.Coprime (p i) (p j)) := by
  intro i _ j _ hij
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

omit [Fintype ι] [DecidableEq ι] in
/-- No repeated prime factors occur in the actual conductor. -/
theorem conductor_squarefree (A : Finset ι) : Squarefree (conductor p A) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp (prime_pairwise_coprime p hp hinj A hi hj hij)
  · intro i _
    exact (hp i).squarefree

omit hinj [Fintype ι] [DecidableEq ι] in
theorem conductor_pos (A : Finset ι) : 0 < conductor p A := by
  exact Finset.prod_pos (fun i _ => (hp i).pos)

omit [Fintype ι] [DecidableEq ι] in
/-- Products of distinct primes divide exactly when all their factors divide. -/
theorem conductor_dvd_iff (A : Finset ι) (n : ℕ) :
    conductor p A ∣ n ↔ ∀ i ∈ A, p i ∣ n := by
  constructor
  · intro h i hi
    exact (Finset.dvd_prod_of_mem p hi).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp (prime_pairwise_coprime p hp hinj A hi hj hij)

omit [Fintype ι] in
/-- Set union is exactly least common multiple for actual squarefree conductors. -/
theorem conductor_union_eq_lcm (A B : Finset ι) :
    conductor p (A ∪ B) = Nat.lcm (conductor p A) (conductor p B) := by
  apply Nat.dvd_antisymm
  · apply (conductor_dvd_iff p hp hinj (A ∪ B) _).2
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.dvd_prod_of_mem p hi).trans (Nat.dvd_lcm_left _ _)
    · exact (Finset.dvd_prod_of_mem p hi).trans (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · apply (conductor_dvd_iff p hp hinj A _).2
      intro i hi
      exact Finset.dvd_prod_of_mem p (Finset.mem_union_left B hi)
    · apply (conductor_dvd_iff p hp hinj B _).2
      intro i hi
      exact Finset.dvd_prod_of_mem p (Finset.mem_union_right A hi)

/-- The formal Boolean monomial is the literal integer divisibility indicator. -/
theorem finiteMonomial_primeConfiguration (A : Finset ι) (k : ℕ+) :
    finiteMonomial A (primeConfiguration p k) =
      if conductor p A ∣ (k : ℕ) then 1 else 0 := by
  unfold finiteMonomial
  rw [Fintype.prod_extend_by_one]
  simp only [primeConfiguration, divisibilityBool, FinitePrimeLikelihood.boolIndicator, decide_eq_true_eq]
  rw [Finset.prod_boole]
  simp only [← conductor_dvd_iff p hp hinj]

/-- Divisibility by the squarefree conductor has the exact inverse-square mass. -/
theorem integral_conductor_indicator (A : Finset ι) :
    (∫ k : ℕ+, (if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0) ∂Q) =
      1 / (conductor p A : ℝ)^2 := by
  simp_rw [← finiteMonomial_primeConfiguration p hp hinj A]
  rw [integral_primeConfiguration p hp hinj (finiteMonomial A), expect_prime_finiteMonomial,
    subsetProduct_eq_conductor]

/-- Joint actual squarefree divisibility uses the least common multiple. -/
theorem integral_conductor_indicator_mul (A B : Finset ι) :
    (∫ k : ℕ+, (if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0) *
      (if conductor p B ∣ (k : ℕ) then (1 : ℝ) else 0) ∂Q) =
      1 / (Nat.lcm (conductor p A) (conductor p B) : ℝ)^2 := by
  simp_rw [← finiteMonomial_primeConfiguration p hp hinj]
  rw [integral_primeConfiguration p hp hinj (fun b => finiteMonomial A b * finiteMonomial B b), expect_prime_finiteMonomial_mul,
    subsetProduct_eq_conductor, conductor_union_eq_lcm p hp hinj]

/-- The likelihood tilts squarefree divisibility mass from d⁻² to d⁻¹. -/
theorem integral_finiteLikelihood_conductor_indicator (A : Finset ι) :
    (∫ k : ℕ+, finiteLikelihood (fun i => (p i : ℝ)) (primeConfiguration p k) *
      (if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0) ∂Q) =
      1 / (conductor p A : ℝ) := by
  simp_rw [← finiteMonomial_primeConfiguration p hp hinj A]
  rw [integral_primeConfiguration p hp hinj (fun b => finiteLikelihood (fun i => (p i : ℝ)) b * finiteMonomial A b),
    expect_finiteLikelihood_monomial _ (prime_cast_ne_zero p hp) (prime_cast_add_one_ne_zero p)]
  simp [conductor]

/-- Literal arithmetic derivative of the normalized residue atom. -/
def divisibilityDerivative (d : ℕ) (k : ℕ+) : ℝ :=
  1 / (d : ℝ) - if d ∣ (k : ℕ) then 1 else 0

omit hp hinj in
/-- Identification with the differentiated residue atom, pointwise at every
positive integer; no integration or closure assertion is used. -/
theorem residueFraction_difference (d : ℕ) (hd : 0 < d) (k : ℕ+) :
    ArithmeticCumulative.residueFraction d (k : ℕ) -
      ArithmeticCumulative.residueFraction d ((k : ℕ) - 1) =
      divisibilityDerivative d k := by
  change Pareto.residue d (k : ℕ) / (d : ℝ) -
    Pareto.residue d ((k : ℕ) - 1) / (d : ℝ) = _
  rw [← sub_div, Pareto.residue_difference d (k : ℕ) k.pos]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  by_cases h : d ∣ (k : ℕ) <;> simp [divisibilityDerivative, h, sub_div, hdR]

/-- The finite Boolean derivative is the actual squarefree residue derivative. -/
theorem finiteDerivativeAtom_primeConfiguration (A : Finset ι) (k : ℕ+) :
    finiteDerivativeAtom (fun i => (p i : ℝ)) A (primeConfiguration p k) =
      divisibilityDerivative (conductor p A) k := by
  rw [finiteDerivativeAtom, subsetProduct_eq_conductor,
    finiteMonomial_primeConfiguration p hp hinj]
  rfl

/-- Exact actual mean of the normalized residue derivative. -/
theorem integral_divisibilityDerivative (A : Finset ι) :
    (∫ k : ℕ+, divisibilityDerivative (conductor p A) k ∂Q) =
      1 / (conductor p A : ℝ) - 1 / (conductor p A : ℝ)^2 := by
  simp_rw [← finiteDerivativeAtom_primeConfiguration p hp hinj]
  rw [integral_primeConfiguration p hp hinj (finiteDerivativeAtom (fun i => (p i : ℝ)) A), expect_finiteDerivativeAtom,
    subsetProduct_eq_conductor]

/-- Exact actual differentiated Gram entry, including the shared-prime lcm term. -/
theorem integral_divisibilityDerivative_mul (A B : Finset ι) :
    (∫ k : ℕ+, divisibilityDerivative (conductor p A) k *
      divisibilityDerivative (conductor p B) k ∂Q) =
      1 / ((conductor p A : ℝ) * (conductor p B : ℝ))
      - 1 / ((conductor p A : ℝ) * (conductor p B : ℝ)^2)
      - 1 / ((conductor p A : ℝ)^2 * (conductor p B : ℝ))
      + 1 / (Nat.lcm (conductor p A) (conductor p B) : ℝ)^2 := by
  simp_rw [← finiteDerivativeAtom_primeConfiguration p hp hinj]
  rw [integral_primeConfiguration p hp hinj (fun b => finiteDerivativeAtom (fun i => (p i : ℝ)) A b *
      finiteDerivativeAtom (fun i => (p i : ℝ)) B b), finiteDerivativeGram]
  simp_rw [subsetProduct_eq_conductor, conductor_union_eq_lcm p hp hinj]

/-- Exact norm square in the normalized inverse-square measure. -/
theorem integral_divisibilityDerivative_sq (A : Finset ι) :
    (∫ k : ℕ+, divisibilityDerivative (conductor p A) k ^ 2 ∂Q) =
      2 * ((conductor p A : ℝ) - 1) / (conductor p A : ℝ)^3 := by
  simp_rw [← finiteDerivativeAtom_primeConfiguration p hp hinj]
  rw [integral_primeConfiguration p hp hinj (fun b => finiteDerivativeAtom (fun i => (p i : ℝ)) A b ^ 2), expect_finiteDerivativeAtom_sq,
    subsetProduct_eq_conductor]

/-- Actual likelihood orthogonality to each squarefree residue derivative. -/
theorem integral_finiteLikelihood_divisibilityDerivative (A : Finset ι) :
    (∫ k : ℕ+, finiteLikelihood (fun i => (p i : ℝ)) (primeConfiguration p k) *
      divisibilityDerivative (conductor p A) k ∂Q) = 0 := by
  simp_rw [← finiteDerivativeAtom_primeConfiguration p hp hinj]
  rw [integral_primeConfiguration p hp hinj (fun b => finiteLikelihood (fun i => (p i : ℝ)) b *
      finiteDerivativeAtom (fun i => (p i : ℝ)) A b)]
  exact likelihood_orthogonal_finiteDerivativeAtom _
    (prime_cast_ne_zero p hp) (prime_cast_add_one_ne_zero p) A

end FinitePrimes

/-- The CRT reference form and the probability law use the very same normalizer. -/
theorem zetaTwoSeries_eq_zetaTwo : Pareto.CRTSparseEnergy.zetaTwoSeries = zetaTwo :=
  zetaTwo_eq_nat_sum.symm

/-- Exact normalized form of the repository's existing CRT/GCD Gram kernel. -/
theorem gcdReferenceKernel_div_zetaTwo (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    Pareto.CRTSparseEnergy.gcdReferenceKernel d e / zetaTwo =
      (d : ℝ) * (e : ℝ) / (Nat.lcm d e : ℝ)^2 := by
  rw [Pareto.CRTSparseEnergy.gcdReferenceKernel_lcm d e (Nat.lcm_pos hd he),
    zetaTwoSeries_eq_zetaTwo]
  field_simp [ne_of_gt zetaTwo_pos]

/-- The pre-existing CRT Gram kernel is the unnormalized Gram matrix of
these actual integer divisibility variables. -/
theorem integral_scaled_conductorIndicators
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A B : Finset ι) :
    (∫ k : ℕ+,
      ((conductor p A : ℝ) * (if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0)) *
      ((conductor p B : ℝ) * (if conductor p B ∣ (k : ℕ) then (1 : ℝ) else 0)) ∂Q) =
      Pareto.CRTSparseEnergy.gcdReferenceKernel (conductor p A) (conductor p B) /
        zetaTwo := by
  have hpoint :
      (fun k : ℕ+ =>
        ((conductor p A : ℝ) * (if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0)) *
        ((conductor p B : ℝ) * (if conductor p B ∣ (k : ℕ) then (1 : ℝ) else 0))) =
      (fun k : ℕ+ => ((conductor p A : ℝ) * (conductor p B : ℝ)) *
        ((if conductor p A ∣ (k : ℕ) then (1 : ℝ) else 0) *
          (if conductor p B ∣ (k : ℕ) then (1 : ℝ) else 0))) := by
    funext k
    ring
  rw [hpoint, integral_const_mul, integral_conductor_indicator_mul p hp hinj,
    gcdReferenceKernel_div_zetaTwo _ _ (conductor_pos p hp A) (conductor_pos p hp B)]
  ring

end RiemannResearch.RH.ZetaTwoProbability
