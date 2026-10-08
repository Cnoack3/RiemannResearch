import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.FinitePrimeLikelihood
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual prime valuations under the inverse-square integer law

The only probability input is `measure_dvd` from `ZetaTwoProbability`.
Independence is established for the actual valuation functions on positive
integers, by a generating pi-system argument. No approximation or RH claim
is made here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoProbability

/-- The prime exponent in a positive integer. -/
def primeValuation (p : ℕ) (k : ℕ+) : ℕ := (k : ℕ).factorization p

/-- The actual divisibility coordinate, with `true` denoting divisibility. -/
def divisibilityBool (p : ℕ) (k : ℕ+) : Bool := decide (p ∣ (k : ℕ))

theorem measure_primePower_dvd (p a : ℕ) (hp : p.Prime) :
    Q {k : ℕ+ | p ^ a ∣ (k : ℕ)} =
      ENNReal.ofReal (1 / ((p : ℝ) ^ a) ^ 2) := by
  simpa using measure_dvd (p ^ a) (pow_pos hp.pos a)

theorem measure_primeValuation_ge (p a : ℕ) (hp : p.Prime) :
    Q {k : ℕ+ | a ≤ primeValuation p k} =
      ENNReal.ofReal (1 / ((p : ℝ) ^ a) ^ 2) := by
  have heq : {k : ℕ+ | a ≤ primeValuation p k} =
      {k : ℕ+ | p ^ a ∣ (k : ℕ)} := by
    ext k
    exact (hp.pow_dvd_iff_le_factorization (ne_of_gt k.pos)).symm
  rw [heq, measure_primePower_dvd p a hp]

theorem measure_primeValuation_eq (p a : ℕ) (hp : p.Prime) :
    Q {k : ℕ+ | primeValuation p k = a} =
      ENNReal.ofReal ((1 - 1 / (p : ℝ) ^ 2) * (1 / ((p : ℝ) ^ a) ^ 2)) := by
  have heq : {k : ℕ+ | primeValuation p k = a} =
      {k : ℕ+ | a ≤ primeValuation p k} \
        {k : ℕ+ | a + 1 ≤ primeValuation p k} := by
    ext k
    simp only [mem_ofPred_eq, mem_sdiff]
    omega
  have hsub : {k : ℕ+ | a + 1 ≤ primeValuation p k} ⊆
      {k : ℕ+ | a ≤ primeValuation p k} := by
    intro k hk
    exact (Nat.le_succ a).trans hk
  rw [heq, measure_sdiff hsub (Set.to_countable _).measurableSet.nullMeasurableSet
    (measure_ne_top Q _), measure_primeValuation_ge p a hp,
    measure_primeValuation_ge p (a + 1) hp,
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [pow_succ]
  field_simp [hp0]
  ring

section Families

variable {ι : Type*}

/-- Distinct prime powers are pairwise coprime, including zero exponents. -/
theorem primePower_product_dvd_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (a : ι → ℕ) (s : Finset ι) (k : ℕ) :
    (∏ i ∈ s, p i ^ a i) ∣ k ↔ ∀ i ∈ s, p i ^ a i ∣ k := by
  constructor
  · intro h i hi
    exact (Finset.dvd_prod_of_mem (fun j => p j ^ a j) hi).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.coprime_pow_primes (a i) (a j) (hp i) (hp j)
        (fun h => hij (hinj h)))

/-- Every finite simultaneous valuation-tail event has the product mass. -/
theorem measure_primeValuation_joint_ge (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (a : ι → ℕ) (s : Finset ι) :
    Q (⋂ i ∈ s, {k : ℕ+ | a i ≤ primeValuation (p i) k}) =
      ∏ i ∈ s, ENNReal.ofReal (1 / ((p i : ℝ) ^ a i) ^ 2) := by
  have heq : (⋂ i ∈ s, {k : ℕ+ | a i ≤ primeValuation (p i) k}) =
      {k : ℕ+ | (∏ i ∈ s, p i ^ a i) ∣ (k : ℕ)} := by
    ext k
    simp only [mem_iInter, mem_ofPred_eq]
    rw [primePower_product_dvd_iff p hp hinj a s]
    exact forall_congr' fun i => forall_congr' fun _ =>
      ((hp i).pow_dvd_iff_le_factorization (ne_of_gt k.pos)).symm
  rw [heq, measure_dvd _ (Finset.prod_pos fun i _ => pow_pos (hp i).pos _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  simp [Nat.cast_prod, Nat.cast_pow, Finset.prod_pow, Finset.prod_inv_distrib]

private def valuationTailSystem (p : ℕ) : Set (Set ℕ+) :=
  Set.range (fun a : ℕ => {k : ℕ+ | a ≤ primeValuation p k})

private theorem valuationTailSystem_isPiSystem (p : ℕ) :
    IsPiSystem (valuationTailSystem p) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
  refine ⟨max a b, ?_⟩
  ext k
  simp

private theorem primeValuation_comap_generated (p : ℕ) :
    (inferInstance : MeasurableSpace ℕ).comap (primeValuation p) =
      MeasurableSpace.generateFrom (valuationTailSystem p) := by
  rw [@BorelSpace.measurable_eq ℕ _ _ _, borel_eq_generateFrom_Ici,
    MeasurableSpace.comap_generateFrom]
  congr 1
  ext t
  simp only [mem_image, mem_range, valuationTailSystem]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Set.Ici a, ⟨a, rfl⟩, rfl⟩

/-- The actual prime valuations are independent. The index type need not be finite. -/
theorem iIndepFun_primeValuation (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    iIndepFun (fun i => primeValuation (p i)) Q := by
  classical
  have htails : iIndepSets (fun i => valuationTailSystem (p i)) Q := by
    rw [iIndepSets_iff]
    intro s f hf
    have hchoose : ∀ i, ∃ a : ℕ, i ∈ s →
        {k : ℕ+ | a ≤ primeValuation (p i) k} = f i := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, ha⟩ := hf i hi
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => False.elim (hi h)⟩
    choose a ha using hchoose
    have hinter : (⋂ i ∈ s, f i) =
        ⋂ i ∈ s, {k : ℕ+ | a i ≤ primeValuation (p i) k} := by
      apply Set.iInter_congr
      intro i
      apply Set.iInter_congr
      intro hi
      exact (ha i hi).symm
    rw [hinter, measure_primeValuation_joint_ge p hp hinj a s]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← ha i hi, measure_primeValuation_ge (p i) (a i) (hp i)]
  exact htails.iIndep
    (fun i => (measurable_of_countable (primeValuation (p i))).comap_le)
    (fun i => valuationTailSystem (p i))
    (fun i => valuationTailSystem_isPiSystem (p i))
    (fun i => primeValuation_comap_generated (p i))

theorem iIndepFun_divisibilityBool (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    iIndepFun (fun i => divisibilityBool (p i)) Q := by
  have h := (iIndepFun_primeValuation p hp hinj).comp
    (fun (_ : ι) (a : ℕ) => decide (1 ≤ a))
    (fun _ => measurable_of_countable (fun a : ℕ => decide (1 ≤ a)))
  have heq : (fun i => divisibilityBool (p i)) =
      (fun i => (fun a : ℕ => decide (1 ≤ a)) ∘ primeValuation (p i)) := by
    funext i k
    simp only [divisibilityBool, Function.comp_apply, primeValuation]
    simp only [(hp i).dvd_iff_one_le_factorization (ne_of_gt k.pos)]
    rfl
  rw [heq]
  exact h

end Families

open FinitePrimeLikelihood

theorem measure_divisibilityBool (p : ℕ) (hp : p.Prime) (b : Bool) :
    Q {k : ℕ+ | divisibilityBool p k = b} =
      ENNReal.ofReal (bernoulliMass (primeParameter (p : ℝ)) b) := by
  cases b
  · have heq : {k : ℕ+ | divisibilityBool p k = false} =
        {k : ℕ+ | p ∣ (k : ℕ)}ᶜ := by
      ext k
      simp [divisibilityBool]
    rw [heq, measure_compl (Set.to_countable _).measurableSet (measure_ne_top Q _),
      measure_univ, measure_dvd p hp.pos]
    simp only [bernoulliMass, primeParameter, Bool.false_eq_true, ↓reduceIte]
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  · simpa [divisibilityBool, bernoulliMass, primeParameter] using measure_dvd p hp.pos

/-- The exact finite Boolean pushforward law for actual distinct primes. -/
theorem measure_boolean_configuration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (b : ι → Bool) :
    Q {k : ℕ+ | (fun i => divisibilityBool (p i) k) = b} =
      ENNReal.ofReal (productMass (fun i => primeParameter (p i : ℝ)) b) := by
  have heq : {k : ℕ+ | (fun i => divisibilityBool (p i) k) = b} =
      ⋂ i, {k : ℕ+ | divisibilityBool (p i) k = b i} := by
    ext k
    simp [funext_iff]
  rw [heq, (iIndepFun_divisibilityBool p hp hinj).meas_iInter]
  · simp_rw [measure_divisibilityBool _ (hp _) _]
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      bernoulliMass_nonneg
        (primeParameter_mem_unitInterval (by exact_mod_cast (hp i).one_le)).1
        (primeParameter_mem_unitInterval (by exact_mod_cast (hp i).one_le)).2 (b i)).symm
  · intro i
    exact (measurableSet_singleton (b i)).preimage (comap_measurable _)

/-- Finite exact valuation configurations have the product geometric law. -/
theorem measure_primeValuation_configuration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (a : ι → ℕ) :
    Q {k : ℕ+ | (fun i => primeValuation (p i) k) = a} =
      ∏ i, ENNReal.ofReal
        ((1 - 1 / (p i : ℝ) ^ 2) * (1 / ((p i : ℝ) ^ a i) ^ 2)) := by
  have heq : {k : ℕ+ | (fun i => primeValuation (p i) k) = a} =
      ⋂ i, {k : ℕ+ | primeValuation (p i) k = a i} := by
    ext k
    simp [funext_iff]
  rw [heq, (iIndepFun_primeValuation p hp hinj).meas_iInter]
  · simp_rw [measure_primeValuation_eq _ _ (hp _)]
  · intro i
    exact (measurableSet_singleton (a i)).preimage (comap_measurable _)

end RiemannResearch.RH.ZetaTwoProbability
