import RiemannResearch.CategoryTheory.AtomCarryPresentation
import RiemannResearch.NumberTheory.PrimePowerCRTDecomposition
import RiemannResearch.RH.ResidueAtomIndependence

/-!
# Finite conductor stages of the atom/carry CRT

Source: the user-provided categorical atom/carry argument (2026-11-17).
This specializes the presentation transform to actual normalized residue atoms,
using canonical maximal-prime-power CRT inverses and literal floor carries.
The resulting direct sum is algebraic; no weighted orthogonality or infinite
coordinate estimate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.FiniteAtomCarryCRT
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.NumberTheory.PrimePowerCRT
open RiemannResearch.CategoryTheory.AtomCarryPresentation

/-- Nontrivial prime-power divisors at a finite conductor stage. -/
def primeConductors (L : ℕ) : Finset ℕ :=
  L.divisors.filter (fun d => 1 < d ∧ d.primeFactors.card = 1)

/-- The cardinality definition is exactly the positive-prime-power dictionary. -/
theorem mem_primeConductors_iff (L d : ℕ) :
    d ∈ primeConductors L ↔
      d ∈ L.divisors ∧ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ d = p ^ k := by
  constructor
  · intro h
    obtain ⟨hd, hgt, hcard⟩ := Finset.mem_filter.mp h
    obtain ⟨p, hpSet⟩ := Finset.card_eq_one.mp hcard
    have hmem : p ∈ d.primeFactors := by rw [hpSet]; simp
    have hp := (Nat.mem_primeFactors.mp hmem).1
    have hd0 : d ≠ 0 := by omega
    refine ⟨hd, p, d.factorization p, hp,
      hp.factorization_pos_of_dvd hd0 (Nat.mem_primeFactors.mp hmem).2.1, ?_⟩
    have he := product_moduli d hd0
    simpa [hpSet, modulus] using he.symm
  · rintro ⟨hd, p, k, hp, hk, rfl⟩
    have hk0 : k ≠ 0 := ne_of_gt hk
    have hgt : 1 < p ^ k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [pow_succ]
      have hpos : 0 < p ^ j := pow_pos hp.pos _
      nlinarith [hp.two_le]
    exact Finset.mem_filter.mpr ⟨hd, hgt, by
      simp [Nat.primeFactors_prime_pow hk0 hp]⟩

/-- The complementary nontrivial divisors. -/
def mixedConductors (L : ℕ) : Finset ℕ :=
  L.divisors.filter (fun d => 1 < d ∧ d.primeFactors.card ≠ 1)

abbrev PrimeIndex (L : ℕ) := ↥(primeConductors L)
abbrev MixedIndex (L : ℕ) := ↥(mixedConductors L)

def primeAtom (L : ℕ) (i : PrimeIndex L) : ℕ → ℝ := residueFraction i.val
def mixedAtom (L : ℕ) (j : MixedIndex L) : ℕ → ℝ := residueFraction j.val
def carryVector (L : ℕ) (j : MixedIndex L) : ℕ → ℝ := fun n => canonicalCarry j.val n

def atomSpan (L : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ d ∈ L.divisors, 1 < d ∧ f = residueFraction d}

theorem combined_atoms_independent (L : ℕ) :
    LinearIndependent ℝ (Sum.elim (primeAtom L) (mixedAtom L)) := by
  let conductor : PrimeIndex L ⊕ MixedIndex L → ℕ := Sum.elim Subtype.val Subtype.val
  have hgt : ∀ i, 1 < conductor i := by
    intro i
    cases i with
    | inl i => exact (Finset.mem_filter.mp i.property).2.1
    | inr i => exact (Finset.mem_filter.mp i.property).2.1
  have hinj : Function.Injective conductor := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext hij)
      | inr j =>
        have hi := (Finset.mem_filter.mp i.property).2.2
        have hj := (Finset.mem_filter.mp j.property).2.2
        change i.val = j.val at hij
        exact (hj (by rw [← hij]; exact hi)).elim
    | inr i =>
      cases j with
      | inl j =>
        have hi := (Finset.mem_filter.mp i.property).2.2
        have hj := (Finset.mem_filter.mp j.property).2.2
        change i.val = j.val at hij
        exact (hi (by rw [hij]; exact hj)).elim
      | inr j => exact congrArg Sum.inr (Subtype.ext hij)
  have h := residueFraction_linearIndependent conductor hgt hinj
  convert h using 1
  funext i
  cases i <;> rfl

/-- Every complementary divisor has at least two distinct prime factors. -/
theorem mixed_card_ge_two (L : ℕ) (j : MixedIndex L) :
    2 ≤ j.val.primeFactors.card := by
  have hj := (Finset.mem_filter.mp j.property).2
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show j.val ≠ 1 by omega)
  have hmem : p ∈ j.val.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
  have hpos : 0 < j.val.primeFactors.card :=
    Finset.card_pos.mpr ⟨p, hmem⟩
  omega

/-- Every maximal prime-power input remains inside the same conductor stage. -/
def factorIndex (L : ℕ) (j : MixedIndex L) (p : j.val.primeFactors) : PrimeIndex L := by
  have hj := Finset.mem_filter.mp j.property
  have hpP := (Nat.mem_primeFactors.mp p.property).1
  have hpow : j.val.factorization p.val ≠ 0 := by
    intro h
    have hh := modulus_one_lt p.property
    simp [modulus, h] at hh
  refine ⟨modulus j.val p.val, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Nat.mem_divisors.mpr ⟨dvd_trans (modulus_dvd j.val p.val)
      (Nat.dvd_of_mem_divisors hj.1), (Nat.mem_divisors.mp hj.1).2⟩
  · exact ⟨modulus_one_lt p.property, by
      simp [modulus, Nat.primeFactors_prime_pow hpow hpP]⟩

/-- The explicit coefficient row of one canonical carry. -/
def rowCoefficients (L : ℕ) (j : MixedIndex L) (i : PrimeIndex L) : ℝ :=
  ∑ p : j.val.primeFactors,
    if i = factorIndex L j p then (coefficient j.val p.val : ℝ) else 0

theorem row_synthesis (L : ℕ) (j : MixedIndex L) (n : ℕ) :
    Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) n =
      ∑ p ∈ j.val.primeFactors, (coefficient j.val p : ℝ) *
        residueFraction (modulus j.val p) n := by
  classical
  simp only [Fintype.linearCombination_apply, rowCoefficients, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  have hinner (p : j.val.primeFactors) :
      (∑ i : PrimeIndex L,
        if i = factorIndex L j p then
          (coefficient j.val p.val : ℝ) * primeAtom L i n else 0) =
      (coefficient j.val p.val : ℝ) * residueFraction (modulus j.val p.val) n := by
    rw [Finset.sum_eq_single (factorIndex L j p)]
    · simp only [if_pos rfl]
      rfl
    · intro i hi hne
      rw [if_neg hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hinner]
  exact Finset.sum_coe_sort j.val.primeFactors
    (fun p : ℕ => (coefficient j.val p : ℝ) * residueFraction (modulus j.val p) n)

theorem carry_eq_row_sub_atom (L : ℕ) (j : MixedIndex L) :
    carryVector L j =
      Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) - mixedAtom L j := by
  funext n
  have hj := (Finset.mem_filter.mp j.property).2.1
  have h := atom_reconstruction j.val (by omega) n
  change (canonicalCarry j.val n : ℝ) =
    Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) n - residueFraction j.val n
  rw [row_synthesis]
  linarith

theorem atomSpan_eq_partition (L : ℕ) :
    atomSpan L = Submodule.span ℝ (Set.range (primeAtom L)) ⊔
      Submodule.span ℝ (Set.range (mixedAtom L)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨d, hd, hgt, rfl⟩
    by_cases hp : d.primeFactors.card = 1
    · have hi : residueFraction d ∈ Submodule.span ℝ (Set.range (primeAtom L)) :=
        Submodule.subset_span ⟨⟨d, Finset.mem_filter.mpr ⟨hd, hgt, hp⟩⟩, rfl⟩
      exact (le_sup_left : Submodule.span ℝ (Set.range (primeAtom L)) ≤
        Submodule.span ℝ (Set.range (primeAtom L)) ⊔
          Submodule.span ℝ (Set.range (mixedAtom L))) hi
    · have hi : residueFraction d ∈ Submodule.span ℝ (Set.range (mixedAtom L)) :=
        Submodule.subset_span ⟨⟨d, Finset.mem_filter.mpr ⟨hd, hgt, hp⟩⟩, rfl⟩
      exact (le_sup_right : Submodule.span ℝ (Set.range (mixedAtom L)) ≤
        Submodule.span ℝ (Set.range (primeAtom L)) ⊔
          Submodule.span ℝ (Set.range (mixedAtom L))) hi
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro f ⟨i, rfl⟩
      have hi := Finset.mem_filter.mp i.property
      exact Submodule.subset_span ⟨i.val, hi.1, hi.2.1, rfl⟩
    · apply Submodule.span_le.mpr
      rintro f ⟨i, rfl⟩
      have hi := Finset.mem_filter.mp i.property
      exact Submodule.subset_span ⟨i.val, hi.1, hi.2.1, rfl⟩

/-- Actual finite CRT synthesis spans: all atoms equal prime powers plus carries. -/
theorem atomSpan_eq_prime_sup_carry (L : ℕ) :
    atomSpan L = Submodule.span ℝ (Set.range (primeAtom L)) ⊔
      Submodule.span ℝ (Set.range (carryVector L)) := by
  rw [atomSpan_eq_partition]
  have h := family_crt_span (primeAtom L) (mixedAtom L) (rowCoefficients L)
  have he : (fun j => Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) -
      mixedAtom L j) = carryVector L := by
    funext j
    exact (carry_eq_row_sub_atom L j).symm
  simpa only [he] using h

/-- The actual prime-power/canonical-carry decomposition is algebraically direct. -/
theorem prime_carry_disjoint (L : ℕ) :
    Disjoint (Submodule.span ℝ (Set.range (primeAtom L)))
      (Submodule.span ℝ (Set.range (carryVector L))) := by
  have h := family_crt_disjoint (primeAtom L) (mixedAtom L) (rowCoefficients L)
    (combined_atoms_independent L)
  have he : (fun j => Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) -
      mixedAtom L j) = carryVector L := by
    funext j
    exact (carry_eq_row_sub_atom L j).symm
  simpa only [he] using h

/-- The concrete finite CRT change is an isomorphism of actual presentations. -/
def presentationIso (L : ℕ) :
    CategoryTheory.Iso
      (ofSynthesis ((Fintype.linearCombination ℝ (primeAtom L)).coprod
        (Fintype.linearCombination ℝ (mixedAtom L))))
      (ofSynthesis ((Fintype.linearCombination ℝ (primeAtom L)).coprod
        (Fintype.linearCombination ℝ (carryVector L)))) := by
  have he : (fun j => Fintype.linearCombination ℝ (primeAtom L) (rowCoefficients L j) -
      mixedAtom L j) = carryVector L := by
    funext j
    exact (carry_eq_row_sub_atom L j).symm
  have hc := family_carrySynthesis (primeAtom L) (mixedAtom L) (rowCoefficients L)
  rw [he] at hc
  simpa only [hc] using crtIso (Fintype.linearCombination ℝ (primeAtom L))
    (Fintype.linearCombination ℝ (mixedAtom L)) (coefficientSynthesis (rowCoefficients L))

end RiemannResearch.RH.FiniteAtomCarryCRT
