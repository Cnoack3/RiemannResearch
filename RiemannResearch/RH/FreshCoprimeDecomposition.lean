import RiemannResearch.RH.CoupledResidualCorrections
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.IntervalCases

/-!
# The exact fresh coprime-to-six complement of old transports

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Sections 5--6, for the statement and canonical-elimination proof strategy.
All subspaces below are in the existing Pareto Hilbert space. The split is
algebraically direct and is not asserted to be orthogonal.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket

/-- The indices which cannot arise by multiplying an old index by two or three. -/
def freshNaturals (M : ℕ) : Finset ℕ :=
  (Finset.Ioc M (2*M)).filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m)

theorem mem_freshNaturals (M m : ℕ) :
    m ∈ freshNaturals M ↔ M < m ∧ m ≤ 2*M ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m := by
  simp only [freshNaturals, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem coprime_six_iff (m : ℕ) :
    Nat.Coprime m 6 ↔ ¬ 2 ∣ m ∧ ¬ 3 ∣ m := by
  change Nat.Coprime m (2*3) ↔ _
  rw [Nat.coprime_mul_iff_right]
  constructor
  · intro h
    exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h.1.symm,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h.2.symm⟩
  · intro h
    exact ⟨((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h.1).symm,
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h.2).symm⟩

/-- The index set is literally the new indices whose gcd with six is one. -/
theorem mem_freshNaturals_iff_gcd (M m : ℕ) :
    m ∈ freshNaturals M ↔ M < m ∧ m ≤ 2*M ∧ Nat.gcd m 6 = 1 := by
  change m ∈ freshNaturals M ↔ M < m ∧ m ≤ 2*M ∧ Nat.Coprime m 6
  rw [mem_freshNaturals, coprime_six_iff]

private theorem neither_two_nor_three_iff (m : ℕ) :
    (¬ 2 ∣ m ∧ ¬ 3 ∣ m) ↔ m % 6 = 1 ∨ m % 6 = 5 := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  omega

private def coprimePrefix (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m)

private theorem coprimePrefix_eq (N : ℕ) :
    coprimePrefix N =
      ((Finset.range ((N+5)/6)).image (fun k => 6*k+1)) ∪
        ((Finset.range ((N+1)/6)).image (fun k => 6*k+5)) := by
  ext m
  simp only [coprimePrefix, Finset.mem_filter, Finset.mem_Icc,
    neither_two_nor_three_iff, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hpos, hupp⟩, h1 | h5⟩
    · exact Or.inl ⟨m/6, by omega, by omega⟩
    · exact Or.inr ⟨m/6, by omega, by omega⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) <;> omega

private theorem card_coprimePrefix (N : ℕ) :
    (coprimePrefix N).card = N - N/2 - N/3 + N/6 := by
  rw [coprimePrefix_eq]
  have hd : Disjoint
      ((Finset.range ((N+5)/6)).image (fun k => 6*k+1))
      ((Finset.range ((N+1)/6)).image (fun k => 6*k+5)) := by
    apply Finset.disjoint_left.mpr
    intro m h1 h5
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp h1
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp h5
    omega
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega),
    Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega),
    Finset.card_range, Finset.card_range]
  have hmod : N % 6 < 6 := Nat.mod_lt N (by omega)
  interval_cases h : N % 6 <;> omega

/-- Exact inclusion-exclusion count of the fresh arithmetic indices. -/
theorem card_freshNaturals (M : ℕ) :
    (freshNaturals M).card =
      (2*M - (2*M)/2 - (2*M)/3 + (2*M)/6) -
        (M - M/2 - M/3 + M/6) := by
  have heq : freshNaturals M = coprimePrefix (2*M) \ coprimePrefix M := by
    ext m
    simp only [mem_freshNaturals, Finset.mem_sdiff, coprimePrefix,
      Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsub : coprimePrefix M ⊆ coprimePrefix (2*M) := by
    intro m hm
    simp only [coprimePrefix, Finset.mem_filter, Finset.mem_Icc] at *
    omega
  rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    card_coprimePrefix, card_coprimePrefix]

/-- A uniform finite error bound for the asymptotic fresh dimension. -/
theorem fresh_count_error (M : ℕ) :
    M ≤ 3 * (freshNaturals M).card + 4 ∧
      3 * (freshNaturals M).card ≤ M + 4 := by
  rw [card_freshNaturals]
  have hmod : M % 6 < 6 := Nat.mod_lt M (by omega)
  interval_cases h : M % 6 <;> omega

/-- The old budget together with its complete permitted binary and ternary transports. -/
def transportedSpace (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  (budgetHilbert M ⊔ (budgetHilbert M).map (hilbertDilationLinear 2 (by omega))) ⊔
    (budgetHilbert (2*M/3)).map (hilbertDilationLinear 3 (by omega))

instance transportedSpaceFiniteDimensional (M : ℕ) :
    FiniteDimensional ℝ (transportedSpace M) := by
  unfold transportedSpace
  infer_instance

def carriedCanonical (M : ℕ) : Set (canonicalIndices (2*M)) :=
  {i | i.val.2 ≤ M ∨ 2 ∣ i.val.2 ∨ 3 ∣ i.val.2}

def freshCanonical (M : ℕ) : Set (canonicalIndices (2*M)) :=
  {i | M < i.val.2 ∧ ¬ 2 ∣ i.val.2 ∧ ¬ 3 ∣ i.val.2}

def carriedSpace (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (canonicalHilbertFamily (2*M) '' carriedCanonical M)

def freshSpace (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (canonicalHilbertFamily (2*M) '' freshCanonical M)

private theorem canonical_generator_eq (N p m : ℕ)
    (hm : 0 < m) (hmN : m ≤ N)
    (hc : p = 3 ∨ (p = 2 ∧ ¬ 3 ∣ m)) :
    canonicalHilbertFamily N
      ⟨(p,m), (mem_canonicalIndices N (p,m)).mpr ⟨hm, hmN, hc⟩⟩ =
      generator p m (by rcases hc with h | ⟨h, _⟩ <;> omega) hm := rfl

theorem canonical_generator_mem_carried (M p m : ℕ)
    (hm : 0 < m) (hmM : m ≤ 2*M)
    (hc : p = 3 ∨ (p = 2 ∧ ¬ 3 ∣ m))
    (hcarry : m ≤ M ∨ 2 ∣ m ∨ 3 ∣ m) :
    generator p m (by rcases hc with h | ⟨h, _⟩ <;> omega) hm ∈ carriedSpace M := by
  refine Submodule.subset_span ?_
  exact ⟨⟨(p,m), (mem_canonicalIndices (2*M) (p,m)).mpr ⟨hm, hmM, hc⟩⟩,
    hcarry, rfl⟩

theorem budget_le_carriedSpace (M : ℕ) : budgetHilbert M ≤ carriedSpace M := by
  rw [← canonicalHilbertFamily_span]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  obtain ⟨hm, hmM, hc⟩ := (mem_canonicalIndices M i.val).mp i.property
  exact canonical_generator_mem_carried M i.val.1 i.val.2 hm (by omega) hc (Or.inl hmM)

private theorem hilbert_binary_three_elimination (k : ℕ) (hk : 0 < k) :
    generator 2 (3*k) (by omega) (by omega) =
      generator 3 (2*k) (by omega) (by omega) +
        generator 2 k (by omega) hk - generator 3 k (by omega) hk := by
  apply hilbertSequence_injective
  funext n
  simp only [hilbertSequence_add, hilbertSequence_sub, Pi.add_apply, Pi.sub_apply,
    generator_sequence_apply]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  ring

/-- Canonical elimination of a carried binary column never creates a fresh index. -/
theorem generator_mem_carriedSpace (M p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hs : p = 2 ∨ p = 3) (hmM : m ≤ 2*M)
    (hcarry : m ≤ M ∨ 2 ∣ m ∨ 3 ∣ m) :
    generator p m hp hm ∈ carriedSpace M := by
  rcases hs with rfl | rfl
  · by_cases h3 : 3 ∣ m
    · obtain ⟨k, rfl⟩ := h3
      have hk : 0 < k := by omega
      have hkM : k ≤ M := by omega
      rw [hilbert_binary_three_elimination k hk]
      exact (carriedSpace M).sub_mem
        ((carriedSpace M).add_mem
          (canonical_generator_mem_carried M 3 (2*k) (by omega) (by omega)
            (Or.inl rfl) (Or.inr (Or.inl ⟨k, rfl⟩)))
          (budget_le_carriedSpace M (generator_mem_budgetHilbert M 2 k (by omega) hk
            (Or.inl rfl) hkM)))
        (budget_le_carriedSpace M (generator_mem_budgetHilbert M 3 k (by omega) hk
          (Or.inr rfl) hkM))
    · exact canonical_generator_mem_carried M 2 m hm hmM (Or.inr ⟨rfl, h3⟩) hcarry
  · exact canonical_generator_mem_carried M 3 m hm hmM (Or.inl rfl) hcarry

private theorem dilated_budget_le_carriedSpace (M N a : ℕ) (ha : 0 < a)
    (hseed : a = 2 ∨ a = 3) (hbound : a*N ≤ 2*M) :
    (budgetHilbert N).map (hilbertDilationLinear a ha) ≤ carriedSpace M := by
  rintro x ⟨f, hf, rfl⟩
  rw [← canonicalHilbertFamily_span] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    obtain ⟨hm, hmN, hs⟩ := (mem_canonicalIndices N i.val).mp i.property
    have hp : 0 < i.val.1 := by rcases hs with h | ⟨h, _⟩ <;> omega
    have hs' : i.val.1 = 2 ∨ i.val.1 = 3 := by tauto
    change hilbertDilation a ha (generator i.val.1 i.val.2 hp hm) ∈ _
    rw [dilation_generator]
    apply generator_mem_carriedSpace M i.val.1 (a*i.val.2) hp (Nat.mul_pos ha hm) hs'
    · exact (Nat.mul_le_mul_left a hmN).trans hbound
    · rcases hseed with rfl | rfl
      · exact Or.inr (Or.inl ⟨i.val.2, rfl⟩)
      · exact Or.inr (Or.inr ⟨i.val.2, rfl⟩)
  | zero => simpa only [map_zero] using (carriedSpace M).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (carriedSpace M).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (carriedSpace M).smul_mem c ih

theorem transportedSpace_le_carriedSpace (M : ℕ) :
    transportedSpace M ≤ carriedSpace M := by
  apply sup_le
  · exact sup_le (budget_le_carriedSpace M)
      (dilated_budget_le_carriedSpace M M 2 (by omega) (Or.inl rfl) (by omega))
  · exact dilated_budget_le_carriedSpace M (2*M/3) 3 (by omega) (Or.inr rfl)
      (Nat.mul_div_le (2*M) 3)

theorem budget_le_transportedSpace (M : ℕ) : budgetHilbert M ≤ transportedSpace M :=
  le_sup_of_le_left le_sup_left

theorem carriedSpace_le_transportedSpace (M : ℕ) :
    carriedSpace M ≤ transportedSpace M := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices (2*M) i.val).mp i.property
  have hp : 0 < i.val.1 := by rcases hs with h | ⟨h, _⟩ <;> omega
  have hs' : i.val.1 = 2 ∨ i.val.1 = 3 := by tauto
  change generator i.val.1 i.val.2 hp hm ∈ transportedSpace M
  rcases hi with hold | heven | hthree
  · exact budget_le_transportedSpace M
      (generator_mem_budgetHilbert M i.val.1 i.val.2 hp hm hs' hold)
  · obtain ⟨k, hk⟩ := heven
    have hkpos : 0 < k := by omega
    have hkM : k ≤ M := by omega
    have hle : (budgetHilbert M).map (hilbertDilationLinear 2 (by omega)) ≤
        transportedSpace M := le_sup_of_le_left le_sup_right
    apply hle
    refine ⟨generator i.val.1 k hp hkpos,
      generator_mem_budgetHilbert M i.val.1 k hp hkpos hs' hkM, ?_⟩
    change hilbertDilation 2 (by omega) _ = _
    rw [dilation_generator]
    apply hilbertSequence_injective
    funext n
    simp only [generator_sequence_apply, hk]
  · obtain ⟨k, hk⟩ := hthree
    have hkpos : 0 < k := by omega
    have hkM : k ≤ 2*M/3 := by omega
    have hle : (budgetHilbert (2*M/3)).map (hilbertDilationLinear 3 (by omega)) ≤
        transportedSpace M := le_sup_right
    apply hle
    refine ⟨generator i.val.1 k hp hkpos,
      generator_mem_budgetHilbert (2*M/3) i.val.1 k hp hkpos hs' hkM, ?_⟩
    change hilbertDilation 3 (by omega) _ = _
    rw [dilation_generator]
    apply hilbertSequence_injective
    funext n
    simp only [generator_sequence_apply, hk]

/-- A complete arithmetic characterization of the transported span. -/
theorem transportedSpace_eq_carriedSpace (M : ℕ) :
    transportedSpace M = carriedSpace M :=
  le_antisymm (transportedSpace_le_carriedSpace M) (carriedSpace_le_transportedSpace M)

theorem carriedSpace_sup_freshSpace (M : ℕ) :
    carriedSpace M ⊔ freshSpace M = budgetHilbert (2*M) := by
  rw [← canonicalHilbertFamily_span]
  unfold carriedSpace freshSpace
  rw [← Submodule.span_union, ← Set.image_union]
  have hcover : carriedCanonical M ∪ freshCanonical M = Set.univ := by
    ext i
    simp only [carriedCanonical, freshCanonical, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_univ, iff_true]
    omega
  rw [hcover, Set.image_univ]

/-- Exact decomposition with all arithmetic restrictions retained. -/
theorem transportedSpace_sup_freshSpace (M : ℕ) :
    transportedSpace M ⊔ freshSpace M = budgetHilbert (2*M) := by
  rw [transportedSpace_eq_carriedSpace, carriedSpace_sup_freshSpace]

/-- The fresh columns are independent modulo every transported old direction. -/
theorem transportedSpace_disjoint_freshSpace (M : ℕ) :
    Disjoint (transportedSpace M) (freshSpace M) := by
  rw [transportedSpace_eq_carriedSpace]
  apply (canonicalHilbertFamily_linearIndependent (2*M)).disjoint_span_image
  apply Set.disjoint_left.mpr
  intro i hi hf
  rcases hi with hold | heven | hthree
  · exact (not_lt_of_ge hold) hf.1
  · exact hf.2.1 heven
  · exact hf.2.2 hthree

/-- A concrete finite list: exactly two generators for each new index coprime to six. -/
def freshIndices (M : ℕ) : Finset (ℕ × ℕ) := {2,3} ×ˢ freshNaturals M

theorem freshIndices_subset_canonical (M : ℕ) :
    freshIndices M ⊆ canonicalIndices (2*M) := by
  intro i hi
  obtain ⟨hp, hm⟩ := Finset.mem_product.mp hi
  obtain ⟨hl, hu, h2, h3⟩ := (mem_freshNaturals M i.2).mp hm
  have hp' : i.1 = 2 ∨ i.1 = 3 := by simpa only [Finset.mem_insert,
    Finset.mem_singleton] using hp
  apply (mem_canonicalIndices (2*M) i).mpr
  refine ⟨by omega, hu, ?_⟩
  rcases hp' with hp' | hp'
  · exact Or.inr ⟨hp', h3⟩
  · exact Or.inl hp'

def freshFamily (M : ℕ) (i : freshIndices M) : ThresholdHilbert :=
  canonicalHilbertFamily (2*M)
    ⟨i.val, freshIndices_subset_canonical M i.property⟩

theorem freshFamily_linearIndependent (M : ℕ) : LinearIndependent ℝ (freshFamily M) := by
  apply (canonicalHilbertFamily_linearIndependent (2*M)).comp
    (fun i : freshIndices M =>
      (⟨i.val, freshIndices_subset_canonical M i.property⟩ : canonicalIndices (2*M)))
  intro i j hij
  exact Subtype.ext (congrArg (fun k : canonicalIndices (2*M) => k.val) hij)

theorem freshFamily_span (M : ℕ) :
    Submodule.span ℝ (Set.range (freshFamily M)) = freshSpace M := by
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i.val, freshIndices_subset_canonical M i.property⟩, ?_, rfl⟩
    obtain ⟨hp, hm⟩ := Finset.mem_product.mp i.property
    obtain ⟨hl, hu, h2, h3⟩ := (mem_freshNaturals M i.val.2).mp hm
    exact ⟨hl, h2, h3⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices (2*M) i.val).mp i.property
    have hindex : i.val ∈ freshIndices M := by
      apply Finset.mem_product.mpr
      constructor
      · have hp : i.val.1 = 2 ∨ i.val.1 = 3 := by tauto
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hp
      · exact (mem_freshNaturals M i.val.2).mpr ⟨hi.1, hmM, hi.2.1, hi.2.2⟩
    exact ⟨⟨i.val, hindex⟩, rfl⟩

/-- Exact omitted dimension, without asymptotic notation or a generic independence hypothesis. -/
theorem finrank_freshSpace (M : ℕ) :
    Module.finrank ℝ (freshSpace M) = 2 * (freshNaturals M).card := by
  rw [← freshFamily_span, finrank_span_eq_card (freshFamily_linearIndependent M),
    Fintype.card_coe]
  simp [freshIndices, Finset.card_product]

def carriedIndices (M : ℕ) : Finset (ℕ × ℕ) :=
  (canonicalIndices (2*M)).filter (fun i => i.2 ≤ M ∨ 2 ∣ i.2 ∨ 3 ∣ i.2)

def carriedFamily (M : ℕ) (i : carriedIndices M) : ThresholdHilbert :=
  canonicalHilbertFamily (2*M) ⟨i.val, (Finset.mem_filter.mp i.property).1⟩

theorem carriedFamily_linearIndependent (M : ℕ) :
    LinearIndependent ℝ (carriedFamily M) := by
  apply (canonicalHilbertFamily_linearIndependent (2*M)).comp
    (fun i : carriedIndices M =>
      (⟨i.val, (Finset.mem_filter.mp i.property).1⟩ : canonicalIndices (2*M)))
  intro i j hij
  exact Subtype.ext (congrArg (fun k : canonicalIndices (2*M) => k.val) hij)

theorem carriedFamily_span (M : ℕ) :
    Submodule.span ℝ (Set.range (carriedFamily M)) = transportedSpace M := by
  rw [transportedSpace_eq_carriedSpace]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.val, (Finset.mem_filter.mp i.property).1⟩,
      (Finset.mem_filter.mp i.property).2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, Finset.mem_filter.mpr ⟨i.property, hi⟩⟩, rfl⟩

theorem carriedIndices_eq_sdiff (M : ℕ) :
    carriedIndices M = canonicalIndices (2*M) \ freshIndices M := by
  ext i
  simp only [carriedIndices, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hc : i ∈ canonicalIndices (2*M)
  · obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices (2*M) i).mp hc
    have hseed : i.1 = 2 ∨ i.1 = 3 := by tauto
    have hseedmem : i.1 ∈ ({2,3} : Finset ℕ) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hseed
    simp only [hc, true_and, freshIndices, Finset.mem_product,
      hseedmem, mem_freshNaturals, hmM]
    omega
  · simp [hc]

/-- Exact number of transported canonical directions. -/
theorem finrank_transportedSpace (M : ℕ) :
    Module.finrank ℝ (transportedSpace M) =
      (4*M - (2*M)/3) - 2*(freshNaturals M).card := by
  rw [← carriedFamily_span,
    finrank_span_eq_card (carriedFamily_linearIndependent M), Fintype.card_coe,
    carriedIndices_eq_sdiff, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (freshIndices_subset_canonical M),
    card_canonicalIndices]
  norm_num [freshIndices, Finset.card_product, show 2*(2*M) = 4*M by omega]

/-- The exact codimension of the transported space inside the doubled budget. -/
theorem transported_codimension (M : ℕ) :
    Module.finrank ℝ (transportedSpace M) + 2*(freshNaturals M).card =
      Module.finrank ℝ (budgetHilbert (2*M)) := by
  have hcard := Finset.card_le_card (freshIndices_subset_canonical M)
  rw [card_canonicalIndices] at hcard
  simp only [freshIndices, Finset.card_product] at hcard
  norm_num at hcard
  rw [finrank_transportedSpace, finrank_budgetHilbert]
  omega

/-- Exact transported increment in the first possible dyadic residue class. -/
theorem transported_increment_mod_six_two (M : ℕ) (hM : M % 6 = 2) :
    Module.finrank ℝ (transportedSpace M) - Module.finrank ℝ (budgetHilbert M) = M+1 := by
  rw [finrank_transportedSpace, finrank_budgetHilbert, card_freshNaturals]
  omega

/-- Exact transported increment in the other possible dyadic residue class. -/
theorem transported_increment_mod_six_four (M : ℕ) (hM : M % 6 = 4) :
    Module.finrank ℝ (transportedSpace M) - Module.finrank ℝ (budgetHilbert M) = M-1 := by
  rw [finrank_transportedSpace, finrank_budgetHilbert, card_freshNaturals]
  omega

end RiemannResearch.RH.Pareto.CoupledResidual
