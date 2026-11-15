import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Finite-coordinate characters on an arbitrary product of circles

A word in coordinate/integer-exponent pairs represents a Laurent character.
Repetitions are allowed, so this indexing includes every finitely supported
integer character without choosing an enumeration. The locality theorem makes
its finite-coordinate dependence explicit. Its linear span is uniformly dense.
Proof strategy: complex Stone-Weierstrass, as formalized in
Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.Analysis.CompactCharacter
variable {ι : Type*}
abbrev Torus (ι : Type*) := ι → Circle

def coordinatePower (i : ι) (k : ℤ) : C(Torus ι, ℂ) :=
  ⟨fun z => ((z i) ^ k : Circle),
    continuous_subtype_val.comp ((continuous_apply i).zpow k)⟩

def character : List (ι × ℤ) → C(Torus ι, ℂ)
  | [] => 1
  | (i,k) :: s => coordinatePower i k * character s

@[simp] theorem character_nil : character ([] : List (ι × ℤ)) = 1 := rfl
@[simp] theorem character_append (s t : List (ι × ℤ)) :
    character (s ++ t) = character s * character t := by
  induction s with
  | nil => simp [character]
  | cons a s ih => rcases a with ⟨i,k⟩; simp [character, ih, mul_assoc]

theorem star_coordinatePower (i : ι) (k : ℤ) :
    star (coordinatePower i k) = coordinatePower i (-k) := by
  ext z
  change star (((z i) ^ k : Circle) : ℂ) = (((z i) ^ (-k) : Circle) : ℂ)
  rw [zpow_neg, Circle.coe_inv_eq_conj]
  rfl

theorem star_character (s : List (ι × ℤ)) :
    star (character s) = character (s.map fun a => (a.1, -a.2)) := by
  induction s with
  | nil => simp [character]
  | cons a s ih => rcases a with ⟨i,k⟩; simp [character, star_coordinatePower, ih]


/-- Each character only uses the finitely many coordinates in its word. -/
theorem character_eq_of_agree (s : List (ι × ℤ)) (x y : Torus ι)
    (h : ∀ a ∈ s, x a.1 = y a.1) : character s x = character s y := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      rcases a with ⟨i,k⟩
      have hi : x i = y i := h (i,k) (by simp)
      have hs : ∀ a ∈ s, x a.1 = y a.1 := fun a ha => h a (by simp [ha])
      simp only [character, ContinuousMap.mul_apply, coordinatePower,
        ContinuousMap.coe_mk, hi, ih hs]

def polynomials (ι : Type*) : StarSubalgebra ℂ C(Torus ι, ℂ) where
  carrier := Submodule.span ℂ (Set.range (character (ι := ι)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  one_mem' := Submodule.subset_span ⟨[], rfl⟩
  algebraMap_mem' c := by
    simpa only [SetLike.mem_coe, character_nil, Algebra.algebraMap_eq_smul_one] using
      (Submodule.span ℂ (Set.range (character (ι := ι)))).smul_mem c
        (Submodule.subset_span ⟨[], rfl⟩)
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨s,rfl⟩ := hf
        induction hg using Submodule.span_induction with
        | mem g hg =>
            obtain ⟨t,rfl⟩ := hg
            exact Submodule.subset_span ⟨s ++ t, character_append s t⟩
        | zero => simp
        | add g h hg hh ig ih =>
            simpa only [SetLike.mem_coe, character_nil, mul_add] using
              Submodule.add_mem _ ig ih
        | smul c g hg ig =>
            simpa only [SetLike.mem_coe, character_nil, mul_smul_comm] using
              Submodule.smul_mem _ c ig
    | zero => simp
    | add f h hf hh ihf ihh =>
            simpa only [SetLike.mem_coe, character_nil, add_mul] using
              Submodule.add_mem _ ihf ihh
    | smul c f hf ih =>
            simpa only [SetLike.mem_coe, character_nil, smul_mul_assoc] using
              Submodule.smul_mem _ c ih
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨s,rfl⟩ := hf
        exact Submodule.subset_span ⟨s.map (fun a => (a.1,-a.2)), (star_character s).symm⟩
    | zero => simp
    | add f g hf hg ihf ihg =>
            simpa only [SetLike.mem_coe, character_nil, star_add] using
              Submodule.add_mem _ ihf ihg
    | smul c f hf ih =>
            simpa only [SetLike.mem_coe, character_nil, star_smul] using
              Submodule.smul_mem _ (star c) ih

theorem polynomials_separate : (polynomials ι).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  refine ⟨character [(i,1)], ⟨character [(i,1)], Submodule.subset_span ⟨[(i,1)],rfl⟩,rfl⟩, ?_⟩
  simpa [character, coordinatePower, Circle.coe_inj] using hi

theorem characters_dense :
    (Submodule.span ℂ (Set.range (character (ι := ι)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (polynomials ι) polynomials_separate
  exact congrArg (fun A : StarSubalgebra ℂ C(Torus ι, ℂ) => A.toSubalgebra.toSubmodule) h

@[simp] theorem coordinatePower_zero (i : ι) : coordinatePower i 0 = 1 := by
  ext z
  change ((z i ^ (0 : ℤ) : Circle) : ℂ) = 1
  simp

theorem coordinatePower_add (i : ι) (a b : ℤ) :
    coordinatePower i (a + b) = coordinatePower i a * coordinatePower i b := by
  ext z
  change (↑(z i ^ (a + b)) : ℂ) = ↑(z i ^ a) * ↑(z i ^ b)
  rw [zpow_add]
  rfl

/-- The joint character indexed by the net integer exponent at each coordinate. -/
def modeCharacter (k : ι →₀ ℤ) : C(Torus ι, ℂ) :=
  k.prod coordinatePower

@[simp] theorem modeCharacter_zero : modeCharacter (0 : ι →₀ ℤ) = 1 := by
  simp [modeCharacter]

@[simp] theorem modeCharacter_single (i : ι) (k : ℤ) :
    modeCharacter (Finsupp.single i k) = coordinatePower i k := by
  classical
  exact Finsupp.prod_single_index (coordinatePower_zero i)

@[simp] theorem modeCharacter_add (k l : ι →₀ ℤ) :
    modeCharacter (k + l) = modeCharacter k * modeCharacter l := by
  classical
  exact Finsupp.prod_add_index (fun i _ => coordinatePower_zero i)
    (fun i _ a b => coordinatePower_add i a b)

/-- Combine repeated coordinates by adding their exponents. -/
def wordExponents : List (ι × ℤ) → ι →₀ ℤ
  | [] => 0
  | (i, k) :: s => Finsupp.single i k + wordExponents s

@[simp] theorem modeCharacter_wordExponents (s : List (ι × ℤ)) :
    modeCharacter (wordExponents s) = character s := by
  induction s with
  | nil => exact modeCharacter_zero
  | cons a s ih =>
    rcases a with ⟨i, k⟩
    simp [wordExponents, character, ih]

theorem exists_wordExponents (k : ι →₀ ℤ) : ∃ s, wordExponents s = k := by
  classical
  induction k using Finsupp.induction with
  | zero => exact ⟨[], rfl⟩
  | single_add i a f hi ha ih =>
    obtain ⟨s, rfl⟩ := ih
    exact ⟨(i, a) :: s, rfl⟩

theorem star_modeCharacter (k : ι →₀ ℤ) :
    star (modeCharacter k) = modeCharacter (-k) := by
  obtain ⟨s, rfl⟩ := exists_wordExponents k
  rw [modeCharacter_wordExponents, star_character, ← modeCharacter_wordExponents]
  congr 1
  induction s with
  | nil => simp [wordExponents]
  | cons a s ih =>
    rcases a with ⟨i, k⟩
    simp [wordExponents, ih, add_comm]

theorem modeCharacters_separate {x y : Torus ι} (h : x ≠ y) :
    ∃ k : ι →₀ ℤ, modeCharacter k x ≠ modeCharacter k y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact ⟨Finsupp.single i 1, by simpa [coordinatePower, Circle.coe_inj] using hi⟩

theorem range_modeCharacter :
    Set.range (modeCharacter (ι := ι)) = Set.range (character (ι := ι)) := by
  ext f
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨s, rfl⟩ := exists_wordExponents k
    exact ⟨s, (modeCharacter_wordExponents s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨wordExponents s, modeCharacter_wordExponents s⟩

theorem modeCharacters_dense :
    (Submodule.span ℂ (Set.range (modeCharacter (ι := ι)))).topologicalClosure = ⊤ := by
  rw [range_modeCharacter]
  exact characters_dense

end RiemannResearch.Analysis.CompactCharacter
