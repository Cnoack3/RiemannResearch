import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.ResidueAtomIndependence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Universal presentation of certified residue carries

Source: user-provided atom/carry CRT presentation. Every carry label retains
its entire reciprocal certificate, including its integer charge. The free
coefficient space consists of finite sums, even though its labels are infinite.
-/

noncomputable section

open scoped BigOperators
namespace RiemannResearch.RH.UniversalAtomCarry

open ArithmeticCumulative

abbrev Atom := {d : ℕ // 1 < d}

/-- The normalized residue sequence of an atom label. -/
def atom (d : Atom) : ℕ → ℝ := residueFraction d.val

def atomSpan : Submodule ℝ (ℕ → ℝ) := Submodule.span ℝ (Set.range atom)

/-- A finite signed reciprocal certificate, with no divisibility requirement. -/
structure Certificate where
  arity : ℕ
  input : Fin arity → ℕ
  input_gt_one : ∀ i, 1 < input i
  coeff : Fin arity → ℤ
  output : ℕ
  output_gt_one : 1 < output
  charge : ℤ
  reciprocal : (∑ i, (coeff i : ℝ) / (input i : ℝ)) = 1 / (output : ℝ) + (charge : ℝ)

/-- The actual integer floor, embedded in real sequences. -/
def Certificate.carry (c : Certificate) (n : ℕ) : ℝ :=
  (QPrimeCRTCarries.carry c.input c.coeff n : ℝ)

theorem Certificate.carry_eq (c : Certificate) (n : ℕ) :
    c.carry n = (∑ i, (c.coeff i : ℝ) * residueFraction (c.input i) n) -
      residueFraction c.output n := by
  have h := QPrimeCRTCarries.residue_eq_sum_sub_carry_of_reciprocal c.output
    (Nat.zero_lt_of_lt c.output_gt_one) c.input
    (fun i => Nat.zero_lt_of_lt (c.input_gt_one i)) c.coeff c.charge c.reciprocal n
  change (QPrimeCRTCarries.carry c.input c.coeff n : ℝ) = _
  linarith

abbrev Label := Sum Atom Certificate
abbrev Word := Label →₀ ℝ

def atomSymbol (d : Atom) : Word := Finsupp.single (.inl d) 1

def carrySymbol (c : Certificate) : Word := Finsupp.single (.inr c) 1

/-- The finite atom expression assigned to a certified carry. -/
def Certificate.expression (c : Certificate) : Atom →₀ ℝ :=
  (∑ i, (c.coeff i : ℝ) • Finsupp.single (⟨c.input i, c.input_gt_one i⟩ : Atom) 1) -
    Finsupp.single ⟨c.output, c.output_gt_one⟩ 1

def atomSynthesis : (Atom →₀ ℝ) →ₗ[ℝ] (ℕ → ℝ) := Finsupp.linearCombination ℝ atom

/-- Include an atom word without introducing any carry symbols. -/
def includeAtoms : (Atom →₀ ℝ) →ₗ[ℝ] Word := Finsupp.linearCombination ℝ atomSymbol

/-- Eliminate all carry symbols using their signed input and output expressions. -/
def eliminate : Word →ₗ[ℝ] (Atom →₀ ℝ) :=
  Finsupp.linearCombination ℝ (Sum.elim (fun d => Finsupp.single d 1) Certificate.expression)

def synthesis : Word →ₗ[ℝ] (ℕ → ℝ) := atomSynthesis.comp eliminate

@[simp] theorem eliminate_atomSymbol (d : Atom) :
    eliminate (atomSymbol d) = Finsupp.single d 1 := by
  simp [eliminate, atomSymbol, Finsupp.linearCombination_single]

@[simp] theorem eliminate_carrySymbol (c : Certificate) :
    eliminate (carrySymbol c) = c.expression := by
  simp [eliminate, carrySymbol, Finsupp.linearCombination_single]

@[simp] theorem eliminate_includeAtoms (v : Atom →₀ ℝ) :
    eliminate (includeAtoms v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single d r =>
    simp [includeAtoms, Finsupp.linearCombination_single, Finsupp.smul_single]

@[simp] theorem synthesis_atomSymbol (d : Atom) : synthesis (atomSymbol d) = atom d := by
  simp [synthesis, atomSynthesis, Finsupp.linearCombination_single]

@[simp] theorem synthesis_carrySymbol (c : Certificate) : synthesis (carrySymbol c) = c.carry := by
  ext n
  rw [c.carry_eq n]
  simp [synthesis, atomSynthesis, Certificate.expression, Finsupp.linearCombination_single,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, atom]

/-- Elimination followed by atom synthesis agrees with direct linear
synthesis of the actual residue and floor sequences on every finite word. -/
theorem synthesis_eq_realized (w : Word) :
    synthesis w = Finsupp.linearCombination ℝ (Sum.elim atom Certificate.carry) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single l r =>
    rw [← Finsupp.smul_single_one l r, map_smul, map_smul,
      Finsupp.linearCombination_single, one_smul]
    cases l with
    | inl d => exact congrArg (fun v : ℕ → ℝ => r • v) (synthesis_atomSymbol d)
    | inr c => exact congrArg (fun v : ℕ → ℝ => r • v) (synthesis_carrySymbol c)

theorem atom_linearIndependent : LinearIndependent ℝ atom := by
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  exact residueFraction_linearIndependent (fun d : s => d.val.val) (fun d => d.val.property)
    (Subtype.val_injective.comp Subtype.val_injective)

/-- The relation is the carry symbol minus its input expression plus its output. -/
def relation (c : Certificate) : Word := carrySymbol c - includeAtoms c.expression

theorem relation_eq (c : Certificate) :
    relation c = carrySymbol c -
      (∑ i, (c.coeff i : ℝ) • atomSymbol ⟨c.input i, c.input_gt_one i⟩) +
      atomSymbol ⟨c.output, c.output_gt_one⟩ := by
  simp [relation, Certificate.expression, includeAtoms, Finsupp.linearCombination_single,
    sub_sub_eq_add_sub]
  abel

def relations : Submodule ℝ Word := Submodule.span ℝ (Set.range relation)

private def residual : Word →ₗ[ℝ] Word := LinearMap.id - includeAtoms.comp eliminate

private theorem residual_mem (w : Word) : residual w ∈ relations := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using relations.add_mem hx hy
  | single l r =>
    have h : Finsupp.single l r = r • Finsupp.single l (1 : ℝ) := by
      simp [Finsupp.smul_single]
    rw [h, map_smul]
    apply relations.smul_mem
    cases l with
    | inl d =>
      change atomSymbol d - includeAtoms (eliminate (atomSymbol d)) ∈ relations
      simp [includeAtoms, Finsupp.linearCombination_single]
    | inr c =>
      change carrySymbol c - includeAtoms (eliminate (carrySymbol c)) ∈ relations
      rw [eliminate_carrySymbol]
      exact Submodule.subset_span (Set.mem_range_self c)

/-- The explicitly generated reciprocal relations give the entire synthesis kernel. -/
theorem relations_eq_ker : relations = LinearMap.ker synthesis := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change atomSynthesis (eliminate (carrySymbol c - includeAtoms c.expression)) = 0
    simp
  · intro w hw
    have hz : eliminate w = 0 := by
      apply (show Function.Injective atomSynthesis from atom_linearIndependent)
      simpa using (show atomSynthesis (eliminate w) = 0 from hw)
    have hr := residual_mem w
    simpa [residual, hz] using hr

theorem range_synthesis : LinearMap.range synthesis = atomSpan := by
  have ha : LinearMap.range atomSynthesis = atomSpan := Finsupp.range_linearCombination ℝ
  rw [← ha]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact ⟨eliminate w, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨includeAtoms v, by simp [synthesis]⟩

/-- The universal quotient synthesizes precisely the algebraic atom span. -/
def quotientEquivAtomSpan : (Word ⧸ relations) ≃ₗ[ℝ] atomSpan :=
  (Submodule.quotEquivOfEq _ _ relations_eq_ker).trans
    (synthesis.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ range_synthesis))

@[simp] theorem quotientEquivAtomSpan_mk (w : Word) :
    (quotientEquivAtomSpan (Submodule.Quotient.mk w) : ℕ → ℝ) = synthesis w := rfl

end RiemannResearch.RH.UniversalAtomCarry
