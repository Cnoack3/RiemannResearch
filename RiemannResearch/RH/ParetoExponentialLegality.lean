import RiemannResearch.NumberTheory.DirichletExponentialDomain
import RiemannResearch.RH.ParetoDirichletExponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# What legality of exp-star(V) would mean

Source: Christian Noack's question about exp-star(V), 13 November 2026.
The image is first defined in physical sequences. Bounded inputs have actual
Hilbert exponentials by the existing moment theorem. Preserving the residue
closure for all bounded legal inputs is equivalent to full residue density:
already the input zero forces the Dirichlet unit into the closure.
The implication to RH is checked; the reverse RH-to-density provider is
retained explicitly. Centered exponentials have a separate sufficient theorem
requiring legality of the positive powers and a factorial energy bound.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExponentialLegality
open RiemannResearch.NumberTheory.DirichletExponential
open ConvolutionExponential CoefficientStabilization

/-- Turn the actual zero-anchored physical sequence into an arithmetic function. -/
def arithmeticInput (v : ThresholdHilbert) : ArithmeticFunction ℝ where
  toFun := hilbertSequence v
  map_zero' := hilbertSequence_zero v

@[simp] theorem arithmeticInput_apply (v : ThresholdHilbert) (n : ℕ) :
    arithmeticInput v n = hilbertSequence v n := rfl

@[simp] theorem arithmeticInput_zero : arithmeticInput 0 = 0 := by
  ext n
  cases n <;> simp [arithmeticInput, hilbertSequence]

/-- Coefficientwise exponential. No assertion that its output belongs to H. -/
def physicalExp (v : ThresholdHilbert) : ℕ → ℝ := convolutionExp (arithmeticInput v)

def expImage (S : Set ThresholdHilbert) : Set (ℕ → ℝ) := physicalExp '' S

theorem physicalExp_summable (v : ThresholdHilbert) (n : ℕ) :
    Summable (fun r : ℕ => ((arithmeticInput v) ^ r) n / (r.factorial : ℝ)) :=
  convolutionExp_summable_at _ _

theorem physicalExp_one (v : ThresholdHilbert) :
    physicalExp v 1 = Real.exp (hilbertSequence v 1) :=
  convolutionExp_at_one _

@[simp] theorem physicalExp_zero :
    physicalExp 0 = fun n => if n = 1 then 1 else 0 := by
  funext n
  simp [physicalExp]

theorem zero_not_mem_expImage (S : Set ThresholdHilbert) :
    (0 : ℕ → ℝ) ∉ expImage S := by
  rintro ⟨v, hv, he⟩
  exact convolutionExp_ne_zero (arithmeticInput v) he

theorem expImage_not_submodule (S : Set ThresholdHilbert) :
    ¬ ∃ W : Submodule ℝ (ℕ → ℝ), (W : Set (ℕ → ℝ)) = expImage S := by
  rintro ⟨W, hW⟩
  apply zero_not_mem_expImage S
  rw [← hW]
  exact W.zero_mem

theorem unit_mem_expImage (S : Set ThresholdHilbert) (hzero : 0 ∈ S) :
    (fun n => if n = 1 then (1 : ℝ) else 0) ∈ expImage S :=
  ⟨0, hzero, physicalExp_zero⟩

def HasBoundedCoordinates (v : ThresholdHilbert) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |hilbertSequence v n| ≤ C

theorem zero_hasBoundedCoordinates : HasBoundedCoordinates 0 := by
  refine ⟨0, le_rfl, ?_⟩
  intro n
  cases n <;> simp [hilbertSequence]

theorem physicalExp_square_summable_of_bounded {v : ThresholdHilbert}
    (hv : HasBoundedCoordinates v) :
    Summable (fun n => positiveWeight n * physicalExp v n ^ 2) := by
  obtain ⟨C, hC, hf⟩ := hv
  exact bounded_convolutionExp_square_summable (arithmeticInput v) hC hf

/-- Genuine H-valued exponential on the bounded physical-coordinate domain. -/
def boundedExp (v : ThresholdHilbert) (hv : HasBoundedCoordinates v) : ThresholdHilbert :=
  sequenceHilbert (physicalExp v) (physicalExp_square_summable_of_bounded hv)

@[simp] theorem boundedExp_sequence (v : ThresholdHilbert) (hv : HasBoundedCoordinates v) :
    hilbertSequence (boundedExp v hv) = physicalExp v :=
  hilbertSequence_sequenceHilbert _ _ (convolutionExp_zero _)

@[simp] theorem boundedExp_zero (hzero : HasBoundedCoordinates 0) :
    boundedExp 0 hzero = paretoPointHilbert 0 := by
  apply hilbertSequence_injective
  rw [boundedExp_sequence, physicalExp_zero, hilbertSequence_paretoPoint]
  rfl

/-- Full legality would include both output square integrability and V membership. -/
def RetainsLegality : Prop :=
  ∀ v : ThresholdHilbert, v ∈ closedSpace →
    ∃ w : ThresholdHilbert, w ∈ closedSpace ∧ hilbertSequence w = physicalExp v

/-- Restrict preservation to the domain with already-proved ambient energy. -/
def RetainsBoundedLegality : Prop :=
  ∀ (v : ThresholdHilbert) (hv : HasBoundedCoordinates v),
    v ∈ closedSpace → boundedExp v hv ∈ closedSpace

theorem retainsBoundedLegality_iff_density :
    RetainsBoundedLegality ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    have hu := h 0 zero_hasBoundedCoordinates (closedSpace.zero_mem)
    rw [boundedExp_zero] at hu
    exact closedSpace_eq_top_iff_one_mem.mpr (firstPoint_mem_iff_one_mem.mp hu)
  · intro h v hv hlegal
    rw [h]
    trivial

theorem retainsLegality_implies_bounded (h : RetainsLegality) : RetainsBoundedLegality := by
  intro v hv hlegal
  obtain ⟨w, hw, hseq⟩ := h v hlegal
  have he : w = boundedExp v hv :=
    hilbertSequence_injective (hseq.trans (boundedExp_sequence v hv).symm)
  rw [← he]
  exact hw

theorem riemannHypothesis_of_retainsBoundedLegality
    (h : RetainsBoundedLegality) : RiemannHypothesis :=
  riemannHypothesis_of_residueExponential_unbounded_prime_legality
    (residueExponential_unbounded_prime_legality_iff_density.mpr
      (retainsBoundedLegality_iff_density.mp h))

theorem riemannHypothesis_of_retainsLegality (h : RetainsLegality) : RiemannHypothesis :=
  riemannHypothesis_of_retainsBoundedLegality (retainsLegality_implies_bounded h)

/-- The reverse classical density theorem remains an explicit provider. -/
theorem retainsBoundedLegality_iff_rh
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    RetainsBoundedLegality ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_retainsBoundedLegality
  · intro hRH
    exact retainsBoundedLegality_iff_density.mpr (hDensity hRH)

/-- Nonnegative inputs whose convolution square has infinite energy also have
an exponential of infinite energy. The divergent-square provider is explicit. -/
theorem exponential_not_square_summable_of_square_not_summable
    (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (hbad : ¬ Summable (fun n => positiveWeight n * (f * f) n ^ 2)) :
    ¬ Summable (fun n => positiveWeight n * convolutionExp f n ^ 2) := by
  intro he
  apply hbad
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) _ (he.mul_left 4)
  intro n
  have hq := convolutionExp_quadratic_lower_of_nonneg f hf n
  have h0 : 0 ≤ (f * f) n := by
    simpa only [pow_two] using convolutionPower_nonneg f hf 2 n
  have h1 : 0 ≤ convolutionExp f n := convolutionExp_nonneg f hf n
  have hs : (f * f) n ^ 2 ≤ 4 * convolutionExp f n ^ 2 := by nlinarith
  calc
    _ ≤ positiveWeight n * (4 * convolutionExp f n ^ 2) :=
      mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg n)
    _ = _ := by ring

/-- Legal powers plus a checked Taylor energy bound give a legal actual exponential. -/
theorem exponential_mem_of_power_legality (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * (f ^ r) n ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ, (∑' n, positiveWeight n * (f ^ r) n ^ 2) ≤
      A ^ r * (r.factorial : ℝ))
    (hlegal : ∀ r : ℕ, powerHilbert f r (henergy r) ∈ closedSpace) :
    ∃ e : ThresholdHilbert, e ∈ closedSpace ∧ hilbertSequence e = convolutionExp f := by
  refine ⟨∑' r : ℕ, (1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r), ?_, ?_⟩
  · exact tsum_mem (Submodule.isClosed_topologicalClosure _) (fun r =>
      closedSpace.smul_mem _ (hlegal r))
  · exact powerHilbert_exp_tsum_sequence f henergy hA hbound

/-- For the centered exponential only the positive powers need be legal.
The factorial energy hypothesis supplies the actual infinite sum. -/
theorem centered_exponential_mem_of_positive_power_legality (f : ArithmeticFunction ℝ)
    (henergy : ∀ r : ℕ, Summable (fun n => positiveWeight n * (f ^ r) n ^ 2))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ r : ℕ, (∑' n, positiveWeight n * (f ^ r) n ^ 2) ≤
      A ^ r * (r.factorial : ℝ))
    (hlegal : ∀ r : ℕ, powerHilbert f (r + 1) (henergy (r + 1)) ∈ closedSpace) :
    ∃ e : ThresholdHilbert, e ∈ closedSpace ∧
      hilbertSequence e = fun n => convolutionExp f n - (if n = 1 then 1 else 0) := by
  let T (r : ℕ) := (1 / (r.factorial : ℝ)) • powerHilbert f r (henergy r)
  have hs : Summable T := powerHilbert_exp_summable f henergy hA hbound
  have ht : T 0 + (∑' r : ℕ, T (r + 1)) = ∑' r : ℕ, T r := by
    simpa only [Finset.sum_range_one] using hs.sum_add_tsum_nat_add 1
  have hT0 : T 0 = powerHilbert f 0 (henergy 0) := by simp [T]
  have heq : (∑' r : ℕ, T (r + 1)) =
      (∑' r : ℕ, T r) - powerHilbert f 0 (henergy 0) := by
    rw [← ht, hT0]
    abel
  refine ⟨∑' r : ℕ, T (r + 1), ?_, ?_⟩
  · exact tsum_mem (Submodule.isClosed_topologicalClosure _) (fun r =>
      closedSpace.smul_mem _ (hlegal r))
  · rw [heq]
    change hilbertSequenceLinear (_ - _) = _
    rw [map_sub]
    change hilbertSequence (∑' r : ℕ, T r) -
      hilbertSequence (powerHilbert f 0 (henergy 0)) = _
    rw [show hilbertSequence (∑' r : ℕ, T r) = convolutionExp f from
      powerHilbert_exp_tsum_sequence f henergy hA hbound, powerHilbert_sequence]
    funext n
    simp only [Pi.sub_apply, convolutionPower_zero]

end RiemannResearch.RH.Pareto.ExponentialLegality
