import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import RiemannResearch.Probability.ZeroOrdinatePrimeDPP
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import RiemannResearch.Analysis.ActualZeroCountNormalization

/-! The unweighted prime-DPP pair statistic with its genuine occurrence-label
diagonal restored. This separates the unconditional first moment from the
signed spacing estimate for distinct ordinates. -/
noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ProjectedDistinctSpacing
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryPositiveGap
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

private theorem sum_div_fiber (T : ℝ) (f : ℝ → ℝ) :
    (∑ i : Copies T, f (copyOrdinate T i) / (actualOrdinateMultiplicity T (copyOrdinate T i) : ℝ)) =
      ∑ u ∈ actualOrdinateSupport T, f u := by
  rw [sum_copies_by_ordinate T (fun u => f u / (actualOrdinateMultiplicity T u : ℝ))]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  have hm := ordinateFiber_card_pos (liftCopy T i)
  rw [ordinateFiber_card_liftCopy] at hm
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

def distinctPairTest (T : ℝ) (w : ℝ → ℝ → ℝ) : ℝ :=
  ∑ u ∈ actualOrdinateSupport T, ∑ v ∈ actualOrdinateSupport T, if u = v then 0 else w u v

/-- The second determinant automatically vanishes on the diagonal, including
different labels at an equal ordinate. For different ordinates its inverse
multiplicity factors cancel exactly on summing over both fibres. -/
theorem prime_expectedPairMass_eq_distinct (T : ℝ) (w : ℝ → ℝ → ℝ) :
    expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
      (fun i j => w (copyOrdinate T i) (copyOrdinate T j)) = distinctPairTest T w := by
  classical
  let g (u v : ℝ) := if u = v then 0 else w u v
  let m (u : ℝ) := (actualOrdinateMultiplicity T u : ℝ)
  have hk (i j : Copies T) : limitingKernel primeFrequencies (liftCopy T i) (liftCopy T j) =
      if copyOrdinate T j = copyOrdinate T i then (m (copyOrdinate T i))⁻¹ else 0 := by
    rw [primeFrequencies_limitingKernel, ordinateFiber_card_liftCopy]
    rfl
  have hp (i j : Copies T) : w (copyOrdinate T i) (copyOrdinate T j) *
      (limitingKernel primeFrequencies (liftCopy T i) (liftCopy T i) *
        limitingKernel primeFrequencies (liftCopy T j) (liftCopy T j) -
       limitingKernel primeFrequencies (liftCopy T i) (liftCopy T j) *
        limitingKernel primeFrequencies (liftCopy T j) (liftCopy T i)) =
      (g (copyOrdinate T i) (copyOrdinate T j) / m (copyOrdinate T j)) / m (copyOrdinate T i) := by
    by_cases he : copyOrdinate T i = copyOrdinate T j
    · simp [hk, g, he]
    · simp [hk, g, he, Ne.symm he, div_eq_mul_inv, mul_left_comm, mul_assoc, mul_comm]
  unfold expectedPairMass
  simp_rw [hp]
  calc
    _ = ∑ i : Copies T,
        (∑ j : Copies T, g (copyOrdinate T i) (copyOrdinate T j) / m (copyOrdinate T j)) /
            m (copyOrdinate T i) := by simp only [Finset.sum_div]
    _ = ∑ i : Copies T, (∑ v ∈ actualOrdinateSupport T, g (copyOrdinate T i) v) /
        m (copyOrdinate T i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∑ j : Copies T, g (copyOrdinate T i) (copyOrdinate T j) / m (copyOrdinate T j)) =
        ∑ v ∈ actualOrdinateSupport T, g (copyOrdinate T i) v from sum_div_fiber T (g _)]
    _ = distinctPairTest T w := sum_div_fiber T (fun u => ∑ v ∈ actualOrdinateSupport T, g u v)

def widthProbe (a b x : ℝ) : ℝ :=
  ((max (b - |x|) 0)^2 - (max (a - |x|) 0)^2) / 2

def unfoldedProbe (T a b u v : ℝ) : ℝ :=
  widthProbe a b ((Real.log T / (2 * Real.pi)) * (u - v)) / (T * Real.log T / (2 * Real.pi))

def restoredPrimeMoment (T a b : ℝ) : ℝ :=
  (∑ i : Copies T, unfoldedProbe T a b (copyOrdinate T i) (copyOrdinate T i)) +
  expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
    (fun i j => unfoldedProbe T a b (copyOrdinate T i) (copyOrdinate T j))

/-- Exact separation of true self-pairs and the ordered distinct-ordinate sum. -/
theorem restoredPrimeMoment_eq (T a b : ℝ) :
    restoredPrimeMoment T a b =
      ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) * widthProbe a b 0 +
        distinctPairTest T (unfoldedProbe T a b) := by
  unfold restoredPrimeMoment
  rw [prime_expectedPairMass_eq_distinct]
  congr 1
  simp only [unfoldedProbe, sub_self, mul_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_copies]
  ring

/-- The restored diagonal has its predicted limit without a spacing or RH
hypothesis. At positive endpoints its value is (b² − a²)/2. -/
theorem restoredDiagonal_tendsto (a b : ℝ) :
    Tendsto (fun T : ℝ => (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)) *
      widthProbe a b 0) atTop (𝓝 (widthProbe a b 0)) := by
  simpa using tendsto_count_div_mainTerm.mul_const (widthProbe a b 0)

theorem widthProbe_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    widthProbe a b 0 = (b^2 - a^2)/2 := by
  simp [widthProbe, max_eq_left ha, max_eq_left hb]

/-- For the prime kernel the second requested limit is precisely a deterministic
spacing limit on distinct heights, after subtraction of the known self-pairs. -/
theorem projectedSineLimit_iff_distinct (a b : ℝ) :
    Tendsto (fun T : ℝ => restoredPrimeMoment T a b) atTop
      (𝓝 (∫ r in a..b, sineWindowEnergy r)) ↔
    Tendsto (fun T : ℝ => distinctPairTest T (unfoldedProbe T a b)) atTop
      (𝓝 ((∫ r in a..b, sineWindowEnergy r) - widthProbe a b 0)) := by
  simp only [restoredPrimeMoment_eq]
  constructor
  · intro h
    have e := h.sub (restoredDiagonal_tendsto a b)
    simpa only [add_sub_cancel_left] using e
  · intro h
    have e := (restoredDiagonal_tendsto a b).add h
    rw [show widthProbe a b 0 + ((∫ r in a..b, sineWindowEnergy r) - widthProbe a b 0) =
      (∫ r in a..b, sineWindowEnergy r) by ring] at e
    exact e

end RiemannResearch.Analysis.ProjectedDistinctSpacing
