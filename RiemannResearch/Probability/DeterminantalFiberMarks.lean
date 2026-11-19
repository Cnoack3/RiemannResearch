import RiemannResearch.Probability.DeterminantalWeightedMoments
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Centred marks on fibres of a determinantal kernel

For a kernel depending only on the classes of two labels, the covariance
correction vanishes against any mark whose sum in each class is zero.
Normalizing marks by the square root of their one-point inclusion
probabilities gives an exact second moment with counting measure.
The proof uses the discrete DPP covariance formula of Lyons,
https://doi.org/10.1007/s10240-003-0016-0.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Probability.DPP

variable {ι α κ Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Set α} {K : α → α → ℝ}

/-- Inverse-square-root inclusion weighting of a signed linear statistic. -/
def normalizedMark (X : Ω → Set α) (K : α → α → ℝ) (e : ι → α) (a : ι → ℝ) : Ω → ℝ :=
  linearStatistic X e (fun i => a i / Real.sqrt (K (e i) (e i)))

/-- A mark is centred separately on the fibres of the labelling map. -/
def FiberCentered (p : ι → κ) (b : ι → ℝ) : Prop :=
  ∀ u : κ → ℝ, (∑ i, u (p i) * b i) = 0

theorem IsDPP.expected_normalizedMark (h : IsDPP μ X K) (e : ι → α)
    (p : ι → κ) (L : κ → κ → ℝ) (hK : ∀ i j, K (e i) (e j) = L (p i) (p j))
    (b : ι → ℝ) (hb : FiberCentered p b) :
    (∫ x, normalizedMark X K e b x ∂μ) = 0 := by
  classical
  unfold normalizedMark
  rw [h.expected_linearStatistic]
  let u := fun t => L t t / Real.sqrt (L t t)
  calc
    _ = ∑ i, u (p i) * b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hK]
      dsimp only [u]
      ring
    _ = 0 := hb u

/-- One centred mark suffices. The other test can depend on every label.
Positive inclusions make the diagonal term exactly the counting pairing. -/
theorem IsDPP.normalizedMark_product_moment (h : IsDPP μ X K) (e : ι ↪ α)
    (p : ι → κ) (L : κ → κ → ℝ) (hK : ∀ i j, K (e i) (e j) = L (p i) (p j))
    (hpos : ∀ i, 0 < K (e i) (e i)) (a b : ι → ℝ) (hb : FiberCentered p b) :
    (∫ x, normalizedMark X K e a x * normalizedMark X K e b x ∂μ) =
      ∑ i, a i * b i := by
  classical
  let A := fun i => a i / Real.sqrt (K (e i) (e i))
  let B := fun i => b i / Real.sqrt (K (e i) (e i))
  have hc := h.linearStatistic_covariance e A B
  change (∫ x, normalizedMark X K e a x * normalizedMark X K e b x ∂μ) -
    (∫ x, normalizedMark X K e a x ∂μ) * (∫ x, normalizedMark X K e b x ∂μ) =
      (∑ i, A i * B i * K (e i) (e i)) -
        ∑ i, ∑ j, A i * B j * K (e i) (e j) * K (e j) (e i) at hc
  rw [h.expected_normalizedMark e p L hK b hb, mul_zero, sub_zero] at hc
  have hrow (i : ι) : (∑ j, A i * B j * K (e i) (e j) * K (e j) (e i)) = 0 := by
    let u := fun t => A i / Real.sqrt (L t t) * L (p i) t * L t (p i)
    calc
      _ = ∑ j, u (p j) * b j := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [B, u]
        rw [hK j j, hK i j, hK j i]
        ring
      _ = 0 := hb u
  simp only [hrow, Finset.sum_const_zero, sub_zero] at hc
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [A, B]
  have hs := Real.sqrt_pos.mpr (hpos i)
  have he := Real.sq_sqrt (hpos i).le
  field_simp [hs.ne']
  nlinarith only [congrArg (fun z : ℝ => a i * b i * z) he]

end RiemannResearch.Probability.DPP
