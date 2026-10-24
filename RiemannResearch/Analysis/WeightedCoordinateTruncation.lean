import RiemannResearch.Analysis.WeightedCoordinateEnergy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Complete tail certificates and independently moving observation heads

Source: exact summable-series head/tail splitting, sixth Ramanujan transfer
program, 24 October 2026. The finite head and physical approximation stage
may move independently. Full omitted tails are kept as equalities first.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.WeightedCoordinateTruncation
open WeightedCoordinateEnergy
variable {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def headEnergy (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range N, w j * (ℓ j x) ^ 2

def tailEnergy (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) (x : H) : ℝ :=
  ∑' j, w (j + N) * (ℓ (j + N) x) ^ 2

def tailMass (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) : ℝ :=
  ∑' j, w (j + N) * ‖ℓ (j + N)‖ ^ 2

theorem head_add_tail_exact (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (N : ℕ) (x : H) :
    headEnergy w ℓ N x + tailEnergy w ℓ N x = observationEnergy w ℓ x :=
  (observation_summable w ℓ hw hs x).sum_add_tsum_nat_add N

theorem tailEnergy_nonneg (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (N : ℕ) (x : H) : 0 ≤ tailEnergy w ℓ N x :=
  tsum_nonneg (fun j => mul_nonneg (hw (j + N)) (sq_nonneg _))

theorem tailMass_nonneg (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (N : ℕ) : 0 ≤ tailMass w ℓ N :=
  tsum_nonneg (fun j => mul_nonneg (hw (j + N)) (sq_nonneg _))

theorem tailEnergy_le (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (N : ℕ) (x : H) :
    tailEnergy w ℓ N x ≤ tailMass w ℓ N * ‖x‖ ^ 2 := by
  have henergy := (observation_summable w ℓ hw hs x).comp_injective
    (i := fun j : ℕ => j + N) (fun i j h => Nat.add_right_cancel h)
  have hmass := hs.comp_injective
    (i := fun j : ℕ => j + N) (fun i j h => Nat.add_right_cancel h)
  have h := henergy.tsum_le_tsum
    (fun j => observation_summand_bound w ℓ hw x (j + N)) (hmass.mul_right (‖x‖ ^ 2))
  simpa only [tailEnergy, tailMass, tsum_mul_right] using h

theorem head_error_interval (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (N : ℕ) (x : H) :
    headEnergy w ℓ N x ≤ observationEnergy w ℓ x ∧
      observationEnergy w ℓ x ≤ headEnergy w ℓ N x + tailMass w ℓ N * ‖x‖ ^ 2 := by
  have he := head_add_tail_exact w ℓ hw hs N x
  have hn := tailEnergy_nonneg w ℓ hw N x
  have hb := tailEnergy_le w ℓ hw hs N x
  constructor <;> linarith

theorem tailMass_tendsto_zero (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    Tendsto (tailMass w ℓ) atTop (𝓝 0) := by
  have he (N : ℕ) : tailMass w ℓ N = observationMass w ℓ -
      ∑ j ∈ Finset.range N, w j * ‖ℓ j‖ ^ 2 := by
    have h := hs.sum_add_tsum_nat_add N
    change _ + tailMass w ℓ N = observationMass w ℓ at h
    linarith
  have h : Tendsto (fun N => observationMass w ℓ -
      ∑ j ∈ Finset.range N, w j * ‖ℓ j‖ ^ 2) atTop
      (𝓝 (observationMass w ℓ - observationMass w ℓ)) :=
    tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  change Tendsto (fun N => tailMass w ℓ N) atTop (𝓝 0)
  simpa only [he, sub_self] using h

theorem moving_tail_tendsto_zero {l : Filter α}
    (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (F : α → H) (J : α → ℕ) (hJ : Tendsto J l atTop)
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ B) :
    Tendsto (fun i => tailEnergy w ℓ (J i) (F i)) l (𝓝 0) := by
  have ht : Tendsto (fun i => tailMass w ℓ (J i) * B) l (𝓝 0) := by
    simpa only [zero_mul, Function.comp_def] using
      ((tailMass_tendsto_zero w ℓ hs).comp hJ).mul_const B
  apply squeeze_zero' (Eventually.of_forall (fun i => tailEnergy_nonneg w ℓ hw _ _)) _ ht
  filter_upwards [hbound] with i hi
  exact (tailEnergy_le w ℓ hw hs _ _).trans
    (mul_le_mul_of_nonneg_left hi (tailMass_nonneg w ℓ hw _))

/-- Independent head motion requires no rate relationship with the family. -/
theorem moving_head_tendsto {l : Filter α}
    (w : ℕ → ℝ) (ℓ : ℕ → H →L[ℝ] ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (F : α → H) (J : α → ℕ) (hJ : Tendsto J l atTop)
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ B) {L : ℝ}
    (hfull : Tendsto (fun i => observationEnergy w ℓ (F i)) l (𝓝 L)) :
    Tendsto (fun i => headEnergy w ℓ (J i) (F i)) l (𝓝 L) := by
  have ht := moving_tail_tendsto_zero w ℓ hw hs F J hJ B hbound
  have he (i : α) : headEnergy w ℓ (J i) (F i) =
      observationEnergy w ℓ (F i) - tailEnergy w ℓ (J i) (F i) := by
    linarith [head_add_tail_exact w ℓ hw hs (J i) (F i)]
  simpa only [he, sub_zero] using hfull.sub ht

end RiemannResearch.Analysis.WeightedCoordinateTruncation
