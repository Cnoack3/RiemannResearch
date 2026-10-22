import RiemannResearch.RH.ParetoSieveContrastClosure

/-!
# Complete parity energy for arbitrary actual Hilbert vectors

Source: the user's Pareto parity-closure handoff, 21 September 2026,
for the component decomposition and the retained full-energy requirement.

Every finite collection of odd pair contrasts is an orthogonal projection.
The resulting complete contrast series is therefore summable for every
actual Hilbert vector and is bounded by its entire norm.  The remaining
energy is retained explicitly and is nonnegative.  No smallness of this
complementary energy, and no unconditional RH conclusion, is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization.TailCapacity

theorem fullOddPairContrast_summand_nonneg (f : ThresholdHilbert) (p : ℕ) :
    0 ≤ coprimePairMass 2 p *
      (inner ℝ (differenceCertificate (p-2)) f)^2 / 2 := by
  exact div_nonneg (mul_nonneg (coprimePairMass_nonneg 2 p) (sq_nonneg _))
    (by norm_num)

theorem fullOddPairContrast_finite_le (f : ThresholdHilbert) (s : Finset ℕ) :
    (∑ p ∈ s, coprimePairMass 2 p *
      (inner ℝ (differenceCertificate (p-2)) f)^2 / 2) ≤ ‖f‖^2 := by
  classical
  let t := s.filter (coprimePairIndex 2)
  have ht (p : ℕ) (hp : p ∈ t) : coprimePairIndex 2 p :=
    (Finset.mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-2) (t : Set ℕ) := by
    intro p hp q hq he
    have hp3 := (ht p hp).1
    have hq3 := (ht q hq).1
    change p-2=q-2 at he
    omega
  have hsep : (((t.image (fun p : ℕ => p-2)) : Finset ℕ) : Set ℕ).Pairwise
      (fun k l => k+1<l ∨ l+1<k) := by
    intro k hk l hl hne
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
    have hp3 := (ht p hp).1
    have hq3 := (ht q hq).1
    have hpo := (ht p hp).2.1
    have hqo := (ht q hq).2.1
    omega
  calc
    _ = ∑ p ∈ t, coprimePairMass 2 p *
        (inner ℝ (differenceCertificate (p-2)) f)^2 / 2 := by
      dsimp only [t]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hi : coprimePairIndex 2 p
      · simp [hi]
      · simp [coprimePairMass, hi]
    _ = parityContrastEnergy (t.image (fun p : ℕ => p-2)) f := by
      rw [parityContrastEnergy, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro p hp
      have hp3 := (ht p hp).1
      have hnat : p-2+2=p := by omega
      have hcast : ((p-2 : ℕ) : ℝ)+2=(p : ℝ) := by exact_mod_cast hnat
      rw [coprimePairMass, if_pos (ht p hp), hcast]
      ring
    _ ≤ ‖f‖^2 := parityContrastEnergy_le_full _ f hsep

/-- The full series is well defined for every actual Hilbert vector. -/
theorem fullOddPairContrast_summable (f : ThresholdHilbert) :
    Summable (fun p => coprimePairMass 2 p *
      (inner ℝ (differenceCertificate (p-2)) f)^2 / 2) :=
  summable_of_sum_le (fullOddPairContrast_summand_nonneg f)
    (fullOddPairContrast_finite_le f)

theorem fullOddPairContrastEnergy_nonneg (f : ThresholdHilbert) :
    0 ≤ fullOddPairContrastEnergy f :=
  tsum_nonneg (fullOddPairContrast_summand_nonneg f)

/-- A genuine full-norm bound, with no truncation or summability premise. -/
theorem fullOddPairContrastEnergy_le_norm_sq (f : ThresholdHilbert) :
    fullOddPairContrastEnergy f ≤ ‖f‖^2 :=
  Real.tsum_le_of_sum_le (fullOddPairContrast_summand_nonneg f)
    (fullOddPairContrast_finite_le f)

/-- Energy outside the entire odd-pair contrast component. -/
def fullParityRemainingEnergy (f : ThresholdHilbert) : ℝ :=
  ‖f‖^2 - fullOddPairContrastEnergy f

theorem fullParityRemainingEnergy_nonneg (f : ThresholdHilbert) :
    0 ≤ fullParityRemainingEnergy f :=
  sub_nonneg.mpr (fullOddPairContrastEnergy_le_norm_sq f)

theorem fullParity_energy_completion (f : ThresholdHilbert) :
    ‖f‖^2 = fullOddPairContrastEnergy f + fullParityRemainingEnergy f := by
  unfold fullParityRemainingEnergy
  ring

/-- Once the contrast is solved, full-energy convergence is exactly the
remaining-energy question; no discarded sign or mixed term is involved. -/
theorem fullParity_norm_sq_tendsto_zero_iff (f : ℕ → ThresholdHilbert)
    (hc : Tendsto (fun n => fullOddPairContrastEnergy (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖f n‖^2) atTop (𝓝 0) ↔
      Tendsto (fun n => fullParityRemainingEnergy (f n)) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [fullParityRemainingEnergy, sub_self] using h.sub hc
  · intro h
    have hsum := hc.add h
    simpa only [← fullParity_energy_completion, add_zero] using hsum

end RiemannResearch.RH.Pareto
