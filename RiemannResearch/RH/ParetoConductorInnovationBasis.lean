import RiemannResearch.RH.ParetoConductorSchurGain
import RiemannResearch.RH.ParetoConductorInnovationCovariance

/-!
# Independent actual conductor innovation vectors

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §3.
The coefficient space is exactly the finite type of new divisors used by the
conductor Schur gain.  Actual arithmetic covariance positivity supplies
injectivity; no abstract full-rank assumption is introduced.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
open RiemannResearch.LinearAlgebra.ConditionalSchur
noncomputable section

/-- Strict covariance positivity in the exact coefficient type used by the
actual finite Schur problem. -/
theorem conductorInnovationCovariance_subtype_pos (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q)
    (c : conductorNewConductors Q p → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : conductorNewConductors Q p, ∑ j : conductorNewConductors Q p,
      c i * c j * conductorInnovationCovariance Q p hQ i.val j.val := by
  classical
  let s := conductorNewConductors Q p
  let b : ℕ → ℝ := fun q => if h : q ∈ s then c ⟨q, h⟩ else 0
  have hb (q : s) : b q.val = c q := by simp [b, q.property]
  have hs : ∀ q ∈ s, q ∣ p * Q ∧ ¬ q ∣ Q := by
    intro q hq
    obtain ⟨hdiv, hnot⟩ := Finset.mem_filter.mp hq
    exact ⟨by simpa [Nat.mul_comm] using Nat.dvd_of_mem_divisors hdiv, hnot⟩
  obtain ⟨i, hci⟩ : ∃ i : s, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have hbn : ∃ q ∈ s, b q ≠ 0 := ⟨i.val, i.property, by rw [hb i]; exact hci⟩
  have hpos := conductorInnovationCovariance_pos p Q hp hQ s b hs hbn
  calc
    0 < ∑ q ∈ s, ∑ r ∈ s, b q * b r * conductorInnovationCovariance Q p hQ q r := hpos
    _ = _ := by
      rw [← Finset.sum_coe_sort s]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_coe_sort s]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hb q, hb r]

/-- A nonzero coefficient vector has strictly positive synthesized innovation
norm in the actual finite weighted Hilbert model. -/
theorem conductor_fluctuation_synthesis_inner_pos (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q)
    (c : conductorNewConductors Q p → ℝ) (hc : c ≠ 0) :
    0 < inner ℝ
      ((Fintype.linearCombination ℝ (fun i : conductorNewConductors Q p =>
        fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
          (conductorNewPacket Q p i))) c)
      ((Fintype.linearCombination ℝ (fun i : conductorNewConductors Q p =>
        fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
          (conductorNewPacket Q p i))) c) := by
  have hdiv (i : conductorNewConductors Q p) : i.val ∣ Q * p :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp i.property).1
  calc
    0 < ∑ i : conductorNewConductors Q p, ∑ j : conductorNewConductors Q p,
        c i * c j * conductorInnovationCovariance Q p hQ i.val j.val :=
      conductorInnovationCovariance_subtype_pos p Q hp hQ c hc
    _ = _ := by
      symm
      simp only [Fintype.linearCombination_apply, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [conductorNewPacket]
      rw [real_inner_comm]
      rw [conductorInnovationCovariance_eq_fluctuation_inner Q p hQ hp.pos
        i.val j.val (hdiv i) (hdiv j)]
      ring

/-- The actual innovation synthesis is injective, supplying the ordinary
finite-dimensional inverse Gram construction without a rank hypothesis. -/
theorem conductor_fluctuation_synthesis_injective (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q) :
    Function.Injective
      (Fintype.linearCombination ℝ (fun i : conductorNewConductors Q p =>
        fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
          (conductorNewPacket Q p i))) := by
  let U := Fintype.linearCombination ℝ (fun i : conductorNewConductors Q p =>
    fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
      (conductorNewPacket Q p i))
  have hker (c : conductorNewConductors Q p → ℝ) (hz : U c = 0) : c = 0 := by
    by_contra hc
    have hpos := conductor_fluctuation_synthesis_inner_pos p Q hp hQ c hc
    change 0 < inner ℝ (U c) (U c) at hpos
    rw [hz] at hpos
    simpa using hpos
  intro c d hcd
  change U c = U d at hcd
  have hz : U (c - d) = 0 := by rw [map_sub, hcd, sub_self]
  exact sub_eq_zero.mp (hker (c - d) hz)

end
end RiemannResearch.RH.Pareto
