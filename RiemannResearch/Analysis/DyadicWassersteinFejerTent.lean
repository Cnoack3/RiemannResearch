import RiemannResearch.Analysis.CircleFejerTent
import RiemannResearch.Analysis.DyadicPrimeTentFejerLimit
import RiemannResearch.Analysis.DyadicWassersteinPrimeCosine

/-! # Optimal individual marginal contributions to the dyadic Wasserstein lower bound

A fixed finite polynomial is tested at every height. Its limiting correction
uses only fixed prime powers. After passing to this height limit one takes the
degree to infinity. All operations concern a single zero occurrence sampled
with analytic multiplicity. -/

noncomputable section
open Filter MeasureTheory Zeta23 Finset
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open ActualZeroOrdinate ZeroOrdinate MontgomeryLocalMass PrimePhaseWindows

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem tent_haar (N : ℕ) :
    (∫ x, fejerTent N x ∂AddCircle.haarAddCircle) = ∑ j ∈ range N, fejerTentWeight N j := by
  change (∫ x : UnitAddCircle, ∑ j ∈ range N,
    fejerTentWeight N j * (1-harmonicCosine (2*j+1 : ℕ) x) ∂AddCircle.haarAddCircle) = _
  have hi (j : ℕ) : Integrable (harmonicCosine (2*j+1 : ℕ)) AddCircle.haarAddCircle :=
    (harmonicCosine _).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_sub (integrable_const _) (hi j),
      integral_harmonicCosine (by exact_mod_cast (by omega : 2*j+1 ≠ 0))]
    simp
  · intro j _
    exact ((integrable_const _).sub (hi j)).const_mul _

private theorem tent_bias_expansion {U : ℝ} (hU : 0 ≤ U) (hm : mass U ≠ 0) (N p : ℕ) :
    angularBias p (fejerTent N) U =
      ∑ j ∈ range N, -fejerTentWeight N j * dyadicPrimeCosineMean (p^(2*j+1)) U := by
  let h (j : ℕ) (ρ : ℂ) := harmonicCosine (2*j+1 : ℕ) (PrimePhaseTorus.primePhase p ρ.im)
  have hmean (j : ℕ) : dyadicPrimeCosineMean (p^(2*j+1)) U = massSum U (h j) / mass U := by
    rw [massSum_eq_realSum_sub hU (h j)]
    simp only [dyadicPrimeCosineMean, h, harmonicCosine_primePhase, Int.cast_natCast, Nat.cast_pow,
      Real.log_pow, mass]
  have hsample : massSum U (fun ρ => fejerTent N (PrimePhaseTorus.primePhase p ρ.im)) =
      ∑ j ∈ range N, fejerTentWeight N j * (mass U - massSum U (h j)) := by
    change (∑ i : Occ U, ∑ j ∈ range N, fejerTentWeight N j * (1-h j i.1.val)) = _
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [← mul_sum, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, massSum, mass,
      show Fintype.card (Occ U) = Ncount U (2*U) from card_windowCopies _ _]
  rw [angularBias, tent_haar, hsample, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [hmean]
  field_simp [hm]
  ring

/-- First limit, with both the prime and the Fejér degree fixed. -/
theorem tendsto_log_angularBias_fejerTent (N : ℕ) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun U => Real.log U * angularBias p (fejerTent N) U) atTop
      (𝓝 (primeFejerConstant N p)) := by
  have h := tendsto_finsetSum (range N) (fun j _ =>
    (tendsto_log_mul_dyadicPrimePowerCosineMean hp (by omega : 0 < 2*j+1)).const_mul
      (-fejerTentWeight N j))
  have he : (∑ j ∈ range N, -fejerTentWeight N j *
      (-Real.log p / Real.sqrt (p:ℝ)^(2*j+1))) = primeFejerConstant N p := by
    rw [primeFejerConstant, mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [fejerTentWeight, inv_pow, div_eq_mul_inv]; ring
  rw [he] at h
  apply h.congr'
  obtain ⟨a,b,ha,hb,hm⟩ := dyadic_mass_bounds
  filter_upwards [hm, eventually_gt_atTop (1:ℝ)] with U hm hU
  have hlog := Real.log_pos hU
  have hu : 0 < U := by linarith
  have hn : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  rw [tent_bias_expansion hu.le hn.ne', mul_sum]
  change (∑ j ∈ range N, -fejerTentWeight N j *
    (Real.log U * dyadicPrimeCosineMean (p^(2*j+1)) U)) = _
  apply sum_congr rfl
  intro j _
  ring

/-- Every strict lower coefficient for the limiting sum is valid eventually.
Pick the witness degree before applying the fixed-degree large-height theorem. -/
theorem eventually_horizontal_add_primeTent_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {c : ℝ}
    (hc : c < 3/4 - Real.log 2 + ∑ p ∈ P, primeTentConstant p) :
    ∀ᶠ U : ℝ in atTop, massSum U (fun ρ => |ρ.re - 1/2|) / mass U + c / Real.log U ≤
      wassersteinOne P (mu P U) (nu P) := by
  have hs := (tendsto_finsetSum P (fun p hp => tendsto_primeFejerConstant (hP p hp))).const_add
    (3/4 - Real.log 2)
  obtain ⟨N,hN⟩ := ((tendsto_order.1 hs).1 c hc).exists
  apply eventually_horizontal_add_angular_lower P (fun _ => fejerTent N)
    (fun p => primeFejerConstant N p)
  · exact fun _ => fejerTent_zero N
  · exact fun _ => fejerTent_lipschitz N
  · exact fun p => tendsto_log_angularBias_fejerTent N (hP p p.property)
  · rw [Finset.sum_coe_sort P (fun q : ℕ => primeFejerConstant N q)]
    simpa only [Pi.add_apply, Finset.sum_apply] using hN

/-- Extended-real formulation also accommodates an infinite lower limit. -/
theorem primeTent_le_liminf_scaled_wasserstein (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((3/4 - Real.log 2 + ∑ p ∈ P, primeTentConstant p : ℝ) : EReal) ≤
      liminf (fun U : ℝ => ((Real.log U * (wassersteinOne P (mu P U) (nu P) -
        massSum U (fun ρ => |ρ.re - 1/2|) / mass U) : ℝ) : EReal)) atTop :=
  le_liminf_scaled_wasserstein P _ (fun _ hc => eventually_horizontal_add_primeTent_lower P hP hc)

end RiemannResearch.Analysis.DyadicZeroWasserstein
