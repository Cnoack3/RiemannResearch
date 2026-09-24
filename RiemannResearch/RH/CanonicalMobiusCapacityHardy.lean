import RiemannResearch.RH.CanonicalMobiusCapacityBounds
import RiemannResearch.RH.CanonicalMobiusMovingBoundary

/-!
# Quantitative capacity and Hardy bounds for actual signed Möbius optimizers

Source: comparison of commits d66e444 and 1235e6b requested by the user,
24 September 2026. The arithmetic input is the repository's formal PNT
ceiling. The signed-covariance minimum is attained even for singular Gram
matrices. No RH-strength capacity or coefficient hypothesis is used.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Any exact-head candidate with the quantitative arithmetic full-norm ceiling
has the same explicit residual budget as the canonical competitor. -/
theorem residualCeiling_of_norm_bound (f : ThresholdHilbert) (C : ℝ) (N : ℕ)
    (hN : 2 ≤ N) (he : ‖f‖^2/(N : ℝ) ≤ canonicalMobiusEnergyCeiling C N) :
    ‖hilbertOne-f‖^2 ≤ ((N : ℝ)+1)*canonicalMobiusResidualCeiling C N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := canonicalMobiusEnergyCeiling_nonneg C N hN
  have hf := (div_le_iff₀ hNR).mp he
  have hh := mul_self_le_mul_self (norm_nonneg (hilbertOne-f)) (norm_sub_le hilbertOne f)
  have hone := hilbertOne_norm_sq
  have hs := sq_nonneg (‖hilbertOne‖-‖f‖)
  have hr : ‖hilbertOne-f‖^2 ≤ 2*‖f‖^2+2 := by nlinarith
  have hi : 0 ≤ 3/(N : ℝ) := by positivity
  have heq : ((N : ℝ)+1)*canonicalMobiusResidualCeiling C N =
      2*(N : ℝ)*canonicalMobiusEnergyCeiling C N+
        2*canonicalMobiusEnergyCeiling C N+3+3/(N : ℝ) := by
    unfold canonicalMobiusResidualCeiling
    field_simp [hNR.ne']
    ring
  rw [heq]
  nlinarith

/-- A finite scheduling certificate for any actual exact-head candidate. -/
theorem exactHead_scheduled_hardy_bound (f : ThresholdHilbert) (N : ℕ)
    (hN : 0 < N)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1)
    (q θ σ : ℝ) (hq : 0 < q) (hql : ((N : ℝ)+1)⁻¹ ≤ q) (hqu : q ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbudget : ‖hilbertOne-f‖^2 ≤ ((N : ℝ)+1)*q)
    (hσ : (2+θ*Real.log q/Real.log ((N : ℝ)+1))/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin (hilbertOne-f)
      (WeightedMellin.verticalPoint σ w)‖^2) ≤ q^(1-θ) := by
  have hb : 1 < (N : ℝ)+1 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hu := WeightedMellin.log_schedule_mem_Icc hb hq hql hqu hθ0 hθ1
  have hz : ∀ j, 0 < j → j ≤ N → hilbertSequence (hilbertOne-f) j = 0 := by
    intro j hj hjN
    change hilbertSequenceLinear (hilbertOne-f) j = 0
    rw [map_sub]
    change hilbertSequence hilbertOne j-hilbertSequence f j = 0
    rw [hhead j hj hjN, hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt hj]
  have hline := WeightedMellin.hardy_energy_le
    (WeightedMellin.finiteEnergy_mono (complexPhysicalStep_finiteEnergy (hilbertOne-f)) hu.1) hσ
  rw [complexPhysicalStep_transform] at hline
  exact hline.trans ((zeroHead_weightedEnergy_le _ N hz _ hu.1).trans
    (WeightedMellin.cutoff_power_times_energy_le hb hq hbudget))

namespace CoefficientStabilization.SignedCovariance
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The attained complete-tail optimizer is no worse in full norm than any
included canonical competitor. All signed covariances remain in the minimum. -/
theorem optimizedAverage_norm_sq_le_member (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (hindex : ∀ i, N ≤ k i) (i : ι) :
    ‖optimizedAverage N k hk‖^2 ≤ ‖canonicalMobiusHilbert (k i)‖^2 := by
  have hp := capacity_pos N k hk
  have h := capacity_mul_tail_energy_ge_one N k hk i
  have hinv : (capacity N k hk)⁻¹ ≤ ‖tailFamily N k i‖^2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).2
    nlinarith
  rw [optimizedAverage_norm_sq N k hk hindex,
    exact_head_norm_sq_split (canonicalMobiusHilbert (k i)) N
      (fun j hj hjN => canonicalMobiusHilbert_exact (k i) j hj (hjN.trans (hindex i)))]
  change (capacity N k hk)⁻¹ ≤ ‖hilbertTailShift (canonicalMobiusHilbert (k i)) N‖^2 at hinv
  linarith

/-- Exact weighted energy of the actual covariance optimizer. The inverse
capacity is its full tail energy; the nonnegative weight defect is retained. -/
theorem optimizedAverage_weighted_energy_exact (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (hindex : ∀ i, N ≤ k i) (u : ℝ) (hu : 1 ≤ u) :
    WeightedMellin.energy (complexPhysicalStep (optimizedAverage N k hk)) u =
      (1-((N : ℝ)+1)^(-u))/u +
        ((N : ℝ)+1)^(1-u)*(capacity N k hk)⁻¹ -
        WeightedMellin.headTailWeightDefect
          (complexPhysicalStep (optimizedAverage N k hk)) ((N : ℝ)+1) u := by
  have h := WeightedMellin.energy_eq_exact_head_add_power_tail_sub_defect
    (complexPhysicalStep_finiteEnergy (optimizedAverage N k hk))
    (show 1 ≤ (N : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) N]) hu
    (complexPhysicalStep_exact_head_ae N
      (fun j hj hjN => optimizedAverage_exact N k hk hindex j (by omega) hjN))
  rw [complexPhysicalStep_critical_energy, optimizedAverage_norm_sq N k hk hindex] at h
  have he : (N : ℝ)/((N : ℝ)+1)+(capacity N k hk)⁻¹-1+1/((N : ℝ)+1) =
      (capacity N k hk)⁻¹ := by
    field_simp
    ring
  simpa only [he] using h

/-- Quantitative inverse-Gram capacity, uniform over finite dimensions and
horizons. The only family requirements are positive indices and inclusion
of the cutoff competitor; no invertibility assumption occurs. -/
theorem capacity_eventual_quantitative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (J : Type) [Fintype J] [Nonempty J] (k : J → ℕ)
        (hk : ∀ i, 0 < k i), (∀ i, N ≤ k i) → (∃ i, k i = N) →
        1 ≤ ((N : ℝ)*canonicalMobiusEnergyCeiling C N -
          (N : ℝ)/((N : ℝ)+1))*capacity N k hk := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, eventually_ge_atTop (2 : ℕ)] with N he hN J _ _ k hk hindex hi
  obtain ⟨i,hi⟩ := hi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤ canonicalMobiusEnergyCeiling C N at he
  have hf := (div_le_iff₀ hNR).mp he
  have h := optimizedAverage_norm_sq_le_member N k hk hindex i
  rw [hi] at h
  rw [optimizedAverage_norm_sq N k hk hindex] at h
  have ht : (capacity N k hk)⁻¹ ≤ (N : ℝ)*canonicalMobiusEnergyCeiling C N -
      (N : ℝ)/((N : ℝ)+1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ht (capacity_pos N k hk).le
  simpa only [inv_mul_cancel₀ (capacity_pos N k hk).ne'] using hm

/-- Every growing signed-covariance dictionary containing its cutoff has the
same unconditional explicit moving-Hardy bound as the arithmetic competitor.
The optimized vectors and all their coefficients are actual defined objects. -/
theorem optimizedAverage_explicit_moving_hardy
    {J : ℕ → Type*} [∀ N, Fintype (J N)] [∀ N, Nonempty (J N)]
    (k : ∀ N, J N → ℕ) (hk : ∀ N i, 0 < k N i)
    (hindex : ∀ N i, N ≤ k N i)
    (hcontains : ∀ᶠ N : ℕ in atTop, ∃ i, k N i = N) :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto (fun N => mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N/2)
        atTop (𝓝 1) ∧
      ∀ᶠ N : ℕ in atTop,
        mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N/2 < 1 ∧
        ‖optimizedAverage N (k N) (hk N)‖^2/(N : ℝ) ≤ canonicalMobiusEnergyCeiling C N ∧
        ∀ σ : ℝ, mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N/2 < σ →
          (∫ w : ℝ, ‖paretoMellin
            (hilbertOne-optimizedAverage N (k N) (hk N))
            (WeightedMellin.verticalPoint σ w)‖^2) ≤
              Real.sqrt (canonicalMobiusResidualCeiling C N) := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  have hq := canonicalMobiusResidualCeiling_tendsto_zero C
  have hlow : ∀ᶠ N : ℕ in atTop,
      (Real.log ((N : ℝ)+1))⁻¹ ≤ canonicalMobiusResidualCeiling C N :=
    (eventually_ge_atTop (2 : ℕ)).mono
      (fun N hN => canonicalMobiusResidualCeiling_log_lower C N hN)
  refine ⟨C,hC,mobiusBudgetHardyBoundary_tendsto_one hq hlow,?_⟩
  filter_upwards [hE,hcontains,eventually_ge_atTop (2 : ℕ),
    hq.eventually (gt_mem_nhds zero_lt_one)] with N he hcontainsN hN hqu
  obtain ⟨i,hi⟩ := hcontainsN
  have hn := optimizedAverage_norm_sq_le_member N (k N) (hk N) (hindex N) i
  rw [hi] at hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heOpt := (div_le_div_of_nonneg_right hn hNR.le).trans he
  have hql : ((N : ℝ)+1)⁻¹ ≤ canonicalMobiusResidualCeiling C N := by
    simpa only [one_div] using canonicalMobiusResidualCeiling_lower C N hN
  have hqp : 0 < canonicalMobiusResidualCeiling C N :=
    lt_of_lt_of_le (inv_pos.mpr (by positivity)) hql
  have hl : 0 < Real.log ((N : ℝ)+1) := Real.log_pos (by linarith)
  have hneg := Real.log_neg hqp hqu
  have hd : (1/2 : ℝ)*Real.log (canonicalMobiusResidualCeiling C N)/
      Real.log ((N : ℝ)+1) < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hneg) hl
  refine ⟨?_,heOpt,?_⟩
  · unfold mobiusBudgetExponent
    linarith
  · intro σ hσ
    have h := exactHead_scheduled_hardy_bound (optimizedAverage N (k N) (hk N)) N
      (by omega) (optimizedAverage_exact N (k N) (hk N) (hindex N))
      (canonicalMobiusResidualCeiling C N) (1/2) σ hqp hql hqu.le
      (by norm_num) (by norm_num) (residualCeiling_of_norm_bound _ C N hN heOpt) hσ
    rw [show (1 : ℝ)-1/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow] at h
    exact h

end CoefficientStabilization.SignedCovariance
end RiemannResearch.RH.Pareto
