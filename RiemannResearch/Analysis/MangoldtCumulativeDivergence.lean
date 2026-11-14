import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Divergence of truncated von Mangoldt cumulative energies
Source: V_vector_space_RH.pdf, Section 7.
The concrete input is the proved prime number theorem, not a new PNT hypothesis.
All signed arithmetic error energies elsewhere in the project remain unchanged.
-/
noncomputable section
open Filter MeasureTheory Set Asymptotics
open scoped Topology ENNReal BigOperators
namespace RiemannResearch.Analysis.MangoldtCumulativeDivergence

theorem psi_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  (isEquivalent_iff_tendsto_one (eventually_ne_atTop (0:ℝ))).mp
    RiemannResearch.NumberTheory.PrimeNumberTheorem.WeakPNT''

theorem exists_psi_lower :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x, A ≤ x → x/2 ≤ Chebyshev.psi x := by
  have he : ∀ᶠ x : ℝ in atTop, (1/2:ℝ) < Chebyshev.psi x / x :=
    psi_ratio_tendsto.eventually (eventually_gt_nhds (by norm_num))
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  refine ⟨max a 1, le_max_right _ _, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hh := (lt_div_iff₀ hx0).mp (ha x ((le_max_left _ _).trans hx))
  linarith

theorem weight_aestronglyMeasurable (s A : ℝ) (hA : 0 < A) :
    AEStronglyMeasurable (fun x : ℝ => x^s) (volume.restrict (Ioi A)) :=
  (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hA.trans hx)))).aestronglyMeasurable
    measurableSet_Ioi

theorem psi_energy_not_integrable (s : ℝ) (hs : s ≤ 2) :
    ¬ IntegrableOn (fun x : ℝ => Chebyshev.psi x ^ 2 * x^(-s-1)) (Ioi 1) := by
  intro h
  obtain ⟨A, hA, hlow⟩ := exists_psi_lower
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hh := (h.mono_set (Ioi_subset_Ioi hA)).const_mul 4
  have hi : IntegrableOn (fun x : ℝ => x^(1-s)) (Ioi A) := by
    apply hh.mono' (weight_aestronglyMeasurable _ _ hA0)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hA0.trans hx
    have hp := hlow x hx.le
    have hpn := Chebyshev.psi_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      x^(1-s) = x^2 * x^(-s-1) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
        congr 1
        norm_num
        ring
      _ ≤ 4 * (Chebyshev.psi x ^ 2 * x^(-s-1)) := by
        have hsq : x^2 ≤ 4 * Chebyshev.psi x^2 := by nlinarith
        have hm := mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx0.le (-s-1))
        nlinarith
  have hc := (integrableOn_Ioi_rpow_iff hA0).mp hi
  linarith

/-- The cumulative function of the actual truncation Λ 1_{n≤N}. -/
def truncated (N : ℕ) (x : ℝ) : ℝ := Chebyshev.psi (min x N)

theorem truncated_nonneg (N : ℕ) (x : ℝ) : 0 ≤ truncated N x :=
  Chebyshev.psi_nonneg _

theorem truncated_le (N : ℕ) (x : ℝ) : truncated N x ≤ Chebyshev.psi x :=
  Chebyshev.psi_mono (min_le_left _ _)

theorem truncated_mono (x : ℝ) : Monotone (fun N : ℕ => truncated N x) := by
  intro N M hNM
  exact Chebyshev.psi_mono (min_le_min le_rfl (Nat.cast_le.mpr hNM))

theorem truncated_measurable (N : ℕ) : Measurable (truncated N) :=
  Chebyshev.psi_mono.measurable.comp (measurable_id.min measurable_const)

def density (s : ℝ) (N : ℕ) (x : ℝ) : ℝ := truncated N x ^ 2 * x^(-s-1)

theorem density_aestronglyMeasurable (s : ℝ) (N : ℕ) :
    AEStronglyMeasurable (density s N) (volume.restrict (Ioi 1)) :=
  ((truncated_measurable N).pow_const 2).aestronglyMeasurable.mul
    (weight_aestronglyMeasurable _ _ zero_lt_one)

theorem density_nonneg (s : ℝ) (N : ℕ) {x : ℝ} (hx : 1 < x) :
    0 ≤ density s N x :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)

theorem density_mono (s : ℝ) {x : ℝ} (hx : 1 < x) :
    Monotone (fun N => density s N x) := by
  intro N M hNM
  exact mul_le_mul_of_nonneg_right
    (sq_le_sq₀ (truncated_nonneg _ _) (truncated_nonneg _ _) |>.mpr (truncated_mono x hNM))
    (Real.rpow_nonneg (zero_lt_one.trans hx).le _)

theorem density_integrable (s : ℝ) (hs : 0 < s) (N : ℕ) :
    IntegrableOn (density s N) (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s-1 < -1) zero_lt_one).const_mul
    (Chebyshev.psi N ^ 2)
  apply hi.mono' (density_aestronglyMeasurable s N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg s N hx)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  exact (sq_le_sq₀ (truncated_nonneg _ _) (Chebyshev.psi_nonneg _) ).mpr
    (Chebyshev.psi_mono (min_le_right _ _))

def energy (s : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi 1, ENNReal.ofReal (density s N x)

theorem energy_ne_top (s : ℝ) (hs : 0 < s) (N : ℕ) : energy s N ≠ ⊤ := by
  apply (lintegral_ofReal_ne_top_iff_integrable (density_aestronglyMeasurable s N) _).mpr
    (density_integrable s hs N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact density_nonneg s N hx

theorem energy_mono (s : ℝ) : Monotone (energy s) := by
  intro N M hNM
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ENNReal.ofReal_le_ofReal (density_mono s hx hNM)

theorem energy_iSup_eq_top (s : ℝ) (hs : s ≤ 2) : ⨆ N, energy s N = ⊤ := by
  have heq : (fun x : ℝ => ⨆ N, ENNReal.ofReal (density s N x)) =ᵐ[volume.restrict (Ioi 1)]
      (fun x => ENNReal.ofReal (Chebyshev.psi x ^ 2 * x^(-s-1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply le_antisymm
    · apply iSup_le
      intro N
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (truncated_nonneg _ _) (Chebyshev.psi_nonneg _)).mpr (truncated_le N x))
        (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    · obtain ⟨N, hN⟩ := exists_nat_ge x
      calc
        _ = ENNReal.ofReal (density s N x) := by simp [density, truncated, min_eq_left hN]
        _ ≤ _ := le_iSup (fun N => ENNReal.ofReal (density s N x)) N
  have hsup := lintegral_iSup'
    (fun N => (density_aestronglyMeasurable s N).aemeasurable.ennreal_ofReal)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact ENNReal.ofReal_mono.comp (density_mono s hx))
  rw [lintegral_congr_ae heq] at hsup
  unfold energy
  rw [← hsup]
  by_contra hfin
  have hm : AEStronglyMeasurable (fun x : ℝ => Chebyshev.psi x ^ 2 * x^(-s-1))
      (volume.restrict (Ioi 1)) :=
    (Chebyshev.psi_mono.measurable.pow_const 2).aestronglyMeasurable.mul
      (weight_aestronglyMeasurable _ _ zero_lt_one)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 1)]
      (fun x : ℝ => Chebyshev.psi x ^ 2 * x^(-s-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  exact psi_energy_not_integrable s hs ((lintegral_ofReal_ne_top_iff_integrable hm hn).mp hfin)

theorem energy_tendsto_top (s : ℝ) (hs : s ≤ 2) :
    Tendsto (energy s) atTop (𝓝 ⊤) := by
  rw [← energy_iSup_eq_top s hs]
  exact tendsto_atTop_iSup (energy_mono s)

theorem truncated_ratio_tendsto_zero (N : ℕ) :
    Tendsto (fun x : ℝ => truncated N x / x) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Chebyshev.psi N / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Chebyshev.psi N)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (N:ℝ)] with x hx
  simp [truncated, min_eq_right hx]

theorem energy_toReal_tendsto_atTop (s : ℝ) (hs0 : 0 < s) (hs : s ≤ 2) :
    Tendsto (fun N => (energy s N).toReal) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  have hR := (energy_tendsto_top s hs).eventually
    (eventually_gt_nhds (ENNReal.ofReal_lt_top : ENNReal.ofReal (max R 0) < ⊤))
  filter_upwards [hR] with N hN
  have hh := ENNReal.toReal_mono (energy_ne_top s hs0 N) hN.le
  rw [ENNReal.toReal_ofReal (le_max_right _ _)] at hh
  exact (le_max_left _ _).trans hh

theorem real_energy_eq (s : ℝ) (N : ℕ) :
    (∫ x in Ioi 1, density s N x) = (energy s N).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae _ (density_aestronglyMeasurable s N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact density_nonneg s N hx

theorem real_energy_tendsto_atTop (s : ℝ) (hs0 : 0 < s) (hs : s ≤ 2) :
    Tendsto (fun N => ∫ x in Ioi 1, density s N x) atTop atTop := by
  simpa only [real_energy_eq] using energy_toReal_tendsto_atTop s hs0 hs

def coordinateSquare (s : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n ^ 2 * (n:ℝ)^(-s)

theorem coordinateSquare_nonneg (s : ℝ) (n : ℕ) : 0 ≤ coordinateSquare s n :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem coordinateSquare_summable (s : ℝ) (hs : 1 < s) :
    Summable (coordinateSquare s) := by
  let δ : ℝ := (s-1)/2
  have hd : 0 < δ := by dsimp [δ]; linarith
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)^2 / (n:ℝ)^δ) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_pow_atTop δ (2:ℝ) hd).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ)) using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_two]
  have hb : ∀ᶠ n : ℕ in atTop, Real.log (n:ℝ)^2 / (n:ℝ)^δ ≤ 1 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  apply (Real.summable_nat_rpow.mpr (show δ-s < -1 by dsimp [δ]; linarith)).of_norm_bounded_eventually_nat
  filter_upwards [hb, eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hlog : Real.log (n:ℝ)^2 ≤ (n:ℝ)^δ :=
    (div_le_one (Real.rpow_pos_of_pos hnpos δ)).mp hn
  have hv : ArithmeticFunction.vonMangoldt n ^ 2 ≤ Real.log (n:ℝ)^2 := by
    have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn0)
    exact (sq_le_sq₀ ArithmeticFunction.vonMangoldt_nonneg hl).mpr
      ArithmeticFunction.vonMangoldt_le_log
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateSquare_nonneg s n)]
  calc
    coordinateSquare s n ≤ (n:ℝ)^δ * (n:ℝ)^(-s) :=
      mul_le_mul_of_nonneg_right (hv.trans hlog) (Real.rpow_nonneg hnpos.le _)
    _ = (n:ℝ)^(δ-s) := by rw [← Real.rpow_add hnpos]; congr 1

/-- The squared weighted coordinate truncation error tends to zero. -/
theorem coordinate_tail_tendsto_zero (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N => (∑' n, coordinateSquare s n) -
      ∑ n ∈ Finset.range N, coordinateSquare s n) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => ∑' n, coordinateSquare s n)
      atTop (𝓝 (∑' n, coordinateSquare s n)) := tendsto_const_nhds
  simpa using hc.sub (coordinateSquare_summable s hs).hasSum.tendsto_sum_nat

/-- No uniform summation bound even on the prescribed finite Mangoldt vectors.
For 1<s≤2 the source squared norms stay bounded while the output energies diverge. -/
theorem no_uniform_mangoldt_summation_bound (s : ℝ) (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, energy s N ≤
      ENNReal.ofReal (C * ∑ n ∈ Finset.range (N+1), coordinateSquare s n) := by
  rintro ⟨C,hC,hbound⟩
  have hb : ⨆ N, energy s N ≤ ENNReal.ofReal (C * ∑' n, coordinateSquare s n) := by
    apply iSup_le
    intro N
    exact (hbound N).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      ((coordinateSquare_summable s hs1).sum_le_tsum _ (fun n _ => coordinateSquare_nonneg s n)) hC))
  rw [energy_iSup_eq_top s hs2] at hb
  exact ENNReal.ofReal_ne_top (top_unique hb)


/-- Explicit finite-sum identification, so the cutoff is the prescribed arithmetic one. -/
theorem truncated_eq_sum (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    truncated N x =
      ∑ n ∈ Finset.Icc 0 N, if (n:ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  rw [truncated, Chebyshev.psi_eq_sum_Icc, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter,
    Nat.le_floor_iff (le_min hx (Nat.cast_nonneg N)), le_min_iff, Nat.cast_le]
  tauto

def coordinate (s : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n * (n:ℝ)^(-s/2) : ℝ)

theorem coordinate_norm_sq (s : ℝ) (n : ℕ) :
    ‖coordinate s n‖ ^ 2 = coordinateSquare s n := by
  by_cases hn : n = 0
  · subst n
    simp [coordinate, coordinateSquare]
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp only [coordinate, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    coordinateSquare]
  rw [← Real.rpow_natCast ((n:ℝ)^(-s/2)) 2, ← Real.rpow_mul hnpos.le]
  congr 2
  norm_num

theorem coordinate_memℓp (s : ℝ) (hs : 1 < s) : Memℓp (coordinate s) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, coordinate_norm_sq] using
    coordinateSquare_summable s hs

def coordinateVector (s : ℝ) (hs : 1 < s) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨coordinate s, coordinate_memℓp s hs⟩

/-- The finite von Mangoldt vectors really converge in the source Hilbert norm. -/
theorem coordinate_truncations_tendsto (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, lp.single 2 n (coordinate s n))
      atTop (𝓝 (coordinateVector s hs)) :=
  (lp.hasSum_single (by norm_num) (coordinateVector s hs)).tendsto_sum_nat

end RiemannResearch.Analysis.MangoldtCumulativeDivergence
