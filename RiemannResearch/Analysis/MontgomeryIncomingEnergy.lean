import RiemannResearch.Analysis.MontgomeryIncomingResolvent
import RiemannResearch.RH.WeilExplicitFormula.MV.Spacing

/-! # Mean square of the incoming resolvent boundary error -/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryIncomingEnergy
open MontgomeryFiniteResolventSignal MontgomeryResolventWeilTest MontgomeryIncomingResolvent

theorem allSignal_measurable (u : ℝ) : Measurable (allSignal u) := by
  letI : Countable Zeta23.zetaZeroConfig.carrier := ActualZeroGaussianLaplace.actualZero_countable
  apply Measurable.tsum
  intro ρ
  unfold fullZeroTerm rationalTerm
  fun_prop

theorem actualSignal_measurable (T u : ℝ) : Measurable (actualSignal T u) := by
  unfold actualSignal signal rationalTerm
  fun_prop

private def envelope (T B t : ℝ) : ℝ := 2*B^2*((1/(1+t))^2+(1/(1+(T-t)))^2)

private theorem envelope_integrable {T : ℝ} (hT : 0 ≤ T) (B : ℝ) :
    IntegrableOn (envelope T B) (Ioc 0 T) := by
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_Icc
  unfold envelope
  have hp : ∀ t ∈ Icc (0:ℝ) T, 1+t ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hm : ∀ t ∈ Icc (0:ℝ) T, 1+(T-t) ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.2])
  exact (((continuousOn_const.div (by fun_prop) hp).pow 2).add
    ((continuousOn_const.div (by fun_prop) hm).pow 2)).const_mul _

private theorem integral_envelope_le {T : ℝ} (hT : 0 ≤ T) (B : ℝ) :
    (∫ t in (0:ℝ)..T, envelope T B t) ≤ 4*B^2 := by
  let g := fun t : ℝ => (1/(1+t))^2
  have hg : ContinuousOn g (Icc (0:ℝ) T) :=
    (continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))).pow 2
  have hr : ContinuousOn (fun t => g (T-t)) (Icc (0:ℝ) T) :=
    hg.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hgi : IntervalIntegrable g volume 0 T := hg.intervalIntegrable_of_Icc hT
  have hri : IntervalIntegrable (fun t => g (T-t)) volume 0 T := hr.intervalIntegrable_of_Icc hT
  have hreflect : (∫ t in (0:ℝ)..T, g (T-t)) = ∫ t in (0:ℝ)..T, g t := by
    simpa only [sub_self,sub_zero] using intervalIntegral.integral_comp_sub_left g T (a := 0) (b := T)
  have hL : (∫ t in (0:ℝ)..T, g t) ≤ 1 := by
    have hh := Zeta23.MV.Adm.integral_inv_sq_Icc hT (c := -1) (Or.inl (by norm_num))
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT] at hh
    have he : g = fun t : ℝ => ((t - -1)^2)⁻¹ := by
      funext t; simp [g,add_comm,inv_pow]
    rw [he,hh]
    have hp : 0 ≤ (T - -1)⁻¹ := inv_nonneg.mpr (by linarith)
    norm_num
    <;> linarith
  change (∫ t in (0:ℝ)..T, (2*B^2)*(g t+g (T-t))) ≤ _
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hgi hri,hreflect]
  nlinarith only [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ B^2)]

private theorem envelope_domination {B T t : ℝ} (ht : t ∈ Icc 0 T) (hB : 0 ≤ B) {x : ℂ}
    (hx : ‖x‖ ≤ B*(1/(1+t)+1/(1+(T-t)))) : ‖x‖^2 ≤ envelope T B t := by
  have h := pow_le_pow_left₀ (norm_nonneg x) hx 2
  let a := 1/(1+t)
  let b := 1/(1+(T-t))
  change ‖x‖^2 ≤ (B*(a+b))^2 at h
  change ‖x‖^2 ≤ 2*B^2*(a^2+b^2)
  nlinarith only [h,sq_nonneg (B*(a-b))]

theorem exists_incoming_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T u : ℝ, 5 ≤ T → 0 ≤ u →
      IntegrableOn (fun t : ℝ => ‖allSignal u t-actualSignal T u t‖^2) (Ioc 0 T) ∧
      (∫ t in (0:ℝ)..T, ‖allSignal u t-actualSignal T u t‖^2) ≤ C*Real.exp u*(Real.log (2*T+4))^2 := by
  obtain ⟨K,hK,hbound⟩ := exists_incoming_bound
  refine ⟨4*K^2,by positivity,fun T u hT hu => ?_⟩
  have hT' : 0 ≤ T := by linarith
  let B := K*Real.exp (u/2)*Real.log (2*T+4)
  have hB : 0 ≤ B := by
    have hlog := Real.log_nonneg (show 1 ≤ 2*T+4 by linarith)
    dsimp [B]; positivity
  have hE := envelope_integrable hT' B
  have hm : Measurable (fun t : ℝ => ‖allSignal u t-actualSignal T u t‖^2) :=
    ((allSignal_measurable u).sub (actualSignal_measurable T u)).norm.pow_const 2
  have hle : ∀ t ∈ Icc (0:ℝ) T, ‖allSignal u t-actualSignal T u t‖^2 ≤ envelope T B t :=
    fun t ht => envelope_domination ht hB (hbound T u t hT hu ht)
  have hN : IntegrableOn (fun t : ℝ => ‖allSignal u t-actualSignal T u t‖^2) (Ioc 0 T) := by
    apply hE.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖(‖allSignal u t-actualSignal T u t‖^2 : ℝ)‖ ≤ envelope T B t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle t (Ioc_subset_Icc_self ht)
  refine ⟨hN,?_⟩
  have he : Real.exp (u/2)^2 = Real.exp u := by rw [pow_two,← Real.exp_add]; congr 1; ring
  calc
    _ ≤ ∫ t in (0:ℝ)..T, envelope T B t := by
      rw [intervalIntegral.integral_of_le hT',intervalIntegral.integral_of_le hT']
      apply integral_mono_ae hN hE
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hle t (Ioc_subset_Icc_self ht)
    _ ≤ 4*B^2 := integral_envelope_le hT' B
    _ = _ := by dsimp [B]; simp only [mul_pow,he]; ring

end RiemannResearch.Analysis.MontgomeryIncomingEnergy

namespace RiemannResearch.Analysis.MontgomeryIncomingEnergy

/--
info: 'RiemannResearch.Analysis.MontgomeryIncomingEnergy.exists_incoming_energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_incoming_energy_bound

end RiemannResearch.Analysis.MontgomeryIncomingEnergy
