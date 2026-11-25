import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.ParetoAffineHeadTower
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.PhysicalHeadMixedInterpolation
import RiemannResearch.RH.PhysicalHeadSnakeSections
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Growth of minimum-norm physical-head mean sections

The norm of the orthogonal affine lift is the least norm of a legal mean-one
vector matching the first physical coordinates of the constant. A right
zeta zero gives a power floor for every such lift. Conversely RH supplies
arbitrarily close finite mixed corrections to any legal mean-one seed.

Source: the physical-head section argument in the research discussion.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth

open CoefficientStabilization AffineHeadTower
open CenteredMeanSnake.PhysicalHeadSections

/-- Least norm required for the mean-one section agreeing with one at sites 1 through N. -/
def kappa (N : ℕ) : ℝ := ‖patch N‖

theorem kappa_isLeast (N : ℕ) :
    IsLeast {a : ℝ | ∃ v ∈ fiber N, ‖v‖ = a} (kappa N) := by
  refine ⟨⟨patch N, (patch_spec N).1, rfl⟩, ?_⟩
  rintro a ⟨v, hv, rfl⟩
  have h := feasible_norm_sq N hv
  change ‖patch N‖ ≤ ‖v‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith [sq_nonneg ‖v-patch N‖])

theorem kappa_sq_eq_one_add_error (N : ℕ) :
    (kappa N)^2 = 1 + ‖patch N - hilbertOne‖^2 := by
  rw [norm_sub_sq_real, (patch_spec N).1.2.1, hilbertOne_norm_sq]
  unfold kappa
  ring

private theorem rhs_one_mem (hRH : RiemannHypothesis) : hilbertOne ∈ closedSpace :=
  BaezDuarte.naturalApproximation_iff_one_mem.mp
    (CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.mp hRH)

theorem kappa_eq_one_of_rh (hRH : RiemannHypothesis) (N : ℕ) : kappa N = 1 := by
  have he : hilbertOne ∈ fiber N := by
    refine ⟨rhs_one_mem hRH, ?_, fun i _ => ?_⟩
    · rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
    · rw [physicalEvaluationCLM_apply, hilbertOne_sequence]
      simp [zeroAnchor]
  have hmin := (kappa_isLeast N).2 (show ‖hilbertOne‖ ∈
      {a : ℝ | ∃ v ∈ fiber N, ‖v‖ = a} from ⟨hilbertOne, he, rfl⟩)
  have hk : 0 ≤ kappa N := norm_nonneg _
  nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne, kappa_sq_eq_one_add_error N,
    sq_nonneg ‖patch N - hilbertOne‖]

/-- The centered Mellin tail gives a power floor with the exact unit mean term. -/
theorem rightZero_kappa_sq_lower (N : ℕ) (s : ℂ) (hs : (1/2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    1 + ((2*s.re-1)/‖s‖^2) * ((N : ℝ)+1)^(2*s.re-1) ≤ (kappa N)^2 := by
  have hp := (patch_spec N).1
  have hhead (j : ℕ) (hj : 0 < j) (hjN : j < N+1) : hilbertSequence (patch N) j = 1 := by
    cases j with
    | zero => omega
    | succ i =>
      simpa only [physicalEvaluationCLM_apply] using hp.2.2 i (by omega)
  have h := legal_exact_head_residual_power_lower {j : ℕ | 0 < j} (fun _ hj => hj)
    (closedSpace_le_legalClosure hp.1) (N+1) (by omega) hhead s hs hs1 hz
  rw [norm_sub_rev hilbertOne (patch N)] at h
  push_cast at h
  rw [kappa_sq_eq_one_add_error]
  exact add_le_add le_rfl h

/-- Arbitrarily large physical heads whose squared section norms have every positive
power upper bound, with the cutoff and its section free to depend on the exponent. -/
def CofinalSubpower (cost : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ᶠ N : ℕ in atTop, cost N ≤ C*((N : ℝ)+1)^ε

theorem cofinalSubpower_kappa_iff_rh :
    CofinalSubpower (fun N => (kappa N)^2) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
    intro s hs hs' hz
    have hs1 : s ≠ 1 := by intro he; simp [he] at hs'
    have hs0 : s ≠ 0 := by
      intro he
      subst s
      norm_num at hs
    let α : ℝ := (2*s.re-1)/2
    have hα : 0 < α := by dsimp [α]; linarith
    let c : ℝ := (2*s.re-1)/‖s‖^2
    have hc : 0 < c := div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) _)
    obtain ⟨C,hC⟩ := h α hα
    have hbase : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun N : ℕ => ((N : ℝ)+1)^α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp hbase
    obtain ⟨N, hu, hlarge⟩ := (hC.and_eventually (hpow.eventually_gt_atTop (C/c))).exists
    let q : ℝ := ((N : ℝ)+1)^α
    have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hlarge' : C/c < q := hlarge
    have hgt : C*q < c*(q*q) := by
      have h1 : C < q*c := (div_lt_iff₀ hc).mp hlarge'
      calc C*q < (q*c)*q := mul_lt_mul_of_pos_right h1 hq
           _ = c*(q*q) := by ring
    have hsplit : ((N : ℝ)+1)^(2*s.re-1) = q*q := by
      dsimp [q]
      rw [← Real.rpow_add (by positivity : 0 < (N : ℝ)+1)]
      congr 1
      dsimp [α]
      ring
    have hl := rightZero_kappa_sq_lower N s hs hs1 hz
    change 1 + c * ((N : ℝ)+1)^(2*s.re-1) ≤ (kappa N)^2 at hl
    rw [hsplit] at hl
    change (kappa N)^2 ≤ C*q at hu
    linarith only [hu, hl, hgt]
  · intro hRH ε hε
    refine ⟨1, Eventually.frequently (Eventually.of_forall (fun N => ?_))⟩
    change (kappa N)^2 ≤ 1 * ((N : ℝ)+1)^ε
    rw [kappa_eq_one_of_rh hRH, one_pow, one_mul]
    exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) hε.le

/-- A non-RH zero forces polynomial escape at every cutoff; on RH all norms are exactly one. -/
theorem kappa_dichotomy :
    (∀ N, kappa N = 1) ∨
      ∃ s : ℂ, (1/2 : ℝ) < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧
        ∀ N : ℕ, 1 + ((2*s.re-1)/‖s‖^2)*((N : ℝ)+1)^(2*s.re-1) ≤ (kappa N)^2 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl (kappa_eq_one_of_rh hRH)
  · right
    have h := mt RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr hRH
    push Not at h
    obtain ⟨s, hs, hs', hz⟩ := h
    have hs1 : s ≠ 1 := by intro he; simp [he] at hs'
    exact ⟨s, hs, hs', hz, fun N => rightZero_kappa_sq_lower N s hs hs1 hz⟩

/-- Without RH the minimum norm eventually exceeds every fixed budget. -/
theorem kappa_tendsto_atTop_of_not_rh (h : ¬ RiemannHypothesis) :
    Tendsto kappa atTop atTop := by
  have hu : normalizedScreenedTwo ≠ hilbertOne :=
    fun he => h (riemannHypothesis_of_normalizedScreenedTwo he)
  have ht := AffineHeadTower.energy_tendsto_atTop_of_seed_ne hu
  apply tendsto_atTop.2
  intro b
  by_cases hb : 0 ≤ b
  · filter_upwards [ht.eventually_ge_atTop (b^2)] with N hN
    apply (sq_le_sq₀ hb (show 0 ≤ kappa N from norm_nonneg _)).mp
    change b^2 ≤ ‖patch N‖^2
    rw [patch_norm_sq]
    exact hN.trans (le_add_of_nonneg_left (sq_nonneg _))
  · exact Eventually.of_forall (fun N => (le_of_lt (lt_of_not_ge hb)).trans (norm_nonneg _))

/-- A fixed legal mean-one seed admits finite mixed head patches with arbitrary
accuracy when the target itself belongs to the legal closure. -/
theorem exists_finite_section_near_one (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hm : inner ℝ g hilbertOne = 1) (he : hilbertOne ∈ closedSpace) (N : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℕ, ∃ m : ThresholdHilbert, m ∈ mixedSpace (Finset.Icc 2 B) ∧
      g+m ∈ fiber N ∧ ‖hilbertOne-(g+m)‖ < δ := by
  have hmix : hilbertOne-g ∈ mixedClosure := by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    refine ⟨closedSpace.sub_mem he hg, ?_⟩
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, hm, sub_self]
  obtain ⟨B,m,hBm,hh,herr⟩ :=
    PhysicalHeadMixedInterpolation.exists_finite_window_near_with_same_head g hmix N hδ
  have hmem := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
    (mixedSpace_window_le_closure B hBm)
  let w : closedSpace := ⟨g+m, closedSpace.add_mem hg hmem.1⟩
  have hh' := (matchesUnitHead_iff_sequence N w).mp (show MatchesUnitHead N w from hh)
  refine ⟨B,m,hBm,⟨w.property, ?_, ?_⟩,herr⟩
  · rw [inner_add_left, hm, hmem.2, add_zero]
  · intro i hi
    rw [physicalEvaluationCLM_apply]
    exact hh' (i+1) (Nat.succ_pos _) (by omega)

/-- Finite mixed corrections to the chosen seed may use conductors larger than
the observed physical head. The energy budget is required cofinally at each exponent. -/
def FiniteSectionSubpower (g : ThresholdHilbert) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
    ∃ B : ℕ, ∃ m : ThresholdHilbert, m ∈ mixedSpace (Finset.Icc 2 B) ∧
      g + m ∈ fiber N ∧ ‖g+m‖^2 ≤ C*((N : ℝ)+1)^ε

/-- The test can use actual finite-window mixed corrections to a fixed mean-one
legal seed. In particular the seed may be the normalized conductor-two packet. -/
theorem finiteSectionSubpower_iff_rh (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hmean : inner ℝ g hilbertOne = 1) :
    FiniteSectionSubpower g ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply cofinalSubpower_kappa_iff_rh.mp
    intro ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨C, hC.mono ?_⟩
    rintro N ⟨B, m, _, hv, hcost⟩
    have hk := (kappa_isLeast N).2 (show ‖g+m‖ ∈
      {a : ℝ | ∃ v ∈ fiber N, ‖v‖ = a} from ⟨g+m, hv, rfl⟩)
    exact ((sq_le_sq₀ (show 0 ≤ kappa N from norm_nonneg _) (norm_nonneg _)).mpr hk).trans hcost
  · intro hRH ε hε
    refine ⟨4, Eventually.frequently (Eventually.of_forall (fun N => ?_))⟩
    obtain ⟨B, m, hm, hf, herr⟩ :=
      exists_finite_section_near_one g hg hmean (rhs_one_mem hRH) N (by norm_num : (0:ℝ)<1)
    have hnorm : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    have hcost : ‖g+m‖ ≤ 2 := by
      calc ‖g+m‖ = ‖((g+m)-hilbertOne)+hilbertOne‖ := by rw [sub_add_cancel]
           _ ≤ ‖(g+m)-hilbertOne‖ + ‖hilbertOne‖ := norm_add_le _ _
           _ ≤ 2 := by rw [norm_sub_rev, hnorm]; linarith
    refine ⟨B, m, hm, hf, ?_⟩
    have hpow : 1 ≤ ((N : ℝ)+1)^ε :=
        Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) hε.le
    have hsq := (sq_le_sq₀ (norm_nonneg (g+m)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hcost
    nlinarith only [hsq, hpow]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth
