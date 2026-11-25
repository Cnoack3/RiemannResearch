import RiemannResearch.RH.MobiusParityInterchange
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ParetoMixedCenteredParityHeads
import RiemannResearch.RH.MixedConductorHead
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.CenteredMeanSnake
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Ambient L¹ approximation by mixed conductors

Consecutive dilations of a finite Möbius approximant belong to the mixed
space and approximate each mean-zero Pareto wavelet in L¹. Finite wavelet
sums and Hilbert-space density then give the entire ambient mean-zero
hyperplane in the L¹ closure. The legal mean-one section supplies the
remaining scalar direction for the full legal space.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open MobiusParityInterchange

/-- Consecutive dilates of a finite natural Möbius vector differ by a mixed vector. -/
theorem adjacentContrast_mem_mixed (n N : ℕ) :
    adjacentContrast n N ∈ PrimePowerSchur.mixedClosure := by
  have hF := CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N
  have h := PrimePowerSchur.mixedClosure.sub_mem
    (PrimePowerSchur.hilbertDilation_sub_self_mem_mixedClosure (n+1) (by omega) hF)
    (PrimePowerSchur.hilbertDilation_sub_self_mem_mixedClosure (n+2) (by omega) hF)
  have hid : adjacentContrast n N =
      (hilbertDilation (n+1) (by omega) (canonicalMobiusHilbert N) - canonicalMobiusHilbert N) -
      (hilbertDilation (n+2) (by omega) (canonicalMobiusHilbert N) - canonicalMobiusHilbert N) := by
    unfold adjacentContrast
    abel
  rwa [hid]

/-- Within the actual Pareto Hilbert space, the L¹ closure of the mixed
conductors is exactly the full ambient mean-zero hyperplane. -/
theorem mixed_L1_approximation_iff_mean_zero (f : ThresholdHilbert) :
    (∀ ε : ℝ, 0 < ε → ∃ v ∈ PrimePowerSchur.mixedClosure, hilbertL1Norm (f-v) < ε) ↔
      inner ℝ f hilbertOne = 0 := by
  let M := PrimePowerSchur.mixedClosure
  constructor
  · intro h
    by_contra hne
    have hpos := abs_pos.mpr hne
    obtain ⟨v, hv, hsmall⟩ := h _ hpos
    have hmean := (PrimePowerSchur.mem_mixedClosure_iff_mem_closedSpace_and_mean_zero v).mp hv
    have hup := inner_one_le_hilbertL1Norm (f-v)
    have hlo := inner_one_le_hilbertL1Norm (-(f-v))
    rw [inner_neg_left, hilbertL1Norm_neg] at hlo
    rw [inner_sub_left, hmean.2, sub_zero] at hup hlo
    exact (not_lt_of_ge (abs_le.mpr ⟨by linarith only [hlo], hup⟩)) hsmall
  · intro hmean
    have hspan (x : ThresholdHilbert) (hx : x ∈ tailBasisSpan) :
        ∀ ε : ℝ, 0 < ε → ∃ v ∈ M, hilbertL1Norm (x-v) < ε := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        intro ε hε
        obtain ⟨N, hN⟩ := ((adjacentContrast_L1_tendsto (fun _ => n)).eventually_lt_const hε).exists
        exact ⟨adjacentContrast n N, adjacentContrast_mem_mixed n N, hN⟩
      | zero =>
        intro ε hε
        exact ⟨0, M.zero_mem, by simpa only [sub_self, hilbertL1Norm_zero] using hε⟩
      | add x y hx hy ihx ihy =>
        intro ε hε
        obtain ⟨v, hv, he⟩ := ihx _ (half_pos hε)
        obtain ⟨w, hw, hd⟩ := ihy _ (half_pos hε)
        refine ⟨v+w, M.add_mem hv hw, ?_⟩
        rw [show x+y-(v+w) = (x-v)+(y-w) by abel]
        exact (hilbertL1Norm_add_le _ _).trans_lt (by linarith only [he, hd])
      | smul c x hx ih =>
        intro ε hε
        by_cases hc : c = 0
        · subst c
          exact ⟨0, M.zero_mem, by simpa only [zero_smul, sub_self, hilbertL1Norm_zero] using hε⟩
        have hp := abs_pos.mpr hc
        obtain ⟨v, hv, hdr⟩ := ih _ (div_pos hε hp)
        refine ⟨c • v, M.smul_mem c hv, ?_⟩
        rw [← smul_sub, hilbertL1Norm_smul, mul_comm]
        exact (lt_div_iff₀ hp).mp hdr
    intro ε hε
    have hh : f ∈ closure (tailBasisSpan : Set ThresholdHilbert) :=
      (tailBasis_mem_closure_iff_mean_zero f).mpr hmean
    obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp hh _ (half_pos hε)
    obtain ⟨v, hv, hnear⟩ := hspan x hx _ (half_pos hε)
    refine ⟨v, hv, ?_⟩
    have hfx : hilbertL1Norm (f-x) < ε/2 :=
      (hilbertL1Norm_le_norm _).trans_lt (by simpa only [dist_eq_norm] using hdist)
    rw [show f-v = (f-x)+(x-v) by abel]
    exact (hilbertL1Norm_add_le _ _).trans_lt (by linarith only [hfx, hnear])

/-- The full legal space approximates every Pareto Hilbert vector in L¹.
Its legal mean-one section supplies the missing scalar direction. -/
theorem legal_L1_approximation (f : ThresholdHilbert) (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ CoefficientStabilization.closedSpace, hilbertL1Norm (f-v) < ε := by
  let c := inner ℝ f hilbertOne
  let u := PrimePowerSchur.normalizedScreenedTwo
  have hmean : inner ℝ (f - c • u) hilbertOne = 0 := by
    rw [inner_sub_left, real_inner_smul_left, PrimePowerSchur.normalizedScreenedTwo_mean,
      mul_one, sub_self]
  obtain ⟨v, hv, herr⟩ := (mixed_L1_approximation_iff_mean_zero _).mpr hmean ε hε
  refine ⟨v + c • u, CoefficientStabilization.closedSpace.add_mem
    ((PrimePowerSchur.mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hv).1
    (CoefficientStabilization.closedSpace.smul_mem c
      (PrimePowerSchur.screenedPrimeClosure_le_closedSpace
        PrimePowerSchur.normalizedScreenedTwo_mem_screenedPrimeClosure)), ?_⟩
  rwa [show f - (v + c • u) = (f-c • u)-v by abel]


/-- The exact quotient seminorm induced by the complete Pareto L¹ norm
is the absolute mean. Its zero set is the entire ambient mean-zero subspace. -/
theorem mixed_L1_distance_isGLB (f : ThresholdHilbert) :
    IsGLB {r : ℝ | ∃ v ∈ PrimePowerSchur.mixedClosure, hilbertL1Norm (f-v) = r}
      |inner ℝ f hilbertOne| := by
  let c := inner ℝ f hilbertOne
  constructor
  · rintro r ⟨v, hv, rfl⟩
    have hmean := (PrimePowerSchur.mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hv
    have h := inner_one_le_hilbertL1Norm (f-v)
    have hn := inner_one_le_hilbertL1Norm (-(f-v))
    rw [inner_neg_left, hilbertL1Norm_neg] at hn
    rw [inner_sub_left, hmean.2, sub_zero] at h hn
    exact abs_le.mpr ⟨by linarith only [hn], h⟩
  · intro r hr
    by_contra! hlt
    have hcenter : inner ℝ (f-c • hilbertOne) hilbertOne = 0 := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
        mul_one, sub_self]
    obtain ⟨v, hv, herr⟩ := (mixed_L1_approximation_iff_mean_zero _).mpr hcenter
      (r-|c|) (sub_pos.mpr hlt)
    have hL : hilbertL1Norm hilbertOne = 1 := by
      have hlo := inner_one_le_hilbertL1Norm hilbertOne
      rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at hlo
      have hn : ‖hilbertOne‖ = 1 := by
        nlinarith only [hilbertOne_norm_sq, norm_nonneg hilbertOne]
      exact le_antisymm ((hilbertL1Norm_le_norm _).trans_eq hn) hlo
    have hupper : hilbertL1Norm (f-v) ≤ hilbertL1Norm ((f-c • hilbertOne)-v) + |c| := by
      conv_lhs => rw [show f-v = ((f-c • hilbertOne)-v) + c • hilbertOne by abel]
      simpa only [hilbertL1Norm_smul, hL, mul_one] using
        hilbertL1Norm_add_le ((f-c • hilbertOne)-v) (c • hilbertOne)
    have hlow := hr (show hilbertL1Norm (f-v) ∈
      {r : ℝ | ∃ z ∈ PrimePowerSchur.mixedClosure, hilbertL1Norm (f-z) = r} from ⟨v, hv, rfl⟩)
    linarith only [hupper, herr, hlow]


/-- Finite mixed packets may be required to match any prescribed initial
interval of a mean-zero target while approximating it in the complete L¹
norm. -/
theorem finite_mixed_L1_approximation_exact_head (f : ThresholdHilbert)
    (hmean : inner ℝ f hilbertOne = 0) (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∃ v ∈ PrimePowerSchur.mixedSpace (Finset.Icc 2 M),
      (∀ k, 0 < k → k ≤ K → hilbertSequence v k = hilbertSequence f k) ∧
      hilbertL1Norm (f-v) < ε := by
  have hfit (L : ℕ) : ∀ δ : ℝ, 0 < δ → ∃ w ∈ PrimePowerSchur.mixedClosure,
      (∀ k, 0 < k → k ≤ L → hilbertSequence w k = hilbertSequence f k) ∧
      hilbertL1Norm (f-w) < δ := by
    induction L with
    | zero =>
      intro δ hδ
      obtain ⟨w, hw, he⟩ := (mixed_L1_approximation_iff_mean_zero f).mpr hmean δ hδ
      exact ⟨w, hw, fun k hk hk0 => (by omega : False).elim, he⟩
    | succ L ih =>
      intro δ hδ
      obtain ⟨M, b, hb, hsites⟩ := PrimePowerSchur.exists_mixed_exact_head
        (fun k => if k = L+1 then 1 else 0) (L+1)
      let p := positiveWeight (L+1)
      have hp : 0 < p := by dsimp [p, positiveWeight]; positivity
      let C := hilbertL1Norm b / p
      have hC : 0 < 1 + C :=
        add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hilbertL1Norm_nonneg b) hp.le)
      obtain ⟨w, hw, hwsite, hwerr⟩ := ih _ (div_pos hδ hC)
      let a := hilbertSequence (f-w) (L+1)
      have ha : |a| ≤ hilbertL1Norm (f-w) / p := by
        apply (le_div_iff₀ hp).mpr
        rw [mul_comm]
        exact (hilbertL1Norm_summable (f-w)).le_tsum (L+1)
          (fun n _ => mul_nonneg (positiveWeight_nonneg n) (abs_nonneg _))
      refine ⟨w+a • b, PrimePowerSchur.mixedClosure.add_mem hw
        (PrimePowerSchur.mixedClosure.smul_mem a
          (PrimePowerSchur.mixedSpace_window_le_closure M hb)), ?_, ?_⟩
      · intro k hk hkL
        simp only [hilbertSequence_add, Pi.add_apply, hilbertSequence_smul, Pi.smul_apply,
          smul_eq_mul, hsites _ hk hkL]
        by_cases he : k = L+1
        · subst k
          simp [a, hilbertSequence_sub, Pi.sub_apply] <;> ring
        · simp only [if_neg he, mul_zero, add_zero]
          exact hwsite _ hk (by omega)
      · have hneg : f - (w + a • b) = (f-w) + -(a • b) := by abel
        rw [hneg]
        calc
          _ ≤ hilbertL1Norm (f-w) + hilbertL1Norm (-(a • b)) := hilbertL1Norm_add_le _ _
          _ = hilbertL1Norm (f-w) + |a| * hilbertL1Norm b := by
            rw [hilbertL1Norm_neg, hilbertL1Norm_smul]
          _ ≤ hilbertL1Norm (f-w) + (hilbertL1Norm (f-w) / p) * hilbertL1Norm b :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right ha (hilbertL1Norm_nonneg b))
          _ = hilbertL1Norm (f-w) * (1+C) := by dsimp only [C]; ring
          _ < δ := (lt_div_iff₀ hC).mp hwerr
  obtain ⟨w, hw, hhead, hnear⟩ := hfit K _ (half_pos hε)
  obtain ⟨M, v, hv, hvhead, hd⟩ :=
    PrimePowerSchur.finite_mixed_approximate_fixed_head K w hw _ (half_pos hε)
  refine ⟨M, v, hv, fun k hk hkK => (hvhead k hk hkK).trans (hhead k hk hkK), ?_⟩
  have hsmall := (hilbertL1Norm_le_norm (w-v)).trans_lt ((norm_sub_rev w v).symm ▸ hd)
  rw [show f-v = (f-w)+(w-v) by abel]
  exact (hilbertL1Norm_add_le _ _).trans_lt (by linarith only [hsmall, hnear])


namespace PrimePowerSchur.CenteredMeanSnake

/-- The same centered boundary at one has representatives vanishing on an
arbitrary physical head and arbitrarily small in the complete Pareto L¹
norm. Each representative is obtained by subtracting a finite mixed fit. -/
theorem boundary_unit_exact_head_L1_representative (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : meanZero, mixedInMeanZero.mkQ z = boundary 1 ∧
      (∀ k : ℕ, 0 < k → k ≤ K → hilbertSequence z.val k = 0) ∧ hilbertL1Norm z.val < ε := by
  have hmean : inner ℝ defect.val hilbertOne = 0 := by
    rw [real_inner_comm]
    exact defect.property
  obtain ⟨M, v, hv, hhead, herr⟩ := finite_mixed_L1_approximation_exact_head
    defect.val hmean K ε hε
  let m := mixedInclusion ⟨v, mixedSpace_window_le_closure M hv⟩
  have hm : m ∈ mixedInMeanZero := mixedSpace_window_le_closure M hv
  refine ⟨defect-m, ?_, ?_, herr⟩
  · have hmq : mixedInMeanZero.mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hm
    rw [map_sub, hmq, sub_zero, boundary_apply, one_smul]
  · intro k hk hkK
    change hilbertSequence (defect.val-v) k = 0
    rw [hilbertSequence_sub, Pi.sub_apply, hhead k hk hkK, sub_self]

/-- A head-vanishing representative must pay the full tail product of the
actual centered defect in the Hilbert norm. -/
theorem boundary_unit_head_energy_lower (K : ℕ) (z : meanZero)
    (hz : mixedInMeanZero.mkQ z = boundary 1)
    (hhead : ∀ k : ℕ, 0 < k → k ≤ K → hilbertSequence z.val k = 0) :
    (‖defect‖^2)^2 ≤ ‖hilbertTailShift defect.val K‖^2 * ‖z‖^2 := by
  have hm : z - defect ∈ mixedInMeanZero := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change mixedInMeanZero.mkQ (z-defect) = 0
    rw [map_sub, hz, boundary_apply, one_smul, sub_self]
  have ho := Submodule.inner_left_of_mem_orthogonal hm defect_orthogonal
  rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero] at ho
  have hcoord (n : ℕ) (hn : n < K) : z.val n = 0 := by
    have hh := hhead (n+1) (Nat.succ_pos _) (by omega)
    change z.val n / Real.sqrt (paretoWeight n) = 0 at hh
    exact (div_eq_zero_iff.mp hh).resolve_right (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne'
  have h := hilbertTailShift_inner_sq_le defect.val z.val K hcoord
  change inner ℝ defect.val z.val = ‖defect‖^2 at ho
  rwa [ho] at h

/-- The head and L¹ requirements already have witnesses for every K. A
uniform Hilbert cost for head-vanishing representatives detects the zero
boundary. -/
theorem boundary_zero_iff_bounded_representative_heads :
    boundary = 0 ↔ ∃ C : ℝ, ∀ K : ℕ, ∃ z : meanZero,
      mixedInMeanZero.mkQ z = boundary 1 ∧
      (∀ k : ℕ, 0 < k → k ≤ K → hilbertSequence z.val k = 0) ∧ ‖z‖^2 ≤ C := by
  constructor
  · intro hb
    refine ⟨0, fun K => ⟨0, by simp [hb], ?_, by simp⟩⟩
    intro k hk hkK
    change hilbertSequenceLinear 0 k = 0
    rw [map_zero]
    rfl
  · rintro ⟨C, hC⟩
    apply boundary_eq_zero_iff_screened.mpr
    apply sub_eq_zero.mp
    change defect.val = 0
    by_contra hd
    have hp : 0 < (‖defect‖^2)^2 := by
      have hdn : 0 < ‖defect.val‖ := norm_pos_iff.mpr hd
      change 0 < (‖defect.val‖^2)^2
      exact pow_pos (pow_pos hdn _) _
    have ht : Tendsto (fun K : ℕ => ‖hilbertTailShift defect.val K‖^2 * C) atTop (𝓝 0) := by
      simpa only [zero_mul] using (hilbertTailShift_energy_tendsto_zero defect.val).mul_const C
    obtain ⟨K, hK⟩ := (ht.eventually_lt_const hp).exists
    obtain ⟨z, hz, hhead, hcost⟩ := hC K
    exact (not_lt_of_ge ((boundary_unit_head_energy_lower K z hz hhead).trans
      (mul_le_mul_of_nonneg_left hcost (sq_nonneg _)))) hK

end PrimePowerSchur.CenteredMeanSnake

end RiemannResearch.RH.Pareto
