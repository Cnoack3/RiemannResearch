import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.MixedConductorHead
import RiemannResearch.RH.MobiusCoefficientDefect
import RiemannResearch.RH.PhysicalCompensatedSource
import RiemannResearch.RH.ParetoRamanujanGramCRT
import RiemannResearch.RH.ParetoMixedCenteredParityHeads
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.Analysis.NestedProjectionEnergy
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite Möbius tests for the ambient Pareto mean boundary

The Riesz vectors of the Möbius differences of orders at least two are total in
the ambient Hilbert space. Their pairings with mixed packets are divisor
incidences. A prescribed finite packet window therefore gives a test involving
only a signed incidence matrix, the complete CRT Gram matrix and a scalar target.
The uniform comparison across windows is an open arithmetic hypothesis.

The quotient criterion is from `CenteredMeanQuotients`. The finite testing
argument combines the repository's dense projection test, exact-head
interpolation and finite Hilbert Gram identities.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting

open CoefficientStabilization CaptureGains
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.DenseProjectionTesting

/-- The exact Möbius observation on a positive packet, for row orders at least two. -/
def incidence (m q : ℕ) : ℝ :=
  if m ∣ q then -(m : ℝ) * (ArithmeticFunction.moebius (q / m) : ℝ) else 0

/-- The signed observation of the centered parity target at order `m ≥ 2`. -/
def target (m : ℕ) : ℝ :=
  incidence m 2 - Real.log 2 * (ArithmeticFunction.moebius m : ℝ)

theorem target_eq_coordinate (m : ℕ) (hm : 1 < m) :
    target m = mobiusDifferenceCLM m centeredParity := by
  rw [centeredParity, map_sub, map_smul, mobius_coordinate_one m (by omega),
    mobiusDifferenceCLM_ramanujanPacketHilbert m 2 hm (by decide)]
  rfl

/-- Index `i` labels Möbius order `i+2`. -/
def test : (ℕ →₀ ℝ) →ₗ[ℝ] ThresholdHilbert :=
  Finsupp.linearCombination ℝ (fun i : ℕ => mobiusRieszHilbert (i + 2))

def targetPairing (w : ℕ →₀ ℝ) : ℝ :=
  ∑ i ∈ w.support, w i * target (i + 2)

def packetPairing (w : ℕ →₀ ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ w.support, w i * incidence (i + 2) q

private theorem test_eq_sum (w : ℕ →₀ ℝ) :
    test w = ∑ i ∈ w.support, w i • mobiusRieszHilbert (i + 2) := rfl

theorem inner_test_target (w : ℕ →₀ ℝ) :
    inner ℝ (test w) centeredParity = targetPairing w := by
  rw [test_eq_sum, sum_inner]
  unfold targetPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, mobiusRieszHilbert_inner, target_eq_coordinate _ (by omega)]

theorem inner_test_packet (w : ℕ →₀ ℝ) (q : ℕ) (hq : 0 < q) :
    inner ℝ (test w) (ramanujanPacketHilbert q) = packetPairing w q := by
  rw [test_eq_sum, sum_inner]
  unfold packetPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, mobiusRieszHilbert_inner,
    mobiusDifferenceCLM_ramanujanPacketHilbert (i + 2) q (by omega) hq]
  rfl

abbrev window (B : ℕ) := mixedConductors (Finset.Icc 2 B)

private theorem window_gt_one (B : ℕ) {q : ℕ} (hq : q ∈ window B) : 1 < q :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1

/-- Complete Pareto Gram matrix of the mixed packets up to conductor `B`. -/
def windowGram (B : ℕ) : Matrix (window B) (window B) ℝ :=
  gramMatrix (PhysicalCompensatedSource.packetFamily (window B))

theorem windowGram_entry (B : ℕ) (i j : window B) (L : ℕ)
    (hL : 0 < L) (hi : i.val ∣ L) (hj : j.val ∣ L) :
    windowGram B i j = ∑ a : Fin L, progressionWeight L (a.val + 1) *
      (ramanujanPacket i.val (a.val + 1) * ramanujanPacket j.val (a.val + 1)) :=
  ramanujanPacketHilbert_inner_eq_crt _ _ _ hL hi hj

/-- The full quadratic form on the arithmetic column pairings. -/
def captured (B : ℕ) (w : ℕ →₀ ℝ) : ℝ :=
  let b : window B → ℝ := fun q => packetPairing w q.val
  dotProduct b ((windowGram B)⁻¹.mulVec b)

theorem captured_eq_projection (B : ℕ) (w : ℕ →₀ ℝ) :
    captured B w = ‖(mixedSpace (Finset.Icc 2 B)).starProjection (test w)‖ ^ 2 := by
  let v := PhysicalCompensatedSource.packetFamily (window B)
  have hv : LinearIndependent ℝ v :=
    PhysicalCompensatedSource.packetFamily_independent _ (fun q h => window_gt_one B h)
  have hc : cross v (test w) = fun q : window B => packetPairing w q.val := by
    funext q
    rw [cross, real_inner_comm]
    exact inner_test_packet w q.val (by have := window_gt_one B q.property; omega)
  have h := projection_inner_eq_inverseGram hv (test w) (test w)
  rw [real_inner_self_eq_norm_sq, hc] at h
  exact h.symm

private theorem test_dense : Dense (Set.range test) := by
  have hr : LinearMap.range test =
      Submodule.span ℝ (Set.range fun i : ℕ => mobiusRieszHilbert (i + 2)) :=
    Finsupp.range_linearCombination ℝ
  intro x
  change x ∈ (LinearMap.range test).topologicalClosure
  rw [hr, mobiusRiesz_total]
  trivial

theorem centeredParity_mem_iff_boundary :
    centeredParity ∈ mixedClosure ↔ CenteredMeanSnake.boundary = 0 := by
  rw [CenteredMeanSnake.boundary_eq_zero_iff_one_mem]
  constructor
  · intro h
    have hg := closedSpace.sub_mem (packet_mem_closedSpace 2 (by decide))
      (mixedClosure_le_closedSpace h)
    have he : ramanujanPacketHilbert 2 - centeredParity = Real.log 2 • hilbertOne := by
      unfold centeredParity
      abel
    rw [he] at hg
    have hl := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    simpa only [smul_smul, inv_mul_cancel₀ hl, one_smul] using
      closedSpace.smul_mem (Real.log 2)⁻¹ hg
  · intro h
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    refine ⟨closedSpace.sub_mem (packet_mem_closedSpace 2 (by decide))
      (closedSpace.smul_mem _ h), ?_⟩
    rw [centeredParity, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    simp

/-- A uniform finite inverse-Gram bound for any prescribed cutoff schedule kills
the ambient boundary. The hypotheses involve only finite arithmetic tests. -/
theorem boundary_eq_zero_of_window_bound (B : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ w : ℕ →₀ ℝ, targetPairing w ^ 2 ≤
      C * captured (B (w.support.sup (fun i => i + 2))) w) :
    CenteredMeanSnake.boundary = 0 := by
  apply centeredParity_mem_iff_boundary.mp
  apply (mem_iff_dense_test_bound mixedClosure centeredParity _ test_dense).mpr
  refine ⟨Real.sqrt C, ?_⟩
  rintro _ ⟨w, rfl⟩
  rw [real_inner_comm, inner_test_target]
  have hb := h w
  let b := B (w.support.sup (fun i => i + 2))
  change targetPairing w ^ 2 ≤ C * captured b w at hb
  rw [captured_eq_projection] at hb
  have hl := RiemannResearch.Analysis.NestedProjectionEnergy.captured_energy_mono
    (mixedSpace_window_le_closure b) (test w)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hC]
  exact hb.trans (mul_le_mul_of_nonneg_left hl hC)

abbrev orders (H : ℕ) := Finset.Icc 2 H

/-- Integer divisor incidences regarded as real matrix entries. -/
def incidenceMatrix (H B : ℕ) : Matrix (orders H) (window B) ℝ :=
  fun m q => incidence m.val q.val

/-- Gram matrix of the projected Möbius tests at this head and packet cutoff. -/
def headGram (H B : ℕ) : Matrix (orders H) (orders H) ℝ :=
  incidenceMatrix H B * (windowGram B)⁻¹ * (incidenceMatrix H B).transpose

private def row (H B : ℕ) (m : orders H) : ThresholdHilbert :=
  (mixedSpace (Finset.Icc 2 B)).starProjection (mobiusRieszHilbert m.val)

private theorem row_gram (H B : ℕ) :
    gramMatrix (row H B) = headGram H B := by
  let v := PhysicalCompensatedSource.packetFamily (window B)
  let r := fun m : orders H => mobiusRieszHilbert m.val
  have hv : LinearIndependent ℝ v :=
    PhysicalCompensatedSource.packetFamily_independent _ (fun q h => window_gt_one B h)
  have hA : observationMatrix v r = incidenceMatrix H B := by
    ext m q
    change inner ℝ (ramanujanPacketHilbert q.val) (mobiusRieszHilbert m.val) = _
    rw [real_inner_comm, mobiusRieszHilbert_inner,
      mobiusDifferenceCLM_ramanujanPacketHilbert _ _ (Finset.mem_Icc.mp m.property).1
        (Nat.zero_lt_one.trans (window_gt_one B q.property))]
    rfl
  have h := projection_kernel_matrix hv r
  rw [hA] at h
  exact h

private theorem row_inner {H B : ℕ} (m : orders H) {x : ThresholdHilbert}
    (hx : x ∈ mixedSpace (Finset.Icc 2 B)) :
    inner ℝ (row H B m) x = mobiusDifferenceCLM m.val x := by
  rw [row, real_inner_comm, ← inner_eq_projected_test _ hx,
    real_inner_comm, mobiusRieszHilbert_inner]

private theorem row_independent (H s : ℕ) (hs : s.Prime) (hHs : H + 1 < s) :
    LinearIndependent ℝ (row H (s * (H + 1))) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let f := normalizedResidueHilbert i.val (Nat.zero_lt_one.trans (Finset.mem_Icc.mp i.property).1)
  obtain ⟨x, hx, hhead⟩ := exists_mixed_exact_head_at (hilbertSequence f) H s hs hHs
  have hall (k : ℕ) (hk : k ≤ H) : hilbertSequence x k = hilbertSequence f k := by
    by_cases h0 : k = 0
    · simp [h0]
    · exact hhead k (Nat.pos_of_ne_zero h0) hk
  have hbi (j : orders H) :
      inner ℝ (row H (s * (H + 1)) j) x = if j = i then -1 else 0 := by
    rw [row_inner j hx]
    have he : mobiusDifferenceCLM j.val x = mobiusDifferenceCLM j.val f := by
      simp only [mobiusDifferenceCLM_apply]
      exact mobiusDifference_congr_initial (Finset.mem_Icc.mp j.property).2 hall
    rw [he, mobius_normalizedResidue _ _ (Finset.mem_Icc.mp j.property).1]
    simp only [Subtype.val_inj]
  have he := congrArg (fun z : ThresholdHilbert => inner ℝ z x) hc
  simpa [sum_inner, real_inner_smul_left, hbi, mul_ite] using he

/-- At every head a fresh prime supplies a strictly positive definite projected
test Gram, without a uniform spectral assumption. -/
theorem headGram_posDef (H s : ℕ) (hs : s.Prime) (hHs : H + 1 < s) :
    (headGram H (s * (H + 1))).PosDef := by
  rw [← row_gram]
  exact gramMatrix_posDef (row_independent H s hs hHs)

/-- Complete least squared norm for the signed parity observations in the window. -/
def headCost (H B : ℕ) : ℝ :=
  let t : orders H → ℝ := fun m => target m.val
  dotProduct t ((headGram H B)⁻¹.mulVec t)

open RiemannResearch.Analysis.FiniteHilbertConstraints in
/-- The inverse-Gram energy is attained. Every feasible vector has an exact
squared norm remainder relative to the minimizer. -/
theorem headCost_minimum (H s : ℕ) (hs : s.Prime) (hHs : H + 1 < s) :
    let B := s * (H + 1)
    ∃ x ∈ mixedSpace (Finset.Icc 2 B),
      (∀ m : orders H, mobiusDifferenceCLM m.val x = target m.val) ∧
      ‖x‖^2 = headCost H B ∧
      ∀ y ∈ mixedSpace (Finset.Icc 2 B),
        (∀ m : orders H, mobiusDifferenceCLM m.val y = target m.val) →
        ‖y‖^2 = headCost H B + ‖y - x‖^2 := by
  classical
  intro B
  let v := row H B
  let t := fun m : orders H => target m.val
  have hv : LinearIndependent ℝ v := row_independent H s hs hHs
  let x := minimumVector hv t
  have hx : x ∈ mixedSpace (Finset.Icc 2 B) := by
    change Fintype.linearCombination ℝ v _ ∈ _
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem ..)
  have hE : ‖x‖ ^ 2 = headCost H B := by
    rw [headCost, ← row_gram, gramMatrix_inverseSource hv t, minimumVector_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  refine ⟨x, hx, fun m => (row_inner m hx).symm.trans (minimumVector_observation hv t m),
    hE, ?_⟩
  intro y hy hm
  rw [← hE]
  apply feasible_norm_sq_completion hv t
  exact fun m => (row_inner m hy).trans (hm m)

/-- The optimal finite interpolation cost bounds every target/test quotient
supported through the same head. -/
theorem targetPairing_sq_le_headCost (H s : ℕ) (hs : s.Prime) (hHs : H + 1 < s)
    (w : ℕ →₀ ℝ) (hw : ∀ i ∈ w.support, i + 2 ≤ H) :
    targetPairing w ^ 2 ≤ headCost H (s * (H + 1)) * captured (s * (H + 1)) w := by
  let B := s * (H + 1)
  obtain ⟨x, hx, hm, hnorm, _⟩ := headCost_minimum H s hs hHs
  have ht : inner ℝ (test w) x = targetPairing w := by
    rw [test_eq_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, mobiusRieszHilbert_inner]
    exact congrArg (w i * ·) (hm ⟨i+2, Finset.mem_Icc.mpr ⟨by omega, hw i hi⟩⟩)
  have he : inner ℝ x ((mixedSpace (Finset.Icc 2 B)).starProjection (test w)) =
      targetPairing w :=
    ((inner_eq_projected_test _ hx _).symm.trans (real_inner_comm _ _)).trans ht
  change _ ≤ headCost H B * captured B w
  rw [← he, ← hnorm, captured_eq_projection]
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm x ((mixedSpace (Finset.Icc 2 B)).starProjection (test w)))
  simpa only [sq_abs, mul_pow] using h

/-- A uniformly bounded subsequence of the explicit interpolation costs on
arbitrarily large heads suffices for the full ambient mean-zero inclusion. -/
theorem one_orthogonal_le_mixedClosure_of_cofinal_headCost
    (s : ℕ → ℕ) (hs : ∀ H, (s H).Prime) (hf : ∀ H, H + 1 < s H)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n : ℕ, ∃ H ≥ n, headCost H (s H * (H + 1)) ≤ C) :
    (Submodule.span ℝ {hilbertOne})ᗮ ≤ mixedClosure := by
  choose H hle hcost using hb
  apply CenteredMeanSnake.one_orthogonal_le_mixedClosure_iff_one_mem.mpr
  apply CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mp
  apply boundary_eq_zero_of_window_bound (fun n => s (H n) * (H n + 1)) C hC
  intro w
  let n := w.support.sup (fun i => i + 2)
  have hw := targetPairing_sq_le_headCost (H n) (s (H n)) (hs _) (hf _) w
    (fun i hi => (Finset.le_sup (f := fun j : ℕ => j + 2) hi).trans (hle n))
  exact hw.trans (mul_le_mul_of_nonneg_right (hcost n) (by
    rw [captured_eq_projection]
    exact sq_nonneg _))

/-- If the cutoff may be chosen after the target fit at each head, uniformly
bounded finite costs are equivalent to vanishing of the boundary. Fixing the
prime schedule in advance leaves a separate arithmetic estimate. -/
theorem boundary_eq_zero_iff_exists_bounded_headCost :
    CenteredMeanSnake.boundary = 0 ↔
      ∃ s : ℕ → ℕ, (∀ H, (s H).Prime) ∧ (∀ H, H + 1 < s H) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ H, headCost H (s H * (H + 1)) ≤ C := by
  constructor
  · intro hb
    have hz := centeredParity_mem_iff_boundary.mpr hb
    have hwin (H : ℕ) : ∃ s : ℕ, s.Prime ∧ H + 1 < s ∧
        headCost H (s * (H + 1)) ≤ (‖centeredParity‖ + 1)^2 := by
      obtain ⟨M, y, hy, hh, hdist⟩ :=
        finite_mixed_approximate_fixed_head H centeredParity hz 1 zero_lt_one
      obtain ⟨s, hs, hp⟩ := Nat.exists_infinite_primes (max (H + 2) M)
      have hf : H + 1 < s := by omega
      have hM : M ≤ s * (H + 1) := by
        have hMs : M ≤ s := (le_max_right _ _).trans hs
        rw [Nat.mul_succ]
        omega
      have hym := mixedSpace_mono (Finset.Icc_subset_Icc (a₁ := 2) le_rfl hM) hy
      have hm (m : orders H) : mobiusDifferenceCLM m.val y = target m.val := by
        rw [target_eq_coordinate _ (Finset.mem_Icc.mp m.property).1]
        simp only [mobiusDifferenceCLM_apply]
        apply mobiusDifference_congr_initial (Finset.mem_Icc.mp m.property).2
        intro n hn
        by_cases h0 : n = 0
        · simp [h0]
        · exact hh n (Nat.pos_of_ne_zero h0) hn
      obtain ⟨x, _, _, _, hmin⟩ := headCost_minimum H s hp hf
      have hle : headCost H (s * (H+1)) ≤ ‖y‖^2 := by
        rw [hmin y hym hm]
        exact le_add_of_nonneg_right (sq_nonneg _)
      have hyn : ‖y‖ ≤ ‖centeredParity‖ + 1 := by
        linarith [norm_sub_norm_le y centeredParity]
      exact ⟨s, hp, hf, hle.trans ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hyn)⟩
    choose s hp hf hcost using hwin
    exact ⟨s, hp, hf, _, sq_nonneg _, hcost⟩
  · rintro ⟨s, hp, hf, C, hC, hcost⟩
    apply CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mpr
    apply CenteredMeanSnake.one_orthogonal_le_mixedClosure_iff_one_mem.mp
    exact one_orthogonal_le_mixedClosure_of_cofinal_headCost s hp hf C hC
      (fun H => ⟨H, le_rfl, hcost H⟩)

/-- At the first nonempty head, the conductor-six column alone gives an
explicit complete-energy upper bound for every fresh-prime window. -/
theorem headCost_two_le (s : ℕ) (hs : s.Prime) (h : 3 < s) :
    headCost 2 (s * 3) ≤ ((Real.log 2 - 2) / 2)^2 * (Real.pi / Real.sqrt 3) := by
  let a := (Real.log 2 - 2) / 2
  let y := a • ramanujanPacketHilbert 6
  have hy : y ∈ mixedSpace (Finset.Icc 2 (s * 3)) :=
    Submodule.smul_mem _ _ (mixed_packet_mul_of_coprime_mem_window
      (a := 2) (b := 3) (by decide) (by decide) (by decide) (by omega))
  have hm (m : orders 2) : mobiusDifferenceCLM m.val y = target m.val := by
    have hm2 : m.val = 2 := le_antisymm (Finset.mem_Icc.mp m.property).2
      (Finset.mem_Icc.mp m.property).1
    rw [hm2]
    change mobiusDifferenceCLM 2 (a • ramanujanPacketHilbert 6) = _
    rw [map_smul, mobiusDifferenceCLM_ramanujanPacketHilbert 2 6 (by decide) (by decide)]
    norm_num [a, target, incidence, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    ring
  obtain ⟨x, _, _, _, hmin⟩ := headCost_minimum 2 s hs h
  have hsum := hmin y hy hm
  have he : ‖y‖^2 = a^2 * (Real.pi / Real.sqrt 3) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, packet_two_six_inner_and_norm.2]
  change headCost 2 (s * 3) ≤ a^2 * _
  rw [← he, hsum]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting
