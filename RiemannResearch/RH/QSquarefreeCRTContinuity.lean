/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.PrimeResidueTopology
import RiemannResearch.NumberTheory.ModularOscillation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeCRTRegularity
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-!
# The exact CRT continuity obligation for the displacement

The existing displacement rigidity theorem implies that any continuous CRT
extension of d is the zero function. Here its existence is characterized both
by congruence uniform continuity and by a single finite modular oscillation
bound. These are conditional research reductions: their premise for the
actual displacement remains Open.

There is an unconditional obstruction to a direct operator-algebra argument:
for every f in QHilbert, Bf tends to zero at physical infinity, and
Bf has a continuous CRT extension if and only if f = 0.
Thus B does not act on CRT-continuous functions by restriction, except at zero.
This does not imply d itself tends to zero: the projection in
d = Pi B(r+d) has not been shown to preserve physical regularity.

If the residual is nonzero, the finite displacement approximants have
eventually arbitrarily large physical values, despite their Hilbert convergence.

Sources: PrimeResidueTopology for finite CRT and the uniform extension theorem;
T. Tao, An Epsilon of Room I (AMS, 2010), Exercise 1.10.28, distinguishes
uniform approximation on the compact product from Hilbert approximation.
The RH bridge and displacement identities are inherited from the imported
repository modules; no new unproved provider is inserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeCRTContinuity
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeCRTRegularity QSquarefreeDisplacementRigidity
open QSquarefreeFiniteDisplacement
open RiemannResearch.NumberTheory.PrimeResidueTopology

theorem B_physical_tendsto_zero (f : QHilbert) :
    Tendsto (qSequence (B f)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun n => |qSequence f n / (n : ℝ)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (qSequence_div_nat_tendsto_zero f).abs
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  cases n with
  | zero => simp
  | succ k =>
    rw [Real.norm_eq_abs, qSequence_B, abs_div, abs_div,
      abs_of_pos (by positivity : 0 < ((k+1 : ℕ) : ℝ) + 1),
      abs_of_pos (by positivity : 0 < ((k+1 : ℕ) : ℝ))]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    linarith

theorem continuous_crt_extension_B_iff (f : QHilbert) :
    HasContinuousCRTExtension (B f) ↔ f = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    apply qSequence_injective
    funext n
    have hzero : qSequence (B f) n = 0 := by
      cases n with
      | zero => simp
      | succ k =>
        rw [← hF (k+1) (Nat.succ_le_succ (Nat.zero_le k))]
        exact continuous_trace_limit_constant F hF (B_physical_tendsto_zero f) _
    rw [qSequence_B] at hzero
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hv := (div_eq_zero_iff.mp hzero).resolve_right hn
    simpa only [← qEvalCLM_apply, map_zero] using hv
  · rintro rfl
    refine ⟨0, ?_⟩
    intro n hn
    simp only [map_zero, ContinuousMap.zero_apply, ← qEvalCLM_apply]

theorem finite_displacement_unbounded_eventually
    (hr : limitingResidual ≠ 0) (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∃ n : ℕ,
      C < |qSequence (finiteDisplacement j) n| := by
  have hx : ∃ n, C < |qSequence displacement n| := by
    by_contra h
    push Not at h
    exact hr (residual_eq_zero_of_displacement_physically_bounded C h)
  obtain ⟨n, hn⟩ := hx
  have ht := (qSequence_tendsto_of_tendsto finiteDisplacement_tendsto n).abs
  filter_upwards [(tendsto_order.mp ht).1 C hn] with j hj
  exact ⟨n, hj⟩

theorem residual_zero_of_modular_oscillation (M : ℕ) (hM : 0 < M)
    (C : ℝ) (h : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n % M = m % M →
      |qSequence displacement n - qSequence displacement m| ≤ C) :
    limitingResidual = 0 := by
  obtain ⟨D, hD, hb⟩ :=
    RiemannResearch.NumberTheory.ModularOscillation.bounded_of_modular_oscillation
      (qSequence displacement) M hM C h
  apply residual_eq_zero_of_displacement_physically_bounded D
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using hD
  | succ k => exact hb _ (Nat.succ_le_succ (Nat.zero_le k))

theorem crt_extension_iff_modular_oscillation (M : ℕ) (hM : 0 < M) :
    HasContinuousCRTExtension displacement ↔
      ∃ C : ℝ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n % M = m % M →
        |qSequence displacement n - qSequence displacement m| ≤ C := by
  constructor
  · intro he
    have hd := displacement_eq_zero_of_residual_eq_zero
      (residual_zero_iff_crt_extension.mpr he)
    refine ⟨0, ?_⟩
    intro n m hn hm hmod
    simp only [hd, ← qEvalCLM_apply, map_zero, sub_zero, abs_zero, le_refl]
  · rintro ⟨C, hC⟩
    exact residual_zero_iff_crt_extension.mp (residual_zero_of_modular_oscillation M hM C hC)

theorem unbounded_modular_oscillation_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (M : ℕ) (hM : 0 < M) (C : ℝ) :
    ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ n % M = m % M ∧
      C < |qSequence displacement n - qSequence displacement m| := by
  by_contra h
  push Not at h
  apply hr
  exact residual_zero_of_modular_oscillation M hM C h


theorem displacement_continuous_extension_eq_zero
    (F : C(PrimeResidueSpace, ℝ))
    (hF : ∀ n : ℕ, 1 ≤ n → F (physicalPoint n) = qSequence displacement n) :
    F = 0 := by
  have hr := residual_zero_iff_crt_extension.mpr ⟨F, hF⟩
  have hd := displacement_eq_zero_of_residual_eq_zero hr
  apply continuous_extension_unique F 0
  intro n hn
  change F (physicalPoint n) = 0
  rw [hF n hn, hd]
  simp only [← qEvalCLM_apply, map_zero]

theorem crt_extension_iff_congruence_uniform_continuity :
    HasContinuousCRTExtension displacement ↔
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset Nat.Primes,
        ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
          (∀ p ∈ S, (n : ZMod p.val) = (m : ZMod p.val)) →
          |qSequence displacement n - qSequence displacement m| < ε := by
  constructor
  · intro he ε hε
    have hd := displacement_eq_zero_of_residual_eq_zero
      (residual_zero_iff_crt_extension.mpr he)
    refine ⟨∅, ?_⟩
    intro n m hn hm hagree
    simpa only [hd, ← qEvalCLM_apply, map_zero, sub_zero, abs_zero] using hε
  · intro hu
    obtain ⟨S, hS⟩ := hu 1 zero_lt_one
    let M := ∏ p ∈ S, p.val
    have hM : 0 < M := Finset.prod_pos (fun p hp => p.property.pos)
    apply residual_zero_iff_crt_extension.mp
    apply residual_zero_of_modular_oscillation M hM 1
    intro n m hn hm hmod
    apply (hS n m hn hm ?_).le
    intro p hp
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ hp) hmod


theorem crt_extension_iff_uniformContinuous :
    HasContinuousCRTExtension displacement ↔
      CRTUniformContinuous (fun n : {n : ℕ // 1 ≤ n} => qSequence displacement n.val) := by
  rw [← exists_extension_iff_uniformContinuous]
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, fun n => hF n.val n.property⟩
  · rintro ⟨F, hF⟩
    exact ⟨F, fun n hn => hF ⟨n, hn⟩⟩

end RiemannResearch.RH.QSquarefreeCRTContinuity
