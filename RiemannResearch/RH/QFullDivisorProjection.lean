import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.ZMod.Basic
import RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Canonical full-conductor projections on a cofinal divisor tower

Source: user-provided Full_Conductor_RH_Projection_Machinery.pdf,
Sections 2.3, 4 and 10.1, and the 9 November 2026 request for a canonical
LCM-indexed construction. A1's full-family witness is already implemented
in QFullDisplacement and is reused here.

For a positive period L, the finite dictionary contains every conductor
dividing L. The existing divisorStage definition is unrestricted:
despite its original module name, no squarefree hypothesis is used here.
This dictionary includes g_L and is L-periodic. A dictionary containing
every conductor up to L instead has common period lcmUpto L.

Both fits are the actual orthogonal projections in their respective
complete physical metrics. Along every nested divisor-exhausting tower,
they converge to the full Q and Pareto projections; their difference
converges to QFullDisplacement.displacement. The Q convergence transfers
to Pareto through QParetoEquivalence.tendsto_toPareto_iff.

Every finite legal function factors through ZMod L and extends
continuously to the all-modulus profinite integers. No continuity of a
limiting physical vector is inferred from Hilbert convergence. The exact
positive-site error at L is one, so these finite fits cannot converge
uniformly to the constant target on the positive integers.

The shared modulus or boundedness estimate for the actual displacement
remains Open; see QFullCRTDisplacement for the conditional RH implication.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullDivisorProjection
open ZetaTwoHilbert QSquarefreeLatticePackets QParetoEquivalence
open ZetaTwoParetoTransfer QParetoClosedProjectionComparison QFullResidueProjection

instance divisorStage_finiteDimensional (L : ℕ+) :
    FiniteDimensional ℝ (divisorStage (L : ℕ)) := by
  apply FiniteDimensional.span_of_finite
  have hr : Set.Finite
      (Set.range (fun d : {d : ℕ // d ∈ (L : ℕ).divisors} => qResidue d.val)) :=
    Set.finite_range _
  apply hr.subset
  rintro f ⟨d, hd, rfl⟩
  exact ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, L.ne_zero⟩⟩, rfl⟩

/-- The same finite physical dictionary in Pareto coordinates. -/
def paretoStage (L : ℕ+) : Submodule ℝ Pareto.ThresholdHilbert :=
  (divisorStage (L : ℕ)).map paretoEquiv.toLinearMap

instance paretoStage_finiteDimensional (L : ℕ+) :
    FiniteDimensional ℝ (paretoStage L) := by
  unfold paretoStage
  infer_instance

/-- The canonical complete-Q projection onto all divisor atoms. -/
def qOptimizer (L : ℕ+) : QHilbert :=
  (divisorStage (L : ℕ)).starProjection qOne

/-- The canonical Pareto projection, represented in Q coordinates. -/
def pOptimizer (L : ℕ+) : QHilbert :=
  pFit (paretoStage L) qOne

theorem toPareto_mem_stage_iff (L : ℕ+) (f : QHilbert) :
    toPareto f ∈ paretoStage L ↔ f ∈ divisorStage (L : ℕ) := by
  constructor
  · rintro ⟨x, hx, hxf⟩
    have he : x = f := paretoEquiv.injective hxf
    exact he ▸ hx
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem qOptimizer_mem (L : ℕ+) : qOptimizer L ∈ divisorStage (L : ℕ) :=
  (divisorStage (L : ℕ)).starProjection_apply_mem qOne

theorem pOptimizer_mem (L : ℕ+) : pOptimizer L ∈ divisorStage (L : ℕ) :=
  pFit_mem _ _ (toPareto_mem_stage_iff L) qOne

/-- Exact quotient factorization for every vector of the finite divisor span. -/
theorem sequence_mod_of_mem (L : ℕ) (f : QHilbert)
    (hf : f ∈ divisorStage L) (n : ℕ) :
    qSequence f (n % L) = qSequence f n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨d, hd, rfl⟩ := hf
      simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction,
        Nat.mod_mod_of_dvd n hd]
  | zero => simp [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
  | add f g hf hg ihf ihg =>
      change qSequenceLinear (f + g) (n % L) = qSequenceLinear (f + g) n
      simp only [map_add, Pi.add_apply]
      exact congrArg₂ (· + ·) ihf ihg
  | smul c f hf ih =>
      change qSequenceLinear (c • f) (n % L) = qSequenceLinear (c • f) n
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact congrArg (c * ·) ih

/-- Every finite legal vector vanishes on the whole common-multiple progression. -/
theorem sequence_zero_of_dvd (L : ℕ) (f : QHilbert)
    (hf : f ∈ divisorStage L) (n : ℕ) (hn : L ∣ n) :
    qSequence f n = 0 := by
  have h := sequence_mod_of_mem L f hf n
  rw [Nat.mod_eq_zero_of_dvd hn, qSequence_zero] at h
  exact h.symm

theorem divisorStage_le_full (L : ℕ+) :
    divisorStage (L : ℕ) ≤ legalSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  have hd0 := Nat.pos_of_dvd_of_pos hd L.pos
  by_cases hd1 : d = 1
  · rw [hd1, qResidue_one]
    exact legalSpan.zero_mem
  · apply Submodule.subset_span
    refine ⟨d - 2, ?_⟩
    change qResidue (d - 2 + 2) = qResidue d
    rw [Nat.sub_add_cancel (by omega : 2 ≤ d)]

/-- Every divisor-exhausting tower has the full all-conductor algebraic union. -/
theorem iSup_divisorStage_eq_full (L : ℕ → ℕ+)
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    (⨆ j, divisorStage (L j : ℕ)) = legalSpan := by
  apply le_antisymm
  · exact iSup_le (fun j => divisorStage_le_full (L j))
  · apply Submodule.span_le.mpr
    rintro f ⟨m, rfl⟩
    obtain ⟨j, hj⟩ := hcofinal (m + 2) (by omega)
    apply le_iSup (fun j => divisorStage (L j : ℕ)) j
    exact Submodule.subset_span ⟨m + 2, hj, rfl⟩

/-- Unconditional convergence to the full Q projection; no density assumption. -/
theorem qOptimizer_tendsto (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (fun j => qOptimizer (L j)) atTop
      (𝓝 (closure.starProjection qOne)) := by
  have hm : Monotone (fun j => divisorStage (L j : ℕ)) :=
    fun i j hij => divisorStage_mono (hnest i j hij)
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun j => divisorStage (L j : ℕ)) hm qOne
  simpa only [qOptimizer, iSup_divisorStage_eq_full L hcofinal, QFullResidueProjection.closure] using h


theorem paretoStage_mono {L K : ℕ+} (hLK : (L : ℕ) ∣ (K : ℕ)) :
    paretoStage L ≤ paretoStage K :=
  Submodule.map_mono (divisorStage_mono hLK)

theorem iSup_paretoStage_eq_full (L : ℕ → ℕ+)
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    (⨆ j, paretoStage (L j)) = legalSpan.map paretoEquiv.toLinearMap := by
  change (⨆ j, (divisorStage (L j : ℕ)).map paretoEquiv.toLinearMap) = _
  rw [← Submodule.map_iSup, iSup_divisorStage_eq_full L hcofinal]

/-- Unconditional convergence to the full Pareto projection in Q coordinates. -/
theorem pOptimizer_tendsto (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (fun j => pOptimizer (L j)) atTop
      (𝓝 (pFit QFullDisplacement.paretoClosure qOne)) := by
  have hm : Monotone (fun j => paretoStage (L j)) :=
    fun i j hij => paretoStage_mono (hnest i j hij)
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun j => paretoStage (L j)) hm (toPareto qOne)
  have ht : Tendsto
      (fun j => (paretoStage (L j)).starProjection (toPareto qOne)) atTop
      (𝓝 (QFullDisplacement.paretoClosure.starProjection (toPareto qOne))) := by
    simpa only [iSup_paretoStage_eq_full L hcofinal,
      QFullDisplacement.paretoClosure] using h
  exact toQCLM.continuous.continuousAt.tendsto.comp ht

/-- The actual finite difference of the two canonical projections. -/
def displacement (L : ℕ+) : QHilbert := qOptimizer L - pOptimizer L

theorem displacement_mem (L : ℕ+) :
    displacement L ∈ divisorStage (L : ℕ) :=
  (divisorStage (L : ℕ)).sub_mem (qOptimizer_mem L) (pOptimizer_mem L)

/-- The matched finite differences converge to A1's full-family displacement. -/
theorem displacement_tendsto (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (fun j => displacement (L j)) atTop
      (𝓝 QFullDisplacement.displacement) :=
  (qOptimizer_tendsto L hnest hcofinal).sub (pOptimizer_tendsto L hnest hcofinal)

/-- The positive running LCM, retaining every prime-power digit. -/
def lcmPeriod (M : ℕ) : ℕ+ := ⟨Nat.lcmUpto M, Nat.lcmUpto_pos M⟩

theorem lcmPeriod_nested {M N : ℕ} (hMN : M ≤ N) :
    (lcmPeriod M : ℕ) ∣ (lcmPeriod N : ℕ) := by
  change (Finset.Icc 1 M).lcm id ∣ (Finset.Icc 1 N).lcm id
  apply Finset.lcm_dvd
  intro d hd
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hMN⟩)

theorem lcmPeriod_exhausts (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    ∀ m : ℕ, 1 < m → ∃ j, m ∣ (lcmPeriod (M j) : ℕ) := by
  intro m hm
  obtain ⟨j, hj⟩ := (hM.eventually (eventually_ge_atTop m)).exists
  exact ⟨j, Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, hj⟩)⟩

/-- The requested construction along arbitrary monotone cofinal cutoffs. -/
theorem lcm_displacement_tendsto (M : ℕ → ℕ) (hmono : Monotone M)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => displacement (lcmPeriod (M j))) atTop
      (𝓝 QFullDisplacement.displacement) :=
  displacement_tendsto (fun j => lcmPeriod (M j))
    (fun i j hij => lcmPeriod_nested (hmono hij)) (lcmPeriod_exhausts M hM)

/-- The values of a legal periodic vector on its finite residue quotient. -/
def residueValues (L : ℕ+) (f : QHilbert) : ZMod (L : ℕ) → ℝ :=
  fun a => qSequence f a.val

theorem factors_through_residue (L : ℕ+) (f : QHilbert)
    (hf : f ∈ divisorStage (L : ℕ)) (n : ℕ) :
    residueValues L f (n : ZMod (L : ℕ)) = qSequence f n := by
  rw [residueValues, ZMod.val_natCast]
  exact sequence_mod_of_mem _ f hf n

open RiemannResearch.NumberTheory.GeneralizedCRT

/-- The finite cylinder function on the compact all-modulus inverse limit. -/
def profiniteLift (L : ℕ+) (f : QHilbert) : ProfiniteInt → ℝ :=
  fun x => residueValues L f (reduce ⟨L, L.ne_zero⟩ x)

/-- Continuity is established at each fixed finite stage. -/
theorem continuous_profiniteLift (L : ℕ+) (f : QHilbert) :
    Continuous (profiniteLift L f) := by
  exact continuous_of_discreteTopology.comp (continuous_reduce ⟨L, L.ne_zero⟩)

/-- The finite cylinder extension agrees with the original physical function. -/
theorem profiniteLift_natCast (L : ℕ+) (f : QHilbert)
    (hf : f ∈ divisorStage (L : ℕ)) (n : ℕ) :
    profiniteLift L f (n : ProfiniteInt) = qSequence f n := by
  unfold profiniteLift
  rw [map_natCast]
  exact factors_through_residue L f hf n

theorem profiniteLift_zero (L : ℕ+) (f : QHilbert) :
    profiniteLift L f 0 = 0 := by
  simp only [profiniteLift, map_zero, residueValues, ZMod.val_zero, qSequence_zero]

/-- Exact compulsory supremum error at the positive site equal to the period. -/
theorem positive_site_error_one (L : ℕ+) (f : QHilbert)
    (hf : f ∈ divisorStage (L : ℕ)) :
    |1 - qSequence f (L : ℕ)| = 1 := by
  rw [sequence_zero_of_dvd _ f hf _ dvd_rfl]
  norm_num

/-- Weighted Hilbert convergence cannot be replaced by uniform approximation to one. -/
theorem no_uniform_approximation_to_one (L : ℕ → ℕ+) (F : ℕ → QHilbert)
    (hF : ∀ j, F j ∈ divisorStage (L j : ℕ)) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j, J ≤ j →
      ∀ n : ℕ, 0 < n → |1 - qSequence (F j) n| < ε) := by
  intro h
  obtain ⟨J, hJ⟩ := h 1 (by norm_num)
  have hb := hJ J le_rfl (L J : ℕ) (L J).pos
  rw [positive_site_error_one (L J) (F J) (hF J)] at hb
  exact lt_irrefl 1 hb

end RiemannResearch.RH.QFullDivisorProjection
