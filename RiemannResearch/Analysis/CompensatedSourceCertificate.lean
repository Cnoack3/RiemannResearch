import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Push
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Sharp compensated-source radius certificates

The positive-part certificate retains the full signed source correction.
Its lower budget is sharp: if the source radius is at most ε times the
true gain radius, the certificate retains (1-2ε)^2 of the true gain.

Source: RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 7, supplies
the source-radius strategy. The tunable Young and sharp relative bounds
extend that argument. Arithmetic construction of the radius is separate;
these declarations do not establish cumulative source divergence.
-/

noncomputable section

namespace RiemannResearch.Analysis.CompensatedSourceCertificate

def radiusCertificate (y t : ℝ) : ℝ := (max (y-t) 0)^2

theorem radiusCertificate_nonneg (y t : ℝ) :
    0 ≤ radiusCertificate y t := sq_nonneg _

theorem radius_positivePart_bounds {x y t : ℝ}
    (hx : 0 ≤ x) (_ht : 0 ≤ t) (hxy : |x-y| ≤ t) :
    max (y-t) 0 ≤ x ∧ x ≤ max (y-t) 0 + 2*t := by
  have hh := abs_le.mp hxy
  constructor
  · exact max_le (by linarith) hx
  · have hm : y-t ≤ max (y-t) 0 := le_max_left _ _
    linarith

theorem radiusCertificate_le {x y t : ℝ}
    (hx : 0 ≤ x) (_ht : 0 ≤ t) (hxy : |x-y| ≤ t) :
    radiusCertificate y t ≤ x^2 := by
  have hl := (radius_positivePart_bounds hx _ht hxy).1
  have hm : 0 ≤ max (y-t) 0 := le_max_right _ _
  have hp := mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hx hm)
  unfold radiusCertificate
  nlinarith

theorem radiusCertificate_sharp_lower {x y t : ℝ}
    (_hx : 0 ≤ x) (_ht : 0 ≤ t) (hxy : |x-y| ≤ t) :
    (max (x-2*t) 0)^2 ≤ radiusCertificate y t := by
  have hh := abs_le.mp hxy
  have hl : max (x-2*t) 0 ≤ max (y-t) 0 := by
    exact max_le_max (by linarith) le_rfl
  have hleft : 0 ≤ max (x-2*t) 0 := le_max_right _ _
  have hright : 0 ≤ max (y-t) 0 := le_max_right _ _
  have hp := mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hright hleft)
  unfold radiusCertificate
  nlinarith

theorem radiusCertificate_relative_lower {x y t ε : ℝ}
    (hx : 0 ≤ x) (_ht : 0 ≤ t) (hxy : |x-y| ≤ t)
    (_hε : 0 ≤ ε) (hhalf : ε ≤ 1/2) (hrel : t ≤ ε*x) :
    (1-2*ε)^2*x^2 ≤ radiusCertificate y t := by
  have hh := abs_le.mp hxy
  have hm : y-t ≤ max (y-t) 0 := le_max_left _ _
  have ha : 0 ≤ (1-2*ε)*x := mul_nonneg (by linarith) hx
  have hb : 0 ≤ max (y-t) 0 := le_max_right _ _
  have hab : (1-2*ε)*x ≤ max (y-t) 0 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb ha)
  unfold radiusCertificate
  nlinarith

theorem radiusCertificate_relative_sharp (x ε : ℝ)
    (hx : 0 ≤ x) (_hε : 0 ≤ ε) (hhalf : ε ≤ 1/2) :
    radiusCertificate ((1-ε)*x) (ε*x) = (1-2*ε)^2*x^2 := by
  have hnonneg : 0 ≤ (1-ε)*x-ε*x := by nlinarith
  unfold radiusCertificate
  rw [max_eq_left hnonneg]
  ring

/-- Tunable Young bound; θ=1 is the previous `g≤2q+8τ` envelope. -/
theorem radiusCertificate_upper_young {x y t θ : ℝ}
    (hx : 0 ≤ x) (_ht : 0 ≤ t) (hxy : |x-y| ≤ t) (hθ : 0 ≤ θ) :
    θ*x^2 ≤ θ*(1+θ)*radiusCertificate y t + 4*(θ+1)*t^2 := by
  have hxup := (radius_positivePart_bounds hx _ht hxy).2
  have hm : 0 ≤ max (y-t) 0 := le_max_right _ _
  have hup : x^2 ≤ (max (y-t) 0 + 2*t)^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hxup)
      (add_nonneg (by linarith : 0 ≤ max (y-t) 0 + 2*t) hx)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hup hθ
  have hs := sq_nonneg (θ*max (y-t) 0 - 2*t)
  unfold radiusCertificate
  nlinarith

def gainCertificate (A τ : ℝ) : ℝ :=
  radiusCertificate (Real.sqrt A) (Real.sqrt τ)

theorem gainCertificate_sharp_lower {g A τ : ℝ}
    (_hg : 0 ≤ g) (_hτ : 0 ≤ τ)
    (hsource : |Real.sqrt g-Real.sqrt A| ≤ Real.sqrt τ) :
    (max (Real.sqrt g-2*Real.sqrt τ) 0)^2 ≤ gainCertificate A τ := by
  exact radiusCertificate_sharp_lower (Real.sqrt_nonneg g)
    (Real.sqrt_nonneg τ) hsource

theorem gainCertificate_le_gain {g A τ : ℝ}
    (hg : 0 ≤ g) (_hτ : 0 ≤ τ)
    (hsource : |Real.sqrt g-Real.sqrt A| ≤ Real.sqrt τ) :
    gainCertificate A τ ≤ g := by
  have h := radiusCertificate_le (Real.sqrt_nonneg g)
    (Real.sqrt_nonneg τ) hsource
  simpa only [Real.sq_sqrt hg, gainCertificate] using h

theorem gainCertificate_relative_lower {g A τ ε : ℝ}
    (hg : 0 ≤ g) (hτ : 0 ≤ τ)
    (hsource : |Real.sqrt g-Real.sqrt A| ≤ Real.sqrt τ)
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1/2) (hbudget : τ ≤ ε^2*g) :
    (1-2*ε)^2*g ≤ gainCertificate A τ := by
  have hright : 0 ≤ ε*Real.sqrt g := mul_nonneg hε (Real.sqrt_nonneg g)
  have heq : (ε*Real.sqrt g)^2 = ε^2*g := by
    rw [mul_pow, Real.sq_sqrt hg]
  have hs : (Real.sqrt τ)^2 ≤ (ε*Real.sqrt g)^2 := by
    rw [Real.sq_sqrt hτ, heq]
    exact hbudget
  have hrel : Real.sqrt τ ≤ ε*Real.sqrt g := by
    nlinarith [Real.sqrt_nonneg τ]
  have h := radiusCertificate_relative_lower (Real.sqrt_nonneg g)
    (Real.sqrt_nonneg τ) hsource hε hhalf hrel
  simpa only [Real.sq_sqrt hg, gainCertificate] using h

theorem gainCertificate_quarter {g A τ : ℝ}
    (hg : 0 ≤ g) (hτ : 0 ≤ τ)
    (hsource : |Real.sqrt g-Real.sqrt A| ≤ Real.sqrt τ)
    (hbudget : τ ≤ g/16) : g/4 ≤ gainCertificate A τ := by
  have h := gainCertificate_relative_lower hg hτ hsource
    (ε := (1/4 : ℝ)) (by norm_num) (by norm_num) (by nlinarith : τ ≤ (1/4 : ℝ)^2*g)
  norm_num at h
  linarith

end RiemannResearch.Analysis.CompensatedSourceCertificate



/-!
The weighted declarations passed coherent Lean checks on 9 October 2026.

Intended as an extension of Analysis/CompensatedSourceCertificate, not a
separate published module. A summable weighted source-error budget transfers
cumulative divergence in both directions. The arithmetic application must
still supply this budget; no RH-strength provider is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.CompensatedSourceCertificate

/-- The full Young error allowance is retained before applying any weight. -/
theorem gainCertificate_weighted_upper {g A τ w : ℝ}
    (hg : 0 ≤ g) (hτ : 0 ≤ τ) (hw : 0 ≤ w)
    (hsource : |Real.sqrt g - Real.sqrt A| ≤ Real.sqrt τ) :
    w*g ≤ 2*(w*gainCertificate A τ) + 8*(w*τ) := by
  have h := radiusCertificate_upper_young (Real.sqrt_nonneg g)
    (Real.sqrt_nonneg τ) hsource (θ := (1 : ℝ)) (by norm_num)
  have hgain : g ≤ 2*gainCertificate A τ + 8*τ := by
    simpa only [one_mul, show (1:ℝ)+1=2 by norm_num,
      Real.sq_sqrt hg, Real.sq_sqrt hτ, gainCertificate,
      show (4:ℝ)*2=8 by norm_num] using h
  have hweighted := mul_le_mul_of_nonneg_left hgain hw
  nlinarith only [hweighted]

/-- Summability transfers without a pointwise relative-error condition.
The weighted error series remains an explicit substantive input. -/
theorem gainCertificate_weighted_summable_iff
    (g A τ w : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hτ : ∀ n, 0 ≤ τ n)
    (hw : ∀ n, 0 ≤ w n)
    (hsource : ∀ n, |Real.sqrt (g n) - Real.sqrt (A n)| ≤ Real.sqrt (τ n))
    (hError : Summable (fun n => w n * τ n)) :
    Summable (fun n => w n * g n) ↔
      Summable (fun n => w n * gainCertificate (A n) (τ n)) := by
  constructor
  · intro hGain
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (radiusCertificate_nonneg _ _))
      (fun n => ?_) hGain
    exact mul_le_mul_of_nonneg_left
      (gainCertificate_le_gain (hg n) (hτ n) (hsource n)) (hw n)
  · intro hCert
    have hmajor := (hCert.mul_left 2).add (hError.mul_left 8)
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (hg n)) (fun n => ?_) hmajor
    exact gainCertificate_weighted_upper (hg n) (hτ n) (hw n) (hsource n)

/-- Exact cumulative divergence equivalence under the summable weighted
error provider. In the RH application the weight is 1/E_n^2. -/
theorem gainCertificate_weighted_divergence_iff
    (g A τ w : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hτ : ∀ n, 0 ≤ τ n)
    (hw : ∀ n, 0 ≤ w n)
    (hsource : ∀ n, |Real.sqrt (g n) - Real.sqrt (A n)| ≤ Real.sqrt (τ n))
    (hError : Summable (fun n => w n * τ n)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, w n * g n) atTop atTop ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        w n * gainCertificate (A n) (τ n)) atTop atTop := by
  have hGain := not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := fun n => w n * g n) (fun n => mul_nonneg (hw n) (hg n))
  have hCert := not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := fun n => w n * gainCertificate (A n) (τ n))
    (fun n => mul_nonneg (hw n) (radiusCertificate_nonneg _ _))
  exact hGain.symm.trans ((not_congr
    (gainCertificate_weighted_summable_iff g A τ w hg hτ hw hsource hError)).trans hCert)

end RiemannResearch.Analysis.CompensatedSourceCertificate



/-!
# Adaptive physical cutoffs for a normalized tail-error budget

The normalized cutoff declarations passed coherent Lean checks on 9 October
2026. The stage floor and complete physical tail hypotheses remain explicit.

The error denominator E n is fixed before choosing the physical cutoff.
The tail provider must hold for every permitted cutoff, and a cutoff can
be enlarged independently of the arithmetic dictionary stage. Under these
explicit hypotheses, a stage-dependent C n / (N + 1) tail estimate supplies
a summable normalized error budget. It does not supply gain divergence or
an actual arithmetic provider for freely adjustable source cutoffs.

The final two declarations formalize the PDF's already stated primorial-
stage choice N_n + 1 ≥ 2^n [L_n(L_n + 1)]². This is a dependency
formalization, not a novelty claim.
-/

noncomputable section
open Filter

namespace RiemannResearch.Analysis.CompensatedSourceCertificate

/-- A freely enlarged cutoff achieves any positive normalized error budget.
The complete physical endpoint N + 1 is retained. -/
theorem normalizedTailError_cutoff_exists
    (E C ε : ℝ) (M : ℕ) (hE : 0 < E) (_hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N : ℕ, M ≤ N ∧
      ∀ τ : ℝ, τ ≤ C / ((N : ℝ) + 1) → τ / E ^ 2 ≤ ε := by
  have hE2 : 0 < E ^ 2 := sq_pos_of_pos hE
  obtain ⟨k, hk⟩ := exists_nat_gt (C / (ε * E ^ 2))
  let N : ℕ := max M k
  refine ⟨N, le_max_left M k, ?_⟩
  have hkN : (k : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (le_max_right M k)
  have hNpos : 0 < (N : ℝ) + 1 := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have hthreshold : C / (ε * E ^ 2) < (N : ℝ) + 1 := by
    linarith only [hk, hkN]
  have hprod : C < ((N : ℝ) + 1) * (ε * E ^ 2) :=
    (div_lt_iff₀ (mul_pos hε hE2)).mp hthreshold
  have hcut : C / ((N : ℝ) + 1) ≤ ε * E ^ 2 := by
    apply (div_le_iff₀ hNpos).mpr
    calc
      C ≤ ((N : ℝ) + 1) * (ε * E ^ 2) := le_of_lt hprod
      _ = (ε * E ^ 2) * ((N : ℝ) + 1) := mul_comm _ _
  intro τ hτ
  exact (div_le_iff₀ hE2).mpr (hτ.trans hcut)

/-- Cutoffs can meet any prescribed stage floor and positive budget while
forming a cofinal sequence. The pointwise comparison is uniform in τ. -/
theorem normalizedTailError_adaptive_cutoffs
    (E C ε : ℕ → ℝ) (L : ℕ → ℕ)
    (hE : ∀ n, 0 < E n) (hC : ∀ n, 0 ≤ C n) (hε : ∀ n, 0 < ε n) :
    ∃ N : ℕ → ℕ,
      (∀ n, max n (L n) ≤ N n) ∧
      Tendsto N atTop atTop ∧
      ∀ n (τ : ℝ), τ ≤ C n / ((N n : ℝ) + 1) →
        τ / (E n) ^ 2 ≤ ε n := by
  classical
  have hex (n : ℕ) := normalizedTailError_cutoff_exists
    (E n) (C n) (ε n) (max n (L n)) (hE n) (hC n) (hε n)
  let N : ℕ → ℕ := fun n => Classical.choose (hex n)
  have hN (n : ℕ) : max n (L n) ≤ N n ∧
      ∀ τ : ℝ, τ ≤ C n / ((N n : ℝ) + 1) →
        τ / (E n) ^ 2 ≤ ε n := Classical.choose_spec (hex n)
  refine ⟨N, fun n => (hN n).1, ?_, fun n => (hN n).2⟩
  exact Filter.tendsto_atTop_mono
    (fun n => (le_max_left n (L n)).trans (hN n).1) Filter.tendsto_id

/-- A summable positive target budget produces a summable normalized
tail error when every cutoff obeys the given physical tail provider. -/
theorem normalizedTailError_adaptive_summable
    (E C ε : ℕ → ℝ) (L : ℕ → ℕ) (τ : ℕ → ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hC : ∀ n, 0 ≤ C n) (hε : ∀ n, 0 < ε n)
    (hBudget : Summable ε)
    (hτ0 : ∀ n N, 0 ≤ τ n N)
    (hTail : ∀ n N, τ n N ≤ C n / ((N : ℝ) + 1)) :
    ∃ N : ℕ → ℕ,
      (∀ n, max n (L n) ≤ N n) ∧
      Tendsto N atTop atTop ∧
      (∀ n, τ n (N n) / (E n) ^ 2 ≤ ε n) ∧
      Summable (fun n => τ n (N n) / (E n) ^ 2) := by
  obtain ⟨N, hN, hcofinal, hupper⟩ :=
    normalizedTailError_adaptive_cutoffs E C ε L hE hC hε
  have hcomparison (n : ℕ) : τ n (N n) / (E n) ^ 2 ≤ ε n :=
    hupper n (τ n (N n)) (hTail n (N n))
  refine ⟨N, hN, hcofinal, hcomparison, ?_⟩
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg (hτ0 n (N n)) (sq_nonneg (E n)))
    hcomparison hBudget

/-- In particular, freely chosen cutoffs make the normalized errors no
larger than 2⁻ⁿ. No lower bound on E n uniform in n is required. -/
theorem normalizedTailError_geometric_cutoffs
    (E C : ℕ → ℝ) (L : ℕ → ℕ) (τ : ℕ → ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hC : ∀ n, 0 ≤ C n)
    (hτ0 : ∀ n N, 0 ≤ τ n N)
    (hTail : ∀ n N, τ n N ≤ C n / ((N : ℝ) + 1)) :
    ∃ N : ℕ → ℕ,
      (∀ n, max n (L n) ≤ N n) ∧
      Tendsto N atTop atTop ∧
      (∀ n, τ n (N n) / (E n) ^ 2 ≤ (1 / 2 : ℝ) ^ n) ∧
      Summable (fun n => τ n (N n) / (E n) ^ 2) := by
  exact normalizedTailError_adaptive_summable
    E C (fun n => (1 / 2 : ℝ) ^ n) L τ hE hC
    (fun n => pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    summable_geometric_two hτ0 hTail

/-- The explicit stage lower bound and head horizon from the paper imply
the geometric normalized error estimate. The error E is evaluated at the
fixed dictionary stage L, independently of the freely chosen horizon N. -/
theorem normalizedTailError_le_geometric_of_stage_bound
    (E τ : ℝ) (L N n : ℕ) (hL : 0 < L)
    (hE : 1 / ((L : ℝ) * ((L : ℝ) + 1)) ≤ E)
    (hτ : τ ≤ 1 / ((N : ℝ) + 1))
    (hN : (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 ≤
      (N : ℝ) + 1) :
    τ / E ^ 2 ≤ (1 / 2 : ℝ) ^ n := by
  let A : ℝ := (L : ℝ) * ((L : ℝ) + 1)
  have hLreal : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hApos : 0 < A := mul_pos hLreal (by linarith)
  have hAE : (1 : ℝ) ≤ E * A := (div_le_iff₀ hApos).mp hE
  have hAE0 : 0 ≤ E * A := (by norm_num : (0 : ℝ) ≤ 1).trans hAE
  have hsq : (1 : ℝ) ≤ E ^ 2 * A ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hAE0).mpr hAE
    simpa only [one_pow, mul_pow] using h
  have hNmul := mul_le_mul_of_nonneg_right hN (sq_nonneg E)
  have hlarge : (2 : ℝ) ^ n ≤ ((N : ℝ) + 1) * E ^ 2 := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ n * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ n * (E ^ 2 * A ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
      _ = ((2 : ℝ) ^ n * A ^ 2) * E ^ 2 := by
        rw [mul_comm (E ^ 2) (A ^ 2), ← mul_assoc]
      _ ≤ ((N : ℝ) + 1) * E ^ 2 := hNmul
  calc
    τ / E ^ 2 ≤ (1 / ((N : ℝ) + 1)) / E ^ 2 :=
      div_le_div_of_nonneg_right hτ (sq_nonneg E)
    _ = 1 / (((N : ℝ) + 1) * E ^ 2) := by rw [div_div]
    _ ≤ 1 / (2 : ℝ) ^ n :=
      one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) n) hlarge
    _ = (1 / 2 : ℝ) ^ n := by simp only [div_pow, one_pow]

/-- Paper specialization: its explicit stage/error and horizon providers
discharge the summable normalized error dependency. -/
theorem normalizedTailError_summable_of_stage_bound
    (E τ : ℕ → ℝ) (L N : ℕ → ℕ)
    (hL : ∀ n, 0 < L n)
    (hE : ∀ n, 1 / ((L n : ℝ) * ((L n : ℝ) + 1)) ≤ E n)
    (hτ0 : ∀ n, 0 ≤ τ n)
    (hτ : ∀ n, τ n ≤ 1 / ((N n : ℝ) + 1))
    (hN : ∀ n, (2 : ℝ) ^ n * ((L n : ℝ) * ((L n : ℝ) + 1)) ^ 2 ≤
      (N n : ℝ) + 1) :
    Summable (fun n => τ n / (E n) ^ 2) := by
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg (hτ0 n) (sq_nonneg (E n)))
    (fun n => normalizedTailError_le_geometric_of_stage_bound
      (E n) (τ n) (L n) (N n) n (hL n) (hE n) (hτ n) (hN n))
    summable_geometric_two

end RiemannResearch.Analysis.CompensatedSourceCertificate




/-!
# Constructive paper horizons for the normalized source-error budget

The constructive horizon declarations passed coherent Lean checks on 9 October
2026. The physical error floor and tail provider remain explicit.

The natural horizon is the paper's explicit choice
N = 2^n [L(L+1)]², enlarged by a requested floor when necessary. The stage
L and its error denominator E are fixed before this horizon is chosen.
These declarations discharge the horizon inequality, not the actual error
floor or physical tail provider, and supply no gain divergence or RH proof.
-/

noncomputable section
open Filter

namespace RiemannResearch.Analysis.CompensatedSourceCertificate

/-- The paper horizon is a natural number; it requires no choice operator. -/
def normalizedTailHorizon (L n : ℕ) : ℕ :=
  2 ^ n * (L * (L + 1)) ^ 2

/-- Enlarge the physical horizon to meet both a requested floor and n. -/
def normalizedTailHorizonWithFloor (L F n : ℕ) : ℕ :=
  max (max n F) (normalizedTailHorizon L n)

/-- Casting the natural horizon gives exactly the paper's real expression. -/
theorem normalizedTailHorizon_cast (L n : ℕ) :
    (normalizedTailHorizon L n : ℝ) =
      (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 := by
  simp only [normalizedTailHorizon, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

/-- The full physical endpoint N + 1 obeys the required paper inequality. -/
theorem normalizedTailHorizon_paper_bound (L n : ℕ) :
    (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 ≤
      (normalizedTailHorizon L n : ℝ) + 1 := by
  rw [← normalizedTailHorizon_cast L n]
  exact le_add_of_nonneg_right zero_le_one

/-- The enlarged horizon meets the floor and is at least the stage index. -/
theorem normalizedTailHorizonWithFloor_lower (L F n : ℕ) :
    max n F ≤ normalizedTailHorizonWithFloor L F n := by
  exact le_max_left _ _

/-- Enlarging the horizon preserves the exact paper endpoint inequality. -/
theorem normalizedTailHorizonWithFloor_paper_bound (L F n : ℕ) :
    (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 ≤
      (normalizedTailHorizonWithFloor L F n : ℝ) + 1 := by
  have hcast : (normalizedTailHorizon L n : ℝ) ≤
      (normalizedTailHorizonWithFloor L F n : ℝ) :=
    Nat.cast_le.mpr (le_max_right (max n F) (normalizedTailHorizon L n))
  calc
    (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 =
        (normalizedTailHorizon L n : ℝ) := (normalizedTailHorizon_cast L n).symm
    _ ≤ (normalizedTailHorizonWithFloor L F n : ℝ) := hcast
    _ ≤ (normalizedTailHorizonWithFloor L F n : ℝ) + 1 :=
      le_add_of_nonneg_right zero_le_one

/-- The constructive enlarged horizons are cofinal for arbitrary stage and
floor sequences, because they are at least their stage index. -/
theorem normalizedTailHorizonWithFloor_cofinal (L F : ℕ → ℕ) :
    Tendsto (fun n => normalizedTailHorizonWithFloor (L n) (F n) n)
      atTop atTop := by
  exact Filter.tendsto_atTop_mono
    (fun n => (le_max_left n (F n)).trans
      (normalizedTailHorizonWithFloor_lower (L n) (F n) n))
    Filter.tendsto_id

/-- The supplied stage-error floor and physical tail estimate give the
geometric normalized budget at the fully explicit enlarged horizon. -/
theorem normalizedTailError_le_geometric_of_explicit_horizon
    (E τ : ℝ) (L F n : ℕ) (hL : 0 < L)
    (hE : 1 / ((L : ℝ) * ((L : ℝ) + 1)) ≤ E)
    (hτ : τ ≤ 1 / ((normalizedTailHorizonWithFloor L F n : ℝ) + 1)) :
    τ / E ^ 2 ≤ (1 / 2 : ℝ) ^ n := by
  exact normalizedTailError_le_geometric_of_stage_bound
    E τ L (normalizedTailHorizonWithFloor L F n) n hL hE hτ
    (normalizedTailHorizonWithFloor_paper_bound L F n)

/-- The horizon is now constructed rather than supplied as an inequality.
The arithmetic error floor and actual tail provider remain explicit. -/
theorem normalizedTailError_summable_of_explicit_horizon
    (E τ : ℕ → ℝ) (L F : ℕ → ℕ)
    (hL : ∀ n, 0 < L n)
    (hE : ∀ n, 1 / ((L n : ℝ) * ((L n : ℝ) + 1)) ≤ E n)
    (hτ0 : ∀ n, 0 ≤ τ n)
    (hτ : ∀ n, τ n ≤
      1 / ((normalizedTailHorizonWithFloor (L n) (F n) n : ℝ) + 1)) :
    Summable (fun n => τ n / (E n) ^ 2) := by
  exact normalizedTailError_summable_of_stage_bound
    E τ L (fun n => normalizedTailHorizonWithFloor (L n) (F n) n)
    hL hE hτ0 hτ
    (fun n => normalizedTailHorizonWithFloor_paper_bound (L n) (F n) n)

end RiemannResearch.Analysis.CompensatedSourceCertificate

/-!
# Normalized-gain divergence and the zero-defect endpoint

Source: user-provided RH_Actual_Arithmetic_Advances_2026-10-07.pdf,
scalar normalized-gain equivalence. The fixed-tail-block proof retains the
exact final error; a positive error floor bounds every prefix. The theorem
supplies neither divergence nor the arithmetic zero-limit provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.CompensatedSourceCertificate

private theorem normalizedGain_telescope (E : ℕ → ℝ) (n m : ℕ) :
    (∑ k ∈ Finset.range m, (E (n+k) - E (n+k+1))) = E n - E (n+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_assoc]
      ring

private theorem normalizedGain_nonneg
    (E : ℕ → ℝ) (hanti : Antitone E) (n : ℕ) :
    0 ≤ (E n - E (n+1)) / (E n) ^ 2 := by
  exact div_nonneg (sub_nonneg.mpr (hanti (Nat.le_succ n))) (sq_nonneg _)

private theorem normalizedGain_prefix_mono
    (E : ℕ → ℝ) (hanti : Antitone E) :
    Monotone (fun N => ∑ n ∈ Finset.range N, (E n - E (n+1)) / (E n) ^ 2) := by
  intro N M hNM
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    (fun n _ _ => normalizedGain_nonneg E hanti n)

/-- A fixed tail block dominates its exact energy drop divided by the
starting error square. The endpoint error is retained. -/
theorem normalizedGain_tailBlock_lower
    (E : ℕ → ℝ) (hpos : ∀ n, 0 < E n) (hanti : Antitone E) (n m : ℕ) :
    (E n - E (n+m)) / (E n) ^ 2 ≤
      ∑ k ∈ Finset.range m,
        (E (n+k) - E (n+k+1)) / (E (n+k)) ^ 2 := by
  calc
    (E n - E (n+m)) / (E n) ^ 2 =
        (∑ k ∈ Finset.range m, (E (n+k) - E (n+k+1))) / (E n) ^ 2 := by
      rw [normalizedGain_telescope]
    _ = ∑ k ∈ Finset.range m,
        (E (n+k) - E (n+k+1)) / (E n) ^ 2 := by simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hgain : 0 ≤ E (n+k) - E (n+k+1) :=
        sub_nonneg.mpr (hanti (Nat.le_succ (n+k)))
      have hden : (E (n+k)) ^ 2 ≤ (E n) ^ 2 :=
        (sq_le_sq₀ (hpos (n+k)).le (hpos n).le).mpr
          (hanti (Nat.le_add_right n k))
      exact div_le_div_of_nonneg_left hgain (sq_pos_of_pos (hpos (n+k))) hden

/-- A positive error floor bounds every normalized-gain prefix. -/
theorem normalizedGain_prefix_upper_of_floor
    (E : ℕ → ℝ) (hpos : ∀ n, 0 < E n) (hanti : Antitone E)
    (δ : ℝ) (hδ : 0 < δ) (hfloor : ∀ n, δ ≤ E n) (N : ℕ) :
    (∑ n ∈ Finset.range N, (E n - E (n+1)) / (E n) ^ 2) ≤
      (E 0 - E N) / δ ^ 2 := by
  calc
    (∑ n ∈ Finset.range N, (E n - E (n+1)) / (E n) ^ 2) ≤
        ∑ n ∈ Finset.range N, (E n - E (n+1)) / δ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hgain : 0 ≤ E n - E (n+1) :=
        sub_nonneg.mpr (hanti (Nat.le_succ n))
      have hden : δ ^ 2 ≤ (E n) ^ 2 :=
        (sq_le_sq₀ hδ.le (hpos n).le).mpr (hfloor n)
      exact div_le_div_of_nonneg_left hgain (sq_pos_of_pos hδ) hden
    _ = (∑ n ∈ Finset.range N, (E n - E (n+1))) / δ ^ 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (E 0 - E N) / δ ^ 2 := by
      rw [show (∑ n ∈ Finset.range N, (E n - E (n+1))) = E 0 - E N from
        by simpa only [zero_add] using normalizedGain_telescope E 0 N]

/-- A zero error limit forces cumulative normalized-gain divergence.
This is a scalar implication; its arithmetic zero-limit input stays open. -/
theorem normalizedGain_divergence_of_zero_limit
    (E : ℕ → ℝ) (hpos : ∀ n, 0 < E n) (hanti : Antitone E)
    (hzero : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (E n - E (n+1)) / (E n) ^ 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let C : ℝ := max b 0 + 1
  have hC : 0 < C := by
    have hmax : 0 ≤ max b 0 := le_max_right _ _
    dsimp only [C]
    linarith
  have hε : 0 < 1 / (2*C) :=
    one_div_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hC)
  obtain ⟨n, hn⟩ := (hzero.eventually_lt_const hε).exists
  have hn' : E n < 1 / (2*C) := hn
  obtain ⟨J, hJ⟩ := (hzero.eventually_lt_const (half_pos (hpos n))).exists
  have hJle : J ≤ n+J := by
    simpa only [Nat.add_comm] using Nat.le_add_right J n
  have hend : E (n+J) < E n / 2 := (hanti hJle).trans_lt hJ
  have hsmall : E n * (2*C) < 1 :=
    (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp hn'
  have hscaled := mul_lt_mul_of_pos_right hsmall (hpos n)
  have hbig : C < (E n - E (n+J)) / (E n) ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos (hpos n))).mpr
    nlinarith only [hend, hscaled]
  have hblock := normalizedGain_tailBlock_lower E hpos hanti n J
  have hprefix0 : 0 ≤ ∑ k ∈ Finset.range n,
      (E k - E (k+1)) / (E k) ^ 2 :=
    Finset.sum_nonneg (fun k hk => normalizedGain_nonneg E hanti k)
  have hsplit : (∑ k ∈ Finset.range (n+J), (E k - E (k+1)) / (E k) ^ 2) =
      (∑ k ∈ Finset.range n, (E k - E (k+1)) / (E k) ^ 2) +
      ∑ k ∈ Finset.range J, (E (n+k) - E (n+k+1)) / (E (n+k)) ^ 2 := by
    rw [Finset.sum_range_add]
  have hlarge : b ≤ ∑ k ∈ Finset.range (n+J),
      (E k - E (k+1)) / (E k) ^ 2 := by
    have hbC : b < C := by
      have hbmax : b ≤ max b 0 := le_max_left _ _
      dsimp only [C]
      linarith
    linarith only [hbC, hbig, hblock, hprefix0, hsplit]
  exact Filter.eventually_atTop.2 ⟨n+J, fun N hN =>
    hlarge.trans (normalizedGain_prefix_mono E hanti hN)⟩

/-- For strictly positive antitone errors, cumulative normalized-gain
divergence is equivalent to the zero-defect limit. Neither side is supplied
by this equivalence for an actual arithmetic sequence. -/
theorem normalizedGain_divergence_iff_zero_limit
    (E : ℕ → ℝ) (hpos : ∀ n, 0 < E n) (hanti : Antitone E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (E n - E (n+1)) / (E n) ^ 2) atTop atTop ↔
      Tendsto E atTop (𝓝 0) := by
  constructor
  · intro hdiv
    by_contra hz
    have hex : ∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ E n := by
      by_contra hfloor
      push Not at hfloor
      apply hz
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro a ha
        exact Filter.Eventually.of_forall (fun n => ha.trans (hpos n))
      · intro b hb
        obtain ⟨n, hn⟩ := hfloor b hb
        exact Filter.eventually_atTop.2 ⟨n, fun N hN => (hanti hN).trans_lt hn⟩
    obtain ⟨δ, hδ, hfloor⟩ := hex
    obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (E 0 / δ ^ 2 + 1)).exists
    have hupper := normalizedGain_prefix_upper_of_floor E hpos hanti δ hδ hfloor N
    have hcoarse : (E 0 - E N) / δ ^ 2 ≤ E 0 / δ ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [hpos N]) (sq_nonneg δ)
    linarith
  · exact normalizedGain_divergence_of_zero_limit E hpos hanti

end RiemannResearch.Analysis.CompensatedSourceCertificate
