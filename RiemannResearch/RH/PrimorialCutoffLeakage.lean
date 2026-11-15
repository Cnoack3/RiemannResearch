import RiemannResearch.RH.PrimorialCutoff
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
/-!
# Failure of the finite provider obtained from a single-cutoff primorial lift

Source: the user's P/Q augmented-density continuation, Priorities A and B.
Insert the concrete source into the identity Z*k*B(g_k)-k*g_k = k*D(g_k).
The resulting approximant belongs to the finite legal span, and its complete
scaled error is exactly the distance from the source to k*D(g_k), divided by Z.

The source norms diverge whereas k*D(g_k) converges to one for cofinal k.
Thus these particular scaled provider errors diverge. This theorem does not
rule out other finite legal approximants or establish or refute RH.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimorialCutoffLeakage
open PrimorialCutoff PrimorialSieveLift ZetaTwoHilbert ZetaTwoProbability
open QDensityMetric QFullResidueProjection
/-- Finite legal approximants obtained by inserting the proposed source into the
normalized density identity. -/
def providerApprox (L K k : ℕ) : QHilbert :=
  (1/zetaTwo) • qResidue k + (1/(zetaTwo*(k : ℝ))) • cutoffLift L K

theorem providerApprox_mem (L K k : ℕ) (hK : 0 < K) (hk : 0 < k) :
    providerApprox L K k ∈ legalSpan :=
  legalSpan.add_mem (legalSpan.smul_mem _ (residue_mem_legalSpan k hk))
    (legalSpan.smul_mem _ (cutoffLift_mem L K hK))

/-- The complete signed error identity, before any norm estimate. -/
theorem provider_error_identity (L K k : ℕ) (hk : 0 < k) :
    (zetaTwo*(k : ℝ)) • (B (qResidue k)-providerApprox L K k) =
      approximation k - cutoffLift L K := by
  have hZ := zetaTwo_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : zetaTwo*(k : ℝ)*(1/zetaTwo) = (k : ℝ) := by
    field_simp
  have h2 : zetaTwo*(k : ℝ)*(1/(zetaTwo*(k : ℝ))) = 1 := by
    field_simp
  rw [providerApprox, smul_sub, smul_add, smul_smul, smul_smul, h1, h2, one_smul,
    approximation_eq_density_combination]
  module

theorem provider_error_norm_identity (L K k : ℕ) (hk : 0 < k) :
    zetaTwo * ((k : ℝ)*‖B (qResidue k)-providerApprox L K k‖) =
      ‖approximation k-cutoffLift L K‖ := by
  have hZ := zetaTwo_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := congrArg norm (provider_error_identity L K k hk)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < zetaTwo*(k : ℝ)), mul_assoc] using h

/-- For this concrete provider family, the required scaled error diverges.
No claim is made about arbitrary finite legal approximants. -/
theorem primorial_provider_scaled_error_tendsto
    (K k : ℕ → ℕ) (hK : ∀ N, 0 < K N) (hk : ∀ N, 0 < k N)
    (hcofinal : Tendsto k atTop atTop) :
    Tendsto (fun N => (k N : ℝ) *
      ‖B (qResidue (k N))-providerApprox (primorial N) (K N) (k N)‖)
      atTop atTop := by
  have hZ := zetaTwo_pos
  have ht := (primorial_cutoff_norms_tendsto K hK).1
  have ha : Tendsto (fun N => ‖approximation (k N)‖) atTop (𝓝 1) := by
    simpa only [Function.comp_def, qOne_norm] using
      (approximation_tendsto.comp hcofinal).norm
  have hb : ∀ᶠ N in atTop, ‖approximation (k N)‖ < 2 :=
    (tendsto_order.mp ha).2 2 (by norm_num)
  apply tendsto_atTop.2
  intro b
  filter_upwards [hb, ht.eventually (eventually_ge_atTop (zetaTwo*b+2))] with N hA hV
  have hn : ‖cutoffLift (primorial N) (K N)‖ ≤
      ‖approximation (k N)-cutoffLift (primorial N) (K N)‖ +
        ‖approximation (k N)‖ := by
    have h := norm_sub_le (approximation (k N))
      (approximation (k N)-cutoffLift (primorial N) (K N))
    simpa only [sub_sub_cancel] using h.trans_eq (add_comm _ _)
  rw [← provider_error_norm_identity _ _ _ (hk N)] at hn
  nlinarith
end RiemannResearch.RH.PrimorialCutoffLeakage
