import RiemannResearch.RH.QRamanujanDPPLaw
import RiemannResearch.Probability.DeterminantalWindowGenerating

/-!
# Complete finite-window laws and signed activity limits in Q

Source: sixth transfer program, 24 October 2026; finite DPP generating
identities as in Kulesza--Taskar, https://arxiv.org/abs/1207.6083. All real
activities, including negative ones, are retained. The exact finite law is
identified, so convergence applies to every configuration, not only occupancy.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open RiemannResearch.Probability.DPP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem window_exactWeight_nonneg (n : ℕ) (e : ι ↪ ℕ) (S : Finset ι) :
    0 ≤ exactWeight (Matrix.of (fun i j => kernel n (e i) (e j))) S :=
  exactWeight_nonneg _ (kernel_principal_posSemidef n e)
    (kernel_complement_posSemidef n e) S

theorem limitWindow_exactWeight_nonneg (e : ι ↪ ℕ) (S : Finset ι) :
    0 ≤ exactWeight (Matrix.of (fun i j => limitKernel (e i) (e j))) S :=
  exactWeight_nonneg _ (limitKernel_principal_posSemidef e)
    (limitKernel_complement_posSemidef e) S

theorem window_restriction (n : ℕ) (e : ι ↪ ℕ) :
    (law n).map (fun x i => x (e i)) =
      (finiteBoolLaw (Matrix.of (fun i j => kernel n (e i) (e j)))
        (window_exactWeight_nonneg n e)).toMeasure := by
  simpa using (law_isDPP n).finite_restriction_law e (window_exactWeight_nonneg n e)

theorem limitWindow_restriction (e : ι ↪ ℕ) :
    limitLaw.map (fun x i => x (e i)) =
      (finiteBoolLaw (Matrix.of (fun i j => limitKernel (e i) (e j)))
        (limitWindow_exactWeight_nonneg e)).toMeasure := by
  simpa using limitLaw_isDPP.finite_restriction_law e (limitWindow_exactWeight_nonneg e)

theorem window_gap (n : ℕ) (e : ι ↪ ℕ) :
    (law n).real {x | ∀ i, x (e i) = false} =
      (1 - Matrix.of (fun i j => kernel n (e i) (e j))).det := by
  simpa using (law_isDPP n).finite_gap e (window_exactWeight_nonneg n e)

theorem limitWindow_gap (e : ι ↪ ℕ) :
    limitLaw.real {x | ∀ i, x (e i) = false} =
      (1 - Matrix.of (fun i j => limitKernel (e i) (e j))).det := by
  simpa using limitLaw_isDPP.finite_gap e (limitWindow_exactWeight_nonneg e)

theorem window_generating (n : ℕ) (e : ι ↪ ℕ) (z : ι → ℝ) :
    (∫ x, ∏ i, if x (e i) = true then z i else 1 ∂law n) =
      (Matrix.diagonal z * Matrix.of (fun i j => kernel n (e i) (e j)) +
        (1 - Matrix.of (fun i j => kernel n (e i) (e j)))).det := by
  convert (law_isDPP n).window_generating e (window_exactWeight_nonneg n e) z using 1
  congr 1
  funext x
  apply Finset.prod_congr rfl
  intro i _
  by_cases hx : x (e i) = true <;> simp [hx]

theorem limitWindow_generating (e : ι ↪ ℕ) (z : ι → ℝ) :
    (∫ x, ∏ i, if x (e i) = true then z i else 1 ∂limitLaw) =
      (Matrix.diagonal z * Matrix.of (fun i j => limitKernel (e i) (e j)) +
        (1 - Matrix.of (fun i j => limitKernel (e i) (e j)))).det := by
  convert limitLaw_isDPP.window_generating e (limitWindow_exactWeight_nonneg e) z using 1
  congr 1
  funext x
  apply Finset.prod_congr rfl
  intro i _
  by_cases hx : x (e i) = true <;> simp [hx]

/-- Every exact finite-window probability converges; no sign restriction on K entries. -/
theorem window_configuration_tendsto (e : ι ↪ ℕ) (S : Finset ι) :
    Tendsto (fun n => (finiteLaw (Matrix.of (fun i j => kernel n (e i) (e j)))
      (window_exactWeight_nonneg n e) S).toReal) atTop
      (𝓝 ((finiteLaw (Matrix.of (fun i j => limitKernel (e i) (e j)))
        (limitWindow_exactWeight_nonneg e) S).toReal)) := by
  simp only [finiteLaw_apply_toReal, exactWeight]
  apply (continuous_id.matrix_det.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hi : i ∈ S
  · simpa [mixedRows, hi] using kernel_tendsto (e i) (e j)
  · simpa [mixedRows, hi, Matrix.sub_apply] using
      (tendsto_const_nhds.sub (kernel_tendsto (e i) (e j)))

/-- Convergence of complete finite generating functions for arbitrary real activities. -/
theorem window_generating_tendsto (e : ι ↪ ℕ) (z : ι → ℝ) :
    Tendsto (fun n => ∫ x, ∏ i, if x (e i) = true then z i else 1 ∂law n)
      atTop (𝓝 (∫ x, ∏ i, if x (e i) = true then z i else 1 ∂limitLaw)) := by
  simp only [window_generating, limitWindow_generating]
  apply (continuous_id.matrix_det.tendsto _).comp
  have hk : Tendsto (fun n => Matrix.of (fun i j => kernel n (e i) (e j))) atTop
      (𝓝 (Matrix.of (fun i j => limitKernel (e i) (e j)))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => kernel_tendsto (e i) (e j)
  exact (tendsto_const_nhds.mul hk).add (tendsto_const_nhds.sub hk)

theorem window_gap_tendsto (e : ι ↪ ℕ) :
    Tendsto (fun n => (law n).real {x | ∀ i, x (e i) = false}) atTop
      (𝓝 (limitLaw.real {x | ∀ i, x (e i) = false})) := by
  simp only [window_gap, limitWindow_gap]
  apply (continuous_id.matrix_det.tendsto _).comp
  exact tendsto_const_nhds.sub
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => kernel_tendsto (e i) (e j))

end RiemannResearch.RH.QRamanujanDPP
