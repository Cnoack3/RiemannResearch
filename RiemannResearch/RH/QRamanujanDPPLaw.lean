import RiemannResearch.RH.QRamanujanDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.Probability.DeterminantalEntry

/-!
# Actual Q Ramanujan determinantal laws

Source: sixth transfer program, 24 October 2026. The existing proved
positive-contraction construction supplies countable laws; terminology follows
Lyons, https://arxiv.org/abs/math/0204325. No RH hypothesis is needed.
-/

noncomputable section
open MeasureTheory Filter
open scoped Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open RiemannResearch.Probability.DPP

def law (n : ℕ) : Measure (ℕ → Bool) :=
  contractionDPP (kernel n)
    (fun I => kernel_principal_posSemidef n (fun i : I => i.1))
    (fun I => by
      let e : I ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
      have h := kernel_complement_posSemidef n e
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, e])

instance law_probability (n : ℕ) : IsProbabilityMeasure (law n) := by
  unfold law
  exact contractionDPP_probability _ _ _

theorem law_isDPP (n : ℕ) : IsDPP (law n) (fun x => {i | x i = true}) (kernel n) :=
  contractionDPP_isDPP _ _ _

def limitLaw : Measure (ℕ → Bool) :=
  contractionDPP limitKernel
    (fun I => limitKernel_principal_posSemidef (fun i : I => i.1))
    (fun I => by
      let e : I ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
      have h := limitKernel_complement_posSemidef e
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, e])

instance limitLaw_probability : IsProbabilityMeasure limitLaw := by
  unfold limitLaw
  exact contractionDPP_probability _ _ _

theorem limitLaw_isDPP : IsDPP limitLaw (fun x => {i | x i = true}) limitKernel :=
  contractionDPP_isDPP _ _ _

theorem occupation (n i : ℕ) : (law n).real {x | x i = true} = kernel n i i :=
  (law_isDPP n).occupation i

theorem vacancy (n i : ℕ) : (law n).real {x | x i = false} = holeKernel n i i := by
  have h := (law_isDPP n).vacancy i
  simpa only [Set.mem_ofPred_eq, Bool.not_eq_true, holeKernel_eq, if_true] using h

theorem limitOccupation (i : ℕ) : limitLaw.real {x | x i = true} = limitKernel i i :=
  limitLaw_isDPP.occupation i

theorem limitVacancy (i : ℕ) : limitLaw.real {x | x i = false} = limitHoleKernel i i := by
  have h := limitLaw_isDPP.vacancy i
  simpa only [Set.mem_ofPred_eq, Bool.not_eq_true, limitHoleKernel_eq, if_true] using h

theorem two_point (n : ℕ) {i j : ℕ} (hij : i ≠ j) :
    (law n).real {x | x i = true ∧ x j = true} =
      kernel n i i * kernel n j j - (kernel n i j) ^ 2 := by
  have h := (law_isDPP n).two_point hij
  simp only [Set.mem_ofPred_eq] at h
  rw [h, ← kernel_symmetric n i j]
  ring

theorem covariance (n : ℕ) {i j : ℕ} (hij : i ≠ j) :
    (law n).real {x | x i = true ∧ x j = true} -
      (law n).real {x | x i = true} * (law n).real {x | x j = true} =
        -(kernel n i j) ^ 2 := by
  rw [two_point n hij, occupation, occupation]
  ring

theorem inclusion_tendsto (m : ℕ) (e : Fin m ↪ ℕ) :
    Tendsto (fun n => (law n).real {x | ∀ i, x (e i) = true}) atTop
      (𝓝 (limitLaw.real {x | ∀ i, x (e i) = true})) := by
  have hn (n : ℕ) : (law n).real {x | ∀ i, x (e i) = true} =
      (Matrix.of (fun i j => kernel n (e i) (e j))).det := by
    simpa only [Set.mem_ofPred_eq] using (law_isDPP n).correlation m e
  have hl : limitLaw.real {x | ∀ i, x (e i) = true} =
      (Matrix.of (fun i j => limitKernel (e i) (e j))).det := by
    simpa only [Set.mem_ofPred_eq] using limitLaw_isDPP.correlation m e
  simp only [hn, hl]
  exact principal_det_tendsto e

theorem vacancy_tendsto (i : ℕ) :
    Tendsto (fun n => (law n).real {x | x i = false}) atTop
      (𝓝 (limitLaw.real {x | x i = false})) := by
  simpa only [vacancy, limitVacancy] using holeKernel_tendsto i i

end RiemannResearch.RH.QRamanujanDPP
