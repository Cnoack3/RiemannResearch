import RiemannResearch.LinearAlgebra.FiniteHilbertSchur

/-!
# Nested conditional projections and the exact Schur covariance

Source: user-provided argument,
`RH_Controlled_Conductor_Schur_2026-09-10.md`, Sections 2--4 and 5.5.
The smaller subspace is the old legal space; the larger subspace is the
complete coarse measurable space. All orthogonality below is proved from
actual orthogonal projections. The formulas retain full Gram entries.
This module supplies no arithmetic lower bound on the resulting gain.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.ConditionalSchur

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The residualized conditional mean of a new packet. -/
def meanPart (V K : Submodule ℝ H) [V.HasOrthogonalProjection]
    [K.HasOrthogonalProjection] (z : H) : H :=
  K.starProjection z - V.starProjection (K.starProjection z)

/-- The genuine fluctuation within the coarse fibers. -/
def fluctuation (K : Submodule ℝ H) [K.HasOrthogonalProjection] (z : H) : H :=
  z - K.starProjection z

/-- Residualization against the old legal space. -/
def packetResidual (V : Submodule ℝ H) [V.HasOrthogonalProjection] (z : H) : H :=
  z - V.starProjection z

variable (V K : Submodule ℝ H) [V.HasOrthogonalProjection] [K.HasOrthogonalProjection]

theorem fluctuation_mem_orthogonal (z : H) : fluctuation K z ∈ Kᗮ :=
  Submodule.sub_starProjection_mem_orthogonal z

theorem inner_mem_fluctuation {x : H} (hx : x ∈ K) (z : H) :
    inner ℝ x (fluctuation K z) = 0 :=
  (K.mem_orthogonal _).mp (fluctuation_mem_orthogonal K z) x hx

theorem smaller_projection_fluctuation (hVK : V ≤ K) (z : H) :
    V.starProjection (fluctuation K z) = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff V).2
  apply (V.mem_orthogonal _).2
  intro x hx
  exact inner_mem_fluctuation K (hVK hx) z

theorem nested_projection (hVK : V ≤ K) (z : H) :
    V.starProjection (K.starProjection z) = V.starProjection z := by
  have h := smaller_projection_fluctuation V K hVK z
  have hh : V.starProjection z = V.starProjection (K.starProjection z) := by
    simpa only [fluctuation, map_sub, sub_eq_zero] using h
  exact hh.symm

theorem packetResidual_split (hVK : V ≤ K) (z : H) :
    packetResidual V z = meanPart V K z + fluctuation K z := by
  unfold packetResidual meanPart fluctuation
  rw [nested_projection V K hVK]
  abel

theorem meanPart_mem (hVK : V ≤ K) (z : H) : meanPart V K z ∈ K :=
  K.sub_mem (K.starProjection_apply_mem z)
    (hVK (V.starProjection_apply_mem (K.starProjection z)))

theorem meanPart_mem_orthogonal (z : H) : meanPart V K z ∈ Vᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (K.starProjection z)

theorem meanPart_fluctuation_orthogonal (hVK : V ≤ K) (x y : H) :
    inner ℝ (meanPart V K x) (fluctuation K y) = 0 :=
  inner_mem_fluctuation K (meanPart_mem V K hVK x) y

/-- Entrywise identity `S = A* A + U* U`, including every mixed entry. -/
theorem gram_split (hVK : V ≤ K) (x y : H) :
    inner ℝ (packetResidual V x) (packetResidual V y) =
      inner ℝ (meanPart V K x) (meanPart V K y) +
        inner ℝ (fluctuation K x) (fluctuation K y) := by
  rw [packetResidual_split V K hVK x, packetResidual_split V K hVK y]
  have hxy := meanPart_fluctuation_orthogonal V K hVK x y
  have hyx := meanPart_fluctuation_orthogonal V K hVK y x
  rw [real_inner_comm] at hyx
  simp only [inner_add_left, inner_add_right, hxy, hyx, add_zero, zero_add]

/-- Only the conditional mean pairs with the old coarse residual. -/
theorem score_eq_mean_score (hVK : V ≤ K) {e : H} (he : e ∈ K) (z : H) :
    inner ℝ (packetResidual V z) e = inner ℝ (meanPart V K z) e := by
  rw [packetResidual_split V K hVK, inner_add_left]
  have h := inner_mem_fluctuation K he z
  rw [real_inner_comm] at h
  rw [h, add_zero]

/-- Exact legal update: the within-fiber variance is an introduced cost. -/
theorem residual_objective (hVK : V ≤ K) {e : H} (he : e ∈ K) (z : H) :
    ‖e - packetResidual V z‖ ^ 2 =
      ‖e - meanPart V K z‖ ^ 2 + ‖fluctuation K z‖ ^ 2 := by
  rw [packetResidual_split V K hVK]
  rw [show e - (meanPart V K z + fluctuation K z) =
    (e - meanPart V K z) - fluctuation K z by abel]
  rw [norm_sub_sq_real,
    inner_mem_fluctuation K (K.sub_mem he (meanPart_mem V K hVK z)) z]
  ring

theorem residual_objective_expanded (hVK : V ≤ K) {e : H} (he : e ∈ K) (z : H) :
    ‖e - packetResidual V z‖ ^ 2 = ‖e‖ ^ 2 -
      2 * inner ℝ (meanPart V K z) e + ‖meanPart V K z‖ ^ 2 +
      ‖fluctuation K z‖ ^ 2 := by
  rw [residual_objective V K hVK he z, norm_sub_sq_real,
    real_inner_comm e (meanPart V K z)]

/-- Three surviving components: invisible residual, visible fitting error,
and the exact innovation covariance. The visibility space is an actual
orthogonally complemented subspace containing the mean correction. -/
theorem residual_three_piece (hVK : V ≤ K) {e : H} (he : e ∈ K) (z : H)
    (A : Submodule ℝ H) [A.HasOrthogonalProjection]
    (hz : meanPart V K z ∈ A) :
    ‖e - packetResidual V z‖ ^ 2 =
      ‖e - A.starProjection e‖ ^ 2 +
        ‖A.starProjection e - meanPart V K z‖ ^ 2 + ‖fluctuation K z‖ ^ 2 := by
  rw [residual_objective V K hVK he]
  have horth : inner ℝ (e - A.starProjection e)
      (A.starProjection e - meanPart V K z) = 0 := by
    rw [real_inner_comm]
    exact (A.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal e) _
      (A.sub_mem (A.starProjection_apply_mem e) hz)
  have hid : e - meanPart V K z = (e - A.starProjection e) -
      -(A.starProjection e - meanPart V K z) := by abel
  rw [hid, norm_sub_sq_real, inner_neg_right, horth, norm_neg]
  ring

omit [K.HasOrthogonalProjection] in
/-- The target's old residual is coarse whenever the target is coarse. -/
theorem target_residual_mem (hVK : V ≤ K) {f : H} (hf : f ∈ K) :
    packetResidual V f ∈ K :=
  K.sub_mem hf (hVK (V.starProjection_apply_mem f))

/-- Pythagoras for the actual change between nested optimal projections. -/
theorem nested_projection_energy (hVK : V ≤ K) (f : H) :
    ‖packetResidual V f‖ ^ 2 =
      ‖K.starProjection f - V.starProjection f‖ ^ 2 +
        ‖packetResidual K f‖ ^ 2 := by
  have horth : inner ℝ (K.starProjection f - V.starProjection f)
      (packetResidual K f) = 0 := by
    exact (K.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal f) _
      (K.sub_mem (K.starProjection_apply_mem f) (hVK (V.starProjection_apply_mem f)))
  have hid : packetResidual V f = (K.starProjection f - V.starProjection f) -
      -(packetResidual K f) := by unfold packetResidual; abel
  rw [hid, norm_sub_sq_real, inner_neg_right, horth, norm_neg]
  ring

section FinitePackets

variable {ι : Type*} [Fintype ι]

theorem meanPart_combination (z : ι → H) (b : ι → ℝ) :
    meanPart V K (finiteSchurCombination z b) =
      finiteSchurCombination (meanPart V K ∘ z) b := by
  simp [meanPart, finiteSchurCombination,
    map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

theorem fluctuation_combination (z : ι → H) (b : ι → ℝ) :
    fluctuation K (finiteSchurCombination z b) =
      finiteSchurCombination (fluctuation K ∘ z) b := by
  simp [fluctuation, finiteSchurCombination,
    map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

theorem packetResidual_combination (z : ι → H) (b : ι → ℝ) :
    packetResidual V (finiteSchurCombination z b) =
      finiteSchurCombination (packetResidual V ∘ z) b := by
  simp [packetResidual, finiteSchurCombination,
    map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

/-- Exact covariance as a full double sum, with no diagonal replacement. -/
theorem fluctuation_quadratic (z : ι → H) (b : ι → ℝ) :
    ‖fluctuation K (finiteSchurCombination z b)‖ ^ 2 =
      ∑ i, ∑ j, b i * b j * inner ℝ (fluctuation K (z i)) (fluctuation K (z j)) := by
  rw [fluctuation_combination K, ← real_inner_self_eq_norm_sq]
  simp only [finiteSchurCombination, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (fluctuation K (z j)) (fluctuation K (z i))]
  ring

theorem finite_residual_objective (hVK : V ≤ K) {e : H} (he : e ∈ K)
    (z : ι → H) (b : ι → ℝ) :
    ‖e - finiteSchurCombination (packetResidual V ∘ z) b‖ ^ 2 =
      ‖e - finiteSchurCombination (meanPart V K ∘ z) b‖ ^ 2 +
        ∑ i, ∑ j, b i * b j *
          inner ℝ (fluctuation K (z i)) (fluctuation K (z j)) := by
  rw [← packetResidual_combination V,
    residual_objective V K hVK he, meanPart_combination V K,
    fluctuation_quadratic K]

/-- Solving the residualized finite normal equations gives the actual
projection residual on the enlarged legal space, not merely a trial error.
The packet family may be redundant. -/
theorem augmented_projection_residual (z : ι → H)
    [(V ⊔ Submodule.span ℝ (Set.range z)).HasOrthogonalProjection]
    (f : H) (b : ι → ℝ)
    (hb : ∀ i, inner ℝ (packetResidual V (z i))
      (finiteSchurCombination (packetResidual V ∘ z) b) =
        inner ℝ (packetResidual V (z i)) (packetResidual V f)) :
    finiteSchurResidual (packetResidual V f) (packetResidual V ∘ z) b =
      packetResidual (V ⊔ Submodule.span ℝ (Set.range z)) f := by
  classical
  let U : Submodule ℝ H := V ⊔ Submodule.span ℝ (Set.range z)
  let e := packetResidual V f
  let t := packetResidual V ∘ z
  let r := finiteSchurResidual e t b
  have he : e ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal f
  have ht (i : ι) : t i ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (z i)
  have htb : finiteSchurCombination t b ∈ Vᗮ := by
    exact (Vᗮ).sum_mem (fun i _ => (Vᗮ).smul_mem (b i) (ht i))
  have hrV : r ∈ Vᗮ := (Vᗮ).sub_mem he htb
  have hzi (i : ι) : inner ℝ (z i) r = 0 := by
    have hn : inner ℝ (z i - V.starProjection (z i)) r = 0 :=
      finiteSchurResidual_orthogonal e t b hb i
    have hp := (V.mem_orthogonal r).mp hrV _ (V.starProjection_apply_mem (z i))
    rw [inner_sub_left] at hn
    linarith
  have hrZ : r ∈ (Submodule.span ℝ (Set.range z))ᗮ := by
    apply ((Submodule.span ℝ (Set.range z)).mem_orthogonal r).2
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact hzi i
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
    | smul c x hx ih => simp only [real_inner_smul_left, ih, mul_zero]
  have hrU : r ∈ Uᗮ := by
    apply (U.mem_orthogonal r).2
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    rw [inner_add_left, (V.mem_orthogonal r).mp hrV x hx,
      ((Submodule.span ℝ (Set.range z)).mem_orthogonal r).mp hrZ y hy, add_zero]
  have hcomb : finiteSchurCombination z b ∈ Submodule.span ℝ (Set.range z) := by
    exact (Submodule.span ℝ (Set.range z)).sum_mem (fun i _ =>
      (Submodule.span ℝ (Set.range z)).smul_mem (b i) (Submodule.subset_span ⟨i, rfl⟩))
  have hid : f - r = V.starProjection f + finiteSchurCombination z b -
      V.starProjection (finiteSchurCombination z b) := by
    change f - (packetResidual V f -
      finiteSchurCombination (packetResidual V ∘ z) b) = _
    rw [← packetResidual_combination V z b]
    unfold packetResidual
    abel
  have hVU : V ≤ U := le_sup_left
  have hZU : Submodule.span ℝ (Set.range z) ≤ U := le_sup_right
  have hremoved : f - r ∈ U := by
    rw [hid]
    exact U.sub_mem (U.add_mem (hVU (V.starProjection_apply_mem f)) (hZU hcomb))
      (hVU (V.starProjection_apply_mem (finiteSchurCombination z b)))
  have hpzero : U.starProjection r = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2 hrU
  have hpfix : U.starProjection (f - r) = f - r :=
    Submodule.starProjection_eq_self_iff.mpr hremoved
  rw [map_sub, hpzero, sub_zero] at hpfix
  change r = f - U.starProjection f
  rw [hpfix]
  abel

end FinitePackets

end RiemannResearch.LinearAlgebra.ConditionalSchur
