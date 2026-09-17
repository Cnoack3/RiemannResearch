import RiemannResearch.RH.ConditionalMeanTailNonattainment

/-!
# Surjectivity of the actual finite residue and conditional-mean heads

Source: `ArithmeticVariationalProof.md`, Section 4, an ordinary proof of
the finite-rank assertion in the user-provided conditional-iid completion,
Section 11. The construction stays inside residues with moduli at most
`N + 1`. It does not assume the desired rank or a bounded interpolation
operator; no bound uniform in `N` is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID

/-- The actual finite arithmetic dictionary through modulus `D`. -/
def finiteResidueSubspace (D : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ d : ℕ, 2 ≤ d ∧ d ≤ D ∧ f = residue d}

theorem finiteResidueSubspace_mono {D E : ℕ} (hDE : D ≤ E) :
    finiteResidueSubspace D ≤ finiteResidueSubspace E := by
  apply Submodule.span_mono
  rintro f ⟨d, hd, hdD, rfl⟩
  exact ⟨d, hd, hdD.trans hDE, rfl⟩

theorem residue_mem_finiteResidueSubspace {d D : ℕ} (hd : 0 < d) (hdD : d ≤ D) :
    residue d ∈ finiteResidueSubspace D := by
  by_cases hd1 : d = 1
  · subst d
    have hz : residue 1 = (0 : ℕ → ℝ) := by funext n; simp [residue, Nat.mod_one]
    rw [hz]
    exact (finiteResidueSubspace D).zero_mem
  · exact Submodule.subset_span ⟨d, by omega, hdD, rfl⟩

theorem finiteResidueSubspace_le_full_legal (D : ℕ) :
    finiteResidueSubspace D ≤ legalSeedSpan (Set.Ici 1) := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, _, rfl⟩
  change residue d ∈ legalSeedSpan (Set.Ici 1)
  simpa only [dilation_one] using
    (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1)
      (show d ∈ Set.Ici 1 from by change 1 ≤ d; omega) (by omega))

/-- Exact interpolation with the concrete support bound `2 ≤ d ≤ N+1`. -/
theorem exists_finite_residue_head (u : ℕ → ℝ) (N : ℕ) :
    ∃ f ∈ finiteResidueSubspace (N + 1), ∀ n, 0 < n → n ≤ N → f n = u n := by
  induction N with
  | zero => exact ⟨0, (finiteResidueSubspace _).zero_mem, by intro n hn hnN; omega⟩
  | succ N ih =>
    obtain ⟨g, hg, hhead⟩ := ih
    have hg' : g ∈ finiteResidueSubspace (N + 2) :=
      finiteResidueSubspace_mono (by omega) hg
    let v : ℕ → ℝ := residue (N + 2) - residue (N + 1)
    have hv : v ∈ finiteResidueSubspace (N + 2) :=
      (finiteResidueSubspace _).sub_mem
        (residue_mem_finiteResidueSubspace (by omega) le_rfl)
        (residue_mem_finiteResidueSubspace (by omega) (by omega))
    have hvlow (n : ℕ) (hn : n ≤ N) : v n = 0 := by
      simp [v, residue, Nat.mod_eq_of_lt (show n < N + 2 by omega),
        Nat.mod_eq_of_lt (show n < N + 1 by omega)]
    have hvdiag : v (N + 1) = ((N + 1 : ℕ) : ℝ) := by
      simp [v, residue, Nat.mod_eq_of_lt (show N + 1 < N + 2 by omega)]
    let c : ℝ := (u (N + 1) - g (N + 1)) / ((N + 1 : ℕ) : ℝ)
    refine ⟨g + c • v, (finiteResidueSubspace _).add_mem hg'
      ((finiteResidueSubspace _).smul_mem c hv), ?_⟩
    intro n hn hnN
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases he : n = N + 1
    · subst n
      rw [hvdiag]
      dsimp [c]
      have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · rw [hvlow n (by omega), mul_zero, add_zero]
      exact hhead n hn (by omega)

/-- A finite desired mean head is recovered by exact arithmetic differencing. -/
theorem cesaro_eq_of_differenced_head (u f : ℕ → ℝ) (N : ℕ)
    (hf : ∀ n, 0 < n → n ≤ N →
      f n = (n : ℝ) * u n - ((n - 1 : ℕ) : ℝ) * u (n - 1)) :
    ∀ t, 0 < t → t ≤ N → cesaro f t = u t := by
  have hmul : ∀ t, t ≤ N → (t : ℝ) * cesaro f t = (t : ℝ) * u t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hrec := cesaro_recover f t
      rw [hf (t + 1) (Nat.succ_pos _) ht] at hrec
      simp only [Nat.add_sub_cancel] at hrec
      linarith
  intro t ht htN
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  exact (mul_left_cancel₀ ht0) (hmul t htN)

/-- The original finite dictionary interpolates arbitrary conditional-mean heads. -/
theorem exists_finite_residue_cesaro_head (u : ℕ → ℝ) (N D : ℕ) (hND : N + 1 ≤ D) :
    ∃ f ∈ finiteResidueSubspace D, ∀ t, 0 < t → t ≤ N → cesaro f t = u t := by
  obtain ⟨f, hf, hhead⟩ := exists_finite_residue_head
    (fun n => (n : ℝ) * u n - ((n - 1 : ℕ) : ℝ) * u (n - 1)) N
  exact ⟨f, finiteResidueSubspace_mono hND hf, cesaro_eq_of_differenced_head u f N hhead⟩

/-- Full row rank, stated as surjectivity of the actual finite arithmetic
conditional-mean head map. -/
theorem finiteResidue_cesaro_head_surjective (N D : ℕ) (hND : N + 1 ≤ D) :
    Function.Surjective
      (fun f : finiteResidueSubspace D => fun i : Fin N => cesaro f.1 (i.1 + 1)) := by
  intro b
  let u : ℕ → ℝ := fun n => if hn : n - 1 < N then b ⟨n - 1, hn⟩ else 0
  obtain ⟨f, hf, hhead⟩ := exists_finite_residue_cesaro_head u N D hND
  refine ⟨⟨f, hf⟩, ?_⟩
  funext i
  change cesaro f (i.1 + 1) = b i
  rw [hhead (i.1 + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt i.2)]
  simp [u, i.2]

end RiemannResearch.RH.Pareto
