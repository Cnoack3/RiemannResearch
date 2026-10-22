import RiemannResearch.RH.DyadicCarryCRT

/-!
# Möbius interpolation is an exact finite-head projection

Source: user-provided `RH_Dyadic_Block_CRT_Energy_and_Mobius_Obstruction_2026-09-20.md`,
Sections 2, 4, and the natural-diagonal discussion. The finite projection and
head-null correction description are proved for the actual arithmetic legal
span, including the empty head. No limiting energy estimate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

@[simp] theorem mobiusJointHead_zero_function (N : ℕ) :
    mobiusJointHead (0 : ℕ → ℝ) N = 0 := by
  funext n
  simp [mobiusJointHead, mobiusDifference]

theorem mobiusJointHead_sub_function (f g : ℕ → ℝ) (N : ℕ) :
    mobiusJointHead (f - g) N = mobiusJointHead f N - mobiusJointHead g N := by
  change mobiusJointHead (fun n => f n - g n) N = _
  funext n
  simp only [mobiusJointHead, Pi.sub_apply, mobiusDifference_sub_function,
    sub_div, sub_mul, Finset.sum_sub_distrib]

theorem mobiusJointHead_add_function (f g : ℕ → ℝ) (N : ℕ) :
    mobiusJointHead (f + g) N = mobiusJointHead f N + mobiusJointHead g N := by
  have he : (f + g) - g = f := by abel
  have hh := mobiusJointHead_sub_function (f + g) g N
  rw [he] at hh
  exact sub_eq_iff_eq_add.mp hh.symm

theorem mobiusJointHead_smul_function (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    mobiusJointHead (c • f) N = c • mobiusJointHead f N := by
  have hd (m : ℕ) : mobiusDifference m (c • f) = c * mobiusDifference m f := by
    unfold mobiusDifference
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  funext n
  simp only [mobiusJointHead, Pi.smul_apply, smul_eq_mul, hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Interpolation coefficients depend only on the anchored prescribed head. -/
theorem mobiusJointHead_congr_head {f g : ℕ → ℝ} (N : ℕ)
    (hhead : ∀ n, n ≤ N → f n = g n) :
    mobiusJointHead f N = mobiusJointHead g N := by
  funext n
  unfold mobiusJointHead
  apply Finset.sum_congr rfl
  intro m hm
  rw [mobiusDifference_congr_initial (Finset.mem_Icc.mp hm).2 hhead]

/-- A residue with no period boundary in the prescribed head is repaired
by the terminal residue. This also holds for the empty head `N = 0`. -/
theorem mobiusJointHead_residue_larger (N d : ℕ) (hd : N + 1 ≤ d) :
    mobiusJointHead (residue d) N = residue (N + 1) := by
  cases N with
  | zero => funext n; simp [mobiusJointHead, residue, Nat.mod_one]
  | succ N =>
    funext n
    unfold mobiusJointHead
    rw [Finset.sum_eq_single 1]
    · rw [mobiusDifference_residue_initial 1 d (by omega)]
      simp [show (1 : ℕ) ≠ d by omega, residue, Nat.mod_one]
    · intro m hm hm1
      rw [mobiusDifference_residue_initial m d (Finset.mem_Icc.mp hm).1]
      have hmd : m ≠ d := by have := (Finset.mem_Icc.mp hm).2; omega
      simp [hm1, hmd]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)).elim

/-- The finite triangular residue differences are fixed by the interpolant. -/
theorem mobiusJointHead_residue_difference (N d : ℕ)
    (hd : 0 < d) (hdN : d ≤ N) :
    mobiusJointHead (residue (N + 1) - residue d) N =
      residue (N + 1) - residue d := by
  funext n
  unfold mobiusJointHead
  have ht (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
      mobiusDifference m (residue (N + 1) - residue d) =
        if m = d then (d : ℝ) else 0 := by
    change mobiusDifference m (fun n => residue (N + 1) n - residue d n) = _
    rw [mobiusDifference_sub_function,
      mobiusDifference_residue_initial m (N + 1) (Finset.mem_Icc.mp hm).1,
      mobiusDifference_residue_initial m d (Finset.mem_Icc.mp hm).1]
    have hne : m ≠ N + 1 := by have := (Finset.mem_Icc.mp hm).2; omega
    simp [hne]
  rw [Finset.sum_eq_single d]
  · rw [ht d (Finset.mem_Icc.mpr ⟨hd, hdN⟩)]
    simp [show (d : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hd]
  · intro m hm hmd
    rw [ht m hm]
    simp [hmd]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hd, hdN⟩)).elim

theorem mobiusJointHead_residue_fixed (N d : ℕ)
    (hd : 0 < d) (hdN : d ≤ N + 1) :
    mobiusJointHead (residue d) N = residue d := by
  by_cases he : d = N + 1
  · subst d
    exact mobiusJointHead_residue_larger N (N + 1) le_rfl
  · have hdiff := mobiusJointHead_sub_function (residue (N + 1)) (residue d) N
    rw [mobiusJointHead_residue_difference N d hd (by omega),
      mobiusJointHead_residue_larger N (N + 1) le_rfl] at hdiff
    funext n
    have hh := congrFun hdiff n
    simp only [Pi.sub_apply] at hh
    linarith

/-- The explicit formula reproduces every vector in the finite dictionary. -/
theorem mobiusJointHead_reproduces {N : ℕ} {f : ℕ → ℝ}
    (hf : f ∈ finiteResidueSubspace (N + 1)) : mobiusJointHead f N = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d, hd, hdN, rfl⟩ := hf
    exact mobiusJointHead_residue_fixed N d (by omega) hdN
  | zero => exact mobiusJointHead_zero_function N
  | add f g hf hg ihf ihg => rw [mobiusJointHead_add_function, ihf, ihg]
  | smul c f hf ih => rw [mobiusJointHead_smul_function, ih]

/-- No additional finite dictionary vector can have the same entire head. -/
theorem finiteResidueSubspace_eq_of_head {N : ℕ} {f g : ℕ → ℝ}
    (hf : f ∈ finiteResidueSubspace (N + 1))
    (hg : g ∈ finiteResidueSubspace (N + 1))
    (hhead : ∀ n, n ≤ N → f n = g n) : f = g := by
  rw [← mobiusJointHead_reproduces hf, ← mobiusJointHead_reproduces hg]
  exact mobiusJointHead_congr_head N hhead

/-- The algebraic space of all finite corrections preserving the head. -/
def headNullResidueSpan (N : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ m : ℕ, N + 1 < m ∧
    f = residue m - residue (N + 1)}

theorem residue_sub_mobiusJointHead_mem (N d : ℕ) (hd : 0 < d) :
    residue d - mobiusJointHead (residue d) N ∈ headNullResidueSpan N := by
  by_cases hdn : d ≤ N + 1
  · rw [mobiusJointHead_residue_fixed N d hd hdn, sub_self]
    exact (headNullResidueSpan N).zero_mem
  · rw [mobiusJointHead_residue_larger N d (by omega)]
    exact Submodule.subset_span ⟨d, by omega, rfl⟩

/-- Subtracting the explicit interpolant removes precisely the finite head
part of every finite legal vector. -/
theorem legal_sub_mobiusJointHead_mem {N : ℕ} {f : ℕ → ℝ}
    (hf : f ∈ legalSeedSpan (Set.Ici 1)) :
    f - mobiusJointHead f N ∈ headNullResidueSpan N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, m, hm, rfl⟩ := hf
    have ha0 : 0 < a := by change 1 ≤ a at ha; omega
    have he : dilation m (residue a) = residue (m * a) - residue m := by
      funext n
      exact residue_mul_floor m a n
    rw [he, mobiusJointHead_sub_function]
    have hh := (headNullResidueSpan N).sub_mem
      (residue_sub_mobiusJointHead_mem N (m * a) (Nat.mul_pos hm ha0))
      (residue_sub_mobiusJointHead_mem N m hm)
    convert hh using 1 <;> abel
  | zero => simp
  | add f g hf hg ihf ihg =>
    rw [mobiusJointHead_add_function]
    convert (headNullResidueSpan N).add_mem ihf ihg using 1 <;> abel
  | smul c f hf ih =>
    rw [mobiusJointHead_smul_function, ← smul_sub]
    exact (headNullResidueSpan N).smul_mem c ih

/-- Every and only finite legal head-zero vector is a finite combination of
the explicit high-modulus differences. -/
theorem headNullResidueSpan_iff (N : ℕ) (f : ℕ → ℝ) :
    f ∈ headNullResidueSpan N ↔
      f ∈ legalSeedSpan (Set.Ici 1) ∧ ∀ n, n ≤ N → f n = 0 := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨m, hm, rfl⟩ := hf
      refine ⟨(legalSeedSpan (Set.Ici 1)).sub_mem
        (finiteResidueSubspace_le_full_legal m
          (residue_mem_finiteResidueSubspace (by omega) le_rfl))
        (finiteResidueSubspace_le_full_legal (N + 1)
          (residue_mem_finiteResidueSubspace (by omega) le_rfl)), ?_⟩
      intro n hn
      simp [residue, Nat.mod_eq_of_lt (show n < m by omega),
        Nat.mod_eq_of_lt (show n < N + 1 by omega)]
    | zero => exact ⟨(legalSeedSpan _).zero_mem, by simp⟩
    | add f g hf hg ihf ihg =>
      exact ⟨(legalSeedSpan _).add_mem ihf.1 ihg.1,
        by intro n hn; simp [ihf.2 n hn, ihg.2 n hn]⟩
    | smul c f hf ih =>
      exact ⟨(legalSeedSpan _).smul_mem c ih.1,
        by intro n hn; simp [ih.2 n hn]⟩
  · rintro ⟨hf, hhead⟩
    have hj : mobiusJointHead f N = 0 := by
      rw [mobiusJointHead_congr_head N (g := 0) hhead,
        mobiusJointHead_zero_function]
    have hh := legal_sub_mobiusJointHead_mem (N := N) hf
    simpa only [hj, sub_zero] using hh

/-- At the natural diagonal the joint block repair is exactly the terminal
residue minus the anchored constant's corrected Möbius approximant. -/
theorem dyadicCarryJointHead_diagonal (k : ℕ) :
    mobiusJointHead (dyadicCarryBlockSequence k) (2 ^ k) =
      residue (2 ^ k + 1) - mobiusJointHead (hilbertSequence hilbertOne) (2 ^ k) := by
  have hhead : ∀ n, n ≤ 2 ^ k → dyadicCarryBlockSequence k n =
      (residue (2 ^ k + 1) - hilbertSequence hilbertOne) n := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [dyadicCarryBlockSequence, residue, hilbertOne_sequence, zeroAnchor]
    · have hnd : ¬ 2 ^ k + 1 ∣ n := by
        intro hd
        have hz := Nat.mod_eq_zero_of_dvd hd
        rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ k + 1)] at hz
        exact hn0 hz
      simp [dyadicCarryBlockSequence, hilbertOne_sequence, zeroAnchor, hn0, hnd]
  rw [mobiusJointHead_congr_head (2 ^ k) hhead, mobiusJointHead_sub_function,
    mobiusJointHead_residue_larger (2 ^ k) (2 ^ k + 1) le_rfl]

theorem dyadicCarryJointError_diagonal (k n : ℕ) :
    dyadicCarryJointError k (2 ^ k) n =
      mobiusJointHead (hilbertSequence hilbertOne) (2 ^ k) n -
        (if 2 ^ k + 1 ∣ n then 0 else 1) := by
  simp only [dyadicCarryJointError, dyadicCarryJointHead_diagonal,
    dyadicCarryBlockSequence, Pi.sub_apply]
  ring

end RiemannResearch.RH.Pareto
