import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair

/-!
# Exact sharp squared amplification of a projected scalar-row transfer

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 7, formula (34). The sharp constant is characterized intrinsically
by its inequality for every scalar and every vector in the permitted tail
subspace. This is the squared operator norm for the Hilbert direct-sum norm.
-/

namespace RiemannResearch.LinearAlgebra
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem schurRemove_eq_self (x d : H) (hx : inner ℝ x d = 0) :
    schurRemove d x = x := by simp [schurRemove, hx]

theorem schurRemove_add (d x y : H) :
    schurRemove d (x + y) = schurRemove d x + schurRemove d y := by
  simp only [schurRemove, inner_add_left, add_div, add_smul]
  abel

theorem schurRemove_smul (d x : H) (a : ℝ) :
    schurRemove d (a • x) = a • schurRemove d x := by
  simp only [schurRemove, inner_smul_left, RCLike.conj_to_real,
    smul_sub, smul_smul, mul_div_assoc]

theorem schurRemove_sub (d x y : H) :
    schurRemove d (x - y) = schurRemove d x - schurRemove d y := by
  rw [sub_eq_add_neg, schurRemove_add]
  have he := schurRemove_smul d y (-1)
  simpa only [neg_one_smul, sub_eq_add_neg] using
    congrArg (fun z => schurRemove d x + z) he

theorem schurRepair_error (F u d e : H) (δ : ℝ) (hed : inner ℝ e d = 0) :
    schurRepair F u d δ - e = schurRemove d ((F - e) + δ • u) := by
  unfold schurRepair
  calc
    _ = schurRemove d (((F - e) + δ • u) + e) - e := by congr 2 <;> abel
    _ = (schurRemove d ((F - e) + δ • u) + e) - e := by
      rw [schurRemove_add, schurRemove_eq_self e d hed]
    _ = _ := by abel

theorem schurRemove_norm_sq_le (x d : H) (hd : d ≠ 0) :
    ‖schurRemove d x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [schurRemove_norm_sq x d hd]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The row bound is an immediate consequence of an exact two-square
completion and Cauchy–Schwarz; it does not assume independent coordinates. -/
theorem scalar_row_energy_le (a : ℝ) (z b : H) :
    ‖z - a • b‖ ^ 2 ≤ (1 + ‖b‖ ^ 2) * (a ^ 2 + ‖z‖ ^ 2) := by
  have he := norm_add_smul_sq_exact z b (-a)
  have hs : (inner ℝ z b) ^ 2 ≤ ‖z‖ ^ 2 * ‖b‖ ^ 2 := by
    simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le z b
  have hn := sq_nonneg (a + inner ℝ z b)
  have hz : z + (-a) • b = z - a • b := by simp [neg_smul, sub_eq_add_neg]
  rw [hz] at he
  nlinarith

def SchurTransferEnergyBoundOn (V : Submodule ℝ H) (β d : H) (C : ℝ) : Prop :=
  ∀ (a : ℝ) (y : H), y ∈ V →
    ‖schurRemove d y - a • schurRemove d β‖ ^ 2 ≤ C * (a ^ 2 + ‖y‖ ^ 2)

theorem schurTransfer_sharp_bound (V : Submodule ℝ H) (β d : H) (hd : d ≠ 0) :
    SchurTransferEnergyBoundOn V β d (1 + ‖schurRemove d β‖ ^ 2) := by
  intro a y _hy
  calc
    _ ≤ (1 + ‖schurRemove d β‖ ^ 2) * (a ^ 2 + ‖schurRemove d y‖ ^ 2) :=
      scalar_row_energy_le a _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (schurRemove_norm_sq_le y d hd))
      (by positivity)

/-- Exact minimality of the proposed squared operator norm. The explicit
orthogonal witness handles the degenerate case where the projected β is zero. -/
theorem schurTransfer_sharp_iff (V : Submodule ℝ H) (β d : H) (C : ℝ)
    (hd : d ≠ 0) (hβV : β ∈ V) (hdV : d ∈ V)
    (hw : ∃ w : H, w ∈ V ∧ w ≠ 0 ∧ inner ℝ w d = 0) :
    SchurTransferEnergyBoundOn V β d C ↔ 1 + ‖schurRemove d β‖ ^ 2 ≤ C := by
  constructor
  · intro hC
    let b := schurRemove d β
    have hbV : b ∈ V := V.sub_mem hβV (V.smul_mem _ hdV)
    have hborth : inner ℝ b d = 0 := schurRemove_inner β d hd
    have hp : schurRemove d b = b := schurRemove_eq_self b d hborth
    by_cases hb : b = 0
    · obtain ⟨w, hwV, hw0, hwd⟩ := hw
      have ht := hC 0 w hwV
      rw [schurRemove_eq_self w d hwd] at ht
      simp only [zero_smul, sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at ht
      have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
      have h1 : 1 ≤ C := le_of_mul_le_mul_right (by simpa using ht) hn
      change 1 + ‖b‖ ^ 2 ≤ C
      simpa [hb] using h1
    · have hB : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
      have ht := hC (-‖b‖ ^ 2) b hbV
      change ‖schurRemove d b - (-‖b‖ ^ 2) • b‖ ^ 2 ≤
        C * ((-‖b‖ ^ 2) ^ 2 + ‖b‖ ^ 2) at ht
      rw [hp] at ht
      have he : b - (-‖b‖ ^ 2) • b = (1 + ‖b‖ ^ 2) • b := by
        calc
          _ = (1 : ℝ) • b + ‖b‖ ^ 2 • b := by simp [sub_eq_add_neg]
          _ = _ := (add_smul _ _ _).symm
      rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at ht
      have hfac : 0 < ‖b‖ ^ 2 * (1 + ‖b‖ ^ 2) := mul_pos hB (by positivity)
      have ht' : (1 + ‖b‖ ^ 2) * (‖b‖ ^ 2 * (1 + ‖b‖ ^ 2)) ≤
          C * (‖b‖ ^ 2 * (1 + ‖b‖ ^ 2)) := by nlinarith [ht]
      exact le_of_mul_le_mul_right ht' hfac
  · intro hC
    intro a y hy
    exact (schurTransfer_sharp_bound V β d hd a y hy).trans
      (mul_le_mul_of_nonneg_right hC (add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- A two-dimensional permitted subspace always supplies the nonzero
orthogonal witness used in the sharpness theorem. -/
theorem exists_nonzero_orthogonal_in_submodule (V : Submodule ℝ H) (v w d : H)
    (hvV : v ∈ V) (hwV : w ∈ V) (hv : ‖v‖ ^ 2 = 1) (hw : ‖w‖ ^ 2 = 1)
    (hvw : inner ℝ v w = 0) : ∃ x : H, x ∈ V ∧ x ≠ 0 ∧ inner ℝ x d = 0 := by
  by_cases hvd : inner ℝ v d = 0
  · refine ⟨v, hvV, ?_, hvd⟩
    intro h
    simp [h] at hv
  · let x := (inner ℝ w d) • v - (inner ℝ v d) • w
    refine ⟨x, V.sub_mem (V.smul_mem _ hvV) (V.smul_mem _ hwV), ?_, ?_⟩
    · intro hx
      have hi : inner ℝ x w = -(inner ℝ v d) := by
        simp [x, inner_sub_left, inner_smul_left, hvw,
          real_inner_self_eq_norm_sq, hw]
      rw [hx, inner_zero_left] at hi
      exact hvd (by linarith)
    · simp only [x, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
      ring

end
end RiemannResearch.LinearAlgebra
