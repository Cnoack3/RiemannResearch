import Mathlib.Tactic.IntervalCases
import RiemannResearch.RH.ThresholdFiniteCertificate

/-!
# Prime-five dilation witness at conductor 180

This finite rational certificate keeps both seeds 2 and 3 and uses legal integer
dilations. Every progression residue is present, including residue 180.
Candidate discovery used weighted least squares; the proof below uses exact
rational arithmetic. The exact periodic regrouping and analytic tail enclosure
must be supplied separately to obtain an infinite norm theorem.
-/

namespace RiemannResearch.RH.TwoSeedThreshold
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- An explicit finite combination of legal two-seed generators. -/
def legalWitness180 (k : ℕ) : ℝ :=
  ((5474) * certificateGenerator 2 1 k +
   (935) * certificateGenerator 2 2 k +
   (165) * certificateGenerator 2 3 k +
   (-521) * certificateGenerator 2 5 k +
   (326) * certificateGenerator 2 6 k +
   (186) * certificateGenerator 2 9 k +
   (-37) * certificateGenerator 2 10 k +
   (36) * certificateGenerator 2 15 k +
   (27) * certificateGenerator 2 18 k +
   (-6) * certificateGenerator 2 30 k +
   (1) * certificateGenerator 2 45 k +
   (2) * certificateGenerator 2 90 k +
   (3914) * certificateGenerator 3 1 k +
   (804) * certificateGenerator 3 3 k +
   (-175) * certificateGenerator 3 5 k +
   (-22) * certificateGenerator 3 15 k) / 10000

/-- Two retained progression weights and the telescoping upper bound. -/
def residueUpper180 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 180) * (r + 181)) +
  1 / (180 * ((r : ℝ) + 181))

theorem legalWitness180_periodic (k : ℕ) :
    legalWitness180 (k + 180) = legalWitness180 k := by
  have h1 : (k + 180) % 1 = k % 1 := by omega
  have h2 : (k + 180) % 2 = k % 2 := by omega
  have h3 : (k + 180) % 3 = k % 3 := by omega
  have h4 : (k + 180) % 4 = k % 4 := by omega
  have h5 : (k + 180) % 5 = k % 5 := by omega
  have h6 : (k + 180) % 6 = k % 6 := by omega
  have h9 : (k + 180) % 9 = k % 9 := by omega
  have h10 : (k + 180) % 10 = k % 10 := by omega
  have h12 : (k + 180) % 12 = k % 12 := by omega
  have h15 : (k + 180) % 15 = k % 15 := by omega
  have h18 : (k + 180) % 18 = k % 18 := by omega
  have h20 : (k + 180) % 20 = k % 20 := by omega
  have h30 : (k + 180) % 30 = k % 30 := by omega
  have h36 : (k + 180) % 36 = k % 36 := by omega
  have h45 : (k + 180) % 45 = k % 45 := by omega
  have h60 : (k + 180) % 60 = k % 60 := by omega
  have h90 : (k + 180) % 90 = k % 90 := by omega
  have h180 : (k + 180) % 180 = k % 180 := by omega
  simp only [legalWitness180, certificateGenerator, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl, show 2 * 5 = 10 from rfl, show 2 * 6 = 12 from rfl, show 2 * 9 = 18 from rfl, show 2 * 10 = 20 from rfl, show 2 * 15 = 30 from rfl, show 2 * 18 = 36 from rfl, show 2 * 30 = 60 from rfl, show 2 * 45 = 90 from rfl, show 2 * 90 = 180 from rfl, show 3 * 1 = 3 from rfl, show 3 * 3 = 9 from rfl, show 3 * 5 = 15 from rfl, show 3 * 15 = 45 from rfl, h1, h2, h3, h4, h5, h6, h9, h10, h12, h15, h18, h20, h30, h36, h45, h60, h90, h180]

theorem legalWitness180_zero : legalWitness180 0 = 0 := by
  norm_num [legalWitness180, certificateGenerator]

private def residueErrorCap180 (r : Fin 180) : ℝ :=
  let blocks : Fin 6 → Fin 30 → ℝ :=
    ![![187295, 15207, 5254, 505903, 248687, 556814, 372194, 17746, 168218, 44718, 393118, 417351, 10175, 13338, 10432, 12879, 188342, 212736, 2347, 380, 56, 445, 180971, 49257, 486, 1099, 23596, 73531, 3936, 8890],
    ![45693, 9850, 12851, 14271, 82701, 172138, 21305, 17970, 13538, 21815, 8201, 9296, 17018, 2239, 3568, 2659, 24527, 30851, 733, 3771, 5133, 2, 34998, 16131, 141, 5817, 4202, 3383, 12423, 7761],
    ![5931, 6601, 24, 3864, 1309, 7636, 4175, 88, 322, 1895, 34762, 35071, 2026, 1594, 1665, 8059, 2027, 3847, 4838, 2547, 341, 198, 12463, 8260, 158, 71, 2, 2014, 5476, 5735],
    ![1702, 2, 31, 85, 6362, 10249, 100, 183, 1983, 3530, 2291, 1431, 4568, 839, 769, 955, 17587, 17851, 1036, 202, 69, 1948, 2895, 607, 1306, 1, 2475, 2144, 2280, 4023],
    ![871, 1047, 1409, 18, 3707, 8493, 7, 1213, 866, 188, 5393, 4515, 370, 482, 402, 2584, 1128, 1154, 2443, 1401, 1771, 1986, 15818, 7614, 1302, 1106, 806, 3277, 486, 282],
    ![3784, 1074, 76, 38, 1780, 6680, 29, 8, 3, 82, 4310, 3734, 172, 192, 211, 145, 3683, 3225, 240, 794, 101, 1296, 1224, 482, 500, 11, 1, 10, 5214, 5378]]
  blocks
    ⟨r.val / 30, by have hr := r.isLt; omega⟩
    ⟨r.val % 30, Nat.mod_lt _ (by norm_num)⟩ / 100000000

/-- Natural indexing is used only to state the short exact cap-block sums. -/
private def residueCapNat180 (k : ℕ) : ℝ :=
  residueErrorCap180 ⟨k % 180, Nat.mod_lt _ (by norm_num)⟩

/-- This is Fin.sum_univ_add with an explicit natural offset. -/
private theorem residueCapNat180_sum_split (offset n m : ℕ) :
    (∑ r : Fin (n+m), residueCapNat180 (offset+r.val)) =
      (∑ r : Fin n, residueCapNat180 (offset+r.val)) +
        ∑ r : Fin m, residueCapNat180 ((offset+n)+r.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_assoc]

private theorem residueCapNat180_row0 :
    (∑ r : Fin 30, residueCapNat180 (0+r.val)) =
      (3725401 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

private theorem residueCapNat180_row1 :
    (∑ r : Fin 30, residueCapNat180 (30+r.val)) =
      (604986 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

private theorem residueCapNat180_row2 :
    (∑ r : Fin 30, residueCapNat180 (60+r.val)) =
      (162999 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

private theorem residueCapNat180_row3 :
    (∑ r : Fin 30, residueCapNat180 (90+r.val)) =
      (89504 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

private theorem residueCapNat180_row4 :
    (∑ r : Fin 30, residueCapNat180 (120+r.val)) =
      (72139 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

private theorem residueCapNat180_row5 :
    (∑ r : Fin 30, residueCapNat180 (150+r.val)) =
      (44477 : ℝ) / 100000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat180, residueErrorCap180]

/-- Sum the exact thirty-residue block totals; no long successor expansion remains. -/
private theorem residueErrorCap180_sum_lt :
    (∑ r : Fin 180, residueErrorCap180 r) < (47 : ℝ) / 1000 := by
  have he : (∑ r : Fin 180, residueErrorCap180 r) =
      ∑ r : Fin 180, residueCapNat180 (0+r.val) := by
    apply Finset.sum_congr rfl
    intro r _
    unfold residueCapNat180
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt r.isLt]
  rw [he]
  rw [residueCapNat180_sum_split 0 30 150, residueCapNat180_row0]
  rw [residueCapNat180_sum_split 30 30 120, residueCapNat180_row1]
  rw [residueCapNat180_sum_split 60 30 90, residueCapNat180_row2]
  rw [residueCapNat180_sum_split 90 30 60, residueCapNat180_row3]
  rw [residueCapNat180_sum_split 120 30 30, residueCapNat180_row4]
  rw [residueCapNat180_row5]
  norm_num

private theorem residueCap180_block0 (r : Fin 180)
    (hlo : 0 ≤ r.val) (hhi : r.val < 30) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

private theorem residueCap180_block1 (r : Fin 180)
    (hlo : 30 ≤ r.val) (hhi : r.val < 60) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

private theorem residueCap180_block2 (r : Fin 180)
    (hlo : 60 ≤ r.val) (hhi : r.val < 90) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

private theorem residueCap180_block3 (r : Fin 180)
    (hlo : 90 ≤ r.val) (hhi : r.val < 120) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

private theorem residueCap180_block4 (r : Fin 180)
    (hlo : 120 ≤ r.val) (hhi : r.val < 150) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

private theorem residueCap180_block5 (r : Fin 180)
    (hlo : 150 ≤ r.val) (hhi : r.val < 180) :
    residueUpper180 (r.val + 1) * (1 - legalWitness180 (r.val + 1)) ^ 2 ≤
      residueErrorCap180 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper180, legalWitness180, certificateGenerator, residueErrorCap180]

/-- Every residue has its full squared error. No positivity or tail term is dropped. -/
theorem legalWitness180_upper_certificate :
    (∑ r : Fin 180, residueUpper180 (r.val + 1) *
      (1 - legalWitness180 (r.val + 1)) ^ 2) < (47 : ℝ) / 1000 := by
  have h (r : Fin 180) : residueUpper180 (r.val + 1) *
      (1 - legalWitness180 (r.val + 1)) ^ 2 ≤ residueErrorCap180 r := by
    by_cases h0 : r.val < 30
    · exact residueCap180_block0 r (by omega) h0
    by_cases h1 : r.val < 60
    · exact residueCap180_block1 r (by omega) h1
    by_cases h2 : r.val < 90
    · exact residueCap180_block2 r (by omega) h2
    by_cases h3 : r.val < 120
    · exact residueCap180_block3 r (by omega) h3
    by_cases h4 : r.val < 150
    · exact residueCap180_block4 r (by omega) h4
    exact residueCap180_block5 r (by omega) r.isLt
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun r _ => h r))
  exact residueErrorCap180_sum_lt

/-- The analytic application still requires a proved enclosure of the actual weights. -/
theorem legalWitness180_error_lt_of_weights
    (w : Fin 180 → ℝ)
    (hw : ∀ r, w r ≤ residueUpper180 (r.val + 1)) :
    (∑ r : Fin 180, w r * (1 - legalWitness180 (r.val + 1)) ^ 2) <
      (47 : ℝ) / 1000 := by
  apply lt_of_le_of_lt _ legalWitness180_upper_certificate
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)

end
end RiemannResearch.RH.TwoSeedThreshold
