import Mathlib.Tactic.IntervalCases
import RiemannResearch.RH.ThresholdFiniteCertificate

/-!
# Prime-five dilation witness at conductor 360

This finite rational certificate keeps both seeds 2 and 3 and uses legal integer
dilations. Every progression residue is present, including residue 360.
Candidate discovery used weighted least squares; the proof below uses exact
rational arithmetic. The exact periodic regrouping and analytic tail enclosure
must be supplied separately to obtain an infinite norm theorem.
-/

namespace RiemannResearch.RH.TwoSeedThreshold
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- An explicit finite combination of legal two-seed generators. -/
def legalWitness360 (k : ℕ) : ℝ :=
  ((570) * certificateGenerator 2 1 k +
   (112) * certificateGenerator 2 2 k +
   (1) * certificateGenerator 2 3 k +
   (52) * certificateGenerator 2 4 k +
   (-59) * certificateGenerator 2 5 k +
   (36) * certificateGenerator 2 6 k +
   (25) * certificateGenerator 2 9 k +
   (-6) * certificateGenerator 2 10 k +
   (-2) * certificateGenerator 2 12 k +
   (6) * certificateGenerator 2 15 k +
   (3) * certificateGenerator 2 18 k +
   (-2) * certificateGenerator 2 20 k +
   (-4) * certificateGenerator 2 30 k +
   (6) * certificateGenerator 2 36 k +
   (-3) * certificateGenerator 2 45 k +
   (372) * certificateGenerator 3 1 k +
   (62) * certificateGenerator 3 3 k +
   (-26) * certificateGenerator 3 5 k +
   (-2) * certificateGenerator 3 15 k) / 1000

/-- Two retained progression weights and the telescoping upper bound. -/
def residueUpper360 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 360) * (r + 361)) +
  1 / (360 * ((r : ℝ) + 361))

theorem legalWitness360_periodic (k : ℕ) :
    legalWitness360 (k + 360) = legalWitness360 k := by
  have h1 : (k + 360) % 1 = k % 1 := by omega
  have h2 : (k + 360) % 2 = k % 2 := by omega
  have h3 : (k + 360) % 3 = k % 3 := by omega
  have h4 : (k + 360) % 4 = k % 4 := by omega
  have h5 : (k + 360) % 5 = k % 5 := by omega
  have h6 : (k + 360) % 6 = k % 6 := by omega
  have h8 : (k + 360) % 8 = k % 8 := by omega
  have h9 : (k + 360) % 9 = k % 9 := by omega
  have h10 : (k + 360) % 10 = k % 10 := by omega
  have h12 : (k + 360) % 12 = k % 12 := by omega
  have h15 : (k + 360) % 15 = k % 15 := by omega
  have h18 : (k + 360) % 18 = k % 18 := by omega
  have h20 : (k + 360) % 20 = k % 20 := by omega
  have h24 : (k + 360) % 24 = k % 24 := by omega
  have h30 : (k + 360) % 30 = k % 30 := by omega
  have h36 : (k + 360) % 36 = k % 36 := by omega
  have h40 : (k + 360) % 40 = k % 40 := by omega
  have h45 : (k + 360) % 45 = k % 45 := by omega
  have h60 : (k + 360) % 60 = k % 60 := by omega
  have h72 : (k + 360) % 72 = k % 72 := by omega
  have h90 : (k + 360) % 90 = k % 90 := by omega
  have h120 : (k + 360) % 120 = k % 120 := by omega
  have h180 : (k + 360) % 180 = k % 180 := by omega
  have h360 : (k + 360) % 360 = k % 360 := by omega
  simp only [legalWitness360, certificateGenerator, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl, show 2 * 4 = 8 from rfl, show 2 * 5 = 10 from rfl, show 2 * 6 = 12 from rfl, show 2 * 9 = 18 from rfl, show 2 * 10 = 20 from rfl, show 2 * 12 = 24 from rfl, show 2 * 15 = 30 from rfl, show 2 * 18 = 36 from rfl, show 2 * 20 = 40 from rfl, show 2 * 30 = 60 from rfl, show 2 * 36 = 72 from rfl, show 2 * 45 = 90 from rfl, show 2 * 60 = 120 from rfl, show 2 * 90 = 180 from rfl, show 2 * 180 = 360 from rfl, show 3 * 1 = 3 from rfl, show 3 * 3 = 9 from rfl, show 3 * 5 = 15 from rfl, show 3 * 15 = 45 from rfl, h1, h2, h3, h4, h5, h6, h8, h9, h10, h12, h15, h18, h20, h24, h30, h36, h40, h45, h60, h72, h90, h120, h180, h360]

theorem legalWitness360_zero : legalWitness360 0 = 0 := by
  norm_num [legalWitness360, certificateGenerator]

private def residueErrorCap360 (r : Fin 360) : ℝ :=
  let blocks : Fin 12 → Fin 30 → ℝ :=
    ![![16821, 1707, 241, 26689, 27278, 39079, 51538, 1203, 18795, 7139, 33265, 33771, 2595, 2821, 3349, 4445, 11621, 19999, 363, 186, 232, 332, 20941, 7864, 433, 286, 2816, 5641, 842, 304],
    ![6137, 202, 232, 296, 3989, 13013, 955, 782, 679, 2940, 387, 1078, 1387, 442, 11, 2, 3878, 3039, 51, 234, 254, 7, 3498, 667, 22, 986, 902, 790, 553, 411],
    ![877, 931, 192, 326, 62, 677, 388, 86, 97, 248, 3415, 4699, 670, 596, 501, 976, 80, 401, 363, 16, 80, 61, 864, 620, 23, 14, 10, 704, 72, 672],
    ![71, 1, 2, 5, 400, 1644, 66, 51, 313, 342, 159, 100, 420, 1, 3, 5, 996, 945, 3, 6, 8, 258, 145, 71, 46, 1, 75, 62, 357, 149],
    ![202, 220, 229, 85, 535, 233, 101, 46, 41, 9, 470, 205, 100, 112, 4, 195, 95, 57, 249, 224, 233, 249, 1473, 847, 276, 253, 239, 415, 3, 72],
    ![176, 2, 72, 61, 15, 738, 37, 30, 27, 171, 57, 542, 9, 56, 43, 36, 195, 528, 11, 1, 50, 130, 64, 38, 20, 71, 65, 56, 128, 161],
    ![36, 42, 45, 32, 20, 80, 86, 27, 1, 3, 372, 190, 16, 20, 27, 2, 341, 59, 92, 9, 11, 14, 421, 20, 24, 29, 1, 131, 27, 7],
    ![194, 103, 108, 116, 384, 809, 152, 140, 133, 144, 16, 60, 65, 7, 65, 58, 63, 220, 1, 8, 9, 53, 64, 220, 43, 99, 93, 85, 33, 135],
    ![11, 13, 2, 23, 11, 55, 52, 7, 6, 1, 197, 270, 5, 4, 2, 112, 13, 46, 52, 46, 5, 6, 263, 90, 4, 3, 2, 20, 85, 19],
    ![84, 1, 1, 1, 65, 134, 3, 5, 6, 56, 33, 16, 84, 38, 45, 50, 397, 343, 32, 15, 14, 43, 39, 10, 15, 22, 78, 72, 17, 45],
    ![34, 38, 40, 4, 23, 190, 3, 19, 17, 6, 97, 164, 1, 1, 22, 55, 22, 18, 61, 10, 12, 14, 240, 95, 11, 9, 8, 111, 2, 18],
    ![55, 23, 1, 2, 56, 195, 6, 5, 4, 6, 83, 65, 11, 19, 15, 12, 61, 77, 7, 17, 1, 52, 16, 18, 4, 1, 1, 1, 117, 135]]
  blocks
    ⟨r.val / 30, by have hr := r.isLt; omega⟩
    ⟨r.val % 30, Nat.mod_lt _ (by norm_num)⟩ / 10000000

/-- Natural indexing is used only to state the short exact cap-block sums. -/
private def residueCapNat360 (k : ℕ) : ℝ :=
  residueErrorCap360 ⟨k % 360, Nat.mod_lt _ (by norm_num)⟩

/-- This is Fin.sum_univ_add with an explicit natural offset. -/
private theorem residueCapNat360_sum_split (offset n m : ℕ) :
    (∑ r : Fin (n+m), residueCapNat360 (offset+r.val)) =
      (∑ r : Fin n, residueCapNat360 (offset+r.val)) +
        ∑ r : Fin m, residueCapNat360 ((offset+n)+r.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_assoc]

private theorem residueCapNat360_row0 :
    (∑ r : Fin 30, residueCapNat360 (0+r.val)) =
      (342596 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row1 :
    (∑ r : Fin 30, residueCapNat360 (30+r.val)) =
      (47824 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row2 :
    (∑ r : Fin 30, residueCapNat360 (60+r.val)) =
      (18721 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row3 :
    (∑ r : Fin 30, residueCapNat360 (90+r.val)) =
      (6705 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row4 :
    (∑ r : Fin 30, residueCapNat360 (120+r.val)) =
      (7472 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row5 :
    (∑ r : Fin 30, residueCapNat360 (150+r.val)) =
      (3590 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row6 :
    (∑ r : Fin 30, residueCapNat360 (180+r.val)) =
      (2185 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row7 :
    (∑ r : Fin 30, residueCapNat360 (210+r.val)) =
      (3680 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row8 :
    (∑ r : Fin 30, residueCapNat360 (240+r.val)) =
      (1425 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row9 :
    (∑ r : Fin 30, residueCapNat360 (270+r.val)) =
      (1764 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row10 :
    (∑ r : Fin 30, residueCapNat360 (300+r.val)) =
      (1345 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

private theorem residueCapNat360_row11 :
    (∑ r : Fin 30, residueCapNat360 (330+r.val)) =
      (1066 : ℝ) / 10000000 := by
  norm_num [Fin.sum_univ_succ, residueCapNat360, residueErrorCap360]

/-- Sum the exact thirty-residue block totals; no long successor expansion remains. -/
private theorem residueErrorCap360_sum_lt :
    (∑ r : Fin 360, residueErrorCap360 r) < (11 : ℝ) / 250 := by
  have he : (∑ r : Fin 360, residueErrorCap360 r) =
      ∑ r : Fin 360, residueCapNat360 (0+r.val) := by
    apply Finset.sum_congr rfl
    intro r _
    unfold residueCapNat360
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt r.isLt]
  rw [he]
  rw [residueCapNat360_sum_split 0 30 330, residueCapNat360_row0]
  rw [residueCapNat360_sum_split 30 30 300, residueCapNat360_row1]
  rw [residueCapNat360_sum_split 60 30 270, residueCapNat360_row2]
  rw [residueCapNat360_sum_split 90 30 240, residueCapNat360_row3]
  rw [residueCapNat360_sum_split 120 30 210, residueCapNat360_row4]
  rw [residueCapNat360_sum_split 150 30 180, residueCapNat360_row5]
  rw [residueCapNat360_sum_split 180 30 150, residueCapNat360_row6]
  rw [residueCapNat360_sum_split 210 30 120, residueCapNat360_row7]
  rw [residueCapNat360_sum_split 240 30 90, residueCapNat360_row8]
  rw [residueCapNat360_sum_split 270 30 60, residueCapNat360_row9]
  rw [residueCapNat360_sum_split 300 30 30, residueCapNat360_row10]
  rw [residueCapNat360_row11]
  norm_num

private theorem residueCap360_block0 (r : Fin 360)
    (hlo : 0 ≤ r.val) (hhi : r.val < 30) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block1 (r : Fin 360)
    (hlo : 30 ≤ r.val) (hhi : r.val < 60) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block2 (r : Fin 360)
    (hlo : 60 ≤ r.val) (hhi : r.val < 90) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block3 (r : Fin 360)
    (hlo : 90 ≤ r.val) (hhi : r.val < 120) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block4 (r : Fin 360)
    (hlo : 120 ≤ r.val) (hhi : r.val < 150) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block5 (r : Fin 360)
    (hlo : 150 ≤ r.val) (hhi : r.val < 180) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block6 (r : Fin 360)
    (hlo : 180 ≤ r.val) (hhi : r.val < 210) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block7 (r : Fin 360)
    (hlo : 210 ≤ r.val) (hhi : r.val < 240) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block8 (r : Fin 360)
    (hlo : 240 ≤ r.val) (hhi : r.val < 270) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block9 (r : Fin 360)
    (hlo : 270 ≤ r.val) (hhi : r.val < 300) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block10 (r : Fin 360)
    (hlo : 300 ≤ r.val) (hhi : r.val < 330) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

private theorem residueCap360_block11 (r : Fin 360)
    (hlo : 330 ≤ r.val) (hhi : r.val < 360) :
    residueUpper360 (r.val + 1) * (1 - legalWitness360 (r.val + 1)) ^ 2 ≤
      residueErrorCap360 r := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [residueUpper360, legalWitness360, certificateGenerator, residueErrorCap360]

/-- Every residue has its full squared error. No positivity or tail term is dropped. -/
theorem legalWitness360_upper_certificate :
    (∑ r : Fin 360, residueUpper360 (r.val + 1) *
      (1 - legalWitness360 (r.val + 1)) ^ 2) < (11 : ℝ) / 250 := by
  have h (r : Fin 360) : residueUpper360 (r.val + 1) *
      (1 - legalWitness360 (r.val + 1)) ^ 2 ≤ residueErrorCap360 r := by
    by_cases h0 : r.val < 30
    · exact residueCap360_block0 r (by omega) h0
    by_cases h1 : r.val < 60
    · exact residueCap360_block1 r (by omega) h1
    by_cases h2 : r.val < 90
    · exact residueCap360_block2 r (by omega) h2
    by_cases h3 : r.val < 120
    · exact residueCap360_block3 r (by omega) h3
    by_cases h4 : r.val < 150
    · exact residueCap360_block4 r (by omega) h4
    by_cases h5 : r.val < 180
    · exact residueCap360_block5 r (by omega) h5
    by_cases h6 : r.val < 210
    · exact residueCap360_block6 r (by omega) h6
    by_cases h7 : r.val < 240
    · exact residueCap360_block7 r (by omega) h7
    by_cases h8 : r.val < 270
    · exact residueCap360_block8 r (by omega) h8
    by_cases h9 : r.val < 300
    · exact residueCap360_block9 r (by omega) h9
    by_cases h10 : r.val < 330
    · exact residueCap360_block10 r (by omega) h10
    exact residueCap360_block11 r (by omega) r.isLt
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun r _ => h r))
  exact residueErrorCap360_sum_lt

/-- The analytic application still requires a proved enclosure of the actual weights. -/
theorem legalWitness360_error_lt_of_weights
    (w : Fin 360 → ℝ)
    (hw : ∀ r, w r ≤ residueUpper360 (r.val + 1)) :
    (∑ r : Fin 360, w r * (1 - legalWitness360 (r.val + 1)) ^ 2) <
      (11 : ℝ) / 250 := by
  apply lt_of_le_of_lt _ legalWitness360_upper_certificate
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)

end
end RiemannResearch.RH.TwoSeedThreshold
