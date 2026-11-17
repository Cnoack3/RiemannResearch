import RiemannResearch.RH.ExactHeadMomentTail
import RiemannResearch.RH.ParetoFiniteCertificates
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic

/-!
# A kernel certificate for the cutoff-seven centered tail

The nine correction coefficients are six-decimal rational roundings of the
retained external witness. All 202 tail residues and their complete infinite
Pareto progression weights are checked. The upper endpoints are rounded
outward on a 10^(-10) grid, independently at every residue.
Source: ResearchData/ExactHeadGreen20261116/moment_probe_certificates.json;
reproduction: ResearchData/ExactHeadGreen20261116/moment_tail_reproduction.md.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomStageSevenMoment
open RiemannResearch
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence
open ExactHeadAtomOptimizer MobiusHeadGreen

theorem probe_formula (r : ℕ) : fittedMomentProbe 7 r =
    (125 * (r : ℝ) + 44 * (r / 2 : ℕ) - 37 * (r / 3 : ℕ) -
      199 * (r / 5 : ℕ) - 280 * (r / 6 : ℕ) - 361 * (r / 7 : ℕ)) / 354 := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  have h6 : ArithmeticFunction.moebius 6 = 1 := moebius_six
  norm_num [fittedMomentProbe, affineMomentDual, mass, energy, weight,
    sum_Icc_one, Finset.sum_range_succ, grid,
    ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_apply_prime (show Nat.Prime 5 by norm_num),
    ArithmeticFunction.moebius_apply_prime (show Nat.Prime 7 by norm_num), h4, h6]
  ring

private def divisors : Finset ℕ := {10,14,15,21,30,35,42,70,105}
private def coeff : ℕ → ℤ
  | 10 => 421603
  | 14 => -689270
  | 15 => -448998
  | 21 => -1205921
  | 30 => -480789
  | 35 => -793449
  | 42 => -1657066
  | 70 => -940424
  | 105 => -2097390
  | _ => 0

def probeCorrection (r : ℕ) : ℝ :=
  ∑ d ∈ divisors, ((coeff d : ℝ) / 1000000) * atom 210 d r

theorem probeCorrection_mem : probeCorrection ∈ upperSpan 210 7 (atom 210) := by
  have hd : divisors ⊆ upperDivisors 210 7 := by decide
  have he : probeCorrection = ∑ d ∈ divisors, ((coeff d : ℝ) / 1000000) • atom 210 d := by
    funext r
    simp [probeCorrection]
  rw [he]
  apply Submodule.sum_mem
  intro d hD
  exact (upperSpan 210 7 (atom 210)).smul_mem _
    (Submodule.subset_span ⟨d, hd hD, rfl⟩)

def centeredProbe (r : ℕ) : ℝ :=
  fittedMomentProbe 7 r - (1 / 2) * target 210 r - probeCorrection r

private def count (d r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun n => Nat.gcd n 210 = d)).card

private theorem atom_eq_count (d r : ℕ) : atom 210 d r = (count d r : ℝ) := by
  simp [atom, count]

private def numerator (r : ℕ) : ℤ :=
  1000000 * (125 * (r : ℤ) + 44 * (r / 2 : ℕ) - 37 * (r / 3 : ℕ) -
    199 * (r / 5 : ℕ) - 280 * (r / 6 : ℕ) - 361 * (r / 7 : ℕ)) -
  177000000 * ((count 1 r : ℤ) - 1) -
  354 * ∑ d ∈ divisors, coeff d * (count d r : ℤ)

private def numData : ℕ → ℤ
  | 0 => 177000000
  | 1 => 125000000
  | 2 => 294000000
  | 3 => 382000000
  | 4 => 551000000
  | 5 => 477000000
  | 6 => 329000000
  | 7 => 93000000
  | 8 => 262000000
  | 9 => 350000000
  | 10 => 170752538
  | 11 => 118752538
  | 12 => -29247462
  | 13 => -81247462
  | 14 => -29245882
  | 15 => 18699410
  | 16 => 187699410
  | 17 => 135699410
  | 18 => -12300590
  | 19 => -64300590
  | 20 => -243548052
  | 21 => -89652018
  | 22 => 79347982
  | 23 => 27347982
  | 24 => -120652018
  | 25 => -194652018
  | 26 => -25652018
  | 27 => 62347982
  | 28 => 114349562
  | 29 => 62349562
  | 30 => -114451132
  | 31 => -166451132
  | 32 => 2548868
  | 33 => 90548868
  | 34 => 259548868
  | 35 => 105429814
  | 36 => -42570186
  | 37 => -94570186
  | 38 => 74429814
  | 39 => 162429814
  | 40 => -16817648
  | 41 => -68817648
  | 42 => 8783716
  | 43 => -43216284
  | 44 => 125783716
  | 45 => 173729008
  | 46 => 342729008
  | 47 => 290729008
  | 48 => 142729008
  | 49 => -93270992
  | 50 => -272518454
  | 51 => -184518454
  | 52 => -15518454
  | 53 => -67518454
  | 54 => -215518454
  | 55 => -289518454
  | 56 => -237516874
  | 57 => -149516874
  | 58 => 19483126
  | 59 => -32516874
  | 60 => -209317568
  | 61 => -261317568
  | 62 => -92317568
  | 63 => 61578466
  | 64 => 230578466
  | 65 => 156578466
  | 66 => 8578466
  | 67 => -43421534
  | 68 => 125578466
  | 69 => 213578466
  | 70 => 155488562
  | 71 => 103488562
  | 72 => -44511438
  | 73 => -96511438
  | 74 => 72488562
  | 75 => 120433854
  | 76 => 289433854
  | 77 => 53433854
  | 78 => -94566146
  | 79 => -146566146
  | 80 => -325813608
  | 81 => -237813608
  | 82 => -68813608
  | 83 => -120813608
  | 84 => -43212244
  | 85 => -117212244
  | 86 => 51787756
  | 87 => 139787756
  | 88 => 308787756
  | 89 => 256787756
  | 90 => 79987062
  | 91 => -156012938
  | 92 => 12987062
  | 93 => 100987062
  | 94 => 269987062
  | 95 => 195987062
  | 96 => 47987062
  | 97 => -4012938
  | 98 => 47988642
  | 99 => 135988642
  | 100 => -43258820
  | 101 => -95258820
  | 102 => -243258820
  | 103 => -295258820
  | 104 => -126258820
  | 105 => 144217240
  | 106 => 313217240
  | 107 => 261217240
  | 108 => 113217240
  | 109 => 61217240
  | 110 => -118030222
  | 111 => -30030222
  | 112 => 21971358
  | 113 => -30028642
  | 114 => -178028642
  | 115 => -252028642
  | 116 => -83028642
  | 117 => 4971358
  | 118 => 173971358
  | 119 => -62028642
  | 120 => -238829336
  | 121 => -290829336
  | 122 => -121829336
  | 123 => -33829336
  | 124 => 135170664
  | 125 => 61170664
  | 126 => 138772028
  | 127 => 86772028
  | 128 => 255772028
  | 129 => 343772028
  | 130 => 164524566
  | 131 => 112524566
  | 132 => -35475434
  | 133 => -271475434
  | 134 => -102475434
  | 135 => -54530142
  | 136 => 114469858
  | 137 => 62469858
  | 138 => -85530142
  | 139 => -137530142
  | 140 => -195620046
  | 141 => -107620046
  | 142 => 61379954
  | 143 => 9379954
  | 144 => -138620046
  | 145 => -212620046
  | 146 => -43620046
  | 147 => 110275988
  | 148 => 279275988
  | 149 => 227275988
  | 150 => 50475294
  | 151 => -1524706
  | 152 => 167475294
  | 153 => 255475294
  | 154 => 307476874
  | 155 => 233476874
  | 156 => 85476874
  | 157 => 33476874
  | 158 => 202476874
  | 159 => 290476874
  | 160 => 111229412
  | 161 => -124770588
  | 162 => -272770588
  | 163 => -324770588
  | 164 => -155770588
  | 165 => -107825296
  | 166 => 61174704
  | 167 => 9174704
  | 168 => 86776068
  | 169 => 34776068
  | 170 => -144471394
  | 171 => -56471394
  | 172 => 112528606
  | 173 => 60528606
  | 174 => -87471394
  | 175 => -241590448
  | 176 => -72590448
  | 177 => 15409552
  | 178 => 184409552
  | 179 => 132409552
  | 180 => -44391142
  | 181 => -96391142
  | 182 => -44389562
  | 183 => 43610438
  | 184 => 212610438
  | 185 => 138610438
  | 186 => -9389562
  | 187 => -61389562
  | 188 => 107610438
  | 189 => 261506472
  | 190 => 82259010
  | 191 => 30259010
  | 192 => -117740990
  | 193 => -169740990
  | 194 => -740990
  | 195 => 47204302
  | 196 => 99205882
  | 197 => 47205882
  | 198 => -100794118
  | 199 => -152794118
  | 200 => -332041580
  | 201 => -244041580
  | 202 => -75041580
  | 203 => -311041580
  | 204 => -459041580
  | 205 => -533041580
  | 206 => -364041580
  | 207 => -276041580
  | 208 => -107041580
  | 209 => -159041580
  | _ => 0

set_option maxHeartbeats 50000000 in
-- Kernel reduction checks all 210 finite gcd-count identities.
set_option maxRecDepth 100000 in
private theorem data_check : ∀ r : Fin 210, numerator r.val = numData r.val := by decide

private theorem residual_data (r : ℕ) (hr : r < 210) :
    centeredProbe r = (numData r : ℝ) / 354000000 := by
  have hn := data_check ⟨r, hr⟩
  change numerator r = numData r at hn
  rw [← hn]
  simp only [centeredProbe, probe_formula, probeCorrection, target, atom_eq_count, numerator]
  generalize r / 2 = r2
  generalize r / 3 = r3
  generalize r / 5 = r5
  generalize r / 6 = r6
  generalize r / 7 = r7
  push_cast
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

private def data (r : ℕ) : ℚ := (numData r : ℚ) / 354000000

private theorem data_cast (r : ℕ) (hr : r < 210) : (data r : ℝ) = centeredProbe r := by
  rw [residual_data r hr]
  simp [data]

private def budget : ℕ → ℕ
  | 8 => 76312625
  | 9 => 109028790
  | 10 => 21249192
  | 11 => 8572291
  | 12 => 440405
  | 13 => 2916032
  | 14 => 327814
  | 15 => 117399
  | 16 => 10449727
  | 17 => 4861146
  | 18 => 35786
  | 19 => 881336
  | 20 => 11456393
  | 21 => 1413395
  | 22 => 1012484
  | 23 => 110429
  | 24 => 1980690
  | 25 => 4767077
  | 26 => 76794
  | 27 => 422020
  | 28 => 1324144
  | 29 => 368131
  | 30 => 1162686
  | 31 => 2310132
  | 32 => 510
  | 33 => 606936
  | 34 => 4711769
  | 35 => 735850
  | 36 => 113736
  | 37 => 532949
  | 38 => 313904
  | 39 => 1423509
  | 40 => 14550
  | 41 => 232579
  | 42 => 3622
  | 43 => 83885
  | 44 => 680712
  | 45 => 1245199
  | 46 => 4651650
  | 47 => 3215936
  | 48 => 745379
  | 49 => 306372
  | 50 => 2519505
  | 51 => 1113583
  | 52 => 7600
  | 53 => 138908
  | 54 => 1367559
  | 55 => 2386309
  | 56 => 1554000
  | 57 => 596227
  | 58 => 9809
  | 59 => 26485
  | 60 => 1064483
  | 61 => 1610143
  | 62 => 195134
  | 63 => 84351
  | 64 => 1149623
  | 65 => 515568
  | 66 => 1506
  | 67 => 37555
  | 68 => 305908
  | 69 => 862137
  | 70 => 445395
  | 71 => 192398
  | 72 => 34722
  | 73 => 159304
  | 74 => 87738
  | 75 => 236527
  | 76 => 1334677
  | 77 => 44459
  | 78 => 136142
  | 79 => 319835
  | 80 => 1546242
  | 81 => 806177
  | 82 => 66078
  | 83 => 199445
  | 84 => 24993
  | 85 => 180169
  | 86 => 34471
  | 87 => 246207
  | 88 => 1178068
  | 89 => 799099
  | 90 => 76069
  | 91 => 283992
  | 92 => 1932
  | 93 => 114676
  | 94 => 804921
  | 95 => 416629
  | 96 => 24540
  | 97 => 169
  | 98 => 23705
  | 99 => 187135
  | 100 => 18621
  | 101 => 88803
  | 102 => 569657
  | 103 => 825707
  | 104 => 148583
  | 105 => 190803
  | 106 => 885984
  | 107 => 606734
  | 108 => 112242
  | 109 => 32322
  | 110 => 118361
  | 111 => 7550
  | 112 => 3983
  | 113 => 7331
  | 114 => 253993
  | 115 => 501839
  | 116 => 53705
  | 117 => 190
  | 118 => 229335
  | 119 => 28759
  | 120 => 420627
  | 121 => 615447
  | 122 => 106579
  | 123 => 8111
  | 124 => 127821
  | 125 => 25843
  | 126 => 131320
  | 127 => 50701
  | 128 => 435045
  | 129 => 776243
  | 130 => 175630
  | 131 => 81164
  | 132 => 7971
  | 133 => 461241
  | 134 => 64950
  | 135 => 18178
  | 136 => 79179
  | 137 => 23312
  | 138 => 43205
  | 139 => 110454
  | 140 => 220979
  | 141 => 66145
  | 142 => 21281
  | 143 => 492
  | 144 => 106207
  | 145 => 247203
  | 146 => 10295
  | 147 => 65105
  | 148 => 413219
  | 149 => 270843
  | 150 => 13223
  | 151 => 12
  | 152 => 142635
  | 153 => 328597
  | 154 => 471267
  | 155 => 269055
  | 156 => 35711
  | 157 => 5425
  | 158 => 196534
  | 159 => 400639
  | 160 => 58190
  | 161 => 72533
  | 162 => 343435
  | 163 => 482359
  | 164 => 109948
  | 165 => 52202
  | 166 => 16652
  | 167 => 372
  | 168 => 32909
  | 169 => 5239
  | 170 => 89616
  | 171 => 13573
  | 172 => 53428
  | 173 => 15326
  | 174 => 31733
  | 175 => 240016
  | 176 => 21487
  | 177 => 961
  | 178 => 136370
  | 179 => 69726
  | 180 => 7773
  | 181 => 36351
  | 182 => 7647
  | 183 => 7322
  | 184 => 172631
  | 185 => 72794
  | 186 => 332
  | 187 => 14056
  | 188 => 42854
  | 189 => 251122
  | 190 => 24658
  | 191 => 3312
  | 192 => 49754
  | 193 => 102627
  | 194 => 2
  | 195 => 7820
  | 196 => 34282
  | 197 => 7706
  | 198 => 34873
  | 199 => 79556
  | 200 => 372997
  | 201 => 200047
  | 202 => 18781
  | 203 => 320377
  | 204 => 692895
  | 205 => 927774
  | 206 => 429732
  | 207 => 245379
  | 208 => 36645
  | 209 => 80343
  | _ => 0

set_option maxHeartbeats 50000000 in
-- Exact integer cross-multiplication checks all 202 outward-rounded bounds.
set_option maxRecDepth 100000 in
private theorem integer_checks : ∀ r : Fin 210, 8 ≤ r.val →
    (10000000000 : ℤ) * numData r.val ^ 2 *
      (210 * ((r.val : ℤ) + 210) * ((r.val : ℤ) + 211) +
       210 * (r.val : ℤ) * ((r.val : ℤ) + 1) +
       (r.val : ℤ) * ((r.val : ℤ) + 1) * ((r.val : ℤ) + 210)) ≤
    (budget r.val : ℤ) * 354000000 ^ 2 * 210 *
      (r.val : ℤ) * ((r.val : ℤ) + 1) * ((r.val : ℤ) + 210) *
      ((r.val : ℤ) + 211) := by decide

private theorem point_checks : ∀ r : Fin 210, 8 ≤ r.val →
    (elementaryProgressionInterval 210 r.val 1).hi * data r.val ^ 2 ≤
      (budget r.val : ℚ) / 10000000000 := by
  intro r hr
  have hrp : (0 : ℚ) < r.val := by
    exact_mod_cast (show 0 < r.val by omega)
  have h0 : (r.val : ℚ) ≠ 0 := hrp.ne'
  have h1 : (r.val : ℚ) + 1 ≠ 0 := by positivity
  have h210 : (r.val : ℚ) + 210 ≠ 0 := by positivity
  have h211 : (r.val : ℚ) + 211 ≠ 0 := by positivity
  let D : ℚ := 354000000 ^ 2 * 210 * (r.val : ℚ) * ((r.val : ℚ) + 1) *
    ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211)
  have hD : 0 < D := by dsimp [D]; positivity
  have hc := integer_checks r hr
  have hq : (10000000000 : ℚ) * (numData r.val : ℚ) ^ 2 *
      (210 * ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211) +
       210 * (r.val : ℚ) * ((r.val : ℚ) + 1) +
       (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210)) ≤
    (budget r.val : ℚ) * 354000000 ^ 2 * 210 *
      (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210) *
      ((r.val : ℚ) + 211) := by exact_mod_cast hc
  have he : (elementaryProgressionInterval 210 r.val 1).hi * data r.val ^ 2 =
      ((numData r.val : ℚ) ^ 2 *
        (210 * ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211) +
         210 * (r.val : ℚ) * ((r.val : ℚ) + 1) +
         (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210))) / D := by
    norm_num [elementaryProgressionInterval, data, D, Finset.sum_range_succ]
    field_simp [h0, h1, h210, h211]
    <;> ring
  rw [he]
  apply (div_le_div_iff₀ hD (by norm_num : (0 : ℚ) < 10000000000)).mpr
  simpa only [D, mul_assoc, mul_comm, mul_left_comm] using hq



set_option maxHeartbeats 50000000 in
-- This is a finite sum of the outward-rounded integer budgets.
set_option maxRecDepth 100000 in
private theorem budget_sum :
    (∑ r ∈ Finset.Icc 8 209, budget r) = 324629179 := by decide

/-- Every infinite progression tail is included in this finite rational certificate. -/
theorem centered_tail_seven_le :
    centeredMomentTailEnergy 7 (1 / 2) probeCorrection ≤ (1 / 30 : ℝ) := by
  have hP : greenPeriod 7 = 210 := by decide
  simp only [centeredMomentTailEnergy, primorial_tail_residues, hP]
  change energy (Finset.Icc 8 209) (progressionWeight 210) centeredProbe ≤ (1 / 30 : ℝ)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 8 209, (budget r : ℝ) / 10000000000 := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hr8, hr209⟩ := Finset.mem_Icc.mp hr
      have hr210 : r < 210 := by omega
      have hw := (elementaryProgressionInterval_contains 210 r 1 (by norm_num) (by omega)).2
      have hc := point_checks ⟨r, hr210⟩ hr8
      have hb : ((elementaryProgressionInterval 210 r 1).hi : ℝ) * (data r : ℝ) ^ 2 ≤
          (budget r : ℝ) / 10000000000 := by
        have hh := (Rat.cast_le (K := ℝ)).2 hc
        push_cast at hh
        exact hh
      rw [data_cast r hr210] at hb
      exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans hb
    _ ≤ _ := by
      have hb : (∑ r ∈ Finset.Icc 8 209, (budget r : ℝ)) = 324629179 := by
        exact_mod_cast budget_sum
      rw [← Finset.sum_div, hb]
      norm_num

theorem fitted_moment_seven_tail_deficit :
    atomFittedMoment (greenPeriod 7) 7 ≤
      (3 / 4) * atomEnergy (greenPeriod 7) 7 + 1 / 30 := by
  have hP : greenPeriod 7 = 210 := by decide
  have hv : probeCorrection ∈ upperSpan (greenPeriod 7) 7 (atom (greenPeriod 7)) := by
    simpa only [hP] using probeCorrection_mem
  have h := fitted_moment_deficit_of_tail_probe_bound 7 (1 / 2) (1 / 30) (1 / 4)
    (by norm_num) (by norm_num) probeCorrection hv centered_tail_seven_le
  norm_num at h ⊢
  exact h

end RiemannResearch.RH.Pareto.ExactHeadAtomStageSevenMoment
