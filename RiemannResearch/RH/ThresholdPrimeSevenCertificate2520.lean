import RiemannResearch.Analysis.UpperCertificateArithmetic
import RiemannResearch.RH.ThresholdFiniteCertificate
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Prime-seven conductor-2520 upper certificate

The witness is a legal two-seed generator combination. The finite inequalities
are reduced to exact integer comparisons; `decide` uses the Lean kernel.
The analytic infinite-series regrouping is supplied in the companion module.
-/

open scoped BigOperators
namespace RiemannResearch.RH.TwoSeedThreshold
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

/-- Explicit signed combination, retaining every nonzero optimized coefficient. -/
def legalWitness2520 (k : ℕ) : ℝ :=
  ((5653) * certificateGenerator 2 1 k +
   (1043) * certificateGenerator 2 2 k +
   (-47) * certificateGenerator 2 3 k +
   (451) * certificateGenerator 2 4 k +
   (-613) * certificateGenerator 2 5 k +
   (487) * certificateGenerator 2 6 k +
   (-162) * certificateGenerator 2 7 k +
   (349) * certificateGenerator 2 9 k +
   (-15) * certificateGenerator 2 10 k +
   (42) * certificateGenerator 2 12 k +
   (-140) * certificateGenerator 2 14 k +
   (186) * certificateGenerator 2 15 k +
   (23) * certificateGenerator 2 18 k +
   (-32) * certificateGenerator 2 20 k +
   (75) * certificateGenerator 2 21 k +
   (-25) * certificateGenerator 2 28 k +
   (-49) * certificateGenerator 2 30 k +
   (45) * certificateGenerator 2 35 k +
   (63) * certificateGenerator 2 36 k +
   (-17) * certificateGenerator 2 42 k +
   (-53) * certificateGenerator 2 45 k +
   (-5) * certificateGenerator 2 60 k +
   (-31) * certificateGenerator 2 63 k +
   (18) * certificateGenerator 2 70 k +
   (2) * certificateGenerator 2 84 k +
   (13) * certificateGenerator 2 90 k +
   (-23) * certificateGenerator 2 105 k +
   (6) * certificateGenerator 2 126 k +
   (6) * certificateGenerator 2 140 k +
   (-7) * certificateGenerator 2 180 k +
   (8) * certificateGenerator 2 210 k +
   (-9) * certificateGenerator 2 252 k +
   (6) * certificateGenerator 2 315 k +
   (-1) * certificateGenerator 2 420 k +
   (-1) * certificateGenerator 2 630 k +
   (1) * certificateGenerator 2 1260 k +
   (3810) * certificateGenerator 3 1 k +
   (734) * certificateGenerator 3 3 k +
   (-251) * certificateGenerator 3 5 k +
   (-113) * certificateGenerator 3 7 k +
   (-47) * certificateGenerator 3 15 k +
   (-37) * certificateGenerator 3 21 k +
   (51) * certificateGenerator 3 35 k +
   (1) * certificateGenerator 3 105 k) / 10000

/-- Two exact progression terms and the telescoping bound for the remaining tail. -/
def residueUpper2520 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 2520) * (r + 2521)) +
  1 / (2520 * ((r : ℝ) + 2521))

private def witnessNumerator2520 (k : ℕ) : ℤ :=
  (5653) * (((k % 2 : ℕ) : ℤ) - ((k % 1 : ℕ) : ℤ)) +
  (1043) * (((k % 4 : ℕ) : ℤ) - ((k % 2 : ℕ) : ℤ)) +
  (-47) * (((k % 6 : ℕ) : ℤ) - ((k % 3 : ℕ) : ℤ)) +
  (451) * (((k % 8 : ℕ) : ℤ) - ((k % 4 : ℕ) : ℤ)) +
  (-613) * (((k % 10 : ℕ) : ℤ) - ((k % 5 : ℕ) : ℤ)) +
  (487) * (((k % 12 : ℕ) : ℤ) - ((k % 6 : ℕ) : ℤ)) +
  (-162) * (((k % 14 : ℕ) : ℤ) - ((k % 7 : ℕ) : ℤ)) +
  (349) * (((k % 18 : ℕ) : ℤ) - ((k % 9 : ℕ) : ℤ)) +
  (-15) * (((k % 20 : ℕ) : ℤ) - ((k % 10 : ℕ) : ℤ)) +
  (42) * (((k % 24 : ℕ) : ℤ) - ((k % 12 : ℕ) : ℤ)) +
  (-140) * (((k % 28 : ℕ) : ℤ) - ((k % 14 : ℕ) : ℤ)) +
  (186) * (((k % 30 : ℕ) : ℤ) - ((k % 15 : ℕ) : ℤ)) +
  (23) * (((k % 36 : ℕ) : ℤ) - ((k % 18 : ℕ) : ℤ)) +
  (-32) * (((k % 40 : ℕ) : ℤ) - ((k % 20 : ℕ) : ℤ)) +
  (75) * (((k % 42 : ℕ) : ℤ) - ((k % 21 : ℕ) : ℤ)) +
  (-25) * (((k % 56 : ℕ) : ℤ) - ((k % 28 : ℕ) : ℤ)) +
  (-49) * (((k % 60 : ℕ) : ℤ) - ((k % 30 : ℕ) : ℤ)) +
  (45) * (((k % 70 : ℕ) : ℤ) - ((k % 35 : ℕ) : ℤ)) +
  (63) * (((k % 72 : ℕ) : ℤ) - ((k % 36 : ℕ) : ℤ)) +
  (-17) * (((k % 84 : ℕ) : ℤ) - ((k % 42 : ℕ) : ℤ)) +
  (-53) * (((k % 90 : ℕ) : ℤ) - ((k % 45 : ℕ) : ℤ)) +
  (-5) * (((k % 120 : ℕ) : ℤ) - ((k % 60 : ℕ) : ℤ)) +
  (-31) * (((k % 126 : ℕ) : ℤ) - ((k % 63 : ℕ) : ℤ)) +
  (18) * (((k % 140 : ℕ) : ℤ) - ((k % 70 : ℕ) : ℤ)) +
  (2) * (((k % 168 : ℕ) : ℤ) - ((k % 84 : ℕ) : ℤ)) +
  (13) * (((k % 180 : ℕ) : ℤ) - ((k % 90 : ℕ) : ℤ)) +
  (-23) * (((k % 210 : ℕ) : ℤ) - ((k % 105 : ℕ) : ℤ)) +
  (6) * (((k % 252 : ℕ) : ℤ) - ((k % 126 : ℕ) : ℤ)) +
  (6) * (((k % 280 : ℕ) : ℤ) - ((k % 140 : ℕ) : ℤ)) +
  (-7) * (((k % 360 : ℕ) : ℤ) - ((k % 180 : ℕ) : ℤ)) +
  (8) * (((k % 420 : ℕ) : ℤ) - ((k % 210 : ℕ) : ℤ)) +
  (-9) * (((k % 504 : ℕ) : ℤ) - ((k % 252 : ℕ) : ℤ)) +
  (6) * (((k % 630 : ℕ) : ℤ) - ((k % 315 : ℕ) : ℤ)) +
  (-1) * (((k % 840 : ℕ) : ℤ) - ((k % 420 : ℕ) : ℤ)) +
  (-1) * (((k % 1260 : ℕ) : ℤ) - ((k % 630 : ℕ) : ℤ)) +
  (1) * (((k % 2520 : ℕ) : ℤ) - ((k % 1260 : ℕ) : ℤ)) +
  (3810) * (((k % 3 : ℕ) : ℤ) - ((k % 1 : ℕ) : ℤ)) +
  (734) * (((k % 9 : ℕ) : ℤ) - ((k % 3 : ℕ) : ℤ)) +
  (-251) * (((k % 15 : ℕ) : ℤ) - ((k % 5 : ℕ) : ℤ)) +
  (-113) * (((k % 21 : ℕ) : ℤ) - ((k % 7 : ℕ) : ℤ)) +
  (-47) * (((k % 45 : ℕ) : ℤ) - ((k % 15 : ℕ) : ℤ)) +
  (-37) * (((k % 63 : ℕ) : ℤ) - ((k % 21 : ℕ) : ℤ)) +
  (51) * (((k % 105 : ℕ) : ℤ) - ((k % 35 : ℕ) : ℤ)) +
  (1) * (((k % 315 : ℕ) : ℤ) - ((k % 105 : ℕ) : ℤ))

private def residueCapInt2520 (k : ℕ) : ℤ :=
  let blocks : Fin 28 → Fin 90 → ℤ :=
    ![![14418460, 1440603, 333335, 27028295, 26470663, 22940341, 35108395, 2343666, 24232795, 6960503, 33968385, 30822244, 3514399, 635292, 3218092, 3208404, 13846772, 22368616, 135303, 1845, 339336, 441774, 21756948, 8854140, 707993, 515441, 3678710, 4136758, 1546879, 346168, 5930605, 355050, 367409, 434322, 6219893, 12060474, 732727, 593872, 528997, 2199891, 694779, 1262665, 1162764, 332227, 9920, 22421, 4577863, 2782596, 12312, 71951, 79126, 16645, 2699554, 1410299, 57141, 515888, 475295, 404599, 933025, 718719, 497916, 537667, 199299, 202419, 117427, 306495, 735312, 285748, 292041, 611563, 4391762, 4698923, 721975, 649085, 336070, 722803, 18042, 387506, 332681, 32420, 55786, 41554, 870651, 156670, 44519, 56020, 59899, 165311, 431057, 129762],
    ![219558, 54518, 58113, 69839, 641253, 1212016, 13855, 65644, 351576, 445257, 74546, 95042, 372641, 3038, 6668, 3368, 679468, 1369910, 86459, 14128, 11958, 123554, 237090, 1263, 168871, 50471, 4190, 1904, 346747, 299821, 56392, 65240, 68116, 7715, 247886, 248482, 62189, 39913, 36470, 1878, 460282, 128145, 44441, 51695, 4829, 124019, 115940, 8231, 348332, 394370, 397199, 413375, 1689737, 702761, 228508, 209895, 132439, 255065, 17780, 53663, 157258, 282, 41489, 85039, 1776, 692429, 50135, 42898, 39966, 155710, 5825, 750766, 78520, 166629, 94398, 84541, 77388, 357561, 1149, 6145, 14269, 58794, 94046, 1290, 116108, 159, 318, 987, 314526, 137900],
    ![23868, 6086, 6846, 52871, 2490, 72614, 57196, 15526, 980, 17302, 393832, 107885, 27174, 31175, 67178, 53440, 506625, 4165, 170377, 64309, 66068, 71744, 408464, 1183, 47320, 52133, 4071, 45425, 58726, 13282, 112564, 54437, 56012, 60998, 236235, 887854, 347075, 330938, 323048, 363104, 28822, 190966, 77, 17201, 50558, 45398, 42761, 155948, 490, 11065, 26586, 7406, 104081, 111684, 12711, 41134, 39198, 65140, 20750, 182128, 904, 394, 25380, 60659, 618, 47302, 28533, 4148, 3642, 273, 156773, 99191, 3948, 5216, 18515, 8093, 79066, 2397, 116894, 95741, 31739, 34906, 300997, 22428, 2149, 35, 6, 6758, 74344, 4760],
    ![80237, 4866, 14159, 16259, 99626, 33669, 26144, 28879, 2254, 649, 98814, 10280, 192210, 130615, 174446, 180466, 473959, 151281, 3262, 88, 158, 3717, 70414, 334, 24917, 1466, 23348, 20754, 31021, 36292, 3987, 5051, 5472, 13654, 2911, 202601, 18798, 23656, 22573, 7692, 48506, 138250, 4214, 3236, 25602, 51772, 5649, 12879, 34972, 7634, 8113, 2173, 117643, 109186, 28647, 25986, 24905, 111769, 10267, 72167, 471, 1867, 21204, 18995, 329, 180187, 19247, 17174, 16349, 22950, 16959, 103882, 9722, 71443, 47877, 44551, 4367, 109783, 3069, 19, 10356, 71141, 37, 26817, 266, 5903, 1485, 995, 55764, 136356],
    ![10430, 9032, 8492, 11336, 1364, 16263, 18157, 571, 13604, 4105, 20326, 52978, 800, 1213, 6202, 5847, 32020, 25104, 9191, 5488, 5838, 6836, 111432, 22630, 566, 908, 3433, 13037, 17877, 85, 56270, 27465, 28142, 30145, 93510, 61749, 27, 2, 1249, 1985, 38420, 2064, 81006, 53051, 31206, 20089, 143212, 6150, 24865, 41881, 42643, 23536, 115078, 1403, 7933, 2679, 2434, 1874, 35087, 19999, 7807, 8843, 156, 15785, 4, 20663, 1361, 194, 136, 1129, 66490, 219306, 59498, 76033, 56156, 81953, 4130, 40951, 343, 2956, 8980, 7909, 16841, 34062, 4345, 3625, 3355, 14439, 9180, 12536],
    ![10625, 2995, 3219, 3856, 44109, 40095, 151, 314, 3317, 5685, 18253, 2283, 26178, 1213, 4977, 5738, 80290, 35647, 557, 324, 400, 10951, 10164, 761, 6986, 5207, 1, 23, 43054, 7044, 13980, 15173, 22930, 11244, 46117, 11689, 8414, 851, 736, 96, 43187, 5982, 14431, 15613, 6539, 1456, 13902, 22, 36270, 30111, 30669, 32319, 139150, 3943, 1777, 2211, 2385, 33, 38846, 7472, 56740, 14990, 2973, 3515, 26266, 12191, 6149, 2595, 2779, 91, 31604, 15343, 3961, 441, 53, 7, 33412, 30297, 118, 2291, 315, 776, 24173, 1658, 19570, 853, 959, 1266, 32386, 19512],
    ![1703, 2101, 2260, 3777, 1310, 14334, 3520, 366, 1971, 73, 28594, 29957, 1011, 740, 10, 1327, 19449, 20659, 1008, 32, 16, 1, 30495, 5769, 341, 524, 83, 12915, 3467, 1643, 17242, 8572, 8861, 4784, 26177, 152672, 48403, 46350, 45479, 51671, 8525, 39112, 841, 17120, 28255, 26738, 17, 36991, 634, 70, 101, 8212, 5673, 36730, 5847, 12859, 12451, 11489, 3275, 31915, 215, 1471, 9301, 17659, 1958, 21273, 276, 6652, 3427, 675, 18306, 53389, 4896, 4322, 1455, 7097, 5724, 591, 18235, 14715, 4167, 4696, 37850, 12230, 607, 422, 359, 2939, 10569, 2023],
    ![12447, 281, 334, 495, 11397, 13721, 44, 112, 1985, 9143, 3450, 1423, 13479, 11548, 17855, 18868, 84127, 42124, 2757, 476, 1, 1180, 13757, 502, 10923, 167, 1665, 3918, 7710, 7180, 4261, 4765, 4959, 405, 6978, 24505, 59, 1682, 1559, 94, 19096, 8272, 3204, 3637, 752, 32, 19892, 2423, 27432, 13703, 14007, 14867, 71392, 4032, 238, 32, 18, 8409, 2776, 933, 12856, 6556, 2956, 3361, 18409, 19626, 9, 43, 63, 280, 25185, 4917, 5127, 202, 102, 188, 15851, 5919, 4057, 8434, 1746, 1856, 9368, 616, 2603, 388, 443, 604, 26661, 22782],
    ![1641, 1363, 1260, 4410, 73, 6015, 3586, 410, 818, 2, 18392, 3739, 5663, 6187, 3357, 596, 12379, 11508, 794, 277, 323, 3, 17691, 15990, 2841, 2479, 9498, 16229, 432, 9564, 1272, 2031, 1909, 1618, 1021, 47000, 7083, 6507, 6282, 15087, 83, 5373, 992, 4, 745, 571, 11439, 21054, 209, 96, 123, 330, 12490, 9511, 728, 11102, 7558, 6975, 2077, 10502, 694, 877, 262, 2825, 274, 4040, 4136, 1266, 1355, 3890, 26776, 61733, 14702, 13891, 9215, 15448, 5, 11576, 346, 535, 4610, 4173, 3719, 14316, 1055, 855, 782, 10718, 452, 9772],
    ![658, 353, 399, 536, 8175, 21962, 599, 453, 1938, 2964, 4712, 70, 13094, 1602, 3720, 1863, 27336, 12663, 92, 1159, 1240, 1481, 3399, 313, 2323, 440, 490, 362, 10337, 10505, 325, 445, 496, 23, 3654, 17605, 1388, 12014, 11731, 7092, 1226, 18615, 304, 1200, 3730, 17636, 204, 7792, 898, 396, 1338, 1565, 24701, 50169, 25582, 24576, 24162, 26160, 1994, 12549, 23, 4336, 11505, 10850, 542, 36279, 5520, 5076, 4904, 11715, 55, 21129, 896, 3110, 1294, 1088, 6704, 19424, 2300, 620, 4303, 8315, 531, 2337, 186, 370, 327, 230, 9669, 10346],
    ![136, 211, 931, 1439, 548, 2222, 4289, 1614, 1, 439, 17702, 6903, 837, 1009, 2591, 666, 13127, 4237, 2139, 89, 111, 178, 15417, 38, 2917, 3225, 303, 2446, 3698, 8, 7196, 3609, 3734, 4079, 15219, 53672, 14901, 18995, 18662, 21246, 1343, 10972, 18, 3809, 9716, 9157, 164, 20504, 1218, 173, 145, 1862, 4182, 11875, 2541, 5550, 5382, 4976, 223, 19342, 1022, 852, 4517, 8300, 1095, 15801, 368, 6984, 6797, 3725, 2030, 38381, 12418, 11798, 8171, 23794, 2369, 13123, 85, 7, 1606, 1395, 4567, 18102, 6009, 5590, 3588, 6938, 446, 6308],
    ![615, 1465, 1384, 2731, 18, 21071, 1717, 1501, 5707, 12032, 749, 8443, 127, 141, 34, 72, 12350, 14412, 304, 11, 18, 352, 6964, 380, 8168, 816, 61, 27, 9319, 409, 6607, 4421, 4548, 37, 3724, 10393, 1, 555, 86, 122, 12463, 6778, 332, 432, 3, 52, 8647, 919, 16962, 9421, 9599, 10091, 32303, 2194, 53, 97, 117, 2434, 2485, 799, 5005, 2351, 176, 249, 4812, 14580, 1781, 1571, 1492, 2205, 2628, 11431, 78, 1374, 410, 314, 6401, 3681, 1364, 3192, 1480, 421, 5888, 252, 4708, 2189, 2276, 1130, 16989, 7898],
    ![61, 106, 127, 109, 3196, 14, 8542, 1166, 1, 369, 13235, 6, 9617, 10089, 13634, 3461, 23773, 1, 5817, 4640, 4762, 5097, 27652, 282, 1208, 440, 163, 1156, 3666, 36, 10071, 1862, 3188, 3462, 12083, 10813, 100, 57, 44, 709, 4497, 72, 10394, 6543, 3600, 3888, 18650, 1863, 2497, 4710, 4831, 2362, 19984, 343, 4742, 162, 186, 256, 11743, 5, 5734, 6089, 2040, 114, 1549, 331, 5427, 4699, 4818, 7707, 32147, 13797, 673, 556, 1399, 3348, 1113, 561, 4539, 1385, 23, 71, 6787, 2336, 1, 11, 18, 2562, 459, 4314],
    ![606, 19, 28, 57, 3187, 6898, 48, 85, 521, 926, 3506, 10, 5536, 408, 1261, 1427, 16119, 5763, 176, 885, 938, 542, 4302, 100, 3387, 1463, 478, 582, 12672, 214, 5437, 5769, 5894, 5164, 14325, 499, 4313, 153, 176, 954, 10148, 656, 3847, 4125, 1995, 70, 6248, 10, 8151, 6856, 6991, 7360, 29838, 11931, 2378, 2162, 2080, 4231, 469, 804, 3389, 1104, 6, 22, 2656, 5288, 183, 248, 779, 1, 7285, 2828, 1070, 180, 791, 246, 10253, 4066, 475, 1517, 73, 114, 3279, 16, 2518, 2, 1, 3, 7489, 6150],
    ![42, 75, 90, 1751, 18, 2376, 346, 1, 927, 182, 5013, 8390, 55, 384, 27, 577, 3592, 5673, 74, 369, 54, 27, 6152, 1761, 12, 32, 582, 2318, 1237, 167, 4941, 2661, 2743, 2967, 12566, 24560, 5442, 5126, 5002, 6040, 25, 4472, 247, 1175, 2771, 2550, 1016, 7510, 446, 21, 15, 2859, 818, 10726, 3479, 4028, 3920, 3657, 453, 9244, 210, 154, 752, 2088, 3, 2739, 842, 410, 378, 19, 5892, 11586, 706, 599, 112, 3547, 24, 2088, 1228, 793, 1, 3, 6725, 1834, 1, 9, 15, 204, 4350, 130],
    ![2750, 16, 23, 46, 2518, 4212, 224, 12, 627, 2642, 799, 465, 3363, 1609, 787, 904, 11965, 21822, 4677, 2748, 2663, 3129, 537, 692, 277, 973, 3513, 3273, 32, 7202, 38, 17, 12, 2592, 68, 12554, 1128, 2617, 2535, 1196, 1907, 11468, 2007, 1829, 3618, 6026, 1, 2341, 871, 166, 187, 245, 8704, 6943, 1690, 1529, 790, 5626, 6, 1782, 1235, 316, 96, 440, 440, 16304, 2557, 2358, 2282, 2947, 49, 13660, 1602, 7481, 5370, 5080, 29, 7162, 65, 54, 397, 4379, 105, 1410, 240, 3, 1, 2, 5956, 9067],
    ![367, 911, 865, 2156, 27, 2769, 537, 516, 1345, 460, 2933, 2991, 435, 519, 1275, 195, 7968, 1035, 1859, 1346, 1400, 1547, 9822, 2083, 24, 9, 877, 2154, 810, 931, 1960, 2, 1, 3, 1779, 16231, 4622, 4361, 4259, 8073, 239, 3838, 153, 69, 69, 41, 4586, 5645, 2, 191, 590, 59, 6647, 1409, 7, 1771, 1708, 2705, 469, 3955, 115, 159, 186, 3374, 50, 2803, 417, 16, 22, 376, 8562, 5209, 1, 8, 236, 2, 5168, 689, 7098, 3612, 1166, 1296, 11810, 16, 1886, 1081, 1127, 108, 3857, 61],
    ![4176, 2337, 3429, 3646, 9922, 1573, 1058, 1181, 76, 173, 7250, 1605, 12539, 4673, 6505, 6800, 19489, 561, 2310, 3900, 3986, 389, 8331, 841, 4603, 2679, 692, 791, 9890, 10, 2878, 3074, 3150, 1609, 6202, 1290, 1238, 216, 237, 878, 10106, 3, 4793, 5043, 2202, 17, 5586, 929, 10220, 9032, 9157, 7294, 24290, 5273, 1177, 1056, 1010, 2261, 72, 1030, 1455, 20, 863, 760, 112, 5155, 4, 1, 1, 503, 2253, 4242, 91, 634, 174, 130, 3397, 5775, 41, 43, 333, 1144, 1271, 62, 895, 148, 6, 1, 4723, 2853],
    ![250, 309, 333, 3, 1284, 55, 3796, 2125, 464, 1251, 8135, 1809, 690, 786, 1584, 594, 8648, 5, 5001, 2303, 2366, 2538, 14114, 409, 4587, 4824, 2033, 14, 5176, 1059, 10141, 9389, 9511, 9846, 18542, 7125, 269, 214, 25, 116, 3261, 214, 6793, 1708, 686, 268, 7059, 181, 2934, 4588, 4675, 753, 6590, 762, 82, 37, 30, 14, 4048, 2529, 288, 350, 28, 414, 261, 668, 762, 170, 153, 2, 4630, 7078, 297, 726, 239, 3125, 119, 954, 1283, 908, 318, 381, 7406, 1785, 38, 20, 14, 55, 3480, 26],
    ![3759, 447, 475, 551, 4825, 669, 1623, 1761, 339, 13, 3912, 27, 5051, 3162, 4558, 4785, 18218, 6145, 674, 162, 146, 719, 1510, 5, 1117, 210, 79, 52, 3400, 286, 2355, 2519, 3530, 393, 3057, 2496, 235, 1, 2, 180, 6165, 2213, 326, 389, 28, 89, 1794, 3, 4436, 2034, 2091, 2244, 12572, 90, 663, 751, 786, 125, 2860, 262, 4568, 2817, 904, 1006, 4452, 3308, 48, 6, 4, 53, 3250, 2172, 312, 452, 960, 860, 1212, 3308, 44, 379, 12, 476, 1776, 5, 1358, 506, 535, 613, 5706, 4758],
    ![28, 13, 9, 298, 301, 1443, 656, 167, 1262, 518, 1659, 2566, 1, 3, 154, 676, 1392, 4186, 3, 7, 10, 23, 4608, 2898, 382, 321, 872, 1907, 374, 290, 2109, 61, 71, 1, 1118, 11968, 2171, 2022, 1964, 4232, 229, 2949, 70, 33, 388, 327, 1976, 2753, 101, 509, 537, 84, 5112, 842, 205, 549, 520, 449, 1683, 925, 1008, 516, 1, 1371, 11, 1772, 397, 36, 218, 741, 7936, 12430, 2461, 2304, 1397, 1662, 441, 312, 1941, 558, 3, 11, 2735, 1325, 9, 2, 1, 1443, 551, 1184],
    ![730, 175, 191, 237, 2371, 4824, 427, 364, 1670, 2120, 229, 536, 1442, 414, 949, 1047, 8713, 2059, 244, 775, 1329, 1, 3649, 499, 3064, 1738, 401, 126, 5170, 237, 2051, 2193, 2248, 1142, 5757, 474, 1504, 5, 8, 221, 5667, 19, 4176, 4376, 2774, 260, 5834, 1494, 7501, 6635, 6727, 6977, 20630, 2630, 347, 747, 714, 1615, 394, 219, 2040, 79, 5, 1, 1015, 2954, 31, 50, 58, 27, 2979, 1738, 325, 22, 221, 268, 4073, 2606, 73, 420, 1, 199, 2059, 41, 674, 101, 90, 63, 2642, 2831],
    ![36, 20, 15, 1578, 57, 1986, 213, 129, 95, 5, 3744, 2770, 41, 63, 2, 204, 1992, 2531, 74, 120, 107, 356, 1594, 2000, 164, 127, 1035, 4583, 440, 3002, 15, 87, 77, 53, 604, 11479, 2366, 2220, 2164, 2649, 48, 876, 286, 341, 989, 897, 803, 3087, 8, 182, 198, 450, 1365, 3219, 633, 1458, 897, 810, 874, 2895, 18, 32, 225, 331, 177, 526, 1219, 1, 1, 146, 3371, 5363, 241, 197, 18, 1524, 346, 994, 680, 448, 1, 5, 3555, 2622, 127, 96, 85, 488, 1245, 401],
    ![1392, 432, 455, 520, 2904, 815, 822, 908, 383, 1, 3335, 484, 6251, 4386, 5774, 4581, 15537, 3609, 10, 70, 80, 15, 1717, 35, 1349, 6, 322, 272, 1624, 1658, 257, 305, 325, 266, 210, 5896, 1004, 1969, 1919, 1051, 582, 7195, 803, 1333, 2410, 3811, 29, 1648, 249, 9, 26, 43, 3944, 4246, 1196, 1098, 1060, 2377, 56, 624, 970, 344, 3, 1, 1517, 4772, 171, 135, 123, 250, 1610, 1149, 485, 141, 6, 1, 3024, 645, 363, 916, 108, 546, 1046, 7, 769, 608, 635, 709, 6754, 1914],
    ![140, 175, 445, 75, 1502, 17, 3536, 670, 38, 270, 5149, 64, 2242, 2377, 3390, 612, 4723, 413, 1218, 911, 944, 1032, 7610, 4, 1004, 1095, 182, 2, 3149, 594, 4643, 1213, 1250, 1351, 4433, 3396, 12, 129, 117, 838, 669, 72, 2147, 1158, 238, 283, 5110, 1152, 430, 1005, 1039, 854, 7018, 18, 648, 58, 50, 32, 1424, 617, 878, 962, 135, 455, 68, 1526, 234, 10, 14, 212, 4730, 11457, 4073, 3895, 2819, 4256, 123, 2020, 85, 6, 468, 410, 1144, 1937, 215, 176, 32, 1466, 246, 1321],
    ![309, 30, 36, 4, 753, 5826, 507, 447, 1622, 2009, 5, 1269, 327, 209, 28, 15, 2477, 2584, 8, 184, 198, 338, 1236, 3, 1509, 720, 61, 84, 3912, 203, 1532, 985, 1018, 397, 2390, 1373, 264, 257, 72, 5, 3072, 450, 1023, 1111, 461, 38, 3509, 676, 6250, 5553, 5629, 5831, 14056, 2835, 597, 532, 508, 1184, 343, 538, 883, 6, 448, 392, 80, 4505, 628, 562, 537, 1650, 147, 5305, 406, 531, 197, 160, 1597, 3776, 79, 3, 64, 392, 1072, 1, 807, 12, 9, 110, 1759, 2551],
    ![4, 11, 15, 782, 71, 591, 783, 264, 6, 66, 3640, 427, 996, 1081, 1749, 906, 6758, 4, 1575, 503, 527, 589, 5819, 2, 877, 487, 13, 781, 577, 36, 2110, 1174, 1731, 1842, 5052, 9392, 2033, 1914, 1868, 1599, 139, 425, 968, 1, 138, 109, 944, 1905, 64, 337, 356, 154, 1534, 845, 2, 160, 147, 116, 1656, 1108, 60, 82, 87, 435, 51, 628, 691, 132, 144, 497, 5411, 1853, 68, 91, 4, 857, 481, 103, 1686, 1347, 342, 122, 3860, 1323, 75, 54, 47, 333, 502, 717],
    ![586, 45, 39, 24, 521, 1371, 193, 231, 9, 392, 964, 1, 1576, 801, 1369, 1466, 7920, 5688, 610, 234, 219, 684, 601, 52, 413, 107, 388, 338, 1036, 670, 608, 674, 699, 141, 1544, 1768, 71, 9, 6, 60, 2288, 2429, 2, 6, 79, 406, 909, 185, 1345, 401, 421, 476, 5183, 1779, 54, 36, 31, 1286, 204, 215, 1256, 1067, 220, 260, 1874, 2826, 10, 4, 28, 1, 2591, 876, 413, 99, 2, 74, 1703, 933, 373, 860, 134, 346, 444, 102, 288, 34, 40, 57, 3275, 2755]]
  blocks
    ⟨(k / 90) % 28, Nat.mod_lt _ (by norm_num)⟩
    ⟨k % 90, Nat.mod_lt _ (by norm_num)⟩

private def weightNumerator2520 (k : ℕ) : ℤ :=
  let r : ℤ := (k : ℤ) + 1
  2520 * (r + 2520) * (r + 2521) + r * (r + 1) * (r + 5040)

private def weightDenominator2520 (k : ℕ) : ℤ :=
  let r : ℤ := (k : ℤ) + 1
  2520 * r * (r + 1) * (r + 2520) * (r + 2521)

private def residueCapCheck2520 (k : ℕ) : Prop :=
  10000000000 * weightNumerator2520 k *
      (10000 - witnessNumerator2520 (k + 1)) ^ 2 ≤
    residueCapInt2520 k * 10000 ^ 2 * weightDenominator2520 k

private instance (k : ℕ) : Decidable (residueCapCheck2520 k) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem legalWitness2520_periodic (k : ℕ) :
    legalWitness2520 (k + 2520) = legalWitness2520 k := by
  have h1 : (k + 2520) % 1 = k % 1 := by omega
  have h2 : (k + 2520) % 2 = k % 2 := by omega
  have h3 : (k + 2520) % 3 = k % 3 := by omega
  have h4 : (k + 2520) % 4 = k % 4 := by omega
  have h5 : (k + 2520) % 5 = k % 5 := by omega
  have h6 : (k + 2520) % 6 = k % 6 := by omega
  have h7 : (k + 2520) % 7 = k % 7 := by omega
  have h8 : (k + 2520) % 8 = k % 8 := by omega
  have h9 : (k + 2520) % 9 = k % 9 := by omega
  have h10 : (k + 2520) % 10 = k % 10 := by omega
  have h12 : (k + 2520) % 12 = k % 12 := by omega
  have h14 : (k + 2520) % 14 = k % 14 := by omega
  have h15 : (k + 2520) % 15 = k % 15 := by omega
  have h18 : (k + 2520) % 18 = k % 18 := by omega
  have h20 : (k + 2520) % 20 = k % 20 := by omega
  have h21 : (k + 2520) % 21 = k % 21 := by omega
  have h24 : (k + 2520) % 24 = k % 24 := by omega
  have h28 : (k + 2520) % 28 = k % 28 := by omega
  have h30 : (k + 2520) % 30 = k % 30 := by omega
  have h35 : (k + 2520) % 35 = k % 35 := by omega
  have h36 : (k + 2520) % 36 = k % 36 := by omega
  have h40 : (k + 2520) % 40 = k % 40 := by omega
  have h42 : (k + 2520) % 42 = k % 42 := by omega
  have h45 : (k + 2520) % 45 = k % 45 := by omega
  have h56 : (k + 2520) % 56 = k % 56 := by omega
  have h60 : (k + 2520) % 60 = k % 60 := by omega
  have h63 : (k + 2520) % 63 = k % 63 := by omega
  have h70 : (k + 2520) % 70 = k % 70 := by omega
  have h72 : (k + 2520) % 72 = k % 72 := by omega
  have h84 : (k + 2520) % 84 = k % 84 := by omega
  have h90 : (k + 2520) % 90 = k % 90 := by omega
  have h105 : (k + 2520) % 105 = k % 105 := by omega
  have h120 : (k + 2520) % 120 = k % 120 := by omega
  have h126 : (k + 2520) % 126 = k % 126 := by omega
  have h140 : (k + 2520) % 140 = k % 140 := by omega
  have h168 : (k + 2520) % 168 = k % 168 := by omega
  have h180 : (k + 2520) % 180 = k % 180 := by omega
  have h210 : (k + 2520) % 210 = k % 210 := by omega
  have h252 : (k + 2520) % 252 = k % 252 := by omega
  have h280 : (k + 2520) % 280 = k % 280 := by omega
  have h315 : (k + 2520) % 315 = k % 315 := by omega
  have h360 : (k + 2520) % 360 = k % 360 := by omega
  have h420 : (k + 2520) % 420 = k % 420 := by omega
  have h504 : (k + 2520) % 504 = k % 504 := by omega
  have h630 : (k + 2520) % 630 = k % 630 := by omega
  have h840 : (k + 2520) % 840 = k % 840 := by omega
  have h1260 : (k + 2520) % 1260 = k % 1260 := by omega
  have h2520 : (k + 2520) % 2520 = k % 2520 := by omega
  simp only [legalWitness2520, certificateGenerator, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl, show 2 * 4 = 8 from rfl, show 2 * 5 = 10 from rfl, show 2 * 6 = 12 from rfl, show 2 * 7 = 14 from rfl, show 2 * 9 = 18 from rfl, show 2 * 10 = 20 from rfl, show 2 * 12 = 24 from rfl, show 2 * 14 = 28 from rfl, show 2 * 15 = 30 from rfl, show 2 * 18 = 36 from rfl, show 2 * 20 = 40 from rfl, show 2 * 21 = 42 from rfl, show 2 * 28 = 56 from rfl, show 2 * 30 = 60 from rfl, show 2 * 35 = 70 from rfl, show 2 * 36 = 72 from rfl, show 2 * 42 = 84 from rfl, show 2 * 45 = 90 from rfl, show 2 * 60 = 120 from rfl, show 2 * 63 = 126 from rfl, show 2 * 70 = 140 from rfl, show 2 * 84 = 168 from rfl, show 2 * 90 = 180 from rfl, show 2 * 105 = 210 from rfl, show 2 * 126 = 252 from rfl, show 2 * 140 = 280 from rfl, show 2 * 180 = 360 from rfl, show 2 * 210 = 420 from rfl, show 2 * 252 = 504 from rfl, show 2 * 315 = 630 from rfl, show 2 * 420 = 840 from rfl, show 2 * 630 = 1260 from rfl, show 2 * 1260 = 2520 from rfl, show 3 * 1 = 3 from rfl, show 3 * 3 = 9 from rfl, show 3 * 5 = 15 from rfl, show 3 * 7 = 21 from rfl, show 3 * 15 = 45 from rfl, show 3 * 21 = 63 from rfl, show 3 * 35 = 105 from rfl, show 3 * 105 = 315 from rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h14, h15, h18, h20, h21, h24, h28, h30, h35, h36, h40, h42, h45, h56, h60, h63, h70, h72, h84, h90, h105, h120, h126, h140, h168, h180, h210, h252, h280, h315, h360, h420, h504, h630, h840, h1260, h2520]

theorem legalWitness2520_zero : legalWitness2520 0 = 0 := by
  norm_num [legalWitness2520, certificateGenerator]

private theorem legalWitness2520_eq_int (k : ℕ) :
    legalWitness2520 k = (witnessNumerator2520 k : ℝ) / 10000 := by
  simp only [legalWitness2520, witnessNumerator2520, certificateGenerator,
    Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_neg,
    Int.cast_ofNat, Int.cast_zero, Int.cast_one]

private theorem residueCapInt2520_block0 (k : ℕ)
    (hlo : 0 ≤ k) (hhi : k < 90) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block1 (k : ℕ)
    (hlo : 90 ≤ k) (hhi : k < 180) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block2 (k : ℕ)
    (hlo : 180 ≤ k) (hhi : k < 270) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block3 (k : ℕ)
    (hlo : 270 ≤ k) (hhi : k < 360) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block4 (k : ℕ)
    (hlo : 360 ≤ k) (hhi : k < 450) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block5 (k : ℕ)
    (hlo : 450 ≤ k) (hhi : k < 540) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block6 (k : ℕ)
    (hlo : 540 ≤ k) (hhi : k < 630) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block7 (k : ℕ)
    (hlo : 630 ≤ k) (hhi : k < 720) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block8 (k : ℕ)
    (hlo : 720 ≤ k) (hhi : k < 810) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block9 (k : ℕ)
    (hlo : 810 ≤ k) (hhi : k < 900) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block10 (k : ℕ)
    (hlo : 900 ≤ k) (hhi : k < 990) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block11 (k : ℕ)
    (hlo : 990 ≤ k) (hhi : k < 1080) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block12 (k : ℕ)
    (hlo : 1080 ≤ k) (hhi : k < 1170) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block13 (k : ℕ)
    (hlo : 1170 ≤ k) (hhi : k < 1260) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block14 (k : ℕ)
    (hlo : 1260 ≤ k) (hhi : k < 1350) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block15 (k : ℕ)
    (hlo : 1350 ≤ k) (hhi : k < 1440) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block16 (k : ℕ)
    (hlo : 1440 ≤ k) (hhi : k < 1530) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block17 (k : ℕ)
    (hlo : 1530 ≤ k) (hhi : k < 1620) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block18 (k : ℕ)
    (hlo : 1620 ≤ k) (hhi : k < 1710) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block19 (k : ℕ)
    (hlo : 1710 ≤ k) (hhi : k < 1800) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block20 (k : ℕ)
    (hlo : 1800 ≤ k) (hhi : k < 1890) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block21 (k : ℕ)
    (hlo : 1890 ≤ k) (hhi : k < 1980) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block22 (k : ℕ)
    (hlo : 1980 ≤ k) (hhi : k < 2070) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block23 (k : ℕ)
    (hlo : 2070 ≤ k) (hhi : k < 2160) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block24 (k : ℕ)
    (hlo : 2160 ≤ k) (hhi : k < 2250) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block25 (k : ℕ)
    (hlo : 2250 ≤ k) (hhi : k < 2340) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block26 (k : ℕ)
    (hlo : 2340 ≤ k) (hhi : k < 2430) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_block27 (k : ℕ)
    (hlo : 2430 ≤ k) (hhi : k < 2520) : residueCapCheck2520 k := by
  interval_cases k <;> decide

private theorem residueCapInt2520_all (k : ℕ) (hk : k < 2520) :
    residueCapCheck2520 k := by
  by_cases h0 : k < 90
  · exact residueCapInt2520_block0 k (by omega) h0
  by_cases h1 : k < 180
  · exact residueCapInt2520_block1 k (by omega) h1
  by_cases h2 : k < 270
  · exact residueCapInt2520_block2 k (by omega) h2
  by_cases h3 : k < 360
  · exact residueCapInt2520_block3 k (by omega) h3
  by_cases h4 : k < 450
  · exact residueCapInt2520_block4 k (by omega) h4
  by_cases h5 : k < 540
  · exact residueCapInt2520_block5 k (by omega) h5
  by_cases h6 : k < 630
  · exact residueCapInt2520_block6 k (by omega) h6
  by_cases h7 : k < 720
  · exact residueCapInt2520_block7 k (by omega) h7
  by_cases h8 : k < 810
  · exact residueCapInt2520_block8 k (by omega) h8
  by_cases h9 : k < 900
  · exact residueCapInt2520_block9 k (by omega) h9
  by_cases h10 : k < 990
  · exact residueCapInt2520_block10 k (by omega) h10
  by_cases h11 : k < 1080
  · exact residueCapInt2520_block11 k (by omega) h11
  by_cases h12 : k < 1170
  · exact residueCapInt2520_block12 k (by omega) h12
  by_cases h13 : k < 1260
  · exact residueCapInt2520_block13 k (by omega) h13
  by_cases h14 : k < 1350
  · exact residueCapInt2520_block14 k (by omega) h14
  by_cases h15 : k < 1440
  · exact residueCapInt2520_block15 k (by omega) h15
  by_cases h16 : k < 1530
  · exact residueCapInt2520_block16 k (by omega) h16
  by_cases h17 : k < 1620
  · exact residueCapInt2520_block17 k (by omega) h17
  by_cases h18 : k < 1710
  · exact residueCapInt2520_block18 k (by omega) h18
  by_cases h19 : k < 1800
  · exact residueCapInt2520_block19 k (by omega) h19
  by_cases h20 : k < 1890
  · exact residueCapInt2520_block20 k (by omega) h20
  by_cases h21 : k < 1980
  · exact residueCapInt2520_block21 k (by omega) h21
  by_cases h22 : k < 2070
  · exact residueCapInt2520_block22 k (by omega) h22
  by_cases h23 : k < 2160
  · exact residueCapInt2520_block23 k (by omega) h23
  by_cases h24 : k < 2250
  · exact residueCapInt2520_block24 k (by omega) h24
  by_cases h25 : k < 2340
  · exact residueCapInt2520_block25 k (by omega) h25
  by_cases h26 : k < 2430
  · exact residueCapInt2520_block26 k (by omega) h26
  exact residueCapInt2520_block27 k (by omega) hk

private theorem residueCapInt2520_sum_split (offset n m : ℕ) :
    (∑ r : Fin (n+m), residueCapInt2520 (offset+r.val)) =
      (∑ r : Fin n, residueCapInt2520 (offset+r.val)) +
        ∑ r : Fin m, residueCapInt2520 ((offset+n)+r.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_assoc]

private theorem residueCapInt2520_sum_row0 :
    (∑ r : Fin 90, residueCapInt2520 (0+r.val)) = (381071967 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row1 :
    (∑ r : Fin 90, residueCapInt2520 (90+r.val)) = (17326054 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row2 :
    (∑ r : Fin 90, residueCapInt2520 (180+r.val)) = (7612533 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row3 :
    (∑ r : Fin 90, residueCapInt2520 (270+r.val)) = (4104114 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row4 :
    (∑ r : Fin 90, residueCapInt2520 (360+r.val)) = (2209485 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row5 :
    (∑ r : Fin 90, residueCapInt2520 (450+r.val)) = (1279249 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row6 :
    (∑ r : Fin 90, residueCapInt2520 (540+r.val)) = (1154021 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row7 :
    (∑ r : Fin 90, residueCapInt2520 (630+r.val)) = (758691 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row8 :
    (∑ r : Fin 90, residueCapInt2520 (720+r.val)) = (573590 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row9 :
    (∑ r : Fin 90, residueCapInt2520 (810+r.val)) = (618792 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row10 :
    (∑ r : Fin 90, residueCapInt2520 (900+r.val)) = (580122 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row11 :
    (∑ r : Fin 90, residueCapInt2520 (990+r.val)) = (366399 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row12 :
    (∑ r : Fin 90, residueCapInt2520 (1080+r.val)) = (400751 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row13 :
    (∑ r : Fin 90, residueCapInt2520 (1170+r.val)) = (287210 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row14 :
    (∑ r : Fin 90, residueCapInt2520 (1260+r.val)) = (221226 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row15 :
    (∑ r : Fin 90, residueCapInt2520 (1350+r.val)) = (256080 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row16 :
    (∑ r : Fin 90, residueCapInt2520 (1440+r.val)) = (186121 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row17 :
    (∑ r : Fin 90, residueCapInt2520 (1530+r.val)) = (283828 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row18 :
    (∑ r : Fin 90, residueCapInt2520 (1620+r.val)) = (224913 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row19 :
    (∑ r : Fin 90, residueCapInt2520 (1710+r.val)) = (169229 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row20 :
    (∑ r : Fin 90, residueCapInt2520 (1800+r.val)) = (117762 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row21 :
    (∑ r : Fin 90, residueCapInt2520 (1890+r.val)) = (168756 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row22 :
    (∑ r : Fin 90, residueCapInt2520 (1980+r.val)) = (95596 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row23 :
    (∑ r : Fin 90, residueCapInt2520 (2070+r.val)) = (135410 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row24 :
    (∑ r : Fin 90, residueCapInt2520 (2160+r.val)) = (130360 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row25 :
    (∑ r : Fin 90, residueCapInt2520 (2250+r.val)) = (118071 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row26 :
    (∑ r : Fin 90, residueCapInt2520 (2340+r.val)) = (91846 : ℤ) := by
  decide

private theorem residueCapInt2520_sum_row27 :
    (∑ r : Fin 90, residueCapInt2520 (2430+r.val)) = (74808 : ℤ) := by
  decide

private theorem residueCapInt2520_sum :
    (∑ r : Fin 2520, residueCapInt2520 r.val) = (420616984 : ℤ) := by
  change (∑ r : Fin 2520, residueCapInt2520 (0+r.val)) = _
  rw [residueCapInt2520_sum_split 0 90 2430, residueCapInt2520_sum_row0]
  rw [residueCapInt2520_sum_split 90 90 2340, residueCapInt2520_sum_row1]
  rw [residueCapInt2520_sum_split 180 90 2250, residueCapInt2520_sum_row2]
  rw [residueCapInt2520_sum_split 270 90 2160, residueCapInt2520_sum_row3]
  rw [residueCapInt2520_sum_split 360 90 2070, residueCapInt2520_sum_row4]
  rw [residueCapInt2520_sum_split 450 90 1980, residueCapInt2520_sum_row5]
  rw [residueCapInt2520_sum_split 540 90 1890, residueCapInt2520_sum_row6]
  rw [residueCapInt2520_sum_split 630 90 1800, residueCapInt2520_sum_row7]
  rw [residueCapInt2520_sum_split 720 90 1710, residueCapInt2520_sum_row8]
  rw [residueCapInt2520_sum_split 810 90 1620, residueCapInt2520_sum_row9]
  rw [residueCapInt2520_sum_split 900 90 1530, residueCapInt2520_sum_row10]
  rw [residueCapInt2520_sum_split 990 90 1440, residueCapInt2520_sum_row11]
  rw [residueCapInt2520_sum_split 1080 90 1350, residueCapInt2520_sum_row12]
  rw [residueCapInt2520_sum_split 1170 90 1260, residueCapInt2520_sum_row13]
  rw [residueCapInt2520_sum_split 1260 90 1170, residueCapInt2520_sum_row14]
  rw [residueCapInt2520_sum_split 1350 90 1080, residueCapInt2520_sum_row15]
  rw [residueCapInt2520_sum_split 1440 90 990, residueCapInt2520_sum_row16]
  rw [residueCapInt2520_sum_split 1530 90 900, residueCapInt2520_sum_row17]
  rw [residueCapInt2520_sum_split 1620 90 810, residueCapInt2520_sum_row18]
  rw [residueCapInt2520_sum_split 1710 90 720, residueCapInt2520_sum_row19]
  rw [residueCapInt2520_sum_split 1800 90 630, residueCapInt2520_sum_row20]
  rw [residueCapInt2520_sum_split 1890 90 540, residueCapInt2520_sum_row21]
  rw [residueCapInt2520_sum_split 1980 90 450, residueCapInt2520_sum_row22]
  rw [residueCapInt2520_sum_split 2070 90 360, residueCapInt2520_sum_row23]
  rw [residueCapInt2520_sum_split 2160 90 270, residueCapInt2520_sum_row24]
  rw [residueCapInt2520_sum_split 2250 90 180, residueCapInt2520_sum_row25]
  rw [residueCapInt2520_sum_split 2340 90 90, residueCapInt2520_sum_row26]
  rw [residueCapInt2520_sum_row27]
  norm_num

private theorem residueUpper2520_eq_int (k : ℕ) :
    residueUpper2520 (k + 1) =
      (weightNumerator2520 k : ℝ) / (weightDenominator2520 k : ℝ) := by
  have h := RiemannResearch.Analysis.residue_upper_common_denominator
    ((k : ℝ) + 1) 2520 (by positivity) (by norm_num)
  simpa only [residueUpper2520, weightNumerator2520, weightDenominator2520,
    Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_zero, Int.cast_one, add_assoc,
    show (2520 : ℝ) + 1 = 2521 from by norm_num,
    show (2 : ℝ) * 2520 = 5040 from by norm_num] using h

private theorem residueCap2520_bound (k : ℕ) (hk : k < 2520) :
    residueUpper2520 (k + 1) * (1 - legalWitness2520 (k + 1)) ^ 2 ≤
      (residueCapInt2520 k : ℝ) / 10000000000 := by
  have hc : (10000000000 : ℝ) * (weightNumerator2520 k : ℝ) *
      (10000 - (witnessNumerator2520 (k + 1) : ℝ)) ^ 2 ≤
      (residueCapInt2520 k : ℝ) * 10000 ^ 2 * (weightDenominator2520 k : ℝ) := by
    exact_mod_cast (residueCapInt2520_all k hk)
  have hB : (0 : ℝ) < (weightDenominator2520 k : ℝ) := by
    simp only [weightDenominator2520, Int.cast_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one]
    positivity
  rw [residueUpper2520_eq_int, legalWitness2520_eq_int]
  have he : 1 - (witnessNumerator2520 (k + 1) : ℝ) / 10000 =
      (10000 - (witnessNumerator2520 (k + 1) : ℝ)) / 10000 := by ring
  rw [he]
  exact RiemannResearch.Analysis.upper_certificate_of_cross_mul
    _ _ _ _ _ _ hB (by norm_num) (by norm_num) hc

private theorem residueCap2520_sum_lt :
    (∑ r : Fin 2520, (residueCapInt2520 r.val : ℝ) / 10000000000) <
      (421 : ℝ) / 10000 := by
  have h : (∑ r : Fin 2520, (residueCapInt2520 r.val : ℝ)) = 420616984 := by
    exact_mod_cast residueCapInt2520_sum
  rw [← Finset.sum_div, h]
  norm_num

/-- Exact integer caps control the full residue error of the actual legal witness. -/
theorem legalWitness2520_upper_certificate :
    (∑ r : Fin 2520, residueUpper2520 (r.val + 1) *
      (1 - legalWitness2520 (r.val + 1)) ^ 2) < (421 : ℝ) / 10000 := by
  apply lt_of_le_of_lt _ residueCap2520_sum_lt
  exact Finset.sum_le_sum fun r _ => residueCap2520_bound r.val r.isLt

/-- Analytic weights are kept intact and need only the proved pointwise enclosure. -/
theorem legalWitness2520_error_lt_of_weights
    (w : Fin 2520 → ℝ)
    (hw : ∀ r, w r ≤ residueUpper2520 (r.val + 1)) :
    (∑ r : Fin 2520, w r * (1 - legalWitness2520 (r.val + 1)) ^ 2) <
      (421 : ℝ) / 10000 := by
  apply lt_of_le_of_lt _ legalWitness2520_upper_certificate
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)
end
end RiemannResearch.RH.TwoSeedThreshold
