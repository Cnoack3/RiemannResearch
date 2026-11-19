/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r109 : List ℤ := eval% propose 108 (checkpoint 3)
private def r110 : List ℤ := eval% propose 109 r109
private def r111 : List ℤ := eval% propose 110 r110
private def r112 : List ℤ := eval% propose 111 r111
private def r113 : List ℤ := eval% propose 112 r112
private def r114 : List ℤ := eval% propose 113 r113
private def r115 : List ℤ := eval% propose 114 r114
private def r116 : List ℤ := eval% propose 115 r115
private def r117 : List ℤ := eval% propose 116 r116
private def r118 : List ℤ := eval% propose 117 r117
private def r119 : List ℤ := eval% propose 118 r118
private def r120 : List ℤ := eval% propose 119 r119
private def r121 : List ℤ := eval% propose 120 r120
private def r122 : List ℤ := eval% propose 121 r121
private def r123 : List ℤ := eval% propose 122 r122
private def r124 : List ℤ := eval% propose 123 r123
private def r125 : List ℤ := eval% propose 124 r124
private def r126 : List ℤ := eval% propose 125 r125
private def r127 : List ℤ := eval% propose 126 r126
private def r128 : List ℤ := eval% propose 127 r127
private def r129 : List ℤ := eval% propose 128 r128
private def r130 : List ℤ := eval% propose 129 r129
private def r131 : List ℤ := eval% propose 130 r130
private def r132 : List ℤ := eval% propose 131 r131
private def r133 : List ℤ := eval% propose 132 r132
private def r134 : List ℤ := eval% propose 133 r133
private def r135 : List ℤ := eval% propose 134 r134
private def r136 : List ℤ := eval% propose 135 r135
private def r137 : List ℤ := eval% propose 136 r136
private def r138 : List ℤ := eval% propose 137 r137
private def r139 : List ℤ := eval% propose 138 r138
private def r140 : List ℤ := eval% propose 139 r139
private def r141 : List ℤ := eval% propose 140 r140
private def r142 : List ℤ := eval% propose 141 r141
private def r143 : List ℤ := eval% propose 142 r142

private def next108 := oneStep 108 (checkpoint 3) r109 (by decide +kernel)
private def next109 := oneStep 109 r109 r110 (by decide +kernel)
private def next110 := oneStep 110 r110 r111 (by decide +kernel)
private def next111 := oneStep 111 r111 r112 (by decide +kernel)
private def next112 := oneStep 112 r112 r113 (by decide +kernel)
private def next113 := oneStep 113 r113 r114 (by decide +kernel)
private def next114 := oneStep 114 r114 r115 (by decide +kernel)
private def next115 := oneStep 115 r115 r116 (by decide +kernel)
private def next116 := oneStep 116 r116 r117 (by decide +kernel)
private def next117 := oneStep 117 r117 r118 (by decide +kernel)
private def next118 := oneStep 118 r118 r119 (by decide +kernel)
private def next119 := oneStep 119 r119 r120 (by decide +kernel)
private def next120 := oneStep 120 r120 r121 (by decide +kernel)
private def next121 := oneStep 121 r121 r122 (by decide +kernel)
private def next122 := oneStep 122 r122 r123 (by decide +kernel)
private def next123 := oneStep 123 r123 r124 (by decide +kernel)
private def next124 := oneStep 124 r124 r125 (by decide +kernel)
private def next125 := oneStep 125 r125 r126 (by decide +kernel)
private def next126 := oneStep 126 r126 r127 (by decide +kernel)
private def next127 := oneStep 127 r127 r128 (by decide +kernel)
private def next128 := oneStep 128 r128 r129 (by decide +kernel)
private def next129 := oneStep 129 r129 r130 (by decide +kernel)
private def next130 := oneStep 130 r130 r131 (by decide +kernel)
private def next131 := oneStep 131 r131 r132 (by decide +kernel)
private def next132 := oneStep 132 r132 r133 (by decide +kernel)
private def next133 := oneStep 133 r133 r134 (by decide +kernel)
private def next134 := oneStep 134 r134 r135 (by decide +kernel)
private def next135 := oneStep 135 r135 r136 (by decide +kernel)
private def next136 := oneStep 136 r136 r137 (by decide +kernel)
private def next137 := oneStep 137 r137 r138 (by decide +kernel)
private def next138 := oneStep 138 r138 r139 (by decide +kernel)
private def next139 := oneStep 139 r139 r140 (by decide +kernel)
private def next140 := oneStep 140 r140 r141 (by decide +kernel)
private def next141 := oneStep 141 r141 r142 (by decide +kernel)
private def next142 := oneStep 142 r142 r143 (by decide +kernel)
private def next143 := oneStep 143 r143 (checkpoint 4) (by decide +kernel)

theorem checked3 : Step 3 := by
  intro h
  have h109 := next108 h
  have h110 := next109 h109
  have h111 := next110 h110
  have h112 := next111 h111
  have h113 := next112 h112
  have h114 := next113 h113
  have h115 := next114 h114
  have h116 := next115 h115
  have h117 := next116 h116
  have h118 := next117 h117
  have h119 := next118 h118
  have h120 := next119 h119
  have h121 := next120 h120
  have h122 := next121 h121
  have h123 := next122 h122
  have h124 := next123 h123
  have h125 := next124 h124
  have h126 := next125 h125
  have h127 := next126 h126
  have h128 := next127 h127
  have h129 := next128 h128
  have h130 := next129 h129
  have h131 := next130 h130
  have h132 := next131 h131
  have h133 := next132 h132
  have h134 := next133 h133
  have h135 := next134 h134
  have h136 := next135 h135
  have h137 := next136 h136
  have h138 := next137 h137
  have h139 := next138 h138
  have h140 := next139 h139
  have h141 := next140 h140
  have h142 := next141 h141
  have h143 := next142 h142
  have h144 := next143 h143
  exact h144

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
