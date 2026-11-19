/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r145 : List ℤ := eval% propose 144 (checkpoint 4)
private def r146 : List ℤ := eval% propose 145 r145
private def r147 : List ℤ := eval% propose 146 r146
private def r148 : List ℤ := eval% propose 147 r147
private def r149 : List ℤ := eval% propose 148 r148
private def r150 : List ℤ := eval% propose 149 r149
private def r151 : List ℤ := eval% propose 150 r150
private def r152 : List ℤ := eval% propose 151 r151
private def r153 : List ℤ := eval% propose 152 r152
private def r154 : List ℤ := eval% propose 153 r153
private def r155 : List ℤ := eval% propose 154 r154
private def r156 : List ℤ := eval% propose 155 r155
private def r157 : List ℤ := eval% propose 156 r156
private def r158 : List ℤ := eval% propose 157 r157
private def r159 : List ℤ := eval% propose 158 r158
private def r160 : List ℤ := eval% propose 159 r159
private def r161 : List ℤ := eval% propose 160 r160
private def r162 : List ℤ := eval% propose 161 r161
private def r163 : List ℤ := eval% propose 162 r162
private def r164 : List ℤ := eval% propose 163 r163
private def r165 : List ℤ := eval% propose 164 r164
private def r166 : List ℤ := eval% propose 165 r165
private def r167 : List ℤ := eval% propose 166 r166
private def r168 : List ℤ := eval% propose 167 r167
private def r169 : List ℤ := eval% propose 168 r168
private def r170 : List ℤ := eval% propose 169 r169
private def r171 : List ℤ := eval% propose 170 r170
private def r172 : List ℤ := eval% propose 171 r171
private def r173 : List ℤ := eval% propose 172 r172
private def r174 : List ℤ := eval% propose 173 r173
private def r175 : List ℤ := eval% propose 174 r174
private def r176 : List ℤ := eval% propose 175 r175
private def r177 : List ℤ := eval% propose 176 r176
private def r178 : List ℤ := eval% propose 177 r177
private def r179 : List ℤ := eval% propose 178 r178

private def next144 := oneStep 144 (checkpoint 4) r145 (by decide +kernel)
private def next145 := oneStep 145 r145 r146 (by decide +kernel)
private def next146 := oneStep 146 r146 r147 (by decide +kernel)
private def next147 := oneStep 147 r147 r148 (by decide +kernel)
private def next148 := oneStep 148 r148 r149 (by decide +kernel)
private def next149 := oneStep 149 r149 r150 (by decide +kernel)
private def next150 := oneStep 150 r150 r151 (by decide +kernel)
private def next151 := oneStep 151 r151 r152 (by decide +kernel)
private def next152 := oneStep 152 r152 r153 (by decide +kernel)
private def next153 := oneStep 153 r153 r154 (by decide +kernel)
private def next154 := oneStep 154 r154 r155 (by decide +kernel)
private def next155 := oneStep 155 r155 r156 (by decide +kernel)
private def next156 := oneStep 156 r156 r157 (by decide +kernel)
private def next157 := oneStep 157 r157 r158 (by decide +kernel)
private def next158 := oneStep 158 r158 r159 (by decide +kernel)
private def next159 := oneStep 159 r159 r160 (by decide +kernel)
private def next160 := oneStep 160 r160 r161 (by decide +kernel)
private def next161 := oneStep 161 r161 r162 (by decide +kernel)
private def next162 := oneStep 162 r162 r163 (by decide +kernel)
private def next163 := oneStep 163 r163 r164 (by decide +kernel)
private def next164 := oneStep 164 r164 r165 (by decide +kernel)
private def next165 := oneStep 165 r165 r166 (by decide +kernel)
private def next166 := oneStep 166 r166 r167 (by decide +kernel)
private def next167 := oneStep 167 r167 r168 (by decide +kernel)
private def next168 := oneStep 168 r168 r169 (by decide +kernel)
private def next169 := oneStep 169 r169 r170 (by decide +kernel)
private def next170 := oneStep 170 r170 r171 (by decide +kernel)
private def next171 := oneStep 171 r171 r172 (by decide +kernel)
private def next172 := oneStep 172 r172 r173 (by decide +kernel)
private def next173 := oneStep 173 r173 r174 (by decide +kernel)
private def next174 := oneStep 174 r174 r175 (by decide +kernel)
private def next175 := oneStep 175 r175 r176 (by decide +kernel)
private def next176 := oneStep 176 r176 r177 (by decide +kernel)
private def next177 := oneStep 177 r177 r178 (by decide +kernel)
private def next178 := oneStep 178 r178 r179 (by decide +kernel)
private def next179 := oneStep 179 r179 (checkpoint 5) (by decide +kernel)

theorem checked4 : Step 4 := by
  intro h
  have h145 := next144 h
  have h146 := next145 h145
  have h147 := next146 h146
  have h148 := next147 h147
  have h149 := next148 h148
  have h150 := next149 h149
  have h151 := next150 h150
  have h152 := next151 h151
  have h153 := next152 h152
  have h154 := next153 h153
  have h155 := next154 h154
  have h156 := next155 h155
  have h157 := next156 h156
  have h158 := next157 h157
  have h159 := next158 h158
  have h160 := next159 h159
  have h161 := next160 h160
  have h162 := next161 h161
  have h163 := next162 h162
  have h164 := next163 h163
  have h165 := next164 h164
  have h166 := next165 h165
  have h167 := next166 h166
  have h168 := next167 h167
  have h169 := next168 h168
  have h170 := next169 h169
  have h171 := next170 h170
  have h172 := next171 h171
  have h173 := next172 h172
  have h174 := next173 h173
  have h175 := next174 h174
  have h176 := next175 h175
  have h177 := next176 h176
  have h178 := next177 h177
  have h179 := next178 h178
  have h180 := next179 h179
  exact h180

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
