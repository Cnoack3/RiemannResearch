import RiemannResearch.Analysis.GapKernelFourierRecurrence

namespace RiemannResearch.Analysis.GapKernelFourierRecurrence
open GapKernelPolynomial

def block (offset : ℕ) (base : List ℤ) : List ℤ → List ℤ
  | [] => base
  | a :: p => add [(2 : ℤ)^(p.length+offset+1)*a] (doubleStep (block offset base p))

theorem transport_append (p q : List ℤ) :
    transport (p ++ q) = block q.length (transport q) p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, transport, List.length_append, ih, block]

end RiemannResearch.Analysis.GapKernelFourierRecurrence
