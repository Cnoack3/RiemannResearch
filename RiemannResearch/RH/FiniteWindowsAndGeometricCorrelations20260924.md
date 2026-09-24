# RH continuation: finite arithmetic windows and geometric residual correlations

Date: 24 September 2026
Baseline: 9c20653bc7242d393fcf7e68160e4e2d6d529d5a
Source handoff: RH_Chat_Record_Signed_Masses_and_Argument_Audit_2026-09-24.md

## Outcome and status

No unconditional proof of the Riemann Hypothesis was obtained.

This continuation establishes exact finite-window localization of the raw
Möbius residual energy and square summability of the actual residual's
normalized dilation correlations on powers of four. It also connects the
finite arithmetic budget to the existing complete dual-projection obstruction.

The finite-window RH theorem retains an explicit cofinal boundedness hypothesis.
No provider for that hypothesis, either signed harmonic mass, or the sublinear
ordinary primitive estimate has been proved. The geometric estimates are
Hilbert-space consequences with the actual arithmetic residual substituted;
they do not establish a new cancellation estimate for Möbius sums.

The coherent Lean check job_RT2nclL8mZst7ZrveR5DdGltWlhgrG03 succeeded:
exit code 0, verified true, 5.116 seconds. The inspected principal declarations
depend only on propext, Classical.choice, and Quot.sound. No sorry, admit,
project-local axiom, or unsafe declaration is included.

The four modules are exported from RiemannResearch.lean. Publication additionally
builds the separated modules through the affected-module checkpoint. Earlier
failed elaboration candidates are not counted as verified results.

## 1. Definitions

Use the complete Pareto norm
\[
 \|f\|_P^2=\sum_{k\ge1}\frac{|f(k)|^2}{k(k+1)},\qquad
 g_d(k)=\frac{k\bmod d}{d}.
\]
Let \(V\) be the closed actual legal span, \(r=1-P_V1\), and \(E=\|r\|_P^2\).
The repository supplies \(r=0\Rightarrow\mathrm{RH}\); this note does not
claim a separately verified converse.

For \(N\ge1\), put
\[
 m_N=\sum_{d=1}^N\frac{\mu(d)}d,\qquad
 U_N(k)=1+\sum_{d=2}^N\mu(d)g_d(k).
\]
Both \(m_N\) and every displayed finite window below are explicit finite
arithmetic expressions, without a limiting projection hidden in their definition.

## 2. Exact localization of the full raw energy

For \(K\ge N\), define
\[
 M_{N,K}=\sum_{N<k\le K}\frac{U_N(k)^2}{k(k+1)},\qquad
 F_{N,K}=\sum_{k>K}\frac{U_N(k)^2}{k(k+1)}.
\]
The new module proves the exact identity
\[
 \boxed{\|U_N\|_P^2
 =m_N^2\sum_{k=1}^N\frac{k}{k+1}+M_{N,K}+F_{N,K}.}
\]
The head follows from the existing arithmetic identity \(U_N(k)=km_N\)
for \(1\le k\le N\). The decomposition uses summability of the complete
weighted coordinate squares.

The existing bound \(|U_N(k)|\le N\), together with telescoping Pareto weights,
gives the unconditional far-tail estimate
\[
 0\le F_{N,K}\le\frac{N^2}{K+1}.
\]
Thus
\[
 \boxed{\|U_N\|_P^2\le B_N+1,\qquad
 B_N=Nm_N^2+M_{N,N^2}.}
\]
The final \(1\) bounds the entire infinite tail; it is not a tail omission.
One can also write the exact head factor as
\(\sum_{k=1}^Nk/(k+1)=N+1-H_{N+1}\).
The formal theorem retains the finite rational sum.

Modules:
- RH/RawMobiusFiniteWindowEnergy.lean
- RH/RawMobiusFiniteWindowCriterion.lean

Principal declarations:
- rawMobiusMiddleEnergy_finite_arithmetic
- rawMobius_head_energy_exact
- rawMobius_energy_three_regions
- rawMobiusFarEnergy_le
- rawMobius_energy_le_square_window
- naturalResidual_eq_rawMobiusResidual

The indexing bridge is exact: the matrix-indexed naturalResidual n equals
the physical raw residual at cutoff \(N=n+1\).

## 3. Connection to the actual remaining obstruction

Let \(Q_n r\) be the existing finite dual-coordinate orthogonal projection.
The new unconditional bridge is
\[
 \boxed{E^2\le(B_{n+1}+1)\,\|r-Q_nr\|_P^2.}
\]
It follows from the complete natural-residual dual pairing and the new
finite-window upper bound. No mixed term or physical tail is dropped.

The new conditional theorem proves
\[
 \boxed{\bigl[\exists C\in\mathbb R,\
 B_N\le C\text{ for arbitrarily large }N\bigr]\Longrightarrow\mathrm{RH}.}
\]
Its exact Lean hypothesis is hbudget in
riemannHypothesis_of_frequently_bounded_raw_square_window.
That argument remains OPEN. A clean foundational axiom report does not
provide hbudget.

The literature supplies a useful way to select head cutoffs: reciprocal
Möbius sign changes yield arbitrarily large \(N\) with \(N|m_N|\le1/2\).
Then \(Nm_N^2\le1/(4N)\). This classical sign-change provider was not
formalized in this continuation, and a uniform bound for \(M_{N,N^2}\)
along those same cutoffs is still missing.

This is a reduction to a finite arithmetic budget, not an estimate proving
that budget is bounded.

## 4. Actual geometric correlation estimates

Write
\[
 D_mf(k)=m f(\lfloor k/m\rfloor),\qquad
 a_m=\langle r,D_mr\rangle_P,\qquad
 A_j=a_{4^j},\qquad b_j=2^{-j}A_j.
\]
All these correlations are for the actual limiting residual.

The normalized target tails \(t_j=2^{-j}D_{4^j}1\) have exact Gram entries
\[
 \langle t_i,t_j\rangle_P=2^{-|i-j|}.
\]
The existing legal-span invariance gives
\(\langle t_j,r\rangle_P=b_j\), with \(b_0=E\).
Orthogonalizing this geometric Gram kernel produces
\[
 e_0=t_0,\qquad e_{j+1}=\frac2{\sqrt3}(t_{j+1}-t_j/2).
\]
These vectors are orthonormal. Bessel's inequality yields both finite and
infinite versions of
\[
 \boxed{E^2+\frac13\sum_{j\ge0}\frac{(A_{j+1}-A_j)^2}{4^j}\le E.}
\]
The series is formally proved summable. Neighboring signed correlations
are retained inside the square.

A separate exact scalar identity, including both finite endpoints, gives
\[
 \boxed{\sum_{j\ge0}\frac{A_j^2}{4^j}\le3E-E^2.}
\]
Again, summability is an explicit proved declaration, not an interpretation
of a potentially nonsummable real tsum.

Modules:
- Analysis/GeometricGramInnovations.lean
- RH/ResidualGeometricInnovations.lean

Principal declarations:
- geometricInnovation_orthonormal
- geometricInnovation_weighted_summable
- geometricInnovation_infinite_bound
- geometric_half_scalar_energy_identity
- quaternaryTail_gram
- residual_geometric_pairing_difference_summable
- residual_geometric_pairing_difference_bound
- residual_geometric_pairing_square_summable
- residual_geometric_pairing_square_tsum_bound

These results strengthen the recorded pointwise normalized correlation
decay to summability on geometric scales. They do not control all terms
in the ordinary primitive identity
\[
 H_r(N)=2\sum_{m=1}^N a_m-Na_{N+1}.
\]
Neither the required signed cancellation nor a fixed sublinear bound for
\(H_r\) follows from the new estimates.

## 5. Source audit and external computation

1. Luis Báez-Duarte, *Arithmetical Aspects of Beurling's Real Variable
   Reformulation of the Riemann Hypothesis*, Proposition 4.4 and
   Proposition 4.7:
   https://arxiv.org/pdf/math/0011254 .
   The natural full sequence does not converge to the target in L2.
   This is not a proof that every bounded subsequence is impossible.
   It is a reason to distinguish full-sequence strong convergence from
   a cofinal boundedness criterion.

2. Eva A. Gallardo-Gutiérrez and Daniel Seco, *Zero-free regions of the
   Riemann zeta function and approximation in weighted Dirichlet spaces*,
   Theorem 3.1 and its proof:
   https://arxiv.org/html/2206.02654v6 .
   This supplies the motivation for the middle-window route and the cited
   reciprocal-Möbius sign-change input. Its required middle-window estimate
   is a hypothesis, not an unconditional provider. The raw-family energy
   formula above is an independently derived specialization; it is not a
   literal import of their boundary-corrected family.

3. Juan Manzur, Waleed Noor and Gustavo Quintero, *A Hardy space approximation
   supporting zero-free half-planes for the zeta-function*, Theorem 3.1:
   https://arxiv.org/html/2606.16097v1 .
   The proved Hardy convergence has boundary parameter greater than 1.
   It does not provide the missing estimate down to the critical boundary.

Wolfram Language independently checked the exact rational head identity
for \(1\le N\le15\), and the four-dimensional geometric Gram inverse and
innovation identity symbolically. These checks supported debugging; the
all-index theorems rely on Lean proofs.

An endpoint correction matters when adapting the Gallardo–Seco formulas.
For their corrected family \(F_N(k)=U_N(k)-(k\bmod N)m_N\),
\(F_N(k)=0\) holds for \(k<N\), whereas \(F_N(N)=Nm_N\).
At \(N=2\), the latter equals 1. Wolfram confirmed this example. The new
Lean decomposition retains the endpoint in its exact head.

## 6. Continuation target

The most concrete unresolved arithmetic task obtained here is:

Find a cofinal sequence \(N_j\) and one finite constant \(C\) such that
\[
 N_jm_{N_j}^2+
 \sum_{N_j<k\le N_j^2}
 \frac{\left(1+\sum_{d=2}^{N_j}\mu(d)(k\bmod d)/d\right)^2}{k(k+1)}
 \le C
 \quad\text{for every }j.
\]

Finite numerical evidence cannot provide the universal/cofinal proof.
The alternative signed-mass and primitive obligations in the supplied audit
also remain open. No unconditional RH declaration has been added.
