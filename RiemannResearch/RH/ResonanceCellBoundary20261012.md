# Resonance-cell blind patterns and their short legal boundary correction

Christian Noack · 12 October 2026

Source: `RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16 (1).md`, especially Sections 5 and 8. This continuation follows the current request to formalize in Lean, superseding the older handoff's instruction not to use Lean. No mathematical novelty claim is made.

## Main result

The selected cells have one common potential on their connected covered component when all their sources vanish. That common potential is detected by one ternary old-boundary packet at odd budgets, or two at even budgets. Its actual projection source has an unconditional logarithmic gain budget.

Set
\[
L=\lfloor M/2\rfloor+1,\quad R=2L,\quad
\lambda_M=\langle b-P_Mb,g_{3,R}\rangle,
\]
\[
K=8\|B_{3,1}\|_H^2+996,\qquad
B_M=8\log(M+1)+K.
\]
For every positive ordinary budget,
\[
\boxed{\lambda_M^2\le B_M\,(D_M-D_{2M}).}
\]
This inequality does not require the selected cell sources to vanish. Under invisibility, it controls exactly the common potential they miss. It does not give a lower bound on \(\lambda_M^2\) in terms of \(D_M\).

## Formalized declarations

`RiemannResearch/LinearAlgebra/ResonanceCellPotentials.lean` adds eighteen public theorems. Its main declarations are:

- `selected_iff_offset`: the exact finite interval of selected cells, including empty cases;
- `selected_source_compatible`: compatibility follows from the exact commuting-square law and the old boundary;
- `selected_invisible_iff_constant`: the necessary and sufficient common-potential classification on all covered canonical vertices;
- `ternary_chain_reconstruction`: exact reconstruction by a signed sum of packet sources;
- `anchored_flat_chain_zero`: a zero root anchor kills every covered invisible potential;
- `boundary_anchor_odd`, `boundary_anchor_even`: the common root uses precisely one or two boundary sources;
- `compatible_displacement_certificate`, `compatible_displacement_bound`: the complete square identity and the coefficient \(6/5\).

`RiemannResearch/RH/ResonanceCellBoundary.lean` adds sixteen public theorems and three private proof helpers. It specializes to the actual weighted Hilbert generators:

- `potential_sources`: the five abstract adjacent differences are exactly the existing genuine `cellSource`;
- `potential_commuting`: the arithmetic provider is discharged by `generator_cocycle`;
- `projection_old_anchored`: the old boundary provider is discharged by projection orthogonality;
- `projection_invisible_iff_constant`: the actual constant-target residual satisfies the common-potential classification;
- `projection_boundary_odd`, `projection_boundary_even`: the actual common potential is the stated boundary packet charge;
- `boundary_correction_cases`: the legal root correction is exactly one or two adjacent packets;
- `boundary_correction_norm_sq_le`: its complete infinite norm is at most \(B_M\);
- `actual_boundary_source_gain`: arbitrary-target nested-projection version;
- `projection_common_source_gain_of_budgets`: constant-target version with ordinary old/new budget membership supplying the legal columns.

The actual theorem requires nested subspaces with orthogonal projections and membership of the old and new legal generators. For \(P=V_M\), \(W=V_{2M}\), these are finite projection geometry and budget membership conditions. No RH assumption or unresolved source estimate is among the inputs. The generic finite-potential theorem has explicit old-anchor and commuting hypotheses; the application module proves both providers for the actual residual.

## Exact reconstruction

Write \(B(m)=\Phi_{2,M}(m)\), \(T(m)=\Phi_{3,M}(m)\). At a selected cell the old boundary and commuting squares give
\[
B(3k)=T(2k),\qquad B(3k+3)=T(2k+2).
\]
Consequently the five sources vanish if and only if
\[
B(3k+1)=B(3k+2)=T(2k)=T(2k+1)=T(2k+2).
\]
Successive cells share \(T(2k+2)\), so every covered vertex has the same value \(\lambda_M=T(2L)\). The exact boundary identity is
\[
\lambda_M=
\begin{cases}
h_{3,M}(M),&M\text{ odd},\\
h_{3,M}(M)+h_{3,M}(M+1),&M\text{ even}.
\end{cases}
\]
The exact signed reconstruction, without invisibility, is
\[
T(2(L+j))=T(2L)+\sum_{i=0}^{j-1}
\left[h_{3,M}(2(L+i))+h_{3,M}(2(L+i)+1)\right].
\]
For compatible sources \(h=(x_0,x_1,x_2,y_0,y_1)\), \(s=\sum x_i=\sum y_i\), Lean proves
\[
6\|h\|_2^2-5s^2
=2\bigl((x_0-x_1)^2+(x_0-x_2)^2+(x_1-x_2)^2\bigr)
+3(y_0-y_1)^2.
\]
This retains every remainder square and implies \(s^2\le(6/5)\|h\|_2^2\).

## Why the boundary gain has logarithmic cost

Take the genuine legal correction
\[
z_M=g_{3,R}-g_{3,M}.
\]
Its source against the old residual is exactly \(\lambda_M\), because \(g_{3,M}\in V_M\). It belongs to \(V_{2M}\), since \(R\le2M\) for \(M>0\). It is one adjacent packet if \(M\) is odd, and two if \(M\) is even.

The existing checked complete packet estimate is
\[
\left|\|A_{3,m}\|_H^2-2\log m\right|
\le2\|B_{3,1}\|_H^2+249.
\]
Applying it to the one/two-packet correction, retaining all interactions before using the norm inequality, yields
\[
\|z_M\|_H^2\le8\log(M+1)+8\|B_{3,1}\|_H^2+996.
\]
Full old-space screening contracts this norm. The exact refitted gain for the screened scalar correction is
\[
2t\langle e_M,z_M\rangle-t^2\|(I-P_M)z_M\|_H^2.
\]
Choosing \(t=\lambda_M/B_M\) gives at least \(\lambda_M^2/B_M\), and the true enlarged optimizer does at least as well. There is no division by \(\lambda_M\), so a zero source is included.

## Geometric omissions: proved on paper, not a Lean rank theorem

Set
\[
c=\max(0,\lfloor2M/3\rfloor-\lfloor M/2\rfloor-1),\quad
d=2M-\lfloor2M/3\rfloor+\lfloor M/3\rfloor.
\]
If \(c>0\), the selected cells cover \(4c+1\) independent canonical vertices, have packet rank \(4c\), and leave blind dimension \(d-4c\). Their graph is a chain of five-cycles sharing one vertex at successive junctions. Choose four tree edges per cell: its two ternary edges and its first two binary edges. Telescoping gives every covered vertex difference from the root; the omitted fifth edge is the signed sum of those four edges. Thus the span is the covered coefficient-sum-zero hyperplane. This proves the rank from canonical independence.

A minimal completion is one covered root column plus every uncovered canonical column, exactly \(d-4c\) additional directions. The formalized boundary correction supplies the root. The uncovered columns remain to be controlled. When \(c=0\), there is no covered component and no selected-cell root interpretation.

Wolfram exact finite incidence ranks confirmed:

| \(M\) | Cells \(c\) | Full increment \(d\) | Cell rank | Blind dimension |
|---:|---:|---:|---:|---:|
| 12 | 1 | 20 | 4 | 16 |
| 24 | 3 | 40 | 12 | 28 |
| 48 | 7 | 80 | 28 | 52 |
| 96 | 15 | 160 | 60 | 100 |

These are finite computations and do not establish an arithmetic lower bound for the actual source. The graph dimension theorem above is not represented as a checked Lean declaration in this continuation.

## Remaining RH obligation

Established: exact classification, actual arithmetic providers, short legal boundary correction, and logarithmic cost of detecting its common source.

Open: an independently proved estimate forcing sufficient actual source in the combined covered and uncovered directions, with complete signed energy control. In particular,
\[
D_M\le C\log(2M)(D_M-D_{2M})+\varepsilon_M,\quad\varepsilon_M\to0
\]
remains unproved. The boundary gain above does not establish it.

Next concrete target: screen the uncovered canonical directions against the cell-tree directions and the boundary root, then estimate the actual remaining Schur source. Keep the signed cross term and Schur-complement energy. Treating the common potential as automatically zero would omit a legal source; treating its new bound as controlling all of \(D_M\) would omit the uncovered directions.

## Verification and literature context

Core development checked in `job_-Zl8Hs8VhVrltwTWLPh0sjYWDIElgyqY` (exit 0). Actual boundary development checked in `job_wyx-mlWw27ELV6zzKkIMlAdn9AK406NF` (exit 0). Decisive axiom outputs contain only `propext`, `Classical.choice`, and `Quot.sound`. Persisted-module audit `job_eQvm3yiuapEa53Pcga6IUGNLXLCbhXUV` built both final modules successfully (exit 0), and checked the decisive theorem axioms. Full incremental server project validation `job_5DusufVtEF1Y-_dQzKSWdP0eMPr_oynn` then succeeded (`lake build RiemannResearch --quiet`, 96.906 seconds). No new Lean source was changed after that build. The final publication checkpoint is a separate acceptance gate; it must validate the exact final repository changes before pushing.

Publication approval: Christian explicitly authorized pushing these verified changes on 12 October 2026. Publication uses the server checkpoint, including validation of any integrated source before the push.

For general discrete Nyman–Beurling context, [Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*](https://arxiv.org/pdf/math/0607733), Theorem 1, uses the same Pareto weight and distinguishes target closure from finite algebra. [Noor, *A Hardy space analysis of the Báez-Duarte criterion*](https://arxiv.org/pdf/1809.09577), discusses unconditional results after smoothing and the unbounded inverse operation. These sources provide context; the boundary identities here are derived from the supplied handoff and existing repository identities.
