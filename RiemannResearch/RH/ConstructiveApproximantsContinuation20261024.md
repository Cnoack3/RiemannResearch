# Constructive exact-head approximation: verified continuation

Date: 24 October 2026.

Source: the user-provided `RH_Constructive_Approximants_Research_Agenda_2026-10-24(1).md`, especially Sections 6, 8, and 10. This continuation implements the averaging construction in the actual complete Pareto Hilbert space, strengthens its quantitative block bound, and removes unnecessary rank hypotheses from sampled repair. It does not prove RH.

## 1. What this continuation establishes

The main constructive result is `Pareto.online_exact_head_block_average_bound`. Suppose an explicit legal family has residuals `r_N = G_N - 1`, vanishes on physical sites `1,...,N`, has certified integer amplitude bounds `|r_N(n)| <= U(N)`, and satisfies a single complete energy bound `norm(r_N)^2 <= C^2` for all N. An executable integer recurrence selects heads using only the amplitudes. For every block offset a and positive block length m,

\[
\left\|\frac1m\sum_{i=0}^{m-1}r_{N_{a+i}}\right\|_P^2
\le \frac{C^2}{m}+\frac{2C\,2^{-a}}{m^2}.
\]

The recurrence needs no numerical value of C. Setting a=m preserves growing exact heads and improves the handoff's mixed-term bound to `2 C 2^(-m)/m^2`. Finite averages preserve membership in the legal linear span. Complete P-to-Q norm comparison transfers convergence of these same functions; no Gram matrix is identified across measures.

**Open arithmetic obligation:** construct the legal family with a bound C independent of N. The theorem exposes this as `hbound`; selecting larger heads does not prove it.

## 2. Executable head selection

For integer amplitude bounds U(N), initialize

\[
(N_0,M_0)=(1,U(1)^2).
\]

Then compute

\[
N_{j+1}=\max\{N_j+1,4^{j+2}M_j\},\qquad
M_{j+1}=\max\{M_j,U(N_{j+1})^2\}.
\]

`Analysis.exactHeadSelection_strictMono` proves strict growth, and
`Analysis.exactHeadSelection_dominates_earlier_amplitude` proves

\[
4^{j+1}U(N_i)^2\le N_j\qquad(i<j).
\]

This avoids a ceiling of an exact real number. When U is an executable integer certificate, the whole selector is executable; no zero enumeration or capacity threshold search is involved.

For an earlier residual r and a later exact-head residual e, the actual-P theorem `exact_head_pairing_sq_le` gives

\[
|\langle r,e\rangle_P|^2
\le \frac{A^2}{N+1}\|e\|_P^2,
\]

from the physical bound |r(n)|<=A and exact vanishing of e through N. It uses the complete tail and its exact Pareto mass. Combining it with the selector gives
`|inner(r_(N_i),r_(N_j))| <= C 2^(-j-1)`.

The generic averaging module first retains the exact signed Gram equality. It then proves the sharper finite bound

\[
\|\overline r_{a,m}\|^2
\le\frac{C^2}{m}
+\frac{2C\,2^{-a}}{m^2}\left(1-(m+1)2^{-m}\right).
\]

The actual-Q bridge `QExactHeadAverages.blockAverage_head_through_first` preserves the full first selected head, rather than merely the number of terms averaged. Its Q-norm bound requires Q-norm and Q-pairing hypotheses explicitly.

## 3. Normalization at every sampling stage

Write u for the exact synthesized projection signal, v for its sampled counterpart, k=norm(u)^2>0, s=inner(u,v), and

\[
E_\perp=v-\frac{s}{k}u,\qquad
d=\max\{s,k/2\},\qquad
\widehat F=\frac{u}{k}+\frac{E_\perp}{d}.
\]

The extended `Analysis.SignalNormalizationStability` module proves:

- d>0, exact unit signal, and membership in any submodule containing u and v.
- Equality with ordinary signal normalization once s>=k/2.
- The exact displacement and unconditional sampling bound

\[
\|\widehat F-u/k\|^2=\frac{\|E_\perp\|^2}{d^2}
\le\frac{4\|v-u\|^2}{k^2}.
\]

- For a unit target t satisfying the actual projection pairings,

\[
\|t-\widehat F\|^2=k^{-1}-1+\frac{\|E_\perp\|^2}{d^2}.
\]

The last result is `safeNormalized_target_error`; it is proved for general target norm as well. The capacity defect remains present. This construction resolves early zero denominators; it supplies no capacity saturation theorem.

## 4. Repair audit and the remaining arithmetic target

The repository already contained the exact head-repair identity, rank-free directional duality, and sampled-repair contraction. They were reused, not added under new names. This continuation adds `exists_sampled_normals_of_feasible` and `exists_projected_sampled_normals_of_feasible`: one feasible legal head interpolant supplies the normal corrections for every sampled baseline, even with dependent observation rows.

The full squarefree physical head matrix is necessarily singular from length four onward: the existing theorem `QSquarefreeHeadRank.four_head_relation` gives

\[
F(4)-F(3)=F(2)-F(1).
\]

Constant heads satisfy the relation. Thus use compressed observations or feasible normal equations; an inverse of the full head Gram is unavailable.

With p the legal projection of 1, r=1-p, projected observation rows u_i, b_i=inner(h_i,r), and Ud=sum d_i u_i, feasibility gives normal solutions d_0 and d_e. The exact identities are

\[
\|e\|^2=\|e+Ud_e-Ud_0\|^2+\|Ud_e-Ud_0\|^2,
\]

\[
\|1-(p+e+Ud_e)\|^2
=\|r\|^2+\|Ud_0\|^2+\|e+Ud_e-Ud_0\|^2.
\]

Sampling error is not amplified. The needed arithmetic estimate is still
`sup_M norm(U_M d_(0,M))^2 < infinity`, equivalently a head-independent directional bound

\[
\left|\sum_i a_i b_{M,i}\right|^2
\le K\left\|\sum_i a_i u_{M,i}\right\|^2.
\]

The existing `FiniteFeasibleGramRepair.bounded_normal_iff_directional` supplies the rank-free equivalence, including feasibility. Its actual squarefree provider is **Open**. The existing `QSquarefreeHeadRepair.closure_capacity_rh_of_uniform_directional_repairs` is the downstream RH consumer.

## 5. Finite complete-norm certificates

See [the finite certificate report](SquarefreeExactHeadFiniteCertificates20261024.md). Twelve rational candidates were certified for heads 1 through 6 using D={2,3,5,6,7,10,11,13,14}. Minimum-norm proposals yield complete squared-norm upper certificates

\[
0.55753289,\ 0.71420994,\ 0.84830845,\ 0.84830845,\ 0.87806378,\ 0.92312738.
\]

These are rigorous bounds for exhibited candidates, not certified minima. Every finite signed synthesis is squared before summation; exact periodic amplitude bounds enclose the entire infinite tail. Standard-library integer/rational recomputation passed. These are Python arithmetic certificates, not Lean kernel certificates. Six finite heads cannot establish a uniform bound.

The [reproducible certificate bundle](https://chatgpt.com/library?file_id=libfile_680712bd867c8191b84e3feca12757a0&account_id=personal) contains the code, rational coefficients, exact interval endpoints, and report.

## 6. An abstract obstruction to a sampling-only proof

The following countermodel is ordinary mathematics, not newly formalized in Lean. It refutes a general Hilbert-space inference, not RH or any assertion specific to the residue dictionary.

In real ell² on coordinates 0,1,..., put x=e₀, h₀=1, h₁=2 and hₙ=2^(1−n) for n≥2. Let φₙ=hₙe₀−eₙ. The finite dictionaries V_N=span(φ₁,...,φ_N) are nested and independent, and every legal vector is orthogonal to h. Writing S_N=Σ_(n=1)^N hₙ², the projection capacities are S_N/(1+S_N)≥4/5 and tend to 13/16. Set every sampled vector equal to its exact signal: sampling discrepancy is identically zero and normalized optimizer norms are uniformly bounded.

Every initial head is feasible: φ_m/h_m matches x on coordinates 0,...,m−1. But any legal F=Σaₙφₙ matching that head has aₙ=0 for n<m and Σ_(n≥m)aₙhₙ=1. For m≥2, Cauchy–Schwarz and Σ_(n≥m)hₙ²=4^(2−m)/3 imply

\[
\|x-F\|^2=\sum_{n\ge m}a_n^2\ge3\,4^{m-2}.
\]

Thus exact sampling, a positive capacity floor, nested independent dictionaries, and finite head feasibility do not imply bounded head-repair energy. An additional property of the actual arithmetic dictionary is essential.

## 7. What is and is not proved analytically

The handoff's height schedule and the Landau/density provider formalizations were not extended here. The uniform integer Landau formula is stated in Pearce-Crump, arXiv:2111.02756, introduction equations (1.3)-(1.4); the explicit Selberg-type density estimate is in Simonič, arXiv:1910.08274. These references support the analytic input discussed in the handoff, not the missing physical repair-energy bound. They were checked during this continuation.

Priority order:

1. Prove the directional repair estimate for the actual compressed squarefree observations, retaining its signed mixed terms.
2. Use certified larger dictionaries to study the target's normal dual direction and repair energy separately from sampling error; avoid bounding an irrelevant worst inverse eigenvalue.
3. If a uniform bound cannot be obtained, compare the actual growth to existing residual-tail lower bounds and identify the specific arithmetic obstruction.
4. Treat effective analytic sampling constants as a separate task. More accurate zero samples cannot remove the unsampled repair floor.

## 8. Verification scope

The new declarations were developed in serialized Lean server snippets, with no placeholders or new axioms. Final publication is gated by the repository checkpoint, which audits sources and validates the affected modules and reverse dependencies. The published commit and its terminal checkpoint result are the evidence for the saved project; snippet checks alone are not that evidence.

The current result is a **conditional research reduction** toward RH. The uniform complete energy or directional repair bound remains **Open**. No conclusion of unconditional RH is asserted.
