# Unconditional prime-phase Lean continuation

Date: October 11, 2026.

This continuation follows the supplied corrected prime-phase note. It adds no
RH assumption and no numerical approximation. The formal results are exact
arithmetic, finite metric estimates, actual-zero operator identities, and
positive horizontal-defect criteria. Neither an RH proof nor mathematical
novelty is claimed.

## Formalization scope

| Topic | Result in this continuation | Status |
|---|---|---|
| Prime phases | Actual `AddCircle 1` coordinates, continuity, two-prime/family injectivity, irrational prime-log ratio | Unconditional Lean theorem |
| Characters | Actual Mathlib Fourier characters equal the exact exponential with summed prime-log frequency | Unconditional Lean theorem |
| Consecutive phases | Exact lag-boundary identity, concrete quotient-metric estimates, growing lag/frequency convergence under its explicit vanishing budget | Unconditional deterministic Lean theorem |
| Diagonal joint tests | Finite Lipschitz-test error and transfer of a supplied diagonal average | Lean transfer theorem; actual Haar specialization is not supplied |
| Signed Gram expansion | Actual multiplicity-weighted integer-frequency Gram, full signed prime-power main, complete even horizontal series and complementary bad term | Unconditional Lean identity |
| Growing support | Exact equivalence between vanishing signed ordinate residual and vanishing complete horizontal correction under the existing Landau support budget | Lean reduction; correction smallness remains Open |
| Positive horizontal mass | Actual finite-cutoff positivity, monotonicity, cofinal epsilon criterion, signed-correction bound | Unconditional Lean theorem |
| All-zero cosh mass | Unconditional summability, two-sided comparison with E4, vanishing iff Mathlib RH | Unconditional Lean equivalence; vanishing remains Open |
| Fixed-mode analytic remainder | Ford--Meng--Zaharescu's unconditional comparison supports the corrected paper statement | Primary-source audit; not newly formalized here |
| Poisson density and full torus Haar limit | No complete new analytic provider in this continuation | Open formalization work |
| Pareto optimizer transfer | No identification of the ordinate Gram with the Pareto Gram | Open research work |

The note's signed all-cutoff jump criterion is not claimed as a new
Lean-verified theorem here. The formal cutoff criteria below use a positive
mass, and the full RH criterion uses every actual nontrivial zero with both
ordinate signs. This avoids adding an unverified real-axis exclusion premise.

## 1. Actual torus coordinates

`Analysis/PrimePhaseTorus.lean` reuses the existing unique-factorization proof
`RH/PrimePhaseCRT.intPrimeLogRelation`. For

\[
u_p(t)=\left(\frac{\log p}{2\pi}t\right)\bmod1,
\]

two distinct prime coordinates determine every real input exactly. The
actual circle Fourier characters satisfy

\[
\prod_{p\in P}\operatorname{fourier}(k_p)(u_p(t))
=\exp\!\left(it\sum_{p\in P}k_p\log p\right).
\]

This identifies an ordinate, not a zero's real part or multiplicity. The
finite identity does not imply growing-mode Fourier cancellation.

## 2. Exact boundary identity and stronger lag estimates

`Analysis/LagPhase.lean` proves, without even an ordering assumption,

\[
\sum_{j<c}(\eta_{j+\ell}-\eta_j)
=\sum_{k<\ell}(\eta_{c+k}-\eta_k).
\]

Boundary bounds in a window of width \(W\) give \(\le\ell W\). Monotonicity
and the actual quotient-metric contractivity then give

\[
\frac1c\sum_{j<c}
d(\omega\eta_{j+\ell}\bmod1,\omega\eta_j\bmod1)
\le |\omega|\frac{\ell W}{c}.
\]

Both \(\omega\) and \(\ell\) may vary with the sample. The formal convergence
condition is exactly \(|\omega|\ell W/c\to0\), with no RH premise and no
uniform Fourier-asymptotic premise. Using the note's unconditional dyadic
counting law on paper, this permits \(|\omega(T)|\ell(T)=o(\log T)\)
when the retained pair count \(c(T)\) remains comparable to \(T\log T\).
The actual-zero ordered enumeration/counting specialization is not assembled
in this module.

For Lipschitz diagonal tests, Lean retains the full finite error budget
\(KL\ell W/c\) before transferring a separately supplied diagonal-average
limit. It does not assert marginal Haar convergence as an axiom.

## 3. Complete actual signed Gram expansion

Write \(G\) for the actual ordinate Gram, \(L\) for the actual centered Landau
Gram, \(B\) for the full integer prime-power operator, and
\(a=T/(2\pi N(T))\). The existing actual Landau residual is

\[
R_L=L-I+aB.
\]

`Analysis/ActualPhaseGramExpansion.lean` defines \(R_P=G-I+aB\) and proves

\[
R_P=R_L-(L-G),
\]

and, for every admissible good/bad mask,

\[
G=I-aB+R_L-C_{\rm even}-C_{\rm bad}.
\]

The complete convergent even series is \(C_{\rm even}\); every complementary
bad-copy term remains in \(C_{\rm bad}\). The bound retains the smaller good
Gram and the full bad correction:

\[
\|R_P\|\le\|R_L\|+
\frac{\|G_{\rm good}\|}{2}
\bigl[\cosh(\delta\log d)-1\bigr]+\|C_{\rm bad}\|.
\]

The already established actual Landau provider discharges \(\|R_L\|\to0\)
when

\[
\frac{d(T)^{7/2}}{(T+3)\log(T+3)}\to0.
\]

Under this elementary support budget, the new checked equivalence is

\[
\boxed{\|R_P\|\to0\quad\Longleftrightarrow\quad\|L-G\|\to0.}
\]

The signed covariance main is retained in the definition of \(R_P\). This
statement alone does not prove \(G\to I\), a physical frame bound, or RH.
It isolates the complete horizontal-correction provider instead of silently
replacing full-zero evaluations by ordinate phases.

## 4. A positive, convergent horizontal detector

`Analysis/ActualZeroCoshMass.lean` first keeps the unnormalized positive
cutoff mass

\[
H_T(u)=\sum_{0<\gamma\le T}m_\rho
\bigl[\cosh(u(\beta-\tfrac12))-1\bigr].
\]

It is monotone in \(T\), each individual zero's charge is bounded by it, and
the complete signed correction is bounded in norm by \(H_T(u)\). For
\(u\ne0\), arbitrarily small mass at arbitrarily high cutoffs is equivalent
to every actual positive-ordinate zero lying on the critical line. This is
an **unnormalized** criterion: division by \(N(T)\) loses the persistence of
a fixed off-line zero's contribution.

For a direct criterion involving Mathlib's full RH statement, retain all
actual nontrivial zeros and define

\[
\mathcal C(u)=\sum_\rho
\frac{m_\rho[\cosh(u(\beta_\rho-\tfrac12))-1]}
{(1+\gamma_\rho^2)^2}.
\]

Existing actual reciprocal-square summability supplies convergence. Lean
proves the quantitative comparison

\[
\boxed{\frac{u^2}{2}E_4\le\mathcal C(u)
\le u^2e^{|u|/2}E_4,}
\qquad
E_4=\sum_\rho\frac{m_\rho(\beta_\rho-\tfrac12)^2}
{(1+\gamma_\rho^2)^2},
\]

and

\[
\boxed{u\ne0\quad\Longrightarrow\quad
\bigl(\mathcal C(u)=0\Longleftrightarrow\mathrm{RH}\bigr).}
\]

Thus this cosh detector is quantitatively comparable to the existing E4
target. It does not bypass that target: proving \(\mathcal C(u)=0\), or
\(E_4=0\), remains Open.

## 5. Remaining analytic work and provenance

The fixed-mode \(O((\log T)^{-2})\) remainder in the corrected note is
unconditional on paper. The relevant primary source is Ford, Meng and
Zaharescu, *Simultaneous Distribution of the Fractional Parts of Riemann Zeta
Zeros*, Lemma 2, [arXiv:1511.06814](https://arxiv.org/pdf/1511.06814).
Together with fixed-x Landau, its unnormalized comparison bound is

\[
O\!\left(\frac{T(\log x)^2}{\log T}
+\frac{T}{(\log T)^{10}}\right)
\]

in the source's explicit range. The formalization must still discharge this
horizontal comparison/zero-density input. Existing actual Landau contour and
prime-power operator estimates already provide the other side; recreating
them is unnecessary.

The next useful mathematical work is a provider for the **actual complete
horizontal correction** in the intended growing-support regime, followed by
an explicit connection to the actual Pareto optimizer residual. Phase-only
positivity or equidistribution does not supply that connection.

All new modules are exported from `RiemannResearch.lean`. No finite computation,
RH-dependent analytic estimate, project-local axiom, or admitted proof is used.

## 6. Verification and exact publication payload

The four new modules contain 48 public theorems. The combined-source check
`job_SRilZcKaC1dyhWSNCE8esW1h79LOKs8g` succeeded with `verified=true`.
Seven key theorem axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The exact persisted source and aggregate exports then passed
`lake build RiemannResearch --quiet` in server job
`job_DYBz4hksIY8ksgRTUEv9nnCJ2ge0rHoa` (state `succeeded`). All four
persisted Lean files were subsequently compared with their reviewed source
and matched exactly. Only documentation changed after that successful build.

The proposed publication consists of exactly these seven repository paths:

| Path | Change |
|---|---|
| `RiemannResearch/Analysis/LagPhase.lean` | New module: boundary identities, circle bounds, and diagonal-test transfers |
| `RiemannResearch/Analysis/PrimePhaseTorus.lean` | New module: actual circle coordinates, injectivity, and exact characters |
| `RiemannResearch/Analysis/ActualPhaseGramExpansion.lean` | New module: complete signed Gram identity and residual equivalence |
| `RiemannResearch/Analysis/ActualZeroCoshMass.lean` | New module: positive cutoff mass and convergent all-zero detector |
| `RiemannResearch/RH/PrimePhaseLeanContinuation20261011.md` | This continuation and its explicit open obligations |
| `RiemannResearch.lean` | Add imports for the four modules |
| `RiemannResearch/THEOREM_CATALOG.md` | Add a status entry for these results and verification |

Destination: branch `main` of
[`Cnoack3/RiemannResearch`](https://github.com/Cnoack3/RiemannResearch),
prepared against base commit `0f4dae4e7eaa8766ec5346fe1eddd03c707036b3`.
An initial publication attempt was rejected by automatic approval review.
After publication was authorized, checkpoint job
`job_f7aL0T5v6TrOx_x-esU5iMOl4cHFsFv8` created the unpublished source commit
`66a6e9908147803efade13e93be914137439748f`, but failed while incorporating
newer `main`: the aggregate imports and theorem catalog had cherry-pick
conflicts. The earlier successful server build remains evidence for that
original source snapshot, not for the later combined recovery.

The four modules and this continuation have now been recovered for integration
in workspace `ws_hpqrnJbaPc0ZNyhBW2ywJ9K2VPm0t9rb`, against base
`415a2c777f274bec07b7a19fadf089640c31f703`. The combined source, imports, and
catalog require a successful final server checkpoint before publication can
be reported. This recovery status does not assert that checkpoint success.
