# Independent audit of moving-remainder commit b306d93

Audit date: October 1, 2026.
Repository: Cnoack3/RiemannResearch.
Pinned commit: b306d93d1b99dc12057a048384c747423987686d.

**Verdict: safe to use as a verified conditional research base for the six audited declarations.** Both new source files compiled independently, and a combined fresh-source check reproduced all six declarations and their foundation audits. The conditional RH application keeps all four substantive obligations explicit. The full signed screening contribution and zero-energy cases are retained. No change to the six Lean proofs is required.

This verdict covers the new modules and the traced application path. It does not certify a new full-project build or a GitHub CI run. The report's arithmetic deductions and countermodel are ordinary mathematical arguments, and its floating-point Gram calculations are numerical diagnostics.

## Verification evidence

An isolated verifier workspace opened directly at the pinned commit, with a clean Git status and HEAD = origin/main = b306d93. Its restored dependency environment matched the pinned toolchain and manifest. The local execution container did not have Lean on PATH; execution below used the connected Lean Verifier.

- Lean: leanprover/lean4:v4.33.0-rc2.
- Mathlib manifest commit: 51e6992efd06126df61a496bebf8f49482a4e129.
- PrimeNumberTheoremAnd manifest commit: a5154676af9aa3095150ee410cdda80555aa0642.
- Dependency environment key: a27aeef7b57d4ad0f88934b9.

| Independent check | Result | Time | Job receipt |
|---|---|---:|---|
| Full source check: Analysis/MovingOrthogonalEnergy.lean | Verified, exit 0; no diagnostics | 7.819 s | job_kuUPiTgF9Df54b5fk1loiTy9PCpCxRfs |
| Full source check: RH/ParetoMovingRemainderTransfer.lean | Verified, exit 0; no diagnostics | 4.630 s | job_d-JynhlU8-zU64gCqwX0l5WeOsbCccRK |
| Expanded signature, dependency, definition, and zero-denominator checks | Verified, exit 0 | 3.612 s | job_voTBcjAmLO52rRgvjBN2uUUVjUTeyMum |
| Combined exact new source bodies and six axiom audits | Verified, exit 0; complete untruncated axiom output | 3.795 s | job_97ZsJpevKFSsbFhTrUI4ET_ryydo6lBN |

The combined check copied the pinned source bodies, placed their imports at the beginning, and closed their file-local noncomputable sections between the bodies. It did not import either new module as a substitute for checking its proof body. Its code SHA-256 was 33b687f2a716b26e31efdbc2cc1d538338577a027029318fa94ea257ac370f7b.

| New source | Lines | Git blob | Checked source SHA-256 |
|---|---:|---|---|
| Analysis/MovingOrthogonalEnergy.lean | 128 | a3c898f842f03e29b31503740acee5fb582dcce0 | 5d6b889801ab7670a3db8fd207238098df5ff08ba5b59e6d693f0e9dd7706926 |
| RH/ParetoMovingRemainderTransfer.lean | 64 | 2b2916dea6e01d9014c2287a7d1522c423bc89f3 | 4cb42932adc8af77c71cd66a9bd8afcfab99b98aa4d3e99703ecdaf421bdad9e |

The source hashes matched the independent file-check receipts. Neither new file contains sorry, admit, axiom, unsafe, or an exact import Mathlib. The read supporting source files also contained no such proof escape. The transitive axiom audit, rather than a source word scan alone, supplies the decisive foundation evidence.

One initial auxiliary audit snippet omitted the IntegerDPP namespace when naming tailInnovation_pairwise_orthogonal. It exited 1 with Unknown constant at that audit command. The corrected expanded check succeeded. This was an audit-harness name-resolution error; neither pinned source file was changed. The successful combined check provides complete independent output for all six requested foundation audits.

A fresh GitHub combined-status call returned statuses = []. The commit-workflow wrapper returned workflow_runs = [], but its documented scope is PR-triggered runs on the first page. These responses supply no CI success verdict and do not establish that every possible Actions trigger has no run.

## The six declarations

All six fresh-source axiom outputs were exactly:

    [propext, Classical.choice, Quot.sound]

There was no sorryAx or project-local axiom in these dependencies. Local hypotheses remain visible in the declaration types and are not listed by #print axioms.

| Declaration | Exact content and assumptions | Audit finding |
|---|---|---|
| maskedPairingVector_norm_le | An orthonormal finite family v, a vector x, and an arbitrary finite mask s give norm(masked pairings) <= norm(x). | Finite Bessel controls the unmasked square sum; masking deletes only nonnegative squares. Orthonormality is explicit. |
| finite_masked_moving_bound | Orthonormal v and the exact representation R(i) = x + sum_k indicator(i in s(k)) d(k) give norm(pairingVector v R) <= norm(x) + sum_k norm(d(k)). | The signed vector decomposition is proved before triangle inequalities. Every increment and mask remains in hR. |
| moving_pairing_prefix_bound | For orthonormal v, sum_(j<N) inner(v(j),R(j))^2 <= (norm(R(0)) + sum_(i<N) norm(R(i+1)-R(i)))^2. | Telescoping uses precisely the increments i<j. The displayed bound includes one unused final nonnegative increment. N=0 is also covered. No variation premise is needed for this finite bound. |
| moving_pairing_summable | Orthonormal v and Summable(i -> norm(R(i+1)-R(i))) imply Summable(j -> inner(v(j),R(j))^2). | Absolute total variation is explicit. Boundedness, convergence, or summability of squared increments is not substituted. The real summability argument does not require completeness of the ambient inner-product space. |
| primeMovingCRTAmplitude_sq | The normalized actual signed moving CRT amplitude squares to primeBlockMovingCRTContrastCertificate. | The actual contrast energy is nonnegative; Real.sq_sqrt is used with that proof. No nonzero-denominator premise is introduced. |
| riemannHypothesis_of_moving_remainder_model | Orthonormality, model square-nonsummability, the exact full amplitude-minus-model identity, and summable absolute variation imply RiemannHypothesis. | All four obligations are explicit arguments. The proof assembles the generic summability bound, complete model-square transfer, and the existing actual CRT contradiction. It provides none of these arithmetic obligations itself. |

The target RiemannHypothesis was printed and is the actual zeta statement:

    forall s : Complex, riemannZeta s = 0 ->
      (not exists n, s = -2 * (n + 1)) -> s != 1 -> s.re = 1/2

The printed Lean definition includes the expected natural-number coercions in the trivial-zero condition.

## Conditional RH dependency path

Write c_j = primeMovingCRTAmplitude j f. The theorem's substantive premises are exactly

\[
(v_j)\text{ orthonormal},\qquad
\neg\operatorname{Summable}(j\mapsto m_j^2),
\]
\[
c_j-m_j=\langle v_j,R_j\rangle\quad\text{for every }j,\qquad
\operatorname{Summable}(j\mapsto\|R_{j+1}-R_j\|).
\]

Their roles are as follows.

1. moving_pairing_summable supplies summability of the **complete** discrepancy squares.
2. If the actual certificates were summable, primeMovingCRTAmplitude_sq would make c_j^2 summable.
3. WeightedScalarEnergy.model_square_summable, with weight 1, would make m_j^2 summable, contradicting hmodel.
4. riemannHypothesis_of_movingCRTContrast_not_summable transfers this actual nonsummability through the fixed-base summability equivalence.
5. The ordinary contrast certificate is bounded by the complete prime block variance. The dyadic block lower-bound theorem transfers its nonsummability to angular increments.
6. The angular capacity identity and nonnegative retained terms give tail-capacity divergence; riemannHypothesis_of_tailCapacity_tendsto concludes RH.

Relevant types were independently checked. Foundation audits also checked model_square_summable, the moving CRT endpoint, the tail-capacity endpoint, innovation orthogonality, the exact base-plus-cross-Gram row identity, and the canonical certificate provider. They use the same three standard foundations.

The traced capacity identities retain initial capacity, prime mean mismatch, contrast remainders, historical head-to-block drift, and composite gains. Sufficient lower-bound arguments use their explicit nonnegativity; they do not replace those complete equalities with a claim that these terms vanish.

**Open:** an independently controlled arithmetic choice of f, m, v, and R satisfying all four premises. Describing a remainder as a Hilbert vector does not prove its representation or variation bound. Existing orthogonality of innovations does not, by itself, discharge the hypotheses for a chosen arithmetic model.

## Full inverse-Gram screening and zero-energy cases

The source chain is concrete.

- FiniteHilbertGram.inverseCoeff is (gramEquiv hv).symm applied to the full cross vector.
- FiniteGramScreenedCapacity.screened is the new vector minus the synthesis of **every** old vector with those inverse-Gram coefficients.
- IntegerDPPSchur.tailInnovation uses that screened vector, and schurSigma is its full norm square.
- factorialPrimeCrossGram(n,m) pairs this screened innovation with the actual factorialPrimeRefinement(m).
- factorialPrimeError_eq_base_add_crossGram keeps the fixed factorial-2 base and all m<n signed columns.
- primeBlockMovingCRTContrastPairing contains all of those earlier columns, after separating the fixed base.

Thus the inverse action, old correlations, actual Schur weights, and signed row sums are retained. The moving object is not a raw observation row or a fixed finite column packet. The exact identity is

\[
P_{\rm total}=P_{\rm moving}+P_{\rm base},
\]
\[
\frac{P_{\rm total}^2}{E}
=\frac{P_{\rm moving}^2}{E}
+\frac{2P_{\rm moving}P_{\rm base}}{E}
+\frac{P_{\rm base}^2}{E}.
\]

This is primeBlockContrastCertificate_eq_movingCRT_split. Fixed-base Bessel summability supports the summability equivalence; the signed mixed term remains in the finite equality.

For the report's raw model, the full screening identity is

\[
\gamma_p=\Gamma_{<p}^{-1}\Gamma_{<p,p},\qquad
T_p=q_p-\gamma_p^\top q_{<p},
\]
\[
B_p=\eta_p-T_p,\qquad
y_p-m_p^{\rm raw}
=\frac{T_p-q_p}{a_p}
=-\frac{\gamma_p^\top q_{<p}}{a_p}.
\]

The moving inverse-Gram term has not been discarded.

The contrast energy E can be zero. Lean's real division is total: x/0 = 0 and sqrt(0) = 0. The expanded audit successfully checked that both c_j and its certificate are zero when E=0. Weighted Cauchy–Schwarz also forces the pairing numerator to be zero because the weights are nonnegative and the test has zero weighted energy. In contrast, every arithmetic Schur pivot sigma is strictly positive by the proved linear independence of the actual tail atoms.

Source-balanced tests, their regression identities, and the inherited split identities also account for zero source masses or empty children. No blanket field cancellation at a zero energy is used.

At a zero-energy block hrep still requires -m_j = inner(v_j,R_j). Such blocks cannot manufacture a divergent model compatible with the variation and orthonormality hypotheses. An arithmetic construction of unit block tests must explicitly handle zero tests; normalizing a zero vector does not establish orthonormality.

## Separate audit of the report's ordinary arguments

| Report item | Independent assessment | Verification status |
|---|---|---|
| Conditional inverse-pivot bound | Correct under negated RH and the actual tail-certificate observations; the old projection is retained. | Ordinary proof. Existing dual-norm and certificate ingredients are formalized; the new specialized inverse-pivot deduction is not one of the six new Lean theorems. |
| Full uncentered and centered block-error consequence | Correct with the stated stronger **rowwise** representation and mutually orthogonal innovation blocks. | Ordinary block-projection proof. The committed generic infinite theorem is the scalar orthonormal consequence. |
| Gram and signed-gap numerical table | Reproduced by independently evaluating the complete pinned Wolfram listing. | 35-digit floating-point diagnostics; no interval certificate or asymptotic divergence proof. |
| Abstract countermodel | Correct; the all-index algebra was checked independently and the finite symbolic diagnostics reproduced. | Ordinary exact Hilbert construction; not the arithmetic residue dictionary and not newly Lean-formalized. |

### Inverse-pivot proof

Negated RH supplies an actual tail certificate z: if no such certificate existed, the checked riemannHypothesis_of_no_tailCertificate would imply RH. Its first coordinate is zero and its observations are inner(t_d,z)=1/d. Let C=norm(z)^2.

For an odd prime p, the report's u_p is the negative of primeDualRepresenter. Its support is {1,p-1,p}, its exact norm square is 2p^2+2, and

\[
\langle g_d,u_p\rangle
=g_d(1)+g_d(p-1)-g_d(p)
=\mathbf1_{\{d=p\}}.
\]

The residue step identity and primality justify the last equality for every d>=2. Removing the first site gives inner(t_d,u_p)=indicator(d=p)-1/d, so inner(t_d,u_p+z)=indicator(d=p). Pairing the fully screened innovation h_p with u_p+z therefore gives exactly 1; every old projection term pairs to zero. Cauchy–Schwarz yields

\[
\frac1{\sigma_p}\le\|u_p+z\|^2
=2p^2+2+2\langle u_p,z\rangle+C
\le4p^2+4+2C.
\]

The signed mixed term is retained before the estimate. Positivity of sigma is available. The finite version requires a compatible finite minimum through conductor p, not merely through the old conductors.

With q_p=Q/p^2, Q=pi^2/(pi^2-8), the displayed bound implies summability of q_p^2/sigma_p by ordinary p-series comparison. Bessel supplies summability of B_p^2/sigma_p for the fixed base. Hence the report's **raw-model deviation from -1** has finite energy with actual weights under failure. This is a necessary failure restriction. It does not establish summability of the full moving screening error, or divergence of a companion model.

### Full-centered-energy deduction

Under the report's rowwise identity a_p epsilon_p=inner(R_j,h_p), normalized innovations in the disjoint blocks are orthonormal, and

\[
D_j=\sum_{p\in B_j}\frac{a_p^2}{\sigma_p}\epsilon_p^2
=\|\Pi_jR_j\|^2.
\]

The mutually orthogonal block projections satisfy Bessel for each fixed vector. The exact telescoping decomposition in their finite direct sum, followed by Minkowski, gives

\[
\sum_{j=0}^{J}D_j
\le\left(\|R_0\|+\sum_{i=0}^{J-1}\|R_{i+1}-R_i\|\right)^2.
\]

Finite variation gives a finite total D budget. The weighted identities retain the parent mean square, both child centered scatters, and the split-gap error square, so the full centered error budget and the contrast error budget are both finite. The corrected strengthening is valid. A scalar contrast representation alone would not establish this stronger rowwise premise.

### Exact abstract countermodel

Put S_n=n(n+1)/2 and

\[
h_n=\sqrt{S_{n-1}/S_n}\,e_n
-\sqrt{n/(S_{n-1}S_n)}\sum_{k<n}\sqrt{k}\,e_k.
\]

The norm is 1. For m<n, the weighted old vector sum_(k<n) sqrt(k)e_k is orthogonal to h_m: its two terms cancel exactly. This proves orthogonality for all indices, independently of the finite matrix check.

For D_n=sqrt(n)e_n, Z_n=sum_(k=2)^n D_k, and z=-e_1,

\[
a_n^2=\frac{n(n-1)}{n+1},\qquad
\eta_n=\langle Z_n,h_n\rangle=\langle z,h_n\rangle
=\frac2{\sqrt{(n-1)n(n+1)}}.
\]

The complete earlier correction is eta_n-a_n. Since

\[
\eta_n^2
=\frac2{(n-1)n}-\frac2{n(n+1)},
\]
\[
\sum_{n=2}^{N}\eta_n^2=1-\frac2{N(N+1)},\qquad
\sum_{n=2}^{\infty}\eta_n^2=1,
\]

growing positive sources coexist with finite fully screened energy. The packets themselves have nonsummable variation. The countermodel satisfies no missing arithmetic-provider hypothesis merely because it has orthogonal refinements. It neither disproves RH nor refutes the conditional transfer theorem.

## Independent Wolfram reproduction

The complete code block in MovingRemaindersDiagnostics20261001.md at the pinned commit was submitted to Wolfram Language without formula changes. It returned:

- zero numerical residual for Gamma(2,2)=(log(2)-1/2)/4;
- all six displayed prime rows matching the report;
- all 114 finite prime-dual pairing residuals exactly zero and the exact norm residual zero;
- the 8-by-8 h-Gram matrix exactly equal to the identity;
- all eight survivor residuals exactly zero;
- eta_n/a_n = 2/[n(n-1)];
- infinite energy sum exactly 1 and the displayed finite telescoping sum.

| j=3 split quantity | Independently reproduced value |
|---|---:|
| Prime children | {11,13}, {17} |
| kappa | 3.8808522087020866 |
| Actual signed gap | 0.1736092848931204 |
| Raw-model signed gap | -0.01168082266507527 |
| Actual contrast energy kappa G^2 | 0.1169695988751883 |
| Complete contrast-error energy | 0.1332390633511011 |
| Raw-model gap energy | 0.0005295097550900916 |

The digamma formula sums every site in each residue class. Indeed

\[
\sum_{j\ge0}\frac1{(r+jL)(r+jL+1)}
=\frac{\psi((r+1)/L)-\psi(r/L)}{L}.
\]

Summing r=1,...,L retains the full physical tail; subtracting 1/(2de) removes exactly the first-site Gram contribution. The LinearSolve calls use the entire old Gram block and its signed cross vector. Repository row n means physical conductor n+3, so the j=3 prime window is correctly indexed.

These finite floating-point results do not establish an infinite-series lower bound. The exact finite symbolic checks are consistent with the separate all-index paper proofs. The report's contextual preprint assessments were not re-audited as independent literature claims; they are not arithmetic premises in the six-theorem proof path.

## Decision for the next research base

Use b306d93 as a checked base for the generic moving Bessel–Minkowski bounds, the exact amplitude-square identity, and the explicitly conditional RH reduction. Keep the four arithmetic obligations Open. Classify the inverse-pivot and block-energy deductions as ordinary proved arguments under their displayed assumptions, and the Wolfram Gram table as diagnostics.

The independent work performed targeted source compilation and kernel elaboration of the new proof bodies. It did not perform a fresh full lake build RiemannResearch, compile every source ancestor from scratch, or obtain GitHub CI success. Restored dependency artifacts were reused in the exact pinned environment.

A reproducible six-foundation audit is:

~~~lean
import RiemannResearch.RH.ParetoMovingRemainderTransfer
open RiemannResearch.Analysis.MovingOrthogonalEnergy
open RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

#print axioms maskedPairingVector_norm_le
#print axioms finite_masked_moving_bound
#print axioms moving_pairing_prefix_bound
#print axioms moving_pairing_summable
#print axioms primeMovingCRTAmplitude_sq
#print axioms riemannHypothesis_of_moving_remainder_model
~~~
