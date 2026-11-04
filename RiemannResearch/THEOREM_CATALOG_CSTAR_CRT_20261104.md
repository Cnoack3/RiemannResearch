# Squarefree multipliers, compression, and CRT — Lean status, 2026-11-04

This catalog records the formalization of the final paper argument in the
user-provided `Pasted text(9).txt`. It separates checked results, inherited
results, remaining formalization, and the still-open RH input. No claim of an
unconditional RH proof is made.

## Setting and scope

The concrete application uses the repository's **real** Q Hilbert space:
\(Q(n)=1/(\zeta(2)n^2)\) for positive integers, squarefree legal closure \(V\),
orthogonal projection \(\Pi\), \(Bf(n)=f(n)/(n+1)\), and \(T=2B\).
Write \(r=1-\Pi1\), \(d=f_Q-f_P\), and \(u=B(r+d)-d\).

The arithmetic theorem is more general: it holds over **every
characteristic-zero field**, including \(\mathbb C\). The Hilbert-space
commutant, irreducibility, and cyclicity applications below are explicitly
real. They are not advertised as a completed complex C*-algebra classification.

## Checked arithmetic and operator results

| Module | Main declaration | Exact content |
| --- | --- | --- |
| `NumberTheory/PrimeMultiplierRigidity.lean` | `constant_of_prime_tests` | The prime four-site residue tests force a multiplier to be constant on all positive integers, over any characteristic-zero field. No boundedness or topology is assumed. |
| `RH/QSquarefreeMultiplierRigidity.lean` | `closure_difference_square` | Every legal vector obeys \(\Delta f(n^2)=\Delta f(n)\), \(n\ge2\). |
| same | `constant_of_prime_products_mem` | Actual legal realizations of \(h g_p\) for every prime force physical constancy of \(h\). |
| same | `preserves_closure_iff_constant` | An everywhere-defined physical multiplier preserves \(V\) iff it is constant. Even continuity and linearity need not be separately assumed. |
| same | `exists_prime_leakage` | Every nonconstant everywhere-defined physical multiplier has a prime atom whose image is outside \(V\). |
| `RH/QSquarefreeJointCommutant.lean` | `physical_multiplier_of_commutes_B` | A bounded real map commuting with \(B\) is a literal physical multiplier. The proof uses the adjoint's coordinate vectors and simple eigenspaces. |
| same | `scalar_of_commutes_B_projection` | The real joint commutant of \(B\) and \(\Pi\) consists of scalar operators. |
| `Analysis/SymmetricInvariantProjection.lean` | `starProjection_commutes_of_symmetric_preserves` | Generic real Hilbert-space reduction from symmetric invariance to commutation with the orthogonal projection. |
| `RH/QSquarefreeJointIrreducibility.lean` | `invariant_subspace_trivial` | Every closed common invariant real subspace of \(B,\Pi\) is zero or the whole space. |
| `RH/QSquarefreeJointCyclicity.lean` | `closedWordSpan_eq_top` | For every nonzero vector, the closed real span of all finite \(B,\Pi\) words applied to that vector is the entire Q space. |

The cyclicity proof is direct: the word span is invariant under both
operators, so its closure is trivial or full; it contains its nonzero starting
vector. It does not invoke a double-commutant theorem. A legal vector's word
orbit need not remain legal.

## Stronger compression and displacement bounds

The first omitted squarefree relation is
\(x_0-2x_1-3x_2+4x_3=0\) in normalized \(\ell^2\) coordinates.

| Quantity | Previously available bound | Checked improvement |
| --- | --- | --- |
| \(\langle f,Bf\rangle/\|f\|^2\), on the four-site kernel | Paper: \(59/120\); repository: \(29/59\) | \(983/2000\) |
| \(4\|Bf\|^2/\|f\|^2\), on the four-site kernel | Paper: \(53/54\) | \(39/40\) |
| \(\|d\|^2/\|r\|^2\), \(r\ne0\) | Repository: \(841/7080\) | Strictly less than \(966289/8136000\) |

The first new certificate is
\[
\begin{aligned}
\operatorname{headGap}(983/2000;x,y,z)
={}&\frac{149}{1200}(x-306y/745+408z/745)^2\\
&+\frac{107319}{745000}(y+32266z/35773)^2
+\frac{15271}{14309200}z^2.
\end{aligned}
\]
It is `QFourSiteReciprocalCertificate.headGap_sos_983_2000`.
The complete infinite tail is supplied by the existing
`fourSite_gap_head_tail_exact`; the new application is
`QSquarefreeDisplacementEnergy.B_inner_le_four_site_983_2000`.

`QSquarefreeSquaredCompression.lean` retains the exact identity
\[
\lambda\|f\|^2-4\|Bf\|^2
=\operatorname{squaredHeadGap}(\lambda;x_1,x_2,x_3)
+\sum_{n\ge0}\left(\lambda-\frac4{(n+6)^2}\right)x_{n+4}^2
\]
before applying its rational three-square certificate at \(\lambda=39/40\).
Its main application is `four_B_norm_sq_le_of_mem_closure`.

The improved displacement identity is
\[
\begin{aligned}
\|r\|^2={}&\frac{8136000}{966289}\|d\|^2\\
&+\frac{2000}{983}
 \left\langle r-\frac{2034}{983}d,
 B\left(r-\frac{2034}{983}d\right)\right\rangle\\
&+\left[\left\|r+\frac{4000}{983}d\right\|^2
-\frac{2000}{983}
 \left\langle r+\frac{4000}{983}d,
 B\left(r+\frac{4000}{983}d\right)\right\rangle\right].
\end{aligned}
\]
Both remainders are retained and nonnegative; the first is positive when
\(r\ne0\). Declarations:
`arithmetic_displacement_energy_exact_983_2000`,
`arithmetic_displacement_energy_bound_983_2000`, and
`arithmetic_displacement_energy_strict_983_2000`.

## Exact compression defect and explicit obstruction

`Analysis/CStarCompressionDefect.lean` proves for a self-adjoint idempotent
\(P\) in a C-star ring:
\[
\|PB^*BP-(PBP)^*(PBP)\|=\|(1-P)BP\|^2,
\]
and the defect vanishes iff \(BP=PBP\). This uses the existing ordered
factorization in `LinearAlgebra/CompressionProductDefect.lean`.

`RH/QSquarefreeCompressionLeakage.lean` constructs an actual Q vector for
\(g_2g_3\), checks its four-site functional is \(1/6\), and concludes it is not
legal. The same module proves for \(L=(I-\Pi)(2B)\Pi\):
\[
\|L\|^2\ge\frac1{90\zeta(2)},\qquad
\|\Pi T^*T\Pi-(\Pi T\Pi)^*(\Pi T\Pi)\|
=\|L\|^2\ge\frac1{90\zeta(2)}>0.
\]
Main declarations: `primeProduct23_not_mem_closure`,
`leakage_norm_sq_lower`, `compressionDefect_norm_eq`,
`compressionDefect_norm_lower`, and `compressionDefect_ne_zero`.

## Actual Schur-witness energies

`RH/QSquarefreeSchurWitness.lean` proves, without introducing an inverse
operator,
\[
\langle1,u\rangle
=\langle r,Br\rangle+\|d\|^2-\langle d,Bd\rangle
=\langle r+d,B(r+d)\rangle-\|d\|^2.
\]
It retains exact lower and upper remainder formulas at arbitrary scalar
parameter and obtains
\[
\langle r,Br\rangle+\frac{1017}{2000}\|d\|^2
\le\langle1,u\rangle
\le\frac{983}{2000}\|r\|^2-\frac{1017}{2000}\|d\|^2.
\]
Also \(\langle1,u\rangle>0\iff r\ne0\).
Main declarations: `witness_mean_q_energy`,
`witness_mean_total_energy`, `witness_mean_lower_remainder`,
`witness_mean_upper_remainder`, `witness_mean_bounds`, and
`witness_mean_pos_iff\).

## CRT distance: exact remaining target

The inherited `QCRTCylinderProjection` module already provides
\(a_L=1-\mathbf1_{L\mid n}\), its complete-Q error \(1/L^2\), and the exact
projected error floor. The extension proves
\[
a_L-\Pi a_L=r-(I-\Pi)\mathbf1_{L\mid n}
\]
and
\[
\left|\operatorname{dist}(a_L,V)-\|r\|\right|
\le\|\mathbf1_{L\mid n}\|.
\]
For every cofinal conductor sequence, this proves
\[
\operatorname{dist}(a_{L_j},V)\longrightarrow\|r\|,
\qquad
\operatorname{dist}(a_{L_j},V)\longrightarrow0\iff r=0.
\]
No squarefreeness assumption is needed for these physical cylinder identities.
Main declarations: `cylinder_leakage_exact`,
`cylinder_infDist_error_le`, `cylinder_infDist_tendsto`, and
`cylinder_infDist_tendsto_zero_iff`.

## Conditional RH reduction: the hypothesis remains Open

`RH/QSquarefreePrimeProductCriterion.lean` defines
`DisplacementPrimeProductsLegal` as the exact condition
\[
\forall p\text{ prime},\ \exists f_p\in V,\quad
f_p(n)=d(n)g_p(n)\quad\text{for every physical }n.
\]
It proves:
- `displacement_bounded_of_prime_products`;
- `residual_zero_iff_displacement_prime_products`;
- `riemannHypothesis_of_displacement_prime_products`.

The last conclusion is Mathlib's `RiemannHypothesis`. Its input is explicitly
the displayed prime-product legality condition. **Open:** no unconditional
provider for that condition has been constructed. Cyclicity, ambient CRT
density, and the improved Hilbert bounds do not supply it.

The equivalence with \(r=0\) prevents this premise from being mistaken for an
automatic consequence of the operator algebra. The old physical
boundedness/polylogarithmic displacement approaches likewise retain their
arithmetic regularity obligation.

## Remaining formalization of the paper

These are distinguished from unresolved mathematical RH inputs:

1. The full **complex** statement
   \(C^*(I,B,\Pi)=\mathcal K(H)+\mathbb C\Pi+\mathbb C(I-\Pi)\), its Calkin
   quotient \(\mathbb C^2\), and its strong-operator closure have not been
   assembled as Lean declarations here.
2. The uniform \(C(X)\) ideal equality and full-support measure construction
   on the infinite CRT compact space have not been formalized here. The
   actual physical cylinder error, convergence, and legal-distance criterion
   are checked.
3. A bundled operator
   \(K=D+C^*(I-A)^{-1}C\), its operator inverse formula, and its compactness
   have not been constructed here. The exact actual-witness energies and
   strengthened estimates are checked.
4. The paper's vector-state nonfaithfulness claim has not been formalized
   here. It is not used in any new theorem.

For the standard irreducible-C-star-algebra/compact-operator theorem used in
the remaining paper proof, see Marc Rieffel's Spring 2008 C-star algebra
lectures, notes by Theo Johnson-Freyd, section 15.2:
https://categorified.net/CstarAlgebras.pdf.
This source supports that standard implication, not an RH estimate or a
claim that the full complex classification is already Lean-verified.

## Individual verification evidence

All Lean submissions were serialized, with a 120-second verification limit.
No individual verification submission timed out. Elaboration errors during
development were repaired before the corresponding source was retained as a
proved result. The successful main declarations' `#print axioms` reports
contained only `propext`, `Classical.choice`, and `Quot.sound`.

| Result | Successful server job | Reported elapsed seconds |
| --- | --- | ---: |
| Characteristic-zero constancy | `job_V6ODNPB6XP7n9K2AT1-WLSSAS3U0Vdih` | 4.960 |
| Actual legal prime products | `job_i982yCc3UKuy_gYyTv9DilXx-BrFY1fi` | 7.778 |
| Multiplier-preservation equivalence | `job_yIKIfo09vVVrK2JpgaMW9eqXCIc-IT82` | 15.223 |
| Improved rational certificate | `job_KtAre6DNch8LJ-SvFWyQ71DmMVVABd1L` | 3.472 |
| Complete-Q B form bound | `job_a2ORcOGx4UCk-gaTiSGnSGiKiBR3JOSi` | 28.557 |
| Strict displacement improvement | `job_NyicuY4o7VafvlyvKrDs6IxaWOOngPNI` | 27.228 |
| C-star defect norm identity | `job_mKzFXN7yaFYQtrNYlapwrHgj6gVDLP8E` | 3.654 |
| Actual witness bounds | `job_cLZoPD1Zzkv5kPH9fHeUjSt2Xi8Llo-E` | 26.656 |
| Positive compression defect | `job_YoL1ZlhafKc4YM9z9FlpRp6KM-fQ6k62` | 6.791 |
| Squared compression \(39/40\) | `job_MWrfVz1Eupw2yVx_aTVXmfFVV9I2cKB_` | 10.250 |
| Real joint commutant | `job_nGPT7G0bu45ORz7QNJHgfmZhmxSpmisU` | 8.795 |
| CRT distance criterion | `job_x5P9MhInbi_xb6Q4Z3ephzUweuy4DlkI` | 5.913 |
| Real irreducibility | `job_WP92en-mCQAtwRqcAIUGlNscBipV-jTJ` | 6.845 |
| Real cyclicity | `job_u8aTip8UcYEYOYaAolG_ZzEFLwTlH5pH` | 17.874 |
| Conditional Mathlib RH theorem | `job_CQu2ryTyNY7bUZlS06EHEQCmT3g40aXJ` | 7.522 |

Workspace opening completed separately; its wall duration was not
instrumented. Status polling obeyed the server's 30-second retry interval.
The figures above are server-reported job durations, which can include
import preparation, and are not isolated kernel timing measurements.

Publication additionally requires the final server checkpoint's source audit,
affected-module/aggregate validation, and successful push. The checkpoint
result, rather than these isolated snippet checks, certifies the final
published project source.
