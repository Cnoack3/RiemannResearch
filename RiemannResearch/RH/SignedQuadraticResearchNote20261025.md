# Signed quadratic corrections: manuscript and research log

Date: 25 October 2026. Source: the user's conversation on fixed finite support, signed quadratic corrections, norms, the Q measure, and additional legal directions. The requested deliverables are `Signed_Quadratic_Correction_Research_Note.tex` and its compiled PDF. This record concentrates on the initial signed-correction discussion and records the later Q connection as a separate continuation.

## Status of this entry

This is a documentation-only research log, not a new Lean theorem or a fresh verification of the entire project. It records prior successful development checks, their unresolved analytic hypotheses, ordinary mathematical deductions, and a prioritized formalization agenda. The four salvaged Lean modules below are not part of this documentation-only change. Their earlier aggregate checkpoint timed out; no publication or aggregate acceptance of that source delta is claimed.

Use `C(a)` (typeset as `\mathcal C(a)`) for the signed correction and reserve `Q` for the probability measure. This removes an ambiguity in the initial discussion.

## Fixed-support statement and its exact scope

Let P be a fixed finite set of primes and S the union of the finite towers p^k, 1 <= k <= K_p. The constant frequency 1 is absent. For complex coefficients define

\[
F_a(t)=\sum_{n\in S}a_n n^{it},\qquad A_2=\|a\|_2^2=\sum_{n\in S}|a_n|^2,
\]
\[
L_T(a)=\frac{1}{T}\left(\sum_{0<\gamma\le T}|F_a(\gamma)|^2-N(T)A_2\right).
\]

The zero sum and N(T) count all actual nontrivial zeros with analytic multiplicity. Equal ordinates are not deduplicated. No RH or simplicity hypothesis is imposed in the paper argument.

The external fixed-frequency phase law is

\[
T^{-1}\sum_{0<\gamma\le T}x^{i\gamma}
=-\frac{\Lambda(x)}{2\pi\sqrt x}+O_x((\log T)^{-1}),\qquad x>1.
\]

Here Lambda vanishes unless x is an integral prime power. This law follows from the published Landau formula together with the horizontal-displacement comparison; Landau's formula for x^rho alone does not suffice. Expanding the square and pairing opposite ordered pairs gives

\[
\mathcal C(a)=-\frac1\pi\sum_{p\in P}\log p
\sum_{k<\ell}p^{-(\ell-k)/2}\Re(a_{p^k}\overline{a_{p^\ell}}),
\qquad
L_T(a)=\mathcal C(a)+O_S(A_2/\log T).
\]

The factor 1/pi results from twice the real part of an oriented coefficient 1/(2pi). Between distinct pure prime towers no integral prime-power ratio occurs. General integer supports must retain all such ratios, including 6/3=2. The coefficient error is uniform on each fixed support; a growing support requires quantitative uniformity.

The coefficient norm is Euclidean. The zero-sample quantity N(T)^(-1) sum |F_a(gamma)|^2 is a squared empirical seminorm when N(T)>0. The signed correction is indefinite and is not a norm. The Q norm below is a third, different norm.

## Exact finite identities and improvements

On one tower write r=p^(-1/2), c=log(p)/(2pi), and K_r=(r^{|k-l|}). Then

\[
\mathcal C_p(a)=c(\|a\|_2^2-a^*K_ra),
\]
\[
\mathcal C_p(a)=c\left(\sum_{k<\ell}r^{\ell-k}|a_k-a_\ell|^2
-\sum_{k=1}^{K}\frac{r(2-r^{k-1}-r^{K-k})}{1-r}|a_k|^2\right).
\]

Both endpoint terms and the negative diagonal term are essential. Coefficients (1,1), (1,-1), and (1,i) on two adjacent powers give negative, positive, and zero correction.

The vector (1,-r/2,1) has zero quadratic value. For r=1/sqrt(2), the vector (1,r,0,-r,-1) satisfies K_r a=a and has norm squared 3, a stronger finite matrix-kernel statement. Zero extension need not preserve the kernel property on an infinite tower. These finite cancellation identities have prior successful development checks.

A useful additional paper-level bound follows from the Poisson symbol

\[
a^*K_ra=\frac1{2\pi}\int_{-\pi}^{\pi}
\frac{1-r^2}{1-2r\cos\theta+r^2}
\left|\sum_k a_ke^{ik\theta}\right|^2\,d\theta:
\]
\[
-\frac{2cr}{1-r}\|a\|_2^2\le\mathcal C_p(a)
\le\frac{2cr}{1+r}\|a\|_2^2.
\]

The asymmetric upper bound improves the positive side of a symmetric row-sum estimate. This particular deduction is not newly Lean-verified in this entry.

For K>=2, the inverse identity K_r^(-1)-I = r(rD-A)/(1-r^2), where A is path adjacency and D its degree matrix, gives by congruence the inertia of rI-D^(-1/2) A D^(-1/2). The path thresholds are cos(j pi/(K-1)), j=0,...,K-1. They determine signs and nullity, not the actual eigenvalues of the correction matrix. For prime p the contiguous correction has a kernel exactly when p=2 and K=1 mod 4. K=1 is separately zero for every prime. This general classification remains a paper deduction/formalization target.

For a zero-diagonal residual matrix satisfying |R_ij| <= eta+kappa(u_i-u_j)^2 off diagonal, define A_0=sum |a_i| and V=sum_ij |a_i||a_j|(u_i-u_j)^2. The refined estimate is

\[
|a^*Ra|\le\eta(A_0^2-A_2)+\kappa V,
\qquad
V=2\left(A_0\sum_i|a_i|u_i^2-(\sum_i|a_i|u_i)^2\right).
\]

This keeps the exact zero-diagonal saving. In the zero application u_i=log(n_i), and the required entrywise analytic estimate remains explicit.

For E(T)=sum (beta-1/2)^2, reflection symmetry yields the sharp scalar bound

\[
\left|\sum_{0<\gamma\le T}(x^{\rho-1/2}-x^{i\gamma})\right|
\le4\left(\cosh\frac{\log x}{2}-1\right)E(T).
\]

The corresponding weighted finite quadratic transfer is development-checked. Decay of E(T)/T is a separate analytic input. The manuscript also preserves the exact cosh-square minus sinh-square identity before estimating absolute values.

For fixed nonempty P, M=max P and tower lengths at most K, published uniform analytic inputs plus rational separation and weighted Cauchy give the paper-level budget

\[
|L_T(a)-\mathcal C(a)|\ll_P
\left(\frac{K^3}{\log T}+\frac{M^K(\log T)^2}{T}\right)\|a\|_2^2
\]

in K log M <= log T/(50 log log T). The geometric sum removes an unnecessary extra factor K from the arithmetic remainder. The manuscript details the 1/k and 1/k^2 coefficient profiles separately. These moving-support conclusions are not new formalized zeta theorems.

Normalization uses N(T)=T(log T-c_0)/(2pi)+O(log T), c_0=1+log(2pi). Thus D_T/N(T)=A_2+2pi C(a)/(log T-c_0)+O_S(A_2/log^2 T). Dividing instead by T log T/(2pi) introduces the additional diagonal correction -c_0 A_2/log T.

## Q measure and legal approximation

The separate complete Hilbert norm is

\[
Q(\{n\})=\frac1{\zeta(2)n^2},\qquad
\|f\|_Q^2=\frac1{\zeta(2)}\sum_{n\ge1}\frac{|f(n)|^2}{n^2}.
\]

The real threshold features u_{p,k}(n)=p^(k/2) sqrt(zeta(2)n/(n+1)) 1_{n>=p^k} realize K_r in this space by telescoping. Different primes are not orthogonal; their inner product is sqrt(min(p^k,q^l)/max(p^k,q^l)). A block decomposition requires a direct sum of copies of L^2(Q). Every such threshold feature vanishes at 1, giving constant-target squared error at least Q({1})=1/zeta(2). This ambient realization does not establish legal approximation.

Actual legal atoms are g_d(n)=(n mod d)/d for squarefree d>=2. The trial

\[
F_5=g_2+g_3+g_5-\tfrac15g_6
\]

is exact at 1,...,5. Its complete Q error squared is below 1/25 in the prior checked candidate. Its sharper bound below 7/250 is an ordinary integral-tail argument plus exact rational arithmetic, not a checked Lean result. The trial

\[
F_7=g_2+g_3+g_5-\tfrac{169}{245}g_6+\tfrac47g_7
\]

preserves that head and has an independent rational certificate below 1/50; that certificate remains outside Lean. Numerical values about 0.0278381000911 and 0.0199234471510 are separately labeled numerical.

For squarefree r,d>H the compensated direction h_d=g_d-(r/d)g_r vanishes on 1,...,H. If b=<1-F,h_d>_Q and c=||h_d||_Q^2>0, exact completion gives error = ||1-F||_Q^2-b^2/c+c(alpha-b/c)^2. Multiple directions require the full Gram matrix. Finite gains do not prove that the constant belongs to the closed legal span.

## Formalization ledger

The salvaged initial modules have 24 theorem declarations in total:

| Salvaged module | Representative declarations | Scope |
| --- | --- | --- |
| `Analysis/OffDiagonalGramBounds.lean` | `offDiagonalMass_eq`, `finiteGramErrorPairing_norm_le_offDiagonal_frequencySpread`, `growingGram_offDiagonal_remainder_tendsto_zero` | Exact finite estimates; entrywise provider and asymptotic budget remain hypotheses |
| `Analysis/ActualDirichletPolynomialOffDiagonal.lean` | `sampledSquare_prime_offDiagonal_remainder_bound`, `sampledSquare_landau_error_cosh`, `sampledSquare_signed_limit_of_phase` | Actual zeros and multiplicities; the signed limit explicitly assumes `hphase` |
| `Analysis/PrimeTowerQuadratic.lean` | `primePowerCovarianceSignedEntry_prime_pow`, `signedCorrection_eq_full_boundary`, `threeTower_signed_correction_zero`, `fiveTower_two_fixed`, `fiveTower_normSq` | Arithmetic entries, endpoints, and finite cancellation |
| `RH/QAdditionalLegalDirections.lean` | `additionalTrial_error_completion`, `additionalTrial_one_error_lt_one_twenty_fifth`, `projection_error_lt_one_twenty_fifth` | 18 further declarations for actual legal directions and complete Q bounds |

The successful development job records were reread on 25 October 2026:

- `job_RL-K5JqjycVDTli-6ob1lT4Il0z7hNZt`: terminal `succeeded`, `verified=true`, exit code 0; server verification-operation duration 8.535 seconds; candidate SHA-256 `032c1b34a67afe00641fb9c1f9eb11034626f898875fd8a835693545e2eb379e`.
- `job_PUDQk8CoqjrD6u7yfCDcOuE2F75wfUGU`: terminal `succeeded`, `verified=true`, exit code 0; server verification-operation duration 61.842 seconds; candidate SHA-256 `1e096790f5299fea86e47c4fd76311f56079839874323b9b325fd3ce2bcb704c`.

These durations are not isolated kernel timings. Prior central axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`; they do not discharge local assumptions in theorem types. Wolfram outputs are excluded from formal verification. Unverified continuation candidates are not included among the verified claims.

The recovered aggregate checkpoint `job_6CwbrzNTDWoU0XJ0L6Z43oiCu33xhaxh` is terminal `failed`: its Lake build timed out after 3600 seconds (3671.824 seconds total job elapsed). No aggregate acceptance or publication commit for the four-module delta is asserted. The source was preserved in `Signed_Quadratic_Salvage_20261023.zip`. Its dirty recovery workspace is unchanged by this documentation task.

## Research agenda with completion criteria

1. **Open: analytic phase provider.** Formalize the quantitative density/horizontal-displacement estimate for actual zeros, combine it with the actual Landau theorem, and supply the exact `hphase` and entrywise remainder hypotheses. Completion requires a specialized theorem with no remaining phase-law assumption, followed by checkpoint acceptance.
2. **Open: full prime-tower assembly.** Formalize disjoint indexing, prime-power-ratio classification, and the ordered-to-unordered factor two. Completion requires the displayed finite-prime-set correction with its actual support definition, not just separate entry identities.
3. **Open: weighted moving-support budgets.** Check rational nearest-prime-power separation, A_(1/2)^2 <= (sum n)A_2, geometric sums, and the two decaying coefficient profiles. Completion requires explicit uniform ranges and remainders, not extrapolation from fixed-support convergence.
4. **Open: spectral bounds and classification.** Formalize the general tridiagonal inverse, positive definiteness, congruence, normalized-path spectrum, prime kernel classification, and asymmetric bounds. Separate contiguous towers from sparse principal submatrices.
5. **Open: cancellation stability.** Prove the exact perturbation identity C(a+h)=C(a)+2 Re(h*Ba)+C(h). Quantify the vanishing linear term for Ba=0 and its possible persistence for C(a)=0 alone.
6. **Open: genuine arithmetic application.** Retain all prime-power-ratio edges for the full squarefree coefficient family, together with exact boundaries and signed norm remainders. Identify a uniform growing-support statement stronger than already unconditional fixed-support laws.
7. **Open: Q tail certificates and closure.** Formalize periodic integral-tail certification to upgrade the 7/250 and 1/50 bounds. Then seek a full-norm estimate uniform in growing exact heads, or prove projection errors tend to zero. Finite decreasing numerical errors and ambient threshold completeness do not discharge this goal.

No RH proof, limiting legal-density result, or mathematical novelty claim is made by this note.

## Primary references

- K. Ford, X. Meng, A. Zaharescu, *Simultaneous distribution of the fractional parts of Riemann zeta zeros*, Bull. London Math. Soc. 49 (2017), 1-9. [Author manuscript](https://arxiv.org/abs/1511.06814), Lemmas 1-2. Supports the external uniform analytic inputs.
- K. Ford, A. Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, J. reine angew. Math. 579 (2005), 145-158. [Author manuscript](https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf), (1.6), (3.8). Supports normalization and the phase comparison.
- G. Fikioris, *Spectral properties of Kac-Murdock-Szego matrices with a complex parameter*, Linear Algebra Appl. 553 (2018), 182-210. [Author manuscript](https://arxiv.org/abs/1804.08140), Theorem 2.1(i), (v). Supports the inverse and Poisson symbol; the correction-inertia calculation is a deduction in this note.
- NIST Digital Library of Mathematical Functions, [25.11.1](https://dlmf.nist.gov/25.11.E1). Supports the Hurwitz-zeta notation for complete periodic residue masses.
