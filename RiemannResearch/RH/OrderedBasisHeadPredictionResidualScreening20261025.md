# Residual-screened onset energy and signed head prediction

Continuation of the supplied head-boundary/tail-response handoff, 25 October 2026.

**Conclusion: RH is not proved.** The ordered evaluation basis, exact head prediction and low/high-onset response split, and a stronger residual-screened weighted Bessel estimate have been developed. The uniform arithmetic provider remains Open. Numerical results below are diagnostics, not certificates.

Incoming published baseline: `696712b892ece6346a84fd956a635487432e3109`.

## Formal development and source map

- `RH/QSquarefreeCorrectionKernel.lean`: `inner_kernel_of_stage` identifies the projected evaluation pairing on actual stage vectors.
- `RH/QSquarefreeEvaluationBasis.lean`: evaluation kernels through physical site N+1 span the actual stage, by the existing exact-head injectivity theorem; Gram–Schmidt innovations lie in that stage, vanish before their physical pivot, and retain zero pivots as zero vectors. The nonzero subtype yields an actual `orderedBasis`. `stage_synthesis` and `movingCorrection_physical_synthesis` preserve exact signed reconstruction. `movingCorrection_sq_le_diagonal` is the handoff's R1 diagonal estimate. `movingCorrection_sq_le_screened_diagonal` improves it by the explicit residual-screening gain, for any finite layer cutoff M>=N+1.
- `RH/QSquarefreeHeadPrediction.lean`: `headKernelSpace_eq` identifies the span of the first H kernels with V_N intersect C_{N,H}-perp. `headResponse_eq_projection` identifies the existing minimum-norm extension. Signed predictor coefficients exist without invertibility; `prediction_normal`, `response_prediction`, and `response_prediction_error_bound` retain the full Gram equations and tail error.
- `RH/QSquarefreeResponseBasis.lean`: `headResponse_synthesis` and `tailResponse_synthesis` identify the low/high-onset expansions with the existing actual response split.
- `Analysis/TriangularWeightedBessel.lean`: `layered_screened_bessel` subtracts the rank-one screening energy in each layer, including zero screening vectors.
- `RH/QTriangularWeightedBessel.lean`: `reciprocal_onset_screened_bessel` and `movingCorrection_onset_screened_bessel` apply this to complete Q tails and the actual residual.

The basis construction uses the Mathlib Gram–Schmidt API, specifically the span, orthogonality, normalization, and inverse-triangular identities documented at https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.html. The actual stage application and the screening refinement are direct developments from the user's handoff; no novelty claim is made.

`QSquarefreeResponseBasis.orderedVector_eq_zero_of_nonsquarefree` additionally proves exact arithmetic sparsity: a nonsquarefree physical pivot m>=2 has zero ordered vector. At an onset, its omitted Mobius coefficient is minus its physical value, which must vanish; head/tail orthogonality then forces the vector itself to vanish. This does not bound the norms of the surviving squarefree pivots. The isolated server audit `job_93X0XMDXg9dkM786zDmdxSmIsOskqzsj` passed in 47.561 reported seconds with only the standard foundational axioms.

R1 and R2 now have concrete source implementations. R3/R4's uniform arithmetic estimates and the original B/KPS/KF providers remain Open. The infinite odd-radical projection remains at its inherited status.

## Actual quantities

Write `Z = zeta(2)`, `Q(n)=1/(Z n^2)` for physical integers `n>=1`, and `Bf(n)=f(n)/(n+1)`. Let `V_N` be the actual span of squarefree atoms `g_d(n)=(n mod d)/d`, with `2<=d<=N+1`. Put

\[
r_N=1-P_N1,\quad \varepsilon_N=\|r_N\|_Q^2,
\quad b_N=P_NBr_N.
\]

All norms and moments here retain the complete infinite Q tail.

Let `u_i` be a finite orthonormal family in `V_N` with physical onsets `s_i`, so `u_i(n)=0` for `n<s_i`. Zero vectors can instead be retained using the norm-at-most-one interface. Set `a_i=<b_N,u_i>_Q=<Br_N,u_i>_Q`.

## The residual supplies an additional Bessel direction

Because `r_N` is orthogonal to every legal stage direction, one can adjoin `r_N/||r_N||` at physical onset 1 to the existing onset-weighted Bessel family. For nonzero residual this yields

\[
\sum_i(s_i+1)^2a_i^2+
\frac{4\langle Br_N,r_N\rangle_Q^2}{\varepsilon_N}
\le\varepsilon_N.
\]

Since `||r_N||<=1`, the division-free weaker form is

\[
\sum_i(s_i+1)^2a_i^2+4\langle Br_N,r_N\rangle_Q^2
\le\varepsilon_N.
\]

This retains actual residual coupling rather than replacing all available energy by `epsilon_N`.

For the stronger layered estimate use zero-based coordinates, and let

\[
T_k=\|\operatorname{tail}_k r_N\|^2,\qquad
C_k=\langle B\operatorname{tail}_k r_N,
                  \operatorname{tail}_k r_N\rangle,
\qquad \delta_0=4,\quad\delta_k=2k+3\ (k\ge1).
\]

Every family member with zero-based onset at least `k` is also orthogonal to `tail_k r_N`. Adjoining the normalized residual tail in each layer gives, for all onsets less than `M`,

\[
\boxed{\quad
\sum_i(s_i+1)^2a_i^2+G_{N,M}\le\varepsilon_N,
\qquad G_{N,M}=\sum_{k<M}\delta_k\frac{C_k^2}{T_k}.
\quad}
\]

The summand is zero when `T_k=0`; then `C_k=0` as well. Every term is nonnegative. For the actual ordered evaluation-kernel basis, any `M>=N+1` is permitted by the formal theorem.

There is an exact identity behind the inequality. Let `U_k` be the span of the basis vectors with onset at least `k`, `q_k=tail_k Br_N`, and

\[
E_k=\|q_k\|^2-C_k^2/T_k-
\sum_{i:\,s_i-1\ge k}a_i^2\ge0.
\]

For M>=1 and an orthonormal family,

\[
\sum_i(s_i+1)^2a_i^2+G_{N,M}
+\sum_{k<M}\delta_kE_k+R_M=\varepsilon_N,
\]

where

\[
R_M=\sum_{j\ge M}
\left(1-\frac{(M+1)^2}{(j+2)^2}\right)|(r_N)_j|^2\ge0.
\]

This full finite identity, the infinite-layer limit, and the complete-gain truncation estimate below are ordinary mathematical consequences recorded for further work; they have not been separately formalized here. The verified inequalities use complete infinite Hilbert tails even though the number of layers is finite.

## The remaining arithmetic estimate

With exact stage synthesis `b_N=sum_i a_i u_i`, define

\[
D_N(n)=\sum_i\frac{|u_i(n)|^2}{(s_i+1)^2}.
\]

Weighted Cauchy--Schwarz now gives the sharper physical estimate

\[
|b_N(n)|^2\le(\varepsilon_N-G_{N,M})D_N(n),\qquad M\ge N+1.
\]

The meaningful open provider is therefore

\[
\boxed{\exists C\ge0\ \forall N,n,\quad
1\le n\le N\Longrightarrow
\exists M\ge N+1,\quad (\varepsilon_N-G_{N,M})D_N(n)\le C^2.}
\]

It is enough to prove this screened product bound, or directly bound the actual signed head extension `h_{N,floor(n/2)}(n)`. No uniform bound on either quantity has been obtained in this research note.

The cutoff `N+1` is not compulsory. The same finite theorem permits any `M>=N+1`: layers beyond the last basis onset have an empty basis subfamily, but their residual-screening gain remains nonnegative. Thus one can pursue the weaker target with a suitable `M=M(N,n)` or with the complete gain `G_N^infinity`. The ordinary complete-gain tail estimate is

\[
0\le G_N^\infty-G_{N,M}\le T_M.
\]

Indeed, Cauchy gives `C_k^2/T_k<=||tail_k Br_N||^2`, and summing the layer increments from `M` onward is bounded by `||tail_M r_N||^2`. This bounds omitted gain; the remaining physical product still requires an arithmetic estimate.

A tempting factor-one-quarter bound does not follow from residual orthogonality alone. For example in unweighted coordinates supported on physical sites 1,9,99, take `r=(1,1,1)/sqrt(3)`, `u1=(2,-1,-1)/sqrt(6)`, `u2=(0,1,-1)/sqrt(2)`. The weighted coefficient energy is `3499/11250>1/4`. The exact three-coordinate value was checked with Wolfram; it is not part of the Lean development. These generic examples do not refute the actual squarefree estimate.

## Complete-Q numerical diagnostics

The computations use every active squarefree conductor. For a periodic product of period `L`, its complete Q weights are

\[
w_L(r)=\frac{\psi_1(r/L)}{ZL^2},\qquad
w_L^B(r)=w_L(r)+\frac{\psi(r/L)-\psi((r+1)/L)}{ZL},
\quad1\le r\le L.
\]

The latter follows from `1/[n^2(n+1)]=1/n^2-1/n+1/(n+1)`. Thus Gram matrices, mixed B moments, residual energies, and residual B moments include the entire infinite tail. Residual tails `T_k,C_k` are obtained by subtracting only the known finite head from these complete moments. Ordered two-pass Gram--Schmidt is applied to whitened evaluation rows. Numerical rank uses a tolerance; it is not an exact rank certificate.

| N | epsilon_N | G_{N,N+1} | G/epsilon | max head D | max screened product | max head abs(b_N) |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | .01167427079 | .004523863457 | .387507 | .9092552743 | .006501545582 | .009900966052 |
| 32 | .009127537008 | .003735578120 | .409265 | 1.248265391 | .006730595670 | .01549382189 |
| 64 | .007553250931 | .003136500423 | .415252 | 1.613916529 | .007128266650 | .01897712808 |
| 128 | .006332068280 | .002673090855 | .422151 | 3.043807358 | .01113722241 | .03836077977 |

Here `max screened product` is `(epsilon_N-G_{N,N+1}) max_{1<=n<=N}D_N(n)`. This is the theoretical upper bound expression, not the squared actual correction. The positive layer subtraction improves the old diagnostic bound by about 39--42%, but these finite values prove no uniform estimate or decay.

Extending the finite layer sum to `M=16384` gives the following additional diagnostics. The displayed tail energies also bound the omitted complete gain mathematically; their computed decimal values are not certified intervals.

| N | G_{N,16384} | fraction of epsilon_N | T_16384 |
|---:|---:|---:|---:|
| 16 | .008375418884 | .717425 | .000006954776283 |
| 32 | .006198706638 | .679122 | .000008960746555 |
| 64 | .004888194443 | .647164 | .00001186910043 |
| 128 | .003900635978 | .616013 | .00001690082379 |

Thus a larger finite screening cutoff can materially improve the tested bound; this requires no infinite-layer theorem. The computed `C_16384` values range from `2.12e-10` to `5.18e-10`, still substantially above moment-subtraction roundoff in this run.

Across the four stages, whitened basis orthogonality errors are below `2.2e-15`; normal-equation residuals are below `8.4e-17`. At `N=128`, the smallest retained complete residual-tail energy in the computed range is `.00231062933` and the smallest residual B-tail moment is `8.59704803e-6`, so subtraction has not nearly exhausted either positive quantity. Reaccumulating the complete C moment in long double changes it by `1.4e-17`. Independently summing the nonnegative residual B energy through physical site `10^6` differs from the full moment by `1.38e-13`; the elementary coefficient-amplitude tail bound is `3.0e-10`. These are numerical consistency checks, not interval-certified errors.

## Signed head-prediction amplification

For `H=floor(n/2)`, the exact predictor is the projection of the `n`-th evaluation kernel onto the span of the first `H` kernels. We computed its minimum-Euclidean-norm coefficient vector by rank-revealing SVD. Because redundant coefficient representations need not have the same l1 norm, a separate linear program minimized l1 over all representations of that same projected kernel.

| N | max canonical row l1 | max minimum attainable row l1 | minimum actual h | maximum actual h |
|---:|---:|---:|---:|---:|
| 16 | 2.05638 | 1.77072 | -.0111688 | .0105083 |
| 32 | 4.42736 | 3.45653 | -.00936410 | .0202219 |
| 64 | 5.20244 | 4.89118 | -.0215663 | .0193260 |
| 128 | 11.07398 | 9.95821 | -.0412850 | .0380912 |

At `N=128,n=114,H=57`, the minimum l1 is approximately `9.958213873`, while the actual head response is `.03809123943` and the actual tail response is `-.002032490550`. At `N=4,n=4,H=2` the unique prediction row already has l1 approximately `1.133083412`. Thus the numerics argue against a simple row-l1-at-most-one induction, even if redundant coefficients are optimized. They do not constitute a certified counterexample. The exact signed actual response remains the relevant weaker target.

The largest prediction identity discrepancy is below `8.1e-17`; the largest LP equality residual in this run is `2.6e-11`. Negative predictor coefficients occur, so positivity must not be assumed.

The numerical diagnostics were computed with NumPy and SciPy from the complete moment formulas above; they do not provide certificates.

## Next concrete research steps

1. Use the newly formalized basis, prediction, and layered screening results; do not redo R1/R2. If pursuing the complete gain, formalize its summability and truncation gap first.
2. Preserve the product `(epsilon_N-G)D_N(n)` in further estimates. Determine whether the arithmetic boundary charge and normal equations control its early-onset component.
3. If using lower-head prediction, target its signed action on actual `b_N` values. The stronger arbitrary-data l1-contraction route has unfavorable numerical evidence.
4. Retain the exact tail-response bound and complete tails. A small tail remainder does not control repeated amplification through predictor rows.
5. Prove a uniform arithmetic provider before invoking the existing RH consumer. The present refinements do not prove RH.


## Verification boundary and continuation

The combined source candidate passed server check `job_qEj54MbhslHKsVfq1d677Q8zaDA7Effb` (reported verification duration 11.396 seconds). Its audited central declarations used only `propext`, `Classical.choice`, and `Quot.sound`. This check covered basis/support/synthesis, head prediction and split, and the initial finite-layer screened estimate. The persisted modules, including explicit `OrthonormalBasis` packaging, passed `job_l2NR8wnygsr4F0IUZcBVpJnujnUClC3h` (34.842 seconds reported). The final arbitrary-cutoff estimate passed `job_CKIEboH3UnwQGCMIhXXK-fg_9gkBSCy2` (22.153 seconds reported), with the same standard axiom list. Opening round-trip and polling durations were not separately retained; these are server-reported verification durations, not pure kernel timings. The final checkpoint governs whole-project publication.

Publication is through the required server checkpoint with push enabled. Its final job, validation scope, and commit are reported in the accompanying chat; this document is prepared before that final publication step. No `sorry`, `admit`, project-local axiom, or unsafe declaration was introduced.

Retained workspace token: `ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj`.
Project root: `/home/cri_2025/lean-agent-workspaces/ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj/RiemannResearch`.
Follow any continuation token returned by the checkpoint. Preserve newer main.

The final RH consumer remains `QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound`. No newly proved declaration supplies its uniform bound. A proof of the displayed uniform screened product, or the actual signed minimum-norm head-extension bound, would supply it. Compactness, coefficient-energy improvement, and finite numerical tables do not establish that provider.


### Completed core publication

The first full checkpoint, `job_lXg3gYZzEPF_Td0HhvucCfzfzsTy-N9f`, succeeded and published commit `b7ee0ca331087ac0fc3ff1fcfc27172110fb9178`. Validation scope was full (aggregate plus six changed modules), reported build validation was 177.138 seconds and total checkpoint duration was 180.559 seconds. Dependency-cache preflight was complete, with 12.796 seconds reported. No integration with newer main was required. This is server-reported timing, not a measurement of pure kernel time. The final continuation checkpoint also validates the explicit-import cleanup and any subsequent arithmetic pivot refinement before publication.
