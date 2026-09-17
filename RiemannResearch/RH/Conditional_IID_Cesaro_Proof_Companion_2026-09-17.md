# Conditional iid and Cesàro: proof companion

Date: 2026-09-17. Source: the user-provided September 16 handoff and the September 17 mathematical completion.

These ordinary mathematical proofs were developed before their Lean translations. This document supplements the original manuscript. It is not a claim that every statement below has been kernel-checked; the separate submission record identifies exact Lean coverage.

The classical weighted Nyman–Beurling theorem is cited as an established external result, not reproved here. Its Lean provider remains an explicit obligation. No uniform or subpolynomial bound on the actual arithmetic minimum energies is asserted, and no unconditional proof of RH is claimed.

# Cofinal minimum-energy criteria: complete mathematical proofs

Use the actual finite legal class V_N={F∈V:F(n)=1, 1≤n≤N}, energy A(F)=∑q_t(CF(t))², and E_N=inf A(V_N). Finite interpolation makes V_N nonempty; its elements have finite energy. Hence E_N is a finite nonnegative real number. Existing proofs give E_N≤E_M for N≤M.

## 1. Cofinal bounds and uniform bounds

Let Y_j→∞ in the positive-integer order. If E_{Y_j}≤B for every j, then for any N choose j with N≤Y_j. Monotonicity gives E_N≤E_{Y_j}≤B. The converse is immediate. An eventual bound along a cofinal sequence suffices: choose j large enough both for the bound and for Y_j≥N. Thus a bound on a cofinal tail is exactly as strong as a bound for all heads.

## 2. Near-minimizers do not change subpolynomial growth

For every j, choose an actual F_j∈V_{Y_j} with A(F_j)<E_{Y_j}+1. Such a function exists by the defining property of the real infimum; no attained minimizer is required. Suppose that for every ε>0 there is C_ε≥0 such that eventually E_{Y_j}≤C_ε Y_j^ε. Eventually Y_j≥1, so

A(F_j)≤E_{Y_j}+1≤C_ε Y_j^ε+1≤(C_ε+1)Y_j^ε.

The same sequence of near-minimizers works simultaneously for every ε: it is selected once with error 1, independently of ε. Conversely, subpolynomial energy of any actual exact-head family bounds E_{Y_j}, since an infimum is no larger than the energy of any feasible vector. This establishes equivalence of subpolynomial growth of the infima and existence of an actual legal family with subpolynomial energy.

## 3. Actual RH consequence

Suppose ζ(s)=0 with σ=Re(s)>1/2 and s≠1. The already proved signed Mellin obstruction yields constants c_s>0 and N_s such that every F∈V_N, N≥N_s, satisfies A(F)≥c_s N^(2σ−1). Taking infima gives E_N≥c_s N^(2σ−1). Put ε=(2σ−1)/2. A subpolynomial upper bound on a cofinal sequence would imply c_s Y_j^ε≤C_ε for all sufficiently large j, contradicting Y_j→∞. Thus no such zero exists; reflection of nontrivial zeros then yields RH. A uniform cofinal bound is a special case.

This proves the sufficient criteria. It does not prove that the required bound holds. The reverse implication from RH remains dependent on the classical weighted Nyman–Beurling theorem, whose Lean provider is a separate obligation.

## 4. Sharp head-plus-tail Mellin obstruction

Fix a zero s with Re(s)>1/2 and s≠1. Write b_s(n)=n[a_s(n)−a_s(n+1)], B_s(N)=∑_{n≤N}b_s(n), and τ_s(N)=∑_{n>N}|b_s(n)|²/q_n. For any F∈V_N, absolute convergence and the exact annihilation identity give

∑_{n>N}b_s(n)CF(n)=−B_s(N).

Weighted Cauchy–Schwarz applied solely to this tail gives

|B_s(N)|²≤τ_s(N)∑_{n>N}q_n|CF(n)|²
             =τ_s(N)[A(F)−N/(N+2)].

If τ_s(N)>0, divide and take the infimum over actual F∈V_N:

E_N≥N/(N+2)+|B_s(N)|²/τ_s(N).

The positive-tail hypothesis is automatic for every sufficiently large N: B_s(N)→1, while V_N is nonempty, so a zero tail would contradict the preceding inequality. No sign has been discarded before the signed head/tail equality.

---

# Canonical Möbius exact heads and the unconditional linear energy bound

Mathematical completion of Section 10.2 of the user's conditional-iid/Cesàro completion. The mathematics below is complete before preparation of the Lean candidate. This file is not a kernel-verification certificate.

Let Y be an integer with Y≥1. Write μ for the ordinary Möbius function, g_d(n)=(n mod d)/d, C for the positive-index Cesàro mean, and q_t=2/((t+1)(t+2)). Set

m_Y=Σ_{1≤d≤Y} μ(d)/d,
F_Y(n)=−Σ_{1≤d≤Y} μ(d)g_d(n)+(Y+1)m_Y g_{Y+1}(n).

The d=1 term vanishes identically, so this is exactly the manuscript's sum beginning at d=2. Every coefficient is deterministic and independent of the evaluation point and latent endpoint.

## 1. Exact divisor-counting identity

For every positive n,

Σ_{1≤d≤n} μ(d) floor(n/d)
=Σ_{1≤d≤n} μ(d) Σ_{1≤k≤n} 1_{d|k}
=Σ_{1≤k≤n} Σ_{d|k} μ(d)=1.

Both sums are finite. The first equality counts positive multiples of d. The middle equality interchanges a finite double sum. The final equality uses the Dirichlet inverse identity Σ_{d|k} μ(d)=1 when k=1 and 0 when k>1. For any Y≥n, extending the d sum to Y adds only zero floor terms.

## 2. Exact signed remainder identity

Euclidean division gives g_d(n)=n/d−floor(n/d). Therefore, for 1≤n≤Y,

Σ_{1≤d≤Y} μ(d)g_d(n)=n m_Y−1.

No absolute values have been introduced into this identity.

Because n<Y+1, g_{Y+1}(n)=n/(Y+1). Substitution yields F_Y(n)=1 for every 1≤n≤Y. Also F_Y(0)=0.

Every normalized generator g_d is (1/d) times the existing raw residue generator. Consequently F_Y belongs to the actual full legal span used in conditionalHeadClass Y. The index d=1 causes no problem because its generator is zero. This proves membership of F_Y in conditionalHeadClass Y, rather than merely asserting that the constraint set has an element.

## 3. Elementary bound on the reciprocal Möbius sum

Put n=Y in the signed remainder identity:

Y m_Y=1+Σ_{1≤d≤Y} μ(d)g_d(Y).

The d=1 summand is zero. For every d≥1, |μ(d)|≤1 and 0≤g_d(Y)<1. Thus

|Y m_Y|≤1+Σ_{2≤d≤Y}|μ(d)|g_d(Y)≤1+(Y−1)=Y.

Since Y>0, division by Y proves |m_Y|≤1. This uses no prime asymptotic, zero-free region, RH, or estimate for the Mertens summatory function.

## 4. Uniform bound for the actual conditional mean

The already established exact generator formula gives

0≤C g_d(t)≤1/2  (d≥1, t≥0).

For d=1 the mean is exactly zero. Finite linearity of C and the triangle inequality therefore give

|C F_Y(t)|
≤(1/2)Σ_{2≤d≤Y}|μ(d)|+(1/2)(Y+1)|m_Y|
≤(Y−1)/2+(Y+1)/2=Y.

This estimate also holds at t=0, where the project defines the Cesàro mean to be zero. For 1≤t≤Y, exactness of the ordinary head gives C F_Y(t)=1.

## 5. Summability and the exact tail mass

The nonnegative energy summands obey

0≤q_t |C F_Y(t)|²≤Y²q_t.

Since Σ_{t≥1}q_t=1, their series converges. Thus all subsequent infinite sums are genuine convergent real sums; none uses a totalized nonsummable `tsum`.

Telescoping q_t=2/(t+1)−2/(t+2) gives

Σ_{1≤t≤Y}q_t=Y/(Y+2),
Σ_{t>Y}q_t=2/(Y+2).

These are the existing conditionalWeight_sum_range and conditionalWeight_tsum_tail statements after the project's k=t−1 indexing shift.

## 6. Actual witness energy and actual variational infimum

Split the convergent energy at Y. The head is exactly one and the tail is bounded in absolute value by Y, hence

conditionalMeanSquare(F_Y)
≤Y/(Y+2)+Y²·2/(Y+2)
=Y(2Y+1)/(Y+2).

The existing infimum theorem applies to the proved class membership:

conditionalHeadMinimum(Y)
≤conditionalMeanSquare(F_Y)
≤Y(2Y+1)/(Y+2)<2Y.

The strict inequality follows because Y>0 and 2Y(Y+2)−Y(2Y+1)=3Y>0. Combined with the already established compulsory-head lower bound,

Y/(Y+2)≤conditionalHeadMinimum(Y)≤Y(2Y+1)/(Y+2)<2Y.

The result is an unconditional linear energy bound. It does not supply the uniform or subpolynomial bound needed for the remaining RH criterion. The proof's only losses are the explicitly displayed coefficient and tail triangle inequalities; it asserts no hidden independence or signed-covariance estimate.

---

# All-Hilbert Cesàro–Mellin bridge

Date: 2026-09-17. Mathematical proof completed before drafting Lean. No Lean verification claim.

Let w_n=1/(n(n+1)) for n≥1, H=ℓ²(w), and F∈H. Write S_N=Σ_{n=1}^N F(n), M_N=S_N/N, with S_0=M_0=0. For s∈ℂ put σ=Re(s), a_s(n)=n^{-s}−(n+1)^{-s}, b_s(n)=n(a_s(n)−a_s(n+1)).

## 1. Prefix estimate for every Hilbert vector

Weighted finite Cauchy–Schwarz gives

|S_N|² ≤ (Σ_{n≤N}w_n|F(n)|²)(Σ_{n≤N}1/w_n)
≤ ‖F‖_H² N(N+1)(N+2)/3.

The sum identity is elementary since Σ(n²+n)=N(N+1)(N+2)/3. Thus the completion's precise bound is valid without pointwise boundedness:

|S_N| ≤ ‖F‖_H sqrt(N(N+1)(N+2)/3).

For formalization a looser estimate avoids an unnecessary cubic-sum lemma:

Σ_{n≤N}1/w_n ≤ N(N+1)²,

because n(n+1)≤(N+1)². Hence

|S_N| ≤ ‖F‖_H (N+1) sqrt(N),  N≥0.

For N≥1 this implies

|M_N| ≤ 2‖F‖_H sqrt(N) = 2‖F‖_H N^{1/2}.

This O(sqrt N) bound is sufficient for all remaining steps and has the correct threshold.

## 2. The retained boundary vanishes

The existing first-difference estimate is |a_s(N+1)|≤|s|(N+1)^{-σ−1}, valid for σ>0. Since N M_N=S_N,

|N a_s(N+1) M_N|
≤ |s|‖F‖_H sqrt(N)(N+1)^{-σ}
≤ |s|‖F‖_H (N+1)^{1/2−σ}.

For σ>1/2 the last power tends to zero. Therefore the exact finite Abel boundary vanishes for every F∈H, not merely bounded F.

## 3. Absolute convergence of the second series

This must be proved separately: convergence of natural-order complex partial sums alone does not establish Lean's unconditional HasSum.

From |b_s(n)|≤|s(s+1)|n^{-σ−1} and the mean estimate,

|b_s(n)M_n|
≤2|s(s+1)|‖F‖_H n^{-σ−1/2}.

Since σ+1/2>1, the dominating p-series converges. Thus Σ b_s(n)M_n is absolutely summable. The first-difference series is already absolutely summable for every F∈H (existing hasSum_first_mellin_pairing), or follows directly by weighted Cauchy–Schwarz.

## 4. Exact infinite pairing

The existing finite identity is

Σ_{n=1}^N a_s(n)F(n)
=Σ_{n=1}^N b_s(n)M_n + N a_s(N+1)M_N.

Both series have genuine HasSum limits; the boundary tends to zero. Passing to the limit proves

Σ_{n≥1} b_s(n)M_n = Σ_{n≥1} a_s(n)F(n).

In project notation, with F=hilbertSequence f and f:ThresholdHilbert,

Σ' k, mellinSecond s (k+1) *
 mean (fun n => (hilbertSequence f n : ℂ)) (k+1)
= s * paretoMellin f s,    Re(s)>1/2.

No boundedness premise remains. This argument does not require a separately constructed continuous operator C:H→J, a RH assumption, or the classical Nyman–Beurling converse.

## 5. Formalization plan grounded in existing declarations

Existing inputs:
- `hilbertSequence_weighted_square`, `hilbert_coordinate_square_summable`, `hilbert_norm_sq`.
- `WeightedPairing.finite_pairing_norm_sq_le`.
- `mellinFirst_norm_le`, `mellinSecond_norm_le`.
- `mellin_pairing_prefix`, `hasSum_first_mellin_pairing`.
- `Real.summable_nat_rpow`, `tendsto_rpow_neg_atTop`.

New reusable declarations should establish: weighted prefix bound; mean O(sqrt N); all-H boundary decay; actual summability of the second pairing; and the all-H exact pairing. A sibling module can avoid modifying existing downstream consumers during the first verification checkpoint. Root coordinates all verification and remote edits.

---

# Complete weighted Cesàro operator argument

Source: user-provided conditional-iid manuscript, Section 4, with details supplied here. This document is a mathematical proof; Lean coverage is tracked separately.

Let all indices be positive integers. Write
\[
w_n=\frac1{n(n+1)},\quad q_t=\frac2{(t+1)(t+2)},\quad
H=\ell^2(w),\quad J=\ell^2(q),\quad
(CF)_t=\frac1t\sum_{n\le t}F_n.
\]
The spaces are real. They are complete Hilbert spaces, by their isometric identifications with ordinary \(\ell^2\), obtained by multiplying coordinate \(n\) by \(\sqrt{w_n}\), respectively \(\sqrt{q_n}\).

## 1. Joint mass and contraction

Define \(a_{nt}=q_t\mathbf1_{n\le t}/t\). The identity
\[
q_t/t=w_t-w_{t+1}
\]
and telescoping imply \(\sum_ta_{nt}=w_n\), while \(\sum_na_{nt}=q_t\). Both total masses are one.

For each \(t\), finite Cauchy–Schwarz gives
\[
|(CF)_t|^2\le t^{-1}\sum_{n\le t}|F_n|^2.
\]
Tonelli for nonnegative series therefore gives
\[
\sum_tq_t|(CF)_t|^2\le\sum_{n,t}a_{nt}|F_n|^2
=\sum_nw_n|F_n|^2.
\]
Thus the explicitly defined linear operator \(C:H\to J\) is a contraction. It fixes the constant sequence one, whose norm is one in both spaces; hence its operator norm is exactly one.

With \(y_0=0\), direct subtraction gives
\[
F_n=n(CF)_n-(n-1)(CF)_{n-1}.
\]
Consequently \(C\) is injective. In fact its range has the exact description
\[
\operatorname{ran} C=\left\{y\in J:
\sum_{n\ge1}w_n\bigl(ny_n-(n-1)y_{n-1}\bigr)^2<\infty\right\}.
\]
The reverse inclusion follows by defining \(F_n=ny_n-(n-1)y_{n-1}\) and telescoping its finite sums.

## 2. Dense and nonclosed range, without a bounded inverse theorem

If \(y\) vanishes for \(n>N\), the inverse just displayed vanishes for \(n>N+1\); it therefore belongs to \(H\). Every finite-support vector of \(J\) lies in the range. Since finite coordinate truncations converge in \(J\), the range is dense.

For a direct witness to nonclosedness, let \(y_n=(-1)^n\). Then \(\|y\|_J^2=\sum_nq_n=1\). Its only possible preimage is
\[
F_n=(2n-1)(-1)^n.
\]
For \(n\ge1\), \((2n-1)^2/[n(n+1)]\ge1/2\): after multiplying by the positive denominator, this is \(2(2n-1)^2-n(n+1)=(n-1)(7n-2)\ge0\). Hence \(F\notin H\), so \(y\notin\operatorname{ran}C\), although every truncation of \(y\) lies in the range and converges to \(y\). The range is not closed.

For \(e_N=\delta_N-\delta_{N+1}\), direct evaluation also gives
\[
Ce_N=\delta_N/N,\quad
\|e_N\|_H^2=\frac2{N(N+2)},\quad
\|Ce_N\|_J^2=\frac2{N^2(N+1)(N+2)}.
\]
Thus no positive uniform lower norm bound exists. This assertion concerns the full Hilbert domain, not the legal arithmetic span.

## 3. Posterior and actual adjoint

Let \((K,T)\) have joint mass \(a_{nt}\). Because \(w_n>0\), its posterior distribution is
\[
\pi_n(t)=P(T=t\mid K=n)=\frac{a_{nt}}{w_n}
=\frac{q_t}{tw_n}\mathbf1_{t\ge n}.
\]
The telescoping marginal identity proves \(\sum_t\pi_n(t)=1\).

For \(G\in J\), define
\[
(DG)_n=\frac1{w_n}\sum_{t\ge n}\frac{q_t}{t}G_t.
\]
Each tail is absolutely convergent: Cauchy–Schwarz bounds its absolute sum by
\[
\left(\sum_{t\ge n}q_tG_t^2\right)^{1/2}
\left(\sum_{t\ge n}q_t/t^2\right)^{1/2}<\infty.
\]
Jensen for the probability vector \(\pi_n\), followed by nonnegative interchange, gives
\[
\sum_nw_n(DG)_n^2\le\sum_{n,t}a_{nt}G_t^2
=\sum_tq_tG_t^2.
\]
Thus \(D:J\to H\) is a contraction.

For \(F\in H\), absolute interchange in the proposed adjoint identity is justified by
\[
\sum_{n,t}a_{nt}|F_nG_t|
=\sum_tq_t(C|F|)_t|G_t|
\le\|C|F|\|_J\|G\|_J\le\|F\|_H\|G\|_J.
\]
Consequently
\[
\langle CF,G\rangle_J=\sum_{n,t}a_{nt}F_nG_t
=\langle F,DG\rangle_H,
\]
so \(D=C^*\). It fixes one and has operator norm one. Consecutive absolutely convergent tails give
\[
w_n(C^*G)_n-w_{n+1}(C^*G)_{n+1}=q_nG_n/n.
\]
Since \(q_n/n>0\), \(C^*\) is injective. This also independently proves that \(C\) has dense range.

## 4. Pair kernel, exact closed expression, and reversibility

Conditionally on \(T=t\), let \(K_1,K_2\) be independent uniform variables on \(\{1,\ldots,t\}\). Their joint mass is
\[
P(K_1=a,K_2=b)=k(\max(a,b)),\qquad
k(m)=\sum_{t\ge m}\frac{q_t}{t^2}.
\]
Every series converges absolutely because \(0\le q_t/t^2\le q_t\). For a finite endpoint \(R\ge m\), partial fractions yield the exact boundary formula
\[
\sum_{t=m}^{R}\frac{q_t}{t^2}
=\sum_{t=m}^{R}\frac1{t^2}
-\frac3{2m}+\frac1{2(m+1)}
+\frac3{2(R+1)}-\frac1{2(R+2)}.
\]
This follows term by term from
\[
\frac{q_t}{t^2}=\frac1{t^2}
-\frac3{2t}+\frac2{t+1}-\frac1{2(t+2)}.
\]
The boundary tends to zero, so
\[
k(m)=\sum_{t\ge m}t^{-2}-\frac3{2m}+\frac1{2(m+1)}.
\]
For arbitrary \(F,G\in H\), Tonelli and the contraction estimate show
\[
\sum_{a,b}|F_aG_b|k(\max(a,b))
=\langle C|F|,C|G|\rangle_J
\le\|F\|_H\|G\|_H.
\]
Hence all signed interchanges are valid and
\[
E[F(K_1)G(K_2)]
=\sum_{a,b}F_aG_bk(\max(a,b))
=\langle CF,CG\rangle_J.
\]
No covariance term has been discarded.

Define \(P(n,m)=k(\max(n,m))/w_n\). Nonnegative interchange gives
\[
\sum_m k(\max(n,m))
=\sum_{t\ge n}\sum_{m\le t}q_t/t^2
=\sum_{t\ge n}q_t/t=w_n.
\]
Therefore every row of \(P\) sums to one. Symmetry gives detailed balance
\(w_nP(n,m)=w_mP(m,n)\), and thus invariance of \(w\).
Its operator is exactly \(C^*C\): expanding \(C^*CF\) and using the absolute-convergence bound above gives the kernel formula coordinatewise. Consequently it is a self-adjoint positive contraction on \(H\), fixes one, and satisfies
\[
\langle F,PF\rangle_H=\|CF\|_J^2\ge0.
\]
Its injectivity follows from that of \(C\). None of these operator statements proves the missing arithmetic approximation or RH-strength bound.

---

# Conditional iid extensions: probability statements and proofs

Source: the user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`, Sections 2 and 6. These arguments use the actual countable mixture, not a replacement independence assumption. No Lean verification is claimed by this document.

Put q_t=2/((t+1)(t+2)), U_t=t^{-1}∑_{n=1}^tδ_n, P_t=δ_t⊗U_t^ℕ, and P=∑_{t≥1}q_tP_t. The natural-number row indices in Lean start at zero. Let T be the latent endpoint and K_i the coordinates.

## 1. Exchangeability, including the entire path law

For every bijection π:ℕ→ℕ, define R_π(t,x)=(t,x∘π). This map is measurable, because every coordinate is measurable. Its inverse is R_{π^{-1}}. For a finite set I and subsets B_i⊆ℕ, independence on the t-th fiber gives

P_t(K_{π(i)}∈B_i for every i∈I)=∏_{i∈I}U_t(B_i).

Indeed π is injective, so the selected coordinates are distinct. The right side is also the probability of the original cylinder. Finite cylinders form a π-system generating the product sigma algebra; equality of two probability measures there implies equality everywhere. Hence (R_π)_*P_t=P_t. Integration with respect to q_t then gives (R_π)_*P=P. This proves exchangeability even for infinite coordinate permutations. The same cylinder proof shows that any injective reindexing preserves the marginal law of the entire infinite path, though the reindexing map need not be invertible.

## 2. Endpoint recovery and its exact error probability

Set M_r=max(K_0,…,K_{r-1}), with M_0=0. Under P_t all coordinates lie in {1,…,t}, simultaneously almost surely (a countable intersection). For r≥1,

P_t(M_r<t)=((t-1)/t)^r.

The events {M_r<t} decrease to {K_i≠t for every i}; their probabilities tend to zero because 0≤(t-1)/t<1. Therefore P_t(∃i:K_i=t)=1. On this event M_r=t for every r>i. Countable mixing proves

P(there exists r_0 such that every r≥r_0 has M_r=T)=1.

There is also the exact unconditional identity

P(M_r≠T)=∑_{t≥1}q_t(1-1/t)^r, r≥1.

Dominated convergence gives convergence to zero. For any cutoff L≥1,

P(M_r≠T)≤(1-1/L)^r+2/(L+2)≤exp(-r/L)+2/(L+2).

The bound splits the sum at L and uses ∑_{t>L}q_t=2/(L+2). It supplies quantitative recovery but is not needed for almost-sure eventual equality. Recovery implies that T is measurable, modulo completion, with respect to the sigma algebra generated by the rows; it does not turn the rows into unconditionally independent variables.

## 3. A common event for every arithmetic observable

For each positive t and each n∈{1,…,t}, apply the ordinary iid strong law under U_t^ℕ to the bounded indicator X_i=1_{K_i=n}. The finite intersection of these events, together with the common support event, has P_t-probability one. On it

ν_r(n):=r^{-1}∑_{i<r}1_{K_i=n}→1/t

for every n≤t. For every function F:ℕ→ℝ, the exact finite identity

r^{-1}∑_{i<r}F(K_i)=∑_{n=1}^tF(n)ν_r(n)

then proves convergence to t^{-1}∑_{n=1}^tF(n). This event was chosen using only finitely many indicator sequences, so it works simultaneously for **all** F; no uncountable intersection of null-set complements is taken. Taking the countable union across latent atoms proves one P-probability-one event on which

∀F:ℕ→ℝ, r^{-1}∑_{i<r}F(K_i)→CF(T).

No global integrability is required for this pathwise statement, since T is finite on each realization. By contrast, the previously proved L² identities require a finite marginal second moment. This statement does not provide a triangular-array conclusion for arbitrary changing F_r.

## 4. Arithmetic events and prime rows

For d≥1, the multiples of d in {1,…,t} are d,2d,…,⌊t/d⌋d, so

U_t({n:d∣n})=⌊t/d⌋/t.

For a,b≥1, a∣n and b∣n is equivalent to lcm(a,b)∣n; hence

U_t({n:a∣n and b∣n})=⌊t/lcm(a,b)⌋/t.

For distinct rows i_1,…,i_m and positive d_j, conditional independence gives the product of these one-row probabilities. Within a row the factors usually do not multiply. The measurable map n↦(v_p(2n))_p transports both exchangeability and conditional iid to the prime-exponent rows. Since 2K_i≤2T simultaneously, only the finitely many primes at most 2T can occur anywhere in the matrix.

## 5. Explicit sample sizes and the smoothed criterion

Let F_j be deterministic arithmetic functions with finite marginal second moments. Define

b_j=E(1-CF_j(T))², v_j=E Var(F_j(K_0)|T).

Both are finite and nonnegative. The already proved exact sample identity is

E(1-r^{-1}∑_{i<r}F_j(K_i))²=b_j+v_j/r, r≥1.

For j≥1, set r_j=max(j,⌈jv_j⌉). Since r_j≥j>0 and r_j≥jv_j, division gives v_j/r_j≤1/j. Thus

b_j≤E(1-r_j^{-1}∑_{i<r_j}F_j(K_i))²≤b_j+1/j.

In particular b_j→0 if and only if these explicit sample errors tend to zero, and r_j→∞. More generally, for any positive ε, r=max(1,⌈v/ε⌉) guarantees total error≤b+ε. This is a deterministic choice from the unconditional fiber variance; the sample size does not depend on the realized T.

If F_Y has unit head through Y and conditional-mean energy at most one, the analytic head/tail argument gives b_Y≤8/(Y+2). Choosing the displayed r_Y then gives the explicit sample bound 1/Y+8/(Y+2). Producing such legal F_Y unconditionally is the unresolved RH-strength issue. The sampling calculation itself supplies no missing arithmetic energy estimate.

## Verification boundaries

All probability theorems above follow unconditionally for the specified model. The RH interpretation additionally uses the independently proved sufficient smoothed-approximation criterion; its reverse direction uses the classical weighted Nyman–Beurling theorem. A Lean theorem taking the reverse implication as a premise does not formalize that classical input. The actual strong-law theorem can be proved fiberwise even when the observable has no global moment; do not add global integrability merely to conceal that distinction.

## 6. Identification of every H vector with a genuine square-integrable observation

Suppose ∑_{n≥1}w_nF(n)²<∞. The already constructed marginal gives P(K_i=n)=w_n. Integration of a nonnegative function over the countable partition {K_i=n} therefore gives E(F(K_i)²)=∑_nw_nF(n)²<∞. Thus every physical weighted-Hilbert vector, including unbounded vectors, produces an actual L² random variable in every row. In the square-root-weight realization F(n)=f_{n-1}/√w_n, this second moment is exactly ∑_j f_j²=‖f‖².

For any real c, put A=E(c-F(K_0))² and B=E(c-CF(T))². Both are finite by the L² triangle inequality and conditional expectation contraction. The exact sample identity gives error B+v/r. Its r=1 case gives A=B+v, so substitution yields

E(c-r^{-1}∑_{i<r}F(K_i))²=A/r+(1-1/r)B.

The countable marginal and latent laws identify A=∑_nw_n(c-F(n))² and B=∑_tq_t(c-CF(t))². In particular, with c=0 and the genuine continuous Cesàro operator C between the two square-root-weight realizations, the identity is ‖f‖²/r+(1-1/r)‖Cf‖². This closes the all-H interpretation of the previously verified identities that required an explicit MemLp premise.

---

# Exact arithmetic tails, finite rank, and strict nonattainment

Date: 2026-09-17. Source: the user-provided conditional-iid/Cesàro mathematical completion, Sections 10–11. This file supplies ordinary mathematical proofs before any new Lean verification. No RH hypothesis or Nyman–Beurling converse is used below.

## 1. Definitions and the actual legal space

For integers n≥0 and d≥1 put R_d(n)=n mod d. The fractional-part generator is g_d=R_d/d when d>0. Its span for d≥2 equals the span of R_d for d≥2. Set

\[
q_t=\frac{2}{(t+1)(t+2)},\qquad
M_f(t)=\frac1t\sum_{n=1}^t f(n)\quad(t\ge1).
\]

The existing Lean legal space uses generators D_mR_a(n)=mR_a(⌊n/m⌋), with a,m positive. The exact identity

\[
D_mR_a=R_{ma}-R_m
\]

shows that allowing every positive a,m gives precisely the same algebraic space V as all positive residue generators. In particular no closure or infinite synthesis is involved. Every f∈V satisfies f(0)=0 and is bounded and periodic: each D_mR_a has period ma, and a common multiple of the finitely many generator periods is a positive period of f.

Write

\[
\mathcal E(f)=\sum_{t\ge1}q_t M_f(t)^2,
\qquad Q_N=\sum_{t=1}^{N}q_t=\frac{N}{N+2}.
\]

The series is finite for legal f because M_f is bounded and Σq_t=1. All subsequent ordinary real series are summable, not merely formal expressions.

## 2. Eventual vanishing of means forces a legal witness to vanish

**Lemma 2.1 (positive-index inversion).** For n≥1,

\[
f(n)=nM_f(n)-(n-1)M_f(n-1),
\]

where 0·M_f(0)=0. This follows by subtracting consecutive finite partial sums.

**Lemma 2.2.** If f has a positive period P and f(n)=0 for all sufficiently large n, then f=0. For any fixed n, select k so n+kP is beyond the vanishing threshold. Periodicity gives f(n)=f(n+kP)=0.

**Theorem 2.3 (tail injectivity on actual legal functions).** For f∈V and N≥0, if M_f(t)=0 for every t>N, then f=0. Indeed Lemma 2.1 gives f(n)=0 for n>N+1, and Lemma 2.2 concludes. Consequently if two legal witnesses have identical Cesàro means on any entire tail, they are equal.

**Corollary 2.4 (positive tail energy).** If f∈V is nonzero, then

\[
\sum_{t>N}q_tM_f(t)^2>0
\qquad(N\ge0).
\]

Every term is nonnegative and every q_t is positive. If the sum were zero, every M_f(t), t>N, would vanish, contrary to Theorem 2.3. This uses convergence of the nonnegative series, already established by boundedness.

## 3. The compulsory head mass is never attained by a legal witness

Suppose N≥1 and f∈V has f(n)=1 for 1≤n≤N. Then M_f(t)=1 for t≤N. The exact energy split and Corollary 2.4 give

\[
\boxed{\mathcal E(f)=Q_N+\sum_{t>N}q_tM_f(t)^2>Q_N.}
\]

Thus the value Q_N does not belong to the actual set of feasible energy values. If the unrestricted infimum E_N equals Q_N, that infimum is not attained by any legal finite combination. This is compatible with arbitrarily accurate approximation to Q_N and with the RH-conditional equality of the infimum. It does not prove E_N>Q_N.

There is also a quantitative gap depending on the particular period. Let P≥1 be a period of f and choose n=1+(N+1)P. Then n−1>N and f(n)=f(1)=1. Weighted Cauchy–Schwarz applied to Lemma 2.1 gives

\[
1\le\left(\frac{n^2}{q_n}+\frac{(n-1)^2}{q_{n-1}}\right)
\left(q_nM_f(n)^2+q_{n-1}M_f(n-1)^2\right).
\]

Since these two coordinates lie in the tail and

\[
\frac{n^2}{q_n}+\frac{(n-1)^2}{q_{n-1}}
=\frac{n(n+1)(2n^2+1)}2,
\]

we obtain the explicit witness-dependent bound

\[
\boxed{\mathcal E(f)\ge Q_N+\frac{2}{n(n+1)(2n^2+1)}.}
\]

The gap deteriorates as the period grows. It supplies no uniform lower gap above Q_N over the unrestricted legal class.

## 4. Concrete finite-generator rank

Fix D≥2. For j=1,…,D−1 define

\[
p_j=R_{j+1}-R_j.
\]

For 1≤n<j both residues equal n, so p_j(n)=0; at n=j, p_j(j)=j. Hence the square evaluation matrix (p_j(n)) for 1≤n,j≤D−1 is lower triangular with diagonal 1,2,…,D−1. Its determinant is (D−1)!≠0, so the head-evaluation map is bijective.

The generator change is invertible: p_j=R_{j+1}−R_j and, because R_1=0,

\[
R_d=\sum_{j=1}^{d-1}p_j\quad(2\le d\le D).
\]

Therefore R_2,…,R_D, and consequently g_2,…,g_D, are linearly independent. Their restriction to the first D−1 positive integers is already linearly independent. Every prescribed head of length Y≤D−1 has a representative in their span: first prescribe arbitrary values on the remaining D−1−Y coordinates, then use the square evaluation inverse.

Replacing ordinary head values by means preserves rank. For positive indices the finite Cesàro transform is lower triangular with diagonal 1,1/2,…,1/(D−1), and its inverse is the finite formula in Lemma 2.1. Thus the actual smoothed head matrix

\[
A_{td}=M_{g_d}(t)\quad(1\le t\le Y,\ 2\le d\le D)
\]

has full row rank whenever D≥Y+1.

## 5. Positivity of both actual Gram matrices

For m_d=M_{g_d} define

\[
G_{de}=\sum_{t\ge1}q_tm_d(t)m_e(t),\qquad
T_{de}=\sum_{t>Y}q_tm_d(t)m_e(t).
\]

The entries converge absolutely because every m_d is bounded and Σq_t=1. For a real coefficient vector c set f_c=Σ_{d=2}^D c_dg_d. Finite interchange gives the exact identities

\[
c^TGc=\mathcal E(f_c),\qquad
c^TTc=\sum_{t>Y}q_tM_{f_c}(t)^2.
\]

If c≠0, generator independence gives f_c≠0; Corollary 2.4 gives c^TTc>0. Thus T is positive definite. The matrix G is positive definite as well, either by the same argument with N=0 or from

\[
G=A^T\operatorname{diag}(q_1,\ldots,q_Y)A+T.
\]

No unsigned substitution appears. These are the matrices built from the actual arithmetic generators.

### 5.1 Exact normalization change between the manuscript and the Lean dictionary

The manuscript matrices in Section 5 use the normalized generators
`g_d(n)=R_d(n)/d`. The Lean matrix candidates `conditionalResidueHeadMatrix`,
`conditionalResidueGramMatrix`, and `conditionalResidueTailMatrix` use the
raw generators `R_d`. These matrices are **not literally equal**.

Let `Δ=diag(d: 2≤d≤D)`, an invertible real diagonal matrix. With superscripts
`g` and `R` distinguishing the normalized and raw dictionaries, respectively,

\[
A^g=A^R\Delta^{-1},\qquad
G^g=\Delta^{-1}G^R\Delta^{-1},\qquad
T^g=\Delta^{-1}T^R\Delta^{-1}.
\]

These are exact entry identities: the head entry has one factor `1/d`,
and a Gram entry with column indices `d,e` has the factor `1/(de)`.
For normalized coefficients `c`, set raw coefficients `a=Δ^{-1}c`.
Then pointwise

\[
\sum_{d=2}^D c_dg_d=\sum_{d=2}^D a_dR_d.
\]

The inverse coefficient map is `c=Δa`. Consequently this is a bijection
of coefficient spaces preserving the **actual witness**, every head
constraint, the full energy, and the tail energy. In particular the two
constrained energy sets and their attained minima are exactly equal.
The inverse compressed matrices themselves agree:

\[
A^g(G^g)^{-1}(A^g)^T=A^R(G^R)^{-1}(A^R)^T,
\]

and likewise with `T`. For the kernel-basis formula, choose normalized
feasible coefficients `c_0=Δa_0` and normalized correction basis
`N_g=ΔN_R`. Then `N_g^TT^gN_g=N_R^TT^RN_R` and
`N_g^TT^gc_0=N_R^TT^Ra_0`, so the exact signed Schur remainder is unchanged.
Thus raw residue matrices are a coordinate presentation of the manuscript
minimization problem, rather than an alternative arithmetic problem.

## 6. The concrete finite minimum

For D≥Y+1≥2, the affine set Ac=1 is nonempty by Section 4. Since G is positive definite and A has full row rank, AG^{-1}A^T is positive definite: for nonzero x, A^Tx≠0 and

\[
x^TAG^{-1}A^Tx=(A^Tx)^TG^{-1}(A^Tx)>0.
\]

Define λ=(AG^{-1}A^T)^{-1}1 and c_*=G^{-1}A^Tλ. Then Ac_*=1. For any other feasible c, z=c−c_* has Az=0, and

\[
z^TGc_*=z^TA^T\lambda=0,
\qquad c^TGc=c_*^TGc_*+z^TGz.
\]

Thus c_* is the unique minimizer and

\[
E_{Y,D}=1^T(AG^{-1}A^T)^{-1}1.
\]

On the affine constraint, c^TGc=Q_Y+c^TTc. Applying the same proved calculation to T gives

\[
E_{Y,D}=Q_Y+1^T(AT^{-1}A^T)^{-1}1>Q_Y.
\]

Finally choose any feasible c_0 and a matrix N whose columns form a basis of ker A. Every feasible vector has the unique form c_0+Nz. With S=N^TTN and h=N^TTc_0, the matrix S is positive definite unless its dimension is zero, and

\[
(c_0+Nz)^TT(c_0+Nz)=c_0^TTc_0+2z^Th+z^TSz.
\]

Completing this exact square gives z_*=-S^{-1}h and

\[
E_{Y,D}=Q_Y+c_0^TTc_0-h^TS^{-1}h.
\]

The zero-dimensional case simply omits the correction term. The strict lower bound proved here concerns each fixed finite D. Uniform or subpolynomial upper bounds as both Y and D grow remain unproved and are the RH-strength research obligation.

## 7. Verification scope

The first Lean priority is the concrete arithmetic statement of Theorem 2.3 and its strict-energy consequence, using the already verified legal periodicity and Cesàro inversion. Finite rank and positive definiteness will only be reported as machine-verified when their actual arithmetic specializations compile. The raw-to-normalized coefficient bijection of Section 5.1 must accompany claims that the raw-residue Lean minimum represents the normalized manuscript minimum. This document itself makes no machine-verification claim.

---

# Classical RH-to-density input: exact mathematical and Lean boundary

The exact classical theorem needed here is Bagchi, “On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis”, Theorem 1: RH is equivalent to density of the normalized residue sequences in ℓ²(1/[n(n+1)]). Source: https://arxiv.org/html/math/0607733v1 . The real statement follows from its complex version by taking real parts. This theorem is an established external mathematical input; the current project has no Lean proof of it.

Given that input, the remaining reverse deduction is elementary. Let V be the finite real residue span, H=ℓ²(w), J=ℓ²(q), and W=closure(C(V)) in J. Under RH, V is dense in H. Continuity of C implies C(H)⊆W; the proved finite-support inversion shows C(H) dense in J, hence W=J. Fix a finite head length N. The finite interpolation map gives a linear right inverse R_N from the finite-dimensional head space into C(V), hence a continuous map. For any M∈W with prescribed head b, choose M_j∈C(V)→M and replace M_j by M_j+R_N(b−head(M_j)). These corrected vectors have exact head b and converge to M. It follows that the infimum of squared norms of actual legal vectors with head b equals the minimum over the closed affine constraint set in W. Existence of the latter minimum follows from Hilbert projection.

For b=(1,…,1) and W=J, the unique minimum vector is the indicator of the first N positive coordinates. Its squared norm is Q_N=N/(N+2). Thus RH implies E_N=Q_N for every N. Conversely that identity bounds all E_N by one; the independent Mellin obstruction proves RH from such a bound. Monotonicity and the cofinal argument in CofinalMinimumProof.md yield the cofinal bounded criterion. The subpolynomial criterion follows from the same document. These deductions do not require an attained minimizer in the algebraic legal span; indeed positive-period tail injectivity rules out attainment of Q_N when N>0.

The Lean declaration `PositiveResidueDensityFromRH` only names the classical input. It is not a proof. Neither this note nor the additional elementary derivations discharge that Lean obligation. A complete machine verification must also formalize the classical theorem and the concrete Hilbert/operator identifications, with no new axiom or hypothesis silently standing in for them.

The separate unresolved mathematical assertion is a uniform, or cofinal subpolynomial, upper bound for the actual legal minimum energies. Its implication to RH is already proved. None of the elementary O(N) estimates proves that assertion.

---

# Normalized residue Mellin identities: precise appendix

Date: 2026-09-17. Mathematics completed before Lean drafting.

For an integer d≥1, the project uses the unnormalized residue r_d(n)=n mod d. The handoff instead uses g_d(n)=r_d(n)/d. Its actual Hilbert representative is f_d=(1/d)·digitHilbert(d,1), whose physical sequence is exactly g_d by hilbertSequence_digitHilbert and division by one. This constructs the same vector directly from the core digit Hilbert model, without a DyadicRegularizedNorm dependency. This normalization is essential: the existing residue transform has a factor d.

The existing analytic continuation theorem states, for Re(s)>0,

s·Mellin(r_d)(s)=d·L_d(s),

where L_d is the actual entire conductor function. Real linearity therefore gives the normalized identity

s·Mellin(f_d)(s)=L_d(s).

The already proved conductor identification gives

L_d(s)=ζ(s)(d^{-1}−d^{-s})  (s≠1),

and its value at the removable point is

L_d(1)=(log d)/d.

These are unconditional arithmetic identities. At s=1 this is the *removable continuation* of the product; one must not substitute Lean's totalized riemannZeta 1 directly into the unregularized product, whose conductor factor is zero.

For Re(s)>1/2 the established first-difference HasSum and the new all-H second-difference pairing identify both actual discrete series with the same normalized conductor function:

Σ a_s(n)g_d(n)=Σ b_s(n)C g_d(n)=L_d(s).

In particular both series at s=1 equal (log d)/d. This proves the exact handoff normalization without any missing factor 1/s.

For the wider range Re(s)>0, g_d is bounded, so Σ a_s(n)g_d(n) converges absolutely. The new bounded-function extension detailed in BoundedPositiveMellinProof.md proves equality with L_d by the actual countable step-integral calculation. MellinStepSeriesPositiveHalfPlane.patch adds that provider while preserving the original all-H Re(s)>1/2 declaration. The updated normalized candidate therefore states the first discrete-series formula on the full Re(s)>0 domain; only the second-series wrapper retains the Re(s)>1/2 scope required by the Hilbert criterion.

Finally, the actual second-difference coefficients have total sum one and satisfy the weighted dual summability theorem. With q_n normalized to total mass one, weighted Cauchy–Schwarz gives

1=|Σ b_s(n)|² ≤ (Σ |b_s(n)|²/q_n)(Σ q_n)=D_s.

Thus D_s≥1 for Re(s)>1/2, with no hypothetical zero or approximation assumption.

Source declarations:
- paretoMellin_residue_conductor; paretoMellin_smul.
- nymanConductorLFunction_eq_conductorZeta; conductorSymbol_eq_cpow.
- nymanConductorLFunction_one and conductorZeta_one.
- digitHilbert; hilbertSequence_digitHilbert; digitSequence.
- hasSum_first_mellin_pairing; cesaro_mellin_pairing_hilbert.
- mellinSecond_hasSum_one; mellinSecond_dual_summable; pairing_norm_sq_le; hasSum_mixtureWeight.

The removable value is already proved in the repository; no new analytic continuation or prime-reciprocal input is necessary.

---

# Bounded first-difference Mellin series on Re(s)>0

Date: 2026-09-17. Mathematics completed before Lean drafting.

The wider discrete-series gap closes directly from absolute integrability of the existing physical step integrand. No analytic-uniqueness theorem for a new series is needed.

Let f be a physical Hilbert vector with |F(n)|≤B and σ=Re(s)>0. On x>1,

|F(floor x) x^{-s-1}| ≤ B x^{-σ-1}.

The right side is integrable because σ>0. The step integrand is measurable, so it is absolutely integrable. Partition [1,∞) into the disjoint cells [k+1,k+2). On each cell F(floor x)=F(k+1), and the exact cell integral is

∫_{k+1}^{k+2} F(floor x) x^{-s-1} dx
= F(k+1) [ (k+1)^{-s}−(k+2)^{-s} ] / s.

Here s≠0 follows from σ>0. Countable additivity for an absolutely integrable function gives a genuine HasSum identity. The boundary point x=1 has measure zero, so the integral over [1,∞) equals the existing Pareto Mellin integral over (1,∞). Multiplying the HasSum equality by s gives

Σ a_s(n)F(n)=s·paretoMellin(f,s),   Re(s)>0.

For normalizedResidueHilbert(d), the physical sequence is residueFraction(d) and satisfies 0≤g_d(n)≤1. The already proved normalized analytic identity then gives

Σ a_s(n)g_d(n)=L_d(s),  Re(s)>0.

Consequently the exact unregularized formula is

Σ a_s(n)g_d(n)=(d^{-1}−d^{-s})ζ(s),  Re(s)>0, s≠1,

and the actual convergent series at s=1 equals (log d)/d.

The existing MellinStepSeries module already contains private, proved cell-disjointness, covering, and cell-integral lemmas. The candidate patch stays in that module and factors the existing proof through an explicit integrability helper. It then adds the bounded-function integrability and HasSum provider, preserving the original all-H Re(s)>1/2 declaration.

Read-only source support: the majorant argument exactly follows arithmetic_generator_integrable_positive in ArithmeticMellinPositiveHalfPlane.lean; the countable cell calculation already underlies hasSum_first_mellin_pairing.

No mathematical gap remains in this bounded positive-half-plane extension. Lean candidate code still requires root verification.

---

# Bundled conditional Mellin functional

Date: 2026-09-17. Mathematical specification before Lean drafting.

The new J model uses real ℓ² coordinates u_k with physical decoding
G(k+1)=u_k/sqrt(q_(k+1)). Consequently Σ q_n G(n)^2=‖u‖².

For Re(s)>1/2 define on this actual real Hilbert space

Λ_s(u)=Σ_{k≥0} b_s(k+1) G(k+1).

The dual-square series D_s=Σ |b_s(k+1)|²/q_(k+1) is summable. Weighted Cauchy–Schwarz gives absolute convergence and

|Λ_s(u)|²≤D_s‖u‖², hence |Λ_s(u)|≤sqrt(D_s)‖u‖.

Absolute convergence permits addition and real scalar multiplication through the series, so Λ_s is a genuine bounded real-linear map J→ℂ.

The constructed cesaroOperator has physical coordinates C(F). The already proved all-H series identity therefore gives

Λ_s(cesaroOperator f)=s·paretoMellin(f,s).

The constructed conditionalOne equals cesaroOperator(hilbertOne), and paretoMellin(hilbertOne,s)=1/s. Since Re(s)>1/2 implies s≠0, this gives Λ_s(conditionalOne)=1.

These are identities for the bundled map, not merely a formal series notation.

For the complexification use J_ℂ = ℓ²(ℕ,ℂ), with G(k+1)=u_k/sqrt(q_(k+1)). Define the actual Hilbert vector

r_s(k)=conjugate(b_s(k+1))/sqrt(q_(k+1)).

Its squared norm is exactly D_s, by the established dual summability. The complex-linear functional is the genuine Riesz functional u↦⟨r_s,u⟩. The ℓ² inner-product series is exactly Σ b_s(k+1)G(k+1), so this construction packages the required series without an assumed convergence or continuity assertion.

Cauchy–Schwarz gives operator norm at most ‖r_s‖; evaluating at r_s gives equality, including the zero-vector case by a separate elementary case split. Therefore the complex operator norm is exactly sqrt(D_s).

The coordinatewise inclusion of the real J model into J_ℂ is a real-linear isometry. Composing the complex functional, restricted to real scalars, with this inclusion gives the real J→ℂ functional and the stated C(f)/conditionalOne identities. The same identities on the embedded vectors hold for the complex functional.

Scope is explicit: the complexified functional is complex-linear and has norm exactly sqrt(D_s); its restriction to real J is real-linear and has norm at most sqrt(D_s). No claim of equality for the real operator norm is made. No new mathematical assumptions, zeta-zero hypotheses, or RH converse are used.

---

# Randomized finite coefficients: exact expected quadratic loss

Ordinary mathematical completion of original handoff Section 9 / completion Section 12, written before preparation of the Lean candidate. This proof is independent of RH and makes no independence assumption.

Let (Ω,Σ,P) be a probability space, E a real Hilbert space, X:Ω→E strongly measurable and square integrable, and e∈E fixed. Write m=∫X dP and Z=X−m.

Square integrability implies Bochner integrability by Cauchy–Schwarz and P(Ω)=1. Also Z and e−X are square integrable, because addition/subtraction of a constant preserves L² on a finite measure space. In particular all three squared norms below are integrable. The scalar mixed term ⟨e−m,Z⟩ is integrable since its absolute value is bounded by ‖e−m‖‖Z‖.

Bochner integration and P(Ω)=1 give ∫Z=0. The exact pointwise identity is

‖e−X‖²=‖e−m‖²−2⟨e−m,Z⟩+‖Z‖².

The continuous linear functional z↦⟨e−m,z⟩ commutes with Bochner integration. Consequently the mixed term has integral zero, and

∫‖e−X‖² dP=‖e−m‖²+∫‖X−m‖² dP.

Nonnegativity of the last integrand proves the deterministic-mean lower bound. This is an exact signed expansion; there is no absolute-value replacement of a correlation.

Now let I be a finite index type, let w_i∈E, and let A:Ω→ℝ^I have square-integrable coordinates. Equivalently, A belongs to L² with values in the finite-dimensional coefficient space. Define the continuous linear synthesis map W(c)=Σ_i c_i w_i. Then X=W(A) lies in L² and

∫X=W(∫A)=Σ_i (∫A_i)w_i.

Writing a_i=∫A_i and using linearity pointwise yields

∫‖e−Σ_i A_i w_i‖² dP
=‖e−Σ_i a_i w_i‖²
 +∫‖Σ_i(A_i−a_i)w_i‖² dP.

This uses the full distribution of the coefficient vector. The coordinates may be arbitrarily dependent. Finite second moments are the only probabilistic hypothesis beyond measurability and normalization.

For any continuous linear operator C:E→H into another real Hilbert space, apply the same theorem to C(e), the directions C(w_i), and the same coefficients. Continuity of C preserves L², so

∫‖C(e−WA)‖² dP
=‖C(e−Wa)‖²+∫‖CW(A−a)‖² dP.

Thus the result applies to the actual conditional-mean contraction once instantiated in its Hilbert-space model. It does not assert boundedness of C's inverse or remove the within-fiber energy from any other identity.

Finally, if L:ℝ^I→ℝ^J is a fixed linear map and L(A)=b almost surely, integrability gives L(a)=b. Therefore deterministic mean coefficients preserve any almost-sure affine feasibility constraint. Randomizing a fixed finite correction space cannot improve expected quadratic loss below its deterministic feasible minimum. No existence theorem for a small-energy arithmetic family follows from this fact.

## Concrete arithmetic consumer

The new CesaroWeightedContraction module supplies `Analysis.Cesaro.cesaroOperator` on `ThresholdHilbert`. Its output coordinate k is sqrt(q_(k+1))·C(hilbertSequence f)(k+1), so its squared Hilbert norm is exactly the desired conditional-mean energy. Every actual legal arithmetic direction has a summable weighted square and a zero anchor. Encoding it with `sequenceHilbert` therefore recovers the identical physical arithmetic function, without an assumed embedding law or summability premise. Substituting this operator and these encoded legal directions in the theorem above is the literal arithmetic application; deterministic mean coefficients remain in the same finite legal span.
