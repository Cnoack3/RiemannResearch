# Möbius factorial jumps, anchored targets, and certified sampling gains

Continuation of `RH_Mobius_ZeroPhase_Handoff_2026-10-21(1).md`, prepared
21 October 2026 for Christian Noack. Base snapshot:
`f26b211eef4f436ef93b96e90f6bea2972d1d219`.

## Scope and verification

This continuation develops actual factorial-block jumps, an obstruction to
linearly compensated cutoff sums, a single-target RH consumer for a restricted
legal dictionary, certified sampled projection gains, and a weaker qualitative
zero-frequency interface. The arithmetic energy provider needed for RH is
still open. The actual zero-density provider is also not supplied.

Final saved-source verification and publication are certified by the terminal
successful Lean-server checkpoint for the containing commit. An accepted job,
an isolated snippet, or an ordinary derivation is not that certificate.
The final report records the decisive job and publication receipt.

## 1. Actual factorial-block jumps

Write
\[
A_{p,d}(n)=v_p(\lfloor n/d\rfloor!),\qquad
\Delta A_{p,d}(n)=A_{p,d}(n)-A_{p,d}(n-1).
\]
The exact identity is
\[
\Delta A_{p,d}(n)=\mathbf1_{d\mid n}\,v_p(n/d)\quad(n>0).
\]
The Lean statement uses actual `Nat.factorial` and `Nat.factorization`.
Its coordinate identity even holds for nonprime factorization indices under
Mathlib's conventions. Consequently, for a finite signed family,
\[
\Delta\left(\sum_d c_d A_{p,d}(n)-\beta n\right)
=\sum_{d\mid n}c_dv_p(n/d)-\beta.
\]
No signed terms are discarded. In particular, a linear correction changes
every jump by the same constant and cannot repair a discrepancy between two
sites that squarefree legality requires to agree.

The concrete ordinary cutoff
\[
T(n)=v_2(n!)-v_2(\lfloor n/2\rfloor!)-v_2(\lfloor n/3\rfloor!)
\]
has jumps \(\Delta T(6)=0\) and \(\Delta T(36)=-1\). Every element of the
constant-enlarged squarefree legal closure has equal jumps at \(6\) and
\(6^2\). Therefore no Q-Hilbert representative of \(T(n)-\beta n\), for
any real \(\beta\), can belong to that closure. This statement quantifies over
a representative; it does not assume every slope gives a Q-integrable vector.

There is also a complete quantitative separation. Let \(h_6\) be the existing
four-site Riesz witness for \(\Delta f(36)-\Delta f(6)\). Its squared norm is
\(2582\zeta(2)\). For any such represented \(x\) and any
\(F\in\mathcal C_{\rm sf}\),
\[
\|x-F\|_Q^2=\frac1{2582\zeta(2)}+
\left\|x-F+\frac{h_6}{2582\zeta(2)}\right\|_Q^2.
\]
Thus the squared error is at least \(1/(2582\zeta(2))\), independently of
the slope. The identity retains the full norm-square remainder.

## 2. The primorial compensation and the old sieve

For squarefree \(L=pM\), with \(p\) prime and \(p\nmid M\), ordinary
Legendre recursion and pairing divisors \(e,pe\) give
\[
\sum_{d\mid L}\mu(d)v_p(\lfloor n/d\rfloor!)
=\sum_{e\mid M}\mu(e)\lfloor n/(pe)\rfloor.
\]
Its compensating slope is
\(\alpha_{L,p}=p^{-1}\sum_{e\mid M}\mu(e)/e\), and its compensated form is exactly
\[
B_{L,p}(n)=-\sum_{e\mid M}\mu(e)g_{pe}(n).
\]
It is legal, but is the existing raw sieve family. This identification does
not evade the previously published sieve-energy obstructions. Moreover,
\[
B_{L,p}(pn)-B_{L,p}(n)=-\sum_{d\mid L}\mu(d)g_d(n).
\]
The individual prime-pair recurrence
\(A_{p,d}(n)-A_{p,pd}(n)=\lfloor n/(pd)\rfloor\) is included in the factorial
block formalization. The finite divisor regrouping and dilation identities
above remain ordinary derivations in this note. Exact Wolfram
checks confirmed the first two identities for \(L=2,6,30,210\), \(p=2\),
and \(0\le n\le100\). Finite checks do not establish any norm limit.

## 3. Removing constants from an anchored dictionary

For \(p>1\), let
\[
V_p=\operatorname{span}_{\mathbb R}
\{g_d:d\ge2,\ d\text{ squarefree},\ p\mid d\}.
\]
All qualifying composite conductors are retained. Define the continuous
three-site charge on the actual Q space by
\[
\ell_p(f)=f(1)+f(p)-f(p+1).
\]
The exact identities are
\[
\ell_p(g_d)=0\ (p\mid d),\qquad
\ell_p(1)=1,\qquad \ell_p(F_p)=0.
\]
For a legal atom, use
\(\Delta g_d(p+1)=1/d-\mathbf1_{d\mid p+1}\) and the impossibility of
\(d\mid p+1\) when \(p\mid d\) and \(p>1\). For the target,
\(F_p(1)=0\) and \(F_p(p)=F_p(p+1)=1\).

The continuous map \(P_pf=f-\ell_p(f)1\) sends \(V_p+\mathbb R1\) into
\(V_p\). Therefore
\[
F_p\in\overline{V_p+\mathbb R1}
\Longrightarrow F_p\in\overline{V_p}
\Longrightarrow F_p\in\mathcal H_{\rm sf}
\Longrightarrow RH.
\]
The last implication reuses the existing single-target Mellin consumer.
This is a **conditional research reduction**: membership has not been proved.
It does not assert that a single target in the unrestricted constant-enlarged
space suffices; the anchored restriction is essential to the argument.

The existing exact-head compactness theorem also yields RH from a uniform
complete-Q bound for anchored-plus-constant approximants matching \(F_p\)
on every finite positive head. That uniform bound remains Open.
Once an exact head reaches \(p+1\), the adjoined constant is already exactly
zero, since the three-site charge can be computed entirely from that head.
This is a finite identity, stronger than merely obtaining vanishing constants
along a limiting sequence.

## 4. Complete signed sampling certificates

Let \(B,E\) be a complete finite weighted form with nonnegative weights
\(w_a\ge0\) and its energy, and put hats
on the form and energy obtained by multiplying weights by \(q_a\), where
\(|q_a-1|\le\delta<1\). The exact source change, for an old-space change \(u\),
is
\[
\widehat B(r-u,z)-B(r,z)
=B((q-1)(r-u),z)-B(u,z).
\]
If \(z\) is screened in the true metric and \(u\) lies in the old space,
then \(B(u,z)=0\) exactly. There is no separate displacement penalty in this
source; the sampling budget is applied to the actual residual \(r-u\).

For \(E(z)>0\), a nonnegative error budget satisfying
\[
\delta^2\widehat E(r)\widehat E(z)
\le(1-\delta)^2\varepsilon^2
\]
gives
\[
\boxed{
\frac{(1-\delta)(|\widehat B(r,z)|-\varepsilon)_+^2}{\widehat E(z)}
\le \frac{B(r,z)^2}{E(z)}.
}
\]
The sampled denominator is positive by relative metric comparison. The
right side is the exact one-direction gain when \(z\) is the actual
screened innovation. The application module also bounds an actual larger
nested-space defect drop, retaining the gains of other directions through
the existing Pythagorean identity.

Complete-Q realization remains explicit: finite weights must include every
arithmetic-progression tail, and the physical vectors must represent the
actual residual and direction. The theorems do not supply positive margins,
new arithmetic directions, or sufficient cofinal accumulation of gains.

## 5. A weaker qualitative zero-frequency interface

Count actual zeros with multiplicity. Let \(N(T)\) be the count,
\(E(T)=\sum_\rho(\Re\rho-1/2)^2\), and let
\(\mathrm{Tail}_\delta(T)\) count copies with
\(|\Re\rho-1/2|>\delta\). For \(\delta\ge0\), the finite estimates are
\[
\delta^2\mathrm{Tail}_\delta(T)\le E(T)
\le\delta^2N(T)+\tfrac14\mathrm{Tail}_\delta(T).
\]
They imply the exact logical equivalence
\[
\left[\forall\delta>0,\quad
\mathrm{Tail}_\delta(T)/N(T)\to0\right]
\iff E(T)/N(T)\to0.
\]
The formulas preserve the original normalizer and handle empty cutoffs with
Lean's zero-division convention. Combining this with the existing actual
reflection estimate removes the horizontal exponential weight at every
fixed frequency. A separately supplied normalized Landau limit then gives
actual ordinate cancellation.

The fixed-strip density hypothesis remains Open as a formal provider. It is
far weaker than RH: any finite collection of off-line zeros is invisible to
this relative-density limit. The torus-to-half-open-bin boundary argument is
also still required for the sampling interface. Neither a growing-frequency
estimate nor a uniform Selberg rate is needed for this qualitative reduction.

Analytic provenance: Ford and Zaharescu, *On the distribution of imaginary
parts of zeros of the Riemann zeta function*, Introduction (Hlawka's classical
unconditional fixed-frequency equidistribution),
<https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>.
This reference supports the analytic background; it does not discharge a
Lean hypothesis.

## 6. Next arithmetic task

The new module map is:

| Module | Main declarations |
| --- | --- |
| `NumberTheory/PrimeFactorialBlockJumps.lean` | `factorialBlock_sub_pred`, `compensated_sum_succ_sub`, `factorialBlock_pair` |
| `RH/QFactorialCutoffObstruction.lean` | `compensatedFactorialCutoffThreeTwo_error_energy_exact`, `compensatedFactorialCutoffThreeTwo_error_sq_lower_bound` |
| `RH/QPrimeAnchoredTarget.lean` | `anchoredWithConstants_exact_head_mem_span`, `riemannHypothesis_of_bounded_anchored_exact_heads` |
| `Analysis/FiniteSampledGain.lean` | `screened_sampled_gain_lower_bound` |
| `Analysis/SampledScreenedGain.lean` | `finite_sampled_budget_le_nested_gain` |
| `Analysis/ActualZeroFixedStripConcentration.lean` | `fixedStripConcentration_iff_relativeEnergy_tendsto_zero`, `tendsto_normalized_ordinate_of_fixedStrip` |

1. Use the exact factorial jumps to reject inadmissible corrections before
   estimating their norm. Avoid relabeling the raw sieve as a new family.
2. Seek a genuinely different anchored family with bounded complete exact-head
   energy, or produce independent lower bounds on sampled certified gains of
   actual legal innovations. Preserve all squarefree composite conductors.
3. For sampled gains, track every complete weight and signed correlation;
   a positive margin must exceed its explicit discrepancy budget.
4. Supply the fixed-strip density provider and the null-boundary box theorem
   for actual zeros if pursuing the qualitative sampling path. Accurate
   sampling alone does not force the limiting legal defect to vanish.

No proof of RH, anchored target membership, or the missing uniform arithmetic
energy/gain estimate is claimed.

## 7. Verification and runtime provenance

The following are precursor checks, not substitutes for the final saved-source
checkpoint described above. The successful targeted checks cover 18 public
theorems: five factorial identities, nine finite sampling results, and four
projection-gain results. The first checkpoint also successfully built the
eight-theorem fixed-strip module, bringing compiler-confirmed declarations to
26 before the repairs recorded below.

| Check | Lean-server job | Outcome | Server elapsed seconds |
| --- | --- | --- | ---: |
| Saved `PrimeFactorialBlockJumps.lean` | `job_hnbYOcb7P1Qeqe-1VBoSQBeulxEvVX7f` | Verified, exit 0 | 17.093 |
| Saved `SampledScreenedGain.lean`, including a successful dependency build of `FiniteSampledGain.lean` | `job_GpxAcM8iORq549u7hzqBaksrbjuV8JHZ` | Verified, exit 0 | 263.864 |
| Exploratory combined candidate | `job_-d9IpdtxIGL3ms4mZ-h-DvPbmHaGVlZK` | Wall timeout | 300.095 |
| Exploratory combined candidate | `job_-unORO6j6FlWkxnPg49F_j8uOoDLEMH6` | Wall timeout | 600.232 |
| First saved cutoff proof | `job_FRL1PlAKmP-UOoVxUNEcStzXFOgwtSlt` | Wall timeout | 600.307 |
| Cutoff proof using abstract algebra helpers | `job_6dMP6To_UnSRbCU4BMdzd6HJ8aMm9inR` | Wall timeout | 300.085 |
| Six saved modules and 46 axiom queries | `job_glXk7-7TlqRDnCgRgmcUbQ66N2U-jBse` | Wall timeout; no axiom report obtained | 1200.072 |
| First checkpoint | `job_fEssQ7IcKjhoPD4B-4t8kkSQ2KanUnbF` | Fixed-strip module built; two RH modules returned proof-script errors; no publication | 2296.853 |

An earlier 34.342-second exploratory run reported two finite-sampling tactic
errors. Both were corrected before the successful saved sampling check.
The cutoff proof was subsequently restructured to use RHS-only small-valuation
calculations and congruence, with local irreducibility of `factorialBlock`.
This prevents accidental tactic unfolding of large concrete factorials; the
timeouts themselves do not establish that such unfolding caused the delay.

The first checkpoint returned concrete errors: implicit factors were not
resolved in one factorization lemma, a casted numeral prevented a denominator
rewrite, and the continuous-projection closure proof needed explicit set and
image typing. These are proof-script errors; they do not refute the stated
mathematical claims. The candidate sources were repaired before the final
validation retry.

The timeout logs ended with dependency-build/replay output and did not return
diagnostics for the proposed remaining modules. These receipts therefore do
not certify or refute those proofs. In particular, no completed axiom audit
is claimed. A source scan of the six new modules found no `sorry`, `admit`,
unsafe declarations, or added axioms.

The elapsed values above are server job durations, including dependency work,
not isolated kernel proof timings. Client polling, source preparation, and
workspace startup time are separate and were not independently benchmarked.
Publication and the final saved-source validation result must be read from the
terminal checkpoint receipt for the containing commit.
