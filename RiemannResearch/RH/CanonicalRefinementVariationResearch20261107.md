# Canonical refinement energy and positive logarithmic variation

Continuation of the 7 November 2026 prime-power update handoff.

## Conclusion

The newly revealed old leakage has a negative contribution to the signed
canonical energy change. An exact arithmetic Parseval formula identifies
that revealed energy. A positive-logarithmic-variation hypothesis for the
actual LCM canonical sequence implies Mathlib's Riemann Hypothesis.

The variation hypothesis is **Open**. These results do not prove the actual
canonical growth estimate or RH.

## Complete-Q refinement identity

Retain the handoff's actual canonical lifts, targets and leakage:
\[
 F_L\in V_L,\quad T_LF_L=h_L,\quad r_L=F_L-h_L,\quad E_L=\|F_L\|_Q^2.
\]
For \(L,M\ge2\), put
\[
 t=T_Mr_L,\qquad q=r_L-t,\qquad z=r_M-q,\qquad
 \delta=L^{-2}-M^{-2}.
\]
Here \(t\in C_M\) and \(q,z,r_M\perp C_M\). The exact identities are
\[
 \|r_M-r_L\|_Q^2=\|t\|_Q^2+\|z\|_Q^2,
 \qquad
 \langle r_L,r_M-r_L\rangle_Q
 =\langle q,z\rangle_Q-\|t\|_Q^2,
\]
and therefore
\[
 \boxed{E_M-E_L=\delta-\|t\|_Q^2+\|z\|_Q^2+
                      2\langle q,z\rangle_Q.}
\]
The energy identity itself does not need \(L\mid M\). If \(L\mid M\), then
\[
 z=(I-T_M)(F_M-F_L),\qquad
 \|F_M-F_L\|_Q^2=\delta+\|t\|_Q^2+\|z\|_Q^2.
\]
This explains the different signs: revealed old leakage increases the source
and update norms, but its contribution to signed energy growth is negative.

For every real \(\alpha\), without a sign assumption on \(\alpha\),
\[
 E_M\le(1+\alpha)E_L
 \quad\Longleftrightarrow\quad
 \|z\|_Q^2+2\langle q,z\rangle_Q
 \le\|t\|_Q^2+\alpha E_L-\delta.
\]
Neither side of this equivalence is asserted unconditionally.

The four generic Hilbert-space lemmas are owned by
Analysis/OrthogonalRefinementEnergy.lean, in namespace InnerProductSpace.
The ten specialized theorems and three vector definitions extend
RH/QCRTNestedCutoffs.lean, which already owns canonical updates.

## Exact arithmetic formula for revealed energy

Let \(\psi_d\) be the repository's divisor wavelet and let
\(J_2(d)=\|\psi_d\|_Q^2\). The existing complete orthogonal basis gives
\[
 \boxed{\|T_Mr_L\|_Q^2
   =\sum_{\substack{d\ge1\\d\mid M,\ d\nmid L}}
        \frac{|\langle F_L,\psi_d\rangle_Q|^2}{J_2(d)}.}
\]
The formal theorem is QCRTLeakageParseval.revealed_leakage_parseval.
Its infinite sum has finite support, namely divisors of \(M\) not dividing \(L\).
Every coefficient is an inner product over the entire physical Q measure.

Two supporting theorems prove orthogonality outside a cell cutoff and the
exact wavelet coordinate of its conditional projection. This is an arithmetic
coordinate formula for the same revealed norm as the handoff's cell
innovations. It does not identify an unnormalized divisor-row bound with a
physical inverse-Gram bound.

## Conditional RH criterion

Use the existing offset indexing
\[
 L_M=\operatorname{lcm}(1,\ldots,M+2),\qquad
 E_M=\|\mathrm{lcmLift}(M)\|_Q^2,
\]
and define
\[
 A_M=\sum_{n=0}^{M-1}
       [\log(1+E_{n+1})-\log(1+E_n)]_+.
\]
Finite signed increments telescope exactly, giving
\[
 0\le\log(1+E_M)\le\log(1+E_0)+A_M.
\]
The new generic theorem proves that \(A_M/\log(M+2)\to0\) forces
\(\log(1+E_M)/\log(M+2)\to0\). The specialized theorem
QCRTPositiveLogVariation.riemannHypothesis_of_positive_log_variation
combines this with the existing actual Mellin-zero power floor:
\[
 \boxed{A_M=o(\log(M+2))\ \Longrightarrow\ \mathrm{RiemannHypothesis}.}
\]
The energy is the actual canonical squared norm; no abstract substitute,
detector assumption, Euler-tail provider or completeness hypothesis is added.

This is a conditional research reduction. The sole new substantive input is
the displayed sublogarithmic bound for \(A_M\), and its status is **Open**.
The four generic variation theorems are in
Analysis/PositiveLogVariation.lean; the actual RH assembly is in
RH/QCRTPositiveLogVariation.lean.

A paper comparison explains the relation to the handoff's sufficient target:
for positive \(E_n\),
\[
 [\log(1+E_{n+1})-\log(1+E_n)]_+
 \le [(E_{n+1}/E_n)-1]_+.
\]
For an increasing step use \(\log(1+x)\le x\) and
\(1+E_n\ge E_n\); for a decreasing step the left side vanishes.
This comparison is not one of the newly formalized declarations.

## Scope and remaining work

- **Established by the new formal arguments:** signed refinement,
  actual hidden-response identification, complete revealed-energy Parseval,
  exact finite telescoping and the conditional variation-to-RH implication.
- **Open:** estimate the actual hidden response and its signed correlation,
  or prove the actual positive-logarithmic-variation bound.
- **Not newly formalized:** the handoff's explicit gcd-cell masses, its
  noncanonical arithmetic obstruction, its full screened coordinate assembly,
  its finite-sum raw-source corollary, or its rational numerical certificates.

The legal-affine condition \(h_L+r_L\in V_L\) still matters for any attempted
growth estimate. The noncanonical counterexample in the handoff does not
refute a canonical-specific estimate.

## Provenance and verification

Source for the research questions: the user-provided
CanonicalPrimePowerUpdatesResearch20261107(1).md, Sections 2, 5 and 7,
published as RH/CanonicalPrimePowerUpdatesResearch20261107.md.
The refinement identities are elementary Hilbert-space deductions, and the
variation criterion uses the repository's existing QCRTZeroGrowth
and SubpolynomialWindowGrowth theorems. No novelty claim is made.

The retained workspace was recovered at published commit
cca9edcaf7e73cdcdff72c07a63501aa715f8424.
The initial opening request timed out after 120.125 seconds; later read-only
requests recovered access. That delay is not a Lean verification duration.

Combined candidate verification and all 22 axiom audits passed in
job_asYRMQ6rALT9ecJijpikvidwQmLOeZR5, with a server-reported duration of
8.250 seconds. All audits showed only propext, Classical.choice and
Quot.sound. This was a combined proof check, separately followed by
verification of the saved owning modules and the publication checkpoint.

The five saved owning modules and all 22 axiom audits then passed in
job_Cdcr0liLJN2Iy1FABGf1l_XKkMCXGGIW, with reported verification time
20.597 seconds. The audit output was untruncated. The only module warning
was an existing missing-header style warning, corrected before checkpoint.
Submission-to-start delay for this job was below 0.001 seconds. Its first
status request was inadvertently made about 20 seconds after submission;
after the returned 60-second interval, the next request observed success.
Polling and request latency are distinct from the reported verification time.
The final checkpoint separately audits and validates the unpublished delta
and any integration, then publishes only the successfully validated commit.
