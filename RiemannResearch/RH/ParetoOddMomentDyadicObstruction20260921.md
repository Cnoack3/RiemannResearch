## Continuation: matched dyadic corrections and their Mellin obstruction

Date: 21 September 2026. Starting published commit:
aa346763a2dc6510a8359b73780b0eacf738818c.

This continuation investigates a concrete signed construction suggested by
the exact parity reduction. It proves that this construction cannot supply
the small-energy witnesses. It does not obstruct the unrestricted Schur
optimizer and does not prove RH.

### A genuine signed, exactly head-cancelling family

Write \(g_d(j)=(j\bmod d)/d\), and let \(t_{d-2}\) be its actual tail vector.
For each odd \(d\ge3\), form
\[
p_d=t_{d-2}-2t_{2d-2}=g_d-2g_{2d}.
\]
The equality is in the actual Pareto Hilbert space: the removed site-one
terms cancel exactly. For every physical \(j<d\), \(p_d(j)=0\).

For arbitrary signed real amplitudes \(b_d\) on finitely many odd moduli, put
\[
F_b=\sum_{d\ \mathrm{odd}}b_dp_d,\qquad
J(b)=\sum_{d\ \mathrm{odd}}\frac{b_d}{d^2}.
\]
There is an explicit coefficient vector in the original full dictionary:
the coefficient at odd \(d\) is \(b_d\), and that at even \(2d\) is \(-2b_d\).
Thus its original odd reciprocal-square moment is exactly \(J(b)\).
Lean verifies both the finite synthesis and this moment identity.
All odd composite moduli and every signed cross term are retained.

### Exact Mellin identity and a positive full-energy floor

The actual bounded Mellin functional at \(s=2\) satisfies
\[
\boxed{\mathcal M_2(p_d)=-\frac{\zeta(2)}{4d^2},\qquad
       \mathcal M_2(F_b)=-\frac{\zeta(2)}4 J(b).}
\]
This follows from the already checked normalized residue transform,
with its factors \(1/d\) and \(1/s\) retained. There is no zero or RH premise.

Every such \(F_b\) vanishes at physical sites one and two. Applying the
proved tail Cauchy-Schwarz estimate beyond \(x=3\) gives
\[
|\mathcal M_2(F_b)|^2\le \frac{\|F_b\|^2}{81}.
\]
Consequently, if \(J(b)=1\),
\[
\boxed{\|F_b\|^2\ge\frac{81}{16}|\zeta(2)|^2>0.}
\]
The constant is exact. Classically it equals \(9\pi^4/64\); the new Lean
theorems retain the zeta expression and use Mathlib's proved nonvanishing
of zeta in \(\operatorname{Re}(s)>1\) to verify strict positivity.
They do not require a separate formal evaluation of \(\zeta(2)\).

This bound applies to all signed mixtures, not just positive averages.
It rules out arbitrarily small energy throughout the matched-pair family.

### Moving the active moduli outward is worse

If \(b_d\) is nonzero only for \(d>N\), the entire physical head through \(N\)
vanishes. The same exact Mellin value is retained, and Lean proves
\[
\boxed{\|F_b\|^2\ge
       \frac{3(N+1)^3}{16}|\zeta(2)|^2\quad\text{when }J(b)=1.}
\]
This is an explicit cubic lower bound, without asymptotic notation or
an omitted infinite tail. Finite exact head cancellation alone does not
provide the required vanishing energy.

### What an independent even correction must accomplish

For any actual Hilbert correction \(v\), when \(J(b)=1\),
\[
\boxed{\mathcal M_2(F_b+v)=\mathcal M_2(v)-\zeta(2)/4,}
\]
and
\[
\boxed{\|F_b+v\|^2\ge
3|\mathcal M_2(v)-\zeta(2)/4|^2.}
\]
These are also checked. They apply in particular when \(v\) is the difference
between the unrestricted optimal even correction and the matched
correction. A successful small-energy family must make the additional
correction's Mellin value approach \(\zeta(2)/4\). Meeting this one condition
is necessary, not sufficient for RH or for small energy.

### An explicit repair of this Mellin obstruction

The next packet is
\[
q_d=p_d-4p_{2d}=g_d-6g_{2d}+8g_{4d}.
\]
It still vanishes at every physical \(j<d\). For odd \(d\), the coefficients
at \(2d\) and \(4d\) are both even-modulus corrections, so its odd
reciprocal-square moment remains \(1/d^2\). Lean verifies this coefficient
moment, the actual Hilbert-vector identity, and
\[
\boxed{\mathcal M_2(q_d)=0,\qquad
       \mathcal M_2\!\left(\sum_d b_dq_d\right)=0.}
\]
Thus the \(s=2\) obstruction can be repaired explicitly without changing
the odd moment. This is a concrete signed construction, but no decay
estimate for its full norm has been established. Vanishing of this single
bounded functional does not imply vanishing Hilbert norm.

### Scope and next target

The handoff's unrestricted even optimizer
\(-G_{EE}^{-1}G_{EO}b\) is not the same as imposing \(c_{2d}=-2c_d\).
The new lower bound concerns the latter restricted coefficient family.
It does not give a lower bound for the original screened form \(b^TS_nb\).

**Established:** explicit matched-pair synthesis and odd moment, exact
head cancellation, exact Mellin evaluation, a positive energy floor for
all signed mixtures, its cubic strengthening under escaping modulus
support, the required Mellin cancellation by an additional correction, and an explicit
three-scale packet that cancels this obstruction while preserving the odd moment.

**Open:** estimate the complete signed Gram energy of the repaired packets,
or exploit independent even coefficients, retaining the complete
Schur correction, to construct odd-moment-one vectors with vanishing
full tail energy; equivalently, prove the actual defect capacities \(Q_n\)
unbounded. RH remains unresolved.

Module: RiemannResearch/RH/ParetoOddMomentDyadicObstruction.lean.

The new results have no RH, not-RH, critical-zero existence, or
RH-to-density assumption. No admitted proof, project-local axiom, or
unsafe declaration is introduced.

### Candidate verification

The complete candidate passed Lean with exit code 0 in about 33 seconds.
Job: `job_BQosMauGZqcBHWa4Rld-kudyqn5x4joB`.

This addition contains 19 proved theorems (including one private helper)
and four definitions. Nine key axiom audits reported only
`[propext, Classical.choice, Quot.sound]`.
There are cosmetic tactic-style warnings, with no admitted proof or
domain-specific axiom. The publishing checkpoint supplies final
installed-module acceptance.
