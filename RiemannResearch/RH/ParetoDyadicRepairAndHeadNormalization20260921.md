# Pareto continuation: repaired-packet obstruction and reciprocal-head normalization

Date: 21 September 2026.
Starting published commit: `9d0271e6d529644b676b9b7fa9b40f166c230af3`.

This continuation follows the two attached handoffs. It investigates the
proposed three-scale repair and the actual full-dictionary odd-moment
problem. RH remains unresolved.

## The repaired packets have a positive full-energy floor

Let `T_2 f(j)=2 f(floor(j/2))`, with `f(0)=0`, be the actual Pareto Hilbert dilation.
Its exact norm identity is `||T_2 f||^2=2||f||^2`.
For the matched packets `p_d=g_d-2g_(2d)`, Lean proves

\[
T_2p_d=2p_{2d},\qquad
q_d=p_d-4p_{2d}=(I-2T_2)p_d.
\]

Writing `R=I-2T_2`, the complete energy, including the signed mixed term, is

\[
\boxed{\|Rf\|^2=9\|f\|^2-4\langle f,T_2f\rangle.}
\]

The exact dilation norm and reverse triangle inequality give

\[
\boxed{\|Rf\|\ge(2\sqrt2-1)\|f\|.}
\]

For every finite signed odd-modulus mixture with
`sum b_d/d^2=1`, it follows that

\[
\boxed{
\left\|\sum_d b_dq_d\right\|^2
\ge (2\sqrt2-1)^2\frac{81|\zeta(2)|^2}{16}>0.
}
\]

The same repair really does cancel the Mellin value at `s=2` for every
Hilbert vector. Thus that exact cancellation coexists with norm expansion.
For arbitrary repair order `r`, the checked stronger estimate is

\[
\boxed{
\left\|R^r\sum_d b_dp_d\right\|^2
\ge (2\sqrt2-1)^{2r}\frac{81|\zeta(2)|^2}{16}.
}
\]

Since `2sqrt(2)-1>1`, increasing this repair order cannot produce small
energy, even when the coefficients and dictionary change with the order.
This settles the proposed repaired-packet route negatively. It does not
bound the unrestricted odd Schur optimizer from below.

Module: `RH/ParetoOddMomentDyadicRepair.lean`.
Key declarations: `dyadicMellinRepair_energy`,
`mellinRepairedCombination_energy_lower`,
`iteratedDyadicPacket_energy_lower`, and
`iteratedDyadicPacket_uniform_floor`.

## A general obstruction to reciprocal-head cancellation

For the full finite dictionary, including every even and composite modulus, put

\[
F_c=\sum_{d\ge2}c_dt_d,\qquad
h(c)=\sum_{d\ge2}\frac{c_d}{d},\qquad
J(c)=\sum_{d\text{ odd}}\frac{c_d}{d^2}.
\]

Here `h` is the first coordinate of the original residue combination.
It is not the first coordinate of `F_c`: the tail atoms already have that
coordinate removed. Let `z=z_2` be the existing infinite coprime certificate and

\[
\kappa=1+\frac{\|z\|^2}{2}=\frac{\pi^2}{\pi^2-8}.
\]

The exact certificate identity and its quantitative consequence are

\[
\boxed{\langle F_c,z\rangle=h(c)-\kappa J(c),}
\qquad
\boxed{|h(c)-\kappa J(c)|\le\|F_c\|\,\|z\|.}
\]

Thus, for `J=1`, small tail energy forces `h` toward `kappa`.
In particular,

\[
\boxed{J(c)=1,\ h(c)=0
\quad\Longrightarrow\quad
\|F_c\|^2\ge\frac{\kappa^2}{\|z\|^2}>0.}
\]

This excludes every exactly reciprocal-head-cancelling normalized signed
family, not just the three-scale construction. Enlarging the support or
changing the finite stencil does not evade this bound while `h=0` is retained.

## A useful exact normalization for the continuing search

For arbitrary coefficients with `J=1`, change only the coefficient at modulus two:

\[
\boxed{c_2^{\sharp}=c_2+2(\kappa-h(c)).}
\]

Every odd coefficient is unchanged, so `J(c sharp)=1`, while
`h(c sharp)=kappa` exactly. The corrected tail vector satisfies

\[
F_c^\sharp=F_c-2\langle F_c,z\rangle t_2,
\qquad \langle F_c^\sharp,z\rangle=0,
\]

\[
\|F_c^\sharp\|
\le (1+2\|z\|\,\|t_2\|)\|F_c\|.
\]

The full signed energy is also retained exactly, with
`a=inner(F_c,z)`:

\[
\boxed{\|F_c^\sharp\|^2
=\|F_c\|^2-4a\langle F_c,t_2\rangle+4a^2\|t_2\|^2.}
\]

The constant is independent of the dictionary and coefficients. Hence
arbitrarily small full-tail witnesses with `J=1` exist if and only if
they exist with the additional exact normalization `h=kappa`.
This is an admissible restriction of the search, rather than a new
unproved requirement. The existence of either witness family remains Open.

The original checked conditional endpoint implies RH from this witness
condition. No converse from RH is newly asserted; the previous classical
RH-to-density provider remains separate.

Module: `RH/ParetoOddMomentHeadNormalization.lean`.
Key declarations: `oddMomentHead_certificate_identity`,
`head_zero_oddMoment_energy_lower`, `normalizeOddHead_synthesis`,
`normalizeOddHead_norm_le`, and `oddMoment_small_tail_iff_normalized_head`.

**Next research target:** construct signed coefficients with
`J=1`, `h=kappa`, and arbitrarily small complete tail energy, using
independent even corrections and retaining the full Gram mixed terms.
Equivalently, prove the existing defect capacities `Q_n` unbounded.

## Why DPP was not used

No additional arithmetic estimate from DPP was identified. Any sampling
scheme whose realizations are normalized repaired packets still produces
vectors subject to the deterministic lower bounds above. Sampling cannot
remove this pathwise obstruction. The attached DPP window criteria still
require an unproved unscaled zero-deficit premise; their formulation does
not establish the needed small-energy witnesses.

No DPP probability theorem is newly claimed or formalized here.

## Verification and continuation

The dyadic candidate passed with exit code 0 in 31.739 seconds in job
`job_GOKtQ6XW6Ls_ali2J8SEkArRp2qOdRKV`. Its two audited endpoint theorems
use only `[propext, Classical.choice, Quot.sound]`.
The final publishing checkpoint supplies installed-module acceptance.

The head-normalization candidate passed with exit code 0 and no warnings in
30.729 seconds in job `job_tC-Kf2-B051bv3ssYboArqS5ppYvvVa0`.
Its three audited results (the normalized-head equivalence, the universal
head-zero floor, and the exact correction energy) use only
`[propext, Classical.choice, Quot.sound]`.

Together the two modules add 34 proved theorems and six definitions.
No `sorry`, `admit`, project-local axiom, unsafe declaration, RH hypothesis,
not-RH hypothesis, density provider, or zeta-zero-existence input is added.
The statements about small-energy witness existence remain equivalences
or conditional consequences: no such witness family has been constructed.

The publishing checkpoint validated both installed modules against their
declared imports and published their exports and research report.
It returned `state: succeeded`, `committed: true`, and `pushed: true`.
Job: `job_WRNQpwowDgDtpPhWA75pRysLdkbSrFN8`.
Code publication commit: `a923ff6c4ec38d8062bf2c7505433d03a5dcd4b2`.
The affected-module build/cache phase took 55.499 seconds; the complete
checkpoint took 65.139 seconds. Cosmetic style warnings remain, with no
compilation errors. No separate full-project build was submitted.

The theorem-catalog patch initially failed before that checkpoint, so a
separate documentation-only checkpoint records the corrected catalog and
this completed receipt. It does not change or reverify the Lean source.

Workspace resume token: `ws_iIiyKm3NO1JdN1JglnG5AR-O6kIsmqB4`.

Project root:
`/home/cri_2025/lean-agent-workspaces/ws_iIiyKm3NO1JdN1JglnG5AR-O6kIsmqB4/RiemannResearch`.
