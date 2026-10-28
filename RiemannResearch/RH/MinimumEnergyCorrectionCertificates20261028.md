# Minimum-energy exact-head correction certificates

28 October 2026. Continuation of the supplied research agenda, priorities 1–4.
Base commit: 0556a4c7a2185140eff485c2bc30779fa1f75a67.

## Mathematical outcome

The finite correction interface now retains every signed term and the full
norm-square remainder. Concrete squarefree legal vectors give complete energy
at most one at heads two and five. A separate conductor-gap argument shows that
the canonical stage j=14 has minimum energy strictly greater than one.
This excludes the bound C=1 for the entire canonical family; it does not exclude
a bound by a larger finite constant, a bounded cofinal subsequence, or slower heads.
No uniform bound and no proof of RH have been obtained.

## Signed correction and schedule comparisons

Write W for the legal zero-head space, F for the feasible seed, and P for its
complete-Q orthogonal projection onto W. For every u in W,

    2 <F,u>_Q - ||u||_Q² = ||PF||_Q² - ||PF-u||_Q².

Thus any actual correction satisfying

    ||F||_Q² - C <= 2 <F,u>_Q - ||u||_Q²

bounds the true minimum by C. The new CRT correctionBlock definition is a
finite linear combination of compensated conductors. Its dictionary membership
and zero head are proved for arbitrary real coefficients; sparse coefficients
therefore implement smaller structured correction blocks. The coefficient
certificate keeps the full source pairing and Gram quadratic form.

The one-direction bound is

    E <= ||F||_Q² - <F,v>_Q² / ||v||_Q²,  v in W, v != 0.

The generic dictionary and head comparison theorems prove exact
squared-distance identities, then derive monotonicity. A fixed-head dictionary
enlargement decreases the minimum; a fixed-dictionary head enlargement increases
it. No monotonicity assertion is made for simultaneous changes.

Files:
- QResidueEnergyCertificates.lean: correction_gain_completion,
  exactHeadAdjustment_le_one_direction, exactHeadAdjustment_dictionary_gain,
  exactHeadAdjustment_head_gain, and their inequality consequences.
- QCRTCorrectionCertificates.lean: correctionBlock, correctionBlock_mem,
  correctedSeed_legal_exact_head, minimumEnergyApproximant_le_block_certificate.

## Concrete upper bounds with the entire infinite tail

The actual vectors

    f6 = g2 + 2*g3 - g6,
    f30 = g2 + g3 + g5 - g30

take only the values zero and one. They have exact heads through 2 and 5,
respectively, and belong to their squarefree divisor stages. Since Q is a
probability measure, their complete norm squares are at most one.
There is no numerical tail cutoff in these proofs.

QCRTFiniteCertificates.lean proves the actual canonical consequences

    ||minimumEnergyApproximant 1||² <= 1,
    ||minimumEnergyApproximant 4||² <= 1.

## A conductor-gap obstruction to the constant one

QCRTConductorGap.lean proves that two vectors in a finite residue dictionary
which agree through H must agree through K if there is no dictionary conductor
in (H,K]. The common head can be arbitrary.

For L=30030 there is no divisor in 16,...,20. Consequently every legal
divisor-stage vector with exact head through 15 agrees with the coprime-count
seed through 20. The forced values are 1 through 16, 2 at 17 and 18, and 3 at
19 and 20. The unnormalized energy on these twenty coordinates is exactly

    89848997132687477 / 54192375991353600 > 329/200 > zetaTwo.

The existing zetaTwo_rational_bounds theorem supplies zetaTwo < 329/200.
The new finite_raw_energy_le lemma includes the complete infinite norm on
the upper side of the inequality. It follows that every such vector has
norm square greater than one. In particular,

    minimumEnergyApproximant_fourteen_gt_one:
      1 < ||minimumEnergyApproximant 14||².

The same proof certifies that every period-210, exact-head-10 vector has
complete energy greater than one. These are lower bounds on every feasible
vector, not lower bounds only on a numerical trial vector.

Enlarging the period can add conductors inside these gaps. This is one reason
to separate period growth from head growth in further experiments.

## Reproducible finite candidate certificates

The existing CRTGramMinimizersResearch20261028.md already records complete-Q
certificates for several maximal-head minima. The present experiments extend
smaller and slower head schedules. They are supplementary rational Python
certificates, distinct from the Lean theorems above.

The scripts and exact witnesses are in the [experiment bundle](https://chatgpt.com/library?file_id=libfile_3a2612c77a048191b8ec721ccd53ffca&account_id=personal).
Unpack it, then run:

    python verify_certificates.py

This standard-library checker verifies 18 fine-denominator and five simple
candidate certificates. Discovery via experiment.py additionally uses NumPy
and SciPy. Every head is checked in exact rational arithmetic. Residuewise
positive weights enclose all inverse-square terms and their infinite tails,
and zetaTwo is enclosed separately by rational bounds. The complete signed
energy identity is checked at every residue.

Representative strict upper bounds for exactly feasible candidates:

| Period L | Head H | Complete energy upper bound |
|---:|---:|---:|
| 6 | 2 | 0.829395 |
| 30 | 4 | 0.896383 |
| 210 | 6 | 0.931542 |
| 2310 | 10 | 0.963277 |
| 30030 | 12 | 0.967726 |
| 30030 | 14 | 0.975244 |

These upper bounds also bound the corresponding minima. The lower endpoint
of a trial-vector interval only bounds that trial vector, and is not a
lower bound on the minimum. The Lean conductor-gap results provide separate
true lower bounds at the two specified stages.

## RH obligation still open

What remains is an explicit expanding-head arithmetic correction family with
one common complete-energy bound, or a bounded cofinal subsequence. The finite
certificate interface and finitely many favorable examples do not provide it.
No new RH theorem with an unproved energy provider has been added.

Only after that provider is established should the existing bounded-exact-head
closure/RH criterion be applied, with its norm/error and indexing conventions.

## Verification record

The isolated conductor-gap check `job_wCTXo9bfPu5ZohCttHIC8uboWiO-M1PI`
succeeded with exit code 0 and reported 118.982 seconds. Its principal
finite lower-bound declarations report only propext, Classical.choice,
and Quot.sound. This duration is the server-reported verification operation,
not a separately instrumented kernel-only duration.

The saved-module import and axiom audit `job_yjfGWy9oFfG3FyAa03RboxMG5Fmfeb5z`
succeeded with exit code 0 and reported 117.511 seconds. All four new modules
compiled, and all seven inspected principal declarations use only propext,
Classical.choice, and Quot.sound. The server's submitted/start timestamps
differ by approximately 0.002 seconds; client polling latency was not measured.

The final server checkpoint is the publication gate for all changed Lean
modules and their affected dependents. The chat reports its terminal job,
validation scope, and exact published commit. Ephemeral checks alone are not
project publication certificates. Workspace-opening and client polling latency
were not individually timed and are not reported as kernel checking time.
