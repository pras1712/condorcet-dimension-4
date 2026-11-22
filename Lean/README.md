# Lean formalization

Theorem 1 is `ElectionLift.coverage_bound` in [Theorem.lean](Condorcet/Theorem.lean).
For every integer $k \ge 2$, it proves
$C_k \le 1 - 3A_2/(k+1) \le 1 - 3z/(k+1)$, where
$z = 351449648252133/512000000000000$. Here $A_k$ is the worst-case opposition
to the best committee of size $k$, and $C_k = 1-A_k$ is the largest coverage
guarantee. A strict ballot is an injective rank function, with smaller ranks
preferred. An outsider beats a committee on a ballot if the voter ranks that
outsider above every committee member.

The finite-election statement is `ElectionLift.finite_strictly_above`.
For each $b < 3z/(k+1)$ it gives one finite strict election in which each
$k$-member committee has an outsider who beats it on more than a fraction
$b$ of the ballots. The outsider may depend on the committee.

## Build and check

With Elan (Lean's toolchain manager) and Git installed, run these commands in
the `Lean/` directory.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Elan selects Lean **4.33.1** from [lean-toolchain](lean-toolchain). Lake
fetches the mathlib revision pinned in [lakefile.toml](lakefile.toml) and the
dependencies pinned in [lake-manifest.json](lake-manifest.json). The cache
command downloads prebuilt dependencies to shorten the first build. Initial
setup needs network access. The default build compiles every proof in the paper
through the public entry point [Condorcet.lean](Condorcet.lean).

[Audit.lean](Audit.lean) checks the axiom dependencies of the main results. The
hand proofs, the general transfer, and the four-or-five dimension bound use
only Lean's standard axioms. The sharper numerical bound also relies on Lean's
native compiler for three finite checks. They verify the total position
weight, the row-score bounds for legal grade assignments, and the exclusion
of a losing score for both challenger types. The audit fails if any listed
theorem uses an additional axiom.

The grade input is [pair-menus.json](pair-menus.json). To compare it and the
Python checker with the records printed in the PDF, run this command **from the
release root** with Python 3 and Poppler's `pdftotext` installed.

```sh
python3 Lean/check_payload.py --checker latex/check_pair_grade.py
```

The script compares the full 178,365-byte JSON input and the Python source
byte for byte. It also accepts a PDF path and a `--pdftotext` executable path.

## Find a proof

Names in the table are relative to the stated namespace. From a Lean file
in this project, use `import Condorcet` to access them all.

| Paper | Namespace and source | Declarations |
|---|---|---|
| Definitions of opposition and universal coverage | `ElectionLift` · [Minimax](Condorcet/Minimax.lean) | `A_eq_sup_min_max`, `C_eq_inf_best_coverage`, `coverage_guarantee_iff` |
| Lemma 1, repeated inner challenges | `ElectionLift` · [Refinement](Condorcet/Refinement.lean) | `repeated_challenges` |
| Lemma 2, realization by strict rankings | `ElectionLift` · [RationalGrades](Condorcet/RationalGrades.lean) | `rational_grade_realization`, `rational_grade_value_le` |
| Corollary 3, self-improvement for pairs | `ElectionLift.Grades` · [Pair](Condorcet/Pair.lean) | `pairValue_le`, `weak_pair_certificate`, `strict_pair_certificate` |
| Propositions 4–7, hand constructions | `ElectionLift.SmallTables` · [SmallTablesResults](Condorcet/SmallTablesResults.lean) | `hand_pair`, `easy_triple`, `sharp_triple`, `four_seats` |
| Proposition 8, combining blocks | `ElectionLift` · [Blocks](Condorcet/Blocks.lean) | `mix_blocks`, `transfer_from_bases` |
| Proposition 9, certified pair bound | `Physical` · [Certificate](Condorcet/Certificate.lean), [LiteralWords](LiteralWords.lean) | `appendix_certificate`, `pair_opposition_exact` |
| Theorem 1, its four numerical bounds and its consequences | `ElectionLift` · [Theorem](Condorcet/Theorem.lean) | `coverage_bound`, `rounded_percentages`, `asymptotic`, `refutes_cyclic_threshold`, `every_triple_blocked` |
| Largest possible Condorcet dimension | `ElectionLift` · [Majority](Condorcet/Majority.lean) | `five_suffice`, `four_or_five` |
| Earlier pair examples | `ElectionLift.Historical` · [Historical](Condorcet/Historical.lean), [Geist](Condorcet/Geist.lean) | `elkind_lang_saffidine`, `cycle_limit`, `speyer_eleven_of_twenty_one`, `geist_pair_opposition`, `geist_dimension` |

For the five-seat upper bound of Song, Nguyen, and Lin, the formalization
follows Prasanna Ramakrishnan's fixed-point proof. The adapted Brouwer
formalization is distributed with its upstream provenance and MIT license.
[Ramakrishnan's proof](https://theorydish.blog/2026/09/11/condorcet-quintets-a-proof-from-the-book/) ·
[Brouwer source and license](Condorcet/External/FixedPointTheorems/PROVENANCE.md)
