# Elections with Condorcet Dimension 4

November 20, 2026

[Read the paper](<Elections with Condorcet Dimension 4.pdf>) · [LaTeX source](latex/strongest-condorcet-coverage-bounds.tex) · [Lean proof guide](Lean/README.md)

A committee covers a voter against an outsider if the voter prefers at least one committee member to that outsider. Let $C_k$ be the largest fraction $c$ such that every finite ranked election with more than $k$ candidates admits a committee of size $k$ covering at least $c$ of the voters against each outsider. Writing $A_2=1-C_2$, the paper proves

$$
C_k \le 1-\frac{3A_2}{k+1}\le 1-\frac{3z}{k+1}
\qquad (k\ge 2), \qquad
z=\frac{351449648252133}{512000000000000}.
$$

In particular, there is a single finite election in which every triple has an outsider ranked above all three members by more than 51.48% of voters. The outsider can depend on the triple. The largest possible Condorcet dimension is four or five. Sections 1 and 2 give a hand proof that four can be necessary. Appendix A prints the full data and checker for the sharper numerical bound.

## Verify the numerical certificate

Start in the folder containing this README. Run the Python checker on the same grade table used by Lean. It uses only the Python 3 standard library.

```sh
python3 latex/check_pair_grade.py Lean/pair-menus.json
```

The expected output is `Verified all 231 type pairs at 351449648252133/512000000000000.`

With Poppler's `pdftotext` on your path, you can also check that the Python source and all 178,365 bytes of the JSON match the records printed in the PDF.

```sh
python3 Lean/check_payload.py --checker latex/check_pair_grade.py
```

## Build the Lean proofs

With Git and the Elan toolchain manager installed, run the following from the package root. The first build needs network access for the pinned Lean 4.33.1 toolchain and mathlib dependencies.

```sh
cd Lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The [proof guide](Lean/README.md) maps each result to its Lean statement. The hand proofs and the four-or-five conclusion use Lean's standard axioms. Three finite computations for the sharper numerical certificate use Lean's native evaluator.

## Rebuild the PDF

From the package root, use a TeX distribution with pdfLaTeX and `latexmk`.

```sh
cd latex
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build strongest-condorcet-coverage-bounds.tex
```

The output is `latex/build/strongest-condorcet-coverage-bounds.pdf`. The comparison plot is included as a vector PDF. To regenerate it, run `python3 plot_bounds.py` in `latex/` with Matplotlib installed. The TeX file contains the bibliography, verifier listing, and grade data. If you edit [the source table](latex/grade-tables.txt) or [the checker](latex/check_pair_grade.py), run `python3 print_verifiers.py` from `latex/` before rebuilding. This regenerates the printed records in the TeX file. The PDF itself gives instructions for recovering both the checker and its input from those records.

## Check the unpacked files

The [SHA-256 manifest](SHA256SUMS) covers every other file in this release. From the package root, run `sha256sum -c SHA256SUMS` on Linux or `shasum -a 256 -c SHA256SUMS` on macOS.
