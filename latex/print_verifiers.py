"""Embed the lower-bound checker and its 113 grade rows into the single TeX file."""
import base64
import json
from pathlib import Path
import textwrap
import zlib

ROOT = Path(__file__).resolve().parent
TEX_PATH = ROOT / "strongest-condorcet-coverage-bounds.tex"
BEGIN_MARK = "% === BEGIN GENERATED VERIFIER AND DATA ==="
END_MARK = "% === END GENERATED VERIFIER AND DATA ==="


def type_indices(field):
    for item in field.split(","):
        first, _, last = item.partition("-")
        yield from range(int(first), int(last or first) + 1)


def normalized_rows():
    templates, words, joins = {}, {}, []
    source = (ROOT / "grade-tables.txt").read_text(encoding="utf-8")
    for line in source.splitlines():
        if not line.strip():
            continue
        tag, *fields = line.split()
        index = int(tag[1:])
        if tag[0] == "W":
            words[tag] = "".join(fields)
        elif tag[0] == "R":
            kind, weight, *grades = fields
            menus = [[g] if g != "." else [] for g in "".join(grades)]
            assert len(menus) == 21 and index not in templates
            templates[index] = (kind, int(weight), menus)
        elif tag[0] == "M":
            for field in fields:
                types, opts = field.split("=")
                for t in type_indices(types):
                    assert not templates[index][2][t]
                    templates[index][2][t] = opts.split("/")
        else:
            assert tag[0] == "J"
            weight, left, right, split = map(int, fields[:4])
            masks = {int(t): int(m, 16) for t, m in
                     (field.split("/") for field in fields[4:])}
            joins.append((weight, left, right, split, masks))

    def expand(kind, option):
        if kind in ("free", "prefix"):
            if ":" not in option:
                return (option, option, 32)
            g, h, count = option.split(":")
            return (g, h, int(count))
        length = int(kind[5:])
        if option in words:
            word = words[option]
        elif len(option) == 1:
            word = option * length
        else:
            runs = (r.partition("*") for r in option.split("+"))
            word = "".join(g * int(count or 1) for g, _, count in runs)
        assert len(word) == length
        return word * (64 // length)

    for kind, _, menus in templates.values():
        for menu in menus:
            assert menu
            menu[:] = [expand(kind, option) for option in menu]

    def as_word(option):
        if isinstance(option, str):
            return option
        g, h, count = option
        return h * count + g * (64 - count)

    result = []
    for kind, weight, menus in templates.values():
        if weight:
            result.append([kind if kind in ("free", "prefix") else "fixed",
                           weight, 80, menus])
    for weight, left, right, split, masks in joins:
        if not weight:
            continue
        combined = []
        for t, (a, b) in enumerate(zip(templates[left][2], templates[right][2])):
            assert max(len(a), len(b)) <= 4
            mask = masks.get(t, -1)
            choices = [(as_word(x), as_word(y))
                       for i, x in enumerate(a) for j, y in enumerate(b)
                       if mask & (1 << (4*i + j))]
            assert choices
            combined.append(choices)
        result.append(["joined", weight, split, combined])
    return result


def listing(lines, size, leading):
    return [rf"\begin{{Verbatim}}[fontsize=\fontsize{{{size}pt}}{{{leading}pt}}\selectfont]",
            *lines, r"\end{Verbatim}"]


def pages(lines, capacity):
    count = (len(lines) + capacity - 1) // capacity
    for i in range(count):
        yield lines[i * len(lines) // count : (i+1) * len(lines) // count]


def format_checker():
    source = (ROOT / "check_pair_grade.py").read_text(encoding="utf-8").splitlines()
    cut = source.index("def two_heads(rows, i):")
    output = []
    for first, last in ((0, cut), (cut, len(source))):
        numbered = []
        for i in range(first, last):
            line = source[i]
            if line:
                indent = len(line) - len(line.lstrip())
                numbered.append(f"P{i+1:03}/{indent:<2}  {line}")
            elif numbered:
                numbered.append("")
        while not numbered[-1]:
            numbered.pop()
        title = f"Python verifier, {numbered[0][:4]}--{numbered[-1][:4]}"
        output.extend([r"\clearpage",
                       rf"\pdfbookmark[2]{{{title}}}{{code-{numbered[0][:4]}}}",
                       r"\subsection*{" + title + "}"])
        if first == 0:
            output.append(r"\phantomsection\label{app:checker}")
        output += listing(numbered, 8.3, 9.6)
    output.append(r"\phantomsection\label{app:checker-end}")
    return "\n".join(output)


def format_data(rows):
    data = json.dumps(rows, separators=(",", ":")).encode("ascii")
    encoded = base64.b64encode(zlib.compress(data, level=9)).decode("ascii")
    records = [f"D{i:03}  {s}" for i, s in enumerate(textwrap.wrap(encoded, 90))]
    output = []
    for group_index, group in enumerate(pages(records, 58)):
        title = f"Grade data, {group[0][:4]}--{group[-1][:4]}"
        output.extend([r"\clearpage",
                       rf"\pdfbookmark[2]{{{title}}}{{data-{group[0][:4]}}}",
                       r"\subsection*{" + title + "}"])
        if group_index == 0:
            output.append(r"\phantomsection\label{app:menus}")
        output += listing(group, 8.4, 10.3)
    output.append(r"\phantomsection\label{app:menus-end}")
    return "\n".join(output)


def update_tex():
    tex = TEX_PATH.read_text(encoding="utf-8")
    start = tex.index(BEGIN_MARK)
    end = tex.index(END_MARK)
    assert start < end
    generated = format_checker() + "\n" + format_data(normalized_rows())
    updated = tex[:start] + BEGIN_MARK + "\n" + generated + "\n" + tex[end:]
    TEX_PATH.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    update_tex()
