"""Verify the pair bound from the JSON grade menus printed in the note."""
import json
import sys
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path

P, Q = 351449648252133, 512000000000000
TYPES = range(21)
R = 80 * 64 * 10**12
TIE = (R + 1) * P - 1
FULL = (R + 1) * Q
TARGET = R * TIE

def credit(h, a, b):
    if h > min(a, b):
        return 0
    return TIE if h == a == b else FULL

@lru_cache(None)
def word_score(h, a, b):
    return sum(credit(z, x, y) for z, x, y in zip(h, a, b))

@lru_cache(None)
def option_scores(kind, split, h, a, b):
    if kind == "fixed":
        return (word_score(h, a, b),)
    if kind == "joined":
        left = word_score(h[0], a[0], b[0])
        right = word_score(h[1], a[1], b[1])
        return (split * left + (80 - split) * right,)
    p, q, r = a[2], b[2], h[2]
    if kind == "prefix":
        return (sum(credit(h[k < r], a[k < p], b[k < q]) for k in range(64)),)
    cells = list(product((0, 1), repeat=2))
    base = [credit(h[0], a[i], b[j]) for i, j in cells]
    gain = [credit(h[1], a[i], b[j]) - t for (i, j), t in zip(cells, base)]
    order = sorted(range(4), key=gain.__getitem__, reverse=True)
    values = []
    for overlap in range(max(0, p + q - 64), min(p, q) + 1):
        sizes = (64 - p - q + overlap, q - overlap, p - overlap, overlap)
        score = sum(n * t for n, t in zip(sizes, base))
        remaining = r
        for k in order:
            used = min(remaining, sizes[k])
            score += used * gain[k]
            remaining -= used
        values.append(score)
    return tuple(values)

def states(row, i, j, heads):
    kind, weight, split, menus = row
    factor = weight if kind == "joined" else 80 * weight
    for a, b in product(menus[i], menus[j]):
        columns = []
        for t in heads:
            choices = [option_scores(kind, split, h, a, b) for h in menus[t]]
            columns.append([factor * max(vals) for vals in zip(*choices)])
        yield from zip(*columns)

def minimal(points):
    front = []
    for x, y in sorted(set(points)):
        if not front or y < front[-1][1]:
            front.append((x, y))
    return front

def two_heads(rows, i):
    fronts = [minimal(states(row, i, i, (i - 1, i))) for row in rows]
    cap_x = TARGET - sum(f[0][0] for f in fronts)
    cap_y = TARGET - sum(f[-1][1] for f in fronts)
    if min(cap_x, cap_y) < 0:
        return True
    partial = [(0, 0)]
    for f in fronts:
        if len(f) > 1:
            extra = [(x - f[0][0], y - f[-1][1]) for x, y in f]
            partial = minimal((x + a, y + b) for x, y in partial for a, b in extra
                              if x + a <= cap_x and y + b <= cap_y)
            if not partial:
                return True
    return False

def read_rows(path):
    rows = json.loads(Path(path).read_text(encoding="utf-8"))
    assert len(rows) == 113 and sum(row[1] for row in rows) == 10**12
    assert sum(row[0] == "joined" for row in rows) == 17
    for kind, weight, split, menus in rows:
        assert kind in ("free", "prefix", "fixed", "joined")
        assert type(weight) is int and weight > 0
        assert len(menus) == 21 and all(menus)
        assert type(split) is int and 0 <= split <= 80
        assert kind == "joined" or split == 80
        for menu in menus:
            for k, opt in enumerate(menu):
                if kind in ("free", "prefix"):
                    g, h, count = opt
                    assert isinstance(g, str) and isinstance(h, str)
                    assert len(g) == len(h) == 1 and type(count) is int
                    assert 0 <= count <= 64
                elif kind == "fixed":
                    assert isinstance(opt, str) and len(opt) == 64
                else:
                    assert len(opt) == 2
                    assert all(isinstance(w, str) and len(w) == 64 for w in opt)
                if kind != "fixed":
                    menu[k] = tuple(opt)
    return rows

def main(path):
    rows = read_rows(path)
    pure = joint = 0
    for i, j in combinations_with_replacement(TYPES, 2):
        if i == j and i in (5, 10, 16):
            assert two_heads(rows, i), (i, j)
            joint += 1
        else:
            h = j - 1 if i else (0 if 1 <= j <= 15 else 20)
            score = sum(min(states(row, i, j, (h,)))[0] for row in rows)
            assert score > TARGET, (i, j)
            pure += 1
    assert (pure, joint) == (228, 3)
    print(f"Verified all {pure + joint} type pairs at {P}/{Q}.")

if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with Python assertions enabled.")
    main(sys.argv[1])
