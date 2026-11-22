"""Draw the small-committee comparison in the introduction."""
from fractions import Fraction
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


def draw_bounds():
    seats = list(range(2, 11))
    pair_bound = Fraction(351449648252133, 512000000000000)
    lower = [float(3 * pair_bound / (k + 1)) for k in seats]
    cyclic = [2 / (k + 1) for k in seats]
    upper = [1 - (1 - 1 / k) * k ** (-1 / (k - 1)) for k in seats]

    teal, rust, gray = "#156660", "#914A20", "#737B7E"
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Source Sans Pro", "DejaVu Sans"],
        "mathtext.fontset": "stix",
        "font.size": 10,
        "pdf.fonttype": 42,
        "axes.spines.top": False,
        "axes.spines.right": False,
    })
    fig, ax = plt.subplots(figsize=(6.25, 3.02))
    fig.subplots_adjust(left=.092, right=.985, bottom=.16, top=.88)
    ax.set_xlim(1.83, 10.17)
    ax.set_ylim(.14, .80)
    ax.set_xticks(seats)
    ax.set_yticks([.2, .3, .4, .5, .6, .7, .8])
    ax.yaxis.set_major_formatter(PercentFormatter(xmax=1, decimals=0))
    ax.set_xlabel("Committee size  $k$", labelpad=3)
    ax.text(0, 1.045, "Blocking fraction", transform=ax.transAxes,
            ha="left", va="bottom", color="#253C41", weight="bold")
    ax.tick_params(length=0, pad=4, labelcolor="#364549")
    for spine in ("left", "bottom"):
        ax.spines[spine].set_color("#BBC4C4")
        ax.spines[spine].set_linewidth(.65)
    ax.set_axisbelow(True)
    ax.grid(axis="y", color="#E4E9E7", linewidth=.6)
    ax.axhline(.5, color="#9DA8A7", linewidth=.9, linestyle=(0, (1.4, 2.2)))
    ax.text(10.1, .508, "Majority threshold", ha="right", va="bottom",
            color="#58676A", fontsize=8.6)

    ax.plot(seats, upper, "-s", color=rust, lw=1.5, ms=4, label="Upper bound")
    ax.plot(seats, lower, "-o", color=teal, lw=1.65, ms=3.8, label="Lower bound")
    ax.plot(seats, cyclic, color=gray, lw=1.15, linestyle=(0, (3.5, 2)),
            label=r"Cyclic  $2/(k+1)$")
    ax.legend(loc="upper right", bbox_to_anchor=(1.01, 1.145), frameon=False,
              ncol=3, borderpad=0, handlelength=1.7, columnspacing=1.0,
              handletextpad=.4, fontsize=9.3)

    for x, y, label, anchor, color in [
        (3, lower[1], "51.48%", (3.42, .538), teal),
        (5, upper[3], "46.50%", (5.74, .474), rust),
    ]:
        ax.annotate(label, xy=(x, y), xytext=anchor, color=color, fontsize=9.5,
                    ha="center", va="center",
                    arrowprops={"arrowstyle": "-", "color": color,
                                "linewidth": .7, "shrinkA": 2, "shrinkB": 3})
    fig.savefig(Path(__file__).with_name("small-committee-bounds.pdf"),
                metadata={"Title": "Blocking fractions for committees of two to ten candidates"})
    plt.close(fig)


if __name__ == "__main__":
    draw_bounds()
