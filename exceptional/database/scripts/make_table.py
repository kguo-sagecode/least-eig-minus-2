"""Write the LaTeX table of counts (exceptional/note/counts-table.tex) from counts.json.
Digits are grouped in threes with thin spaces; the column "exceptional" is (A) + (B)."""
import json, sys


def num(x):
    return "$" + f"{x:,}".replace(",", "\\,") + "$"


with open(sys.argv[1]) as f:
    C = json.load(f)
rows = [(int(k), v) for k, v in C["per_n"].items()]
rows.sort()
tS = sum(v["connected_E8_represented"] for _, v in rows)
tA = sum(v["minus2"] for _, v in rows)
tB = sum(v["above_minus2"] for _, v in rows)
tM = sum(v["maximal"] for _, v in rows)
t = C["totals_over_complete_n"]
assert (tA, tB, tM) == (t["minus2"], t["above_minus2"], t["maximal"])
with open(sys.argv[2], "w") as out:
    out.write("\\begin{tabular}{rrrrrr}\n\\toprule\n$n$ & $\\lvert\\cS_n\\rvert$ & (A) $\\lambda_{\\min}=-2$ & "
              "(B) $\\lambda_{\\min}>-2$ & exceptional & maximal\\\\\n\\midrule\n")
    for k, v in rows:
        out.write(f"{k} & {num(v['connected_E8_represented'])} & {num(v['minus2'])} & "
                  f"{num(v['above_minus2'])} & {num(v['minus2'] + v['above_minus2'])} & {num(v['maximal'])}\\\\\n")
    out.write("\\midrule\n")
    out.write(f"total & {num(tS)} & {num(tA)} & {num(tB)} & {num(tA + tB)} & {num(tM)}\\\\\n"
              "\\bottomrule\n\\end{tabular}\n")
