"""Bound omitted swash-zone counts from the publisher's rounded Appendix A tables."""

import argparse
import json
import xml.etree.ElementTree as ET
from fractions import Fraction as F
from math import ceil, floor
from itertools import pairwise
from pathlib import Path


def table_rows(root, name):
    table = next(t for t in root.iter("table-wrap") if t.findtext("label") == name)
    return [
        [" ".join("".join(cell.itertext()).split()) for cell in row]
        for row in table.iter("tr")
    ]


def admissible(area, reading, scale=1):
    # Independent two-decimal rounding of both printed area and printed index.
    half = F(1, 200)
    low = max(0, ceil((area - half) * max(reading - half, 0) / scale))
    high = floor((area + half) * (reading + half) / scale)
    return list(range(low, high + 1))


def get_rows(path):
    root = ET.parse(path).getroot()
    mains = {}
    for line in table_rows(root, "Table 2")[1:]:
        if len(line) == 6:
            site, _, *line = line
        season, n, density, index = line
        mains[(site, season[:3], season[-2:])] = int(n)
    assert len(mains) == 16
    result = []
    for i, site in enumerate(("Goro", "Volano", "Estensi", "Spina"), 1):
        rows = table_rows(root, f"Table A{i}")
        assert rows[0][2] == "SZ"
        area = F(rows[1][1])
        for ds, cs in zip(rows[2:6], rows[6:10]):
            if ds[0] == "Density":
                ds = ds[1:]
            if cs[0] == "CCI":
                cs = cs[1:]
            season, den, index = ds[0], F(ds[1]), F(cs[1])
            assert cs[0] == season
            bounds = admissible(area, den)
            bound_index = admissible(area, index, 20)
            assert bounds and len(bound_index) == 1 and bound_index[0] in bounds
            total = mains[site, season[:3], season[-2:]]
            options = [total]
            if site == "Volano" and season == "Winter 24":
                # Text gives 2258 overall. The other three seasonal counts imply 439.
                options.append(
                    2258
                    - sum(
                        v
                        for (s, t, y), v in mains.items()
                        if s == site and (t, y) != ("Win", "24")
                    )
                )
            result.append(
                {
                    "site": site,
                    "season": season,
                    "swash_area": str(area),
                    "density": str(den),
                    "swash_low": bounds[0],
                    "swash_high": bounds[-1],
                    "using_cci": bound_index[0],
                    "whole_options": options,
                    "eligible": site != "Goro"
                    and (site, season) != ("Spina", "Summer 24"),
                }
            )
    return result


def compare(records):
    comparison = []
    for site in ("Volano", "Estensi", "Spina"):
        vals = [r for r in records if r["site"] == site and r["eligible"]]
        for r, s in pairwise(vals):
            deltas = {b - a for a in r["whole_options"] for b in s["whole_options"]}
            lo = min(deltas) - s["swash_high"] + r["swash_low"]
            hi = max(deltas) - s["swash_low"] + r["swash_high"]
            robust = (min(deltas) > 0 and hi < 0) or (max(deltas) < 0 and lo > 0)
            comparison.append(
                {
                    "site": site,
                    "seasons": [r["season"], s["season"]],
                    "whole_delta": sorted(deltas),
                    "inland_change_range": [lo, hi],
                    "robust_sign_reversal": robust,
                }
            )
    return comparison


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("article_xml", type=Path)
    p.add_argument("--json", type=Path)
    args = p.parse_args()
    rows = get_rows(args.article_xml)
    pairs = compare(rows)
    assert len(pairs) == 8
    flip = [x for x in pairs if x["robust_sign_reversal"]]
    assert len(flip) == 1 and flip[0]["site"] == "Spina"
    print(json.dumps(flip[0]))
    print("Eligible comparisons:", len(pairs))
    if args.json:
        args.json.write_text(
            json.dumps({"tables": rows, "comparisons": pairs}, indent=2) + "\n"
        )
