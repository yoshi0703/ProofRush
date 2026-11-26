"""Reproduce field counts via SQL and enumerate random audits of lower-zone bags."""

import argparse
import csv
import hashlib
import io
import json
import sqlite3
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, pairwise
from math import comb
from pathlib import Path


FILES = {
    "cefas-data.csv": "3bff081e2864704db2e355c72cb51391116dc41c9bfcef446b8977fe3f49604a",
    "cefas-metadata.csv": "2c5891f7f1aa8c16e135e47ff4de9cb1e183e9377d144245d761baaa87411c22",
}


def original_rows(folder, name):
    content = (folder / name).read_bytes()
    assert hashlib.sha256(content).hexdigest() == FILES[name]
    return csv.DictReader(io.StringIO(content.decode("utf-8-sig")))


def observations(folder, subtotal=False):
    con = sqlite3.connect(":memory:")
    con.execute(
        "CREATE TABLE meta (site TEXT, day DATE, event TEXT, zone TEXT, cleaning TEXT, PRIMARY KEY(event, zone))"
    )
    con.execute(
        "CREATE TABLE cells (event TEXT, zone TEXT, material TEXT, category TEXT, n INTEGER, PRIMARY KEY(event,zone,category))"
    )
    for row in original_rows(folder, "cefas-metadata.csv"):
        day = "{:04}-{:02}-{:02}".format(
            *[int(row[x]) for x in ("Year", "Month", "Day")]
        )
        assert float(row["Total_Beach_Cleaned_Lenght_(m)"]) == 100
        con.execute(
            "INSERT INTO meta VALUES (?,?,?,?,?)",
            (row["Location"], day, row["Event_ID"], row["Type"], row["Last_Clean"]),
        )
    daily = set(
        con.execute("SELECT event, zone FROM meta WHERE cleaning='day before survey'")
    )
    for row in original_rows(folder, "cefas-data.csv"):
        if (row["Event_ID"], row["Type"]) not in daily:
            continue
        cat = row["Category"].strip()
        val = row["Value"].strip()
        if (
            cat.startswith("Wgt_")
            or cat.endswith("_description")
            or cat.startswith("Total_") != subtotal
        ):
            continue
        if cat == "Pellets/nurdles" and val in ("present", ""):
            continue
        n = Fraction(val)
        assert n >= 0 and n.denominator == 1
        con.execute(
            "INSERT INTO cells VALUES (?,?,?,?,?)",
            (row["Event_ID"], row["Type"], row["Material"], cat, int(n)),
        )
    query = """
    WITH obs AS (
      SELECT m.site, m.day, m.zone, SUM(c.n) AS n FROM meta m JOIN cells c USING(event,zone)
      WHERE m.cleaning='day before survey' AND EXISTS (
       SELECT 1 FROM meta p WHERE p.site=m.site AND p.zone=m.zone AND p.day=date(m.day,'-1 day'))
      GROUP BY m.site,m.day,m.zone
    )
    SELECT site,day,
      SUM(CASE zone WHEN 'From high tide line to back of the beach' THEN n END),
      SUM(CASE zone WHEN 'From below high tide line to water' THEN n END)
      FROM obs GROUP BY site,day HAVING COUNT(*)=2 ORDER BY site,day
    """
    table = defaultdict(list)
    for site, day, upper, lower in con.execute(query):
        assert upper >= 0 and lower >= 0
        table[site].append((day, upper, lower))
    assert sorted(len(vals) for vals in table.values()) == [9, 10]
    return table


def audit(records):
    n = len(records)
    full = sum(u + l for _, u, l in records)
    low = sum(l for _, _, l in records)
    results = {}
    for k in range(1, n + 1):
        deviations = [
            Fraction(n * sum(sample) - k * low, k * full)
            for sample in combinations([l for _, _, l in records], k)
        ]
        assert len(deviations) == comb(n, k) and sum(deviations) == 0
        coverage = {}
        for tol in (10, 20, 30):
            good = sum(100 * abs(d) <= tol for d in deviations)
            coverage[str(tol)] = [good, len(deviations)]
        results[k] = {
            "within_pct": coverage,
            "max_absolute_pct": float(100 * max(map(abs, deviations))),
        }
    return results


def summary(records):
    u = sum(x[1] for x in records)
    lower = sum(x[2] for x in records)
    ratios = [Fraction(x, x + y) for _, x, y in records]
    lo, hi = min(ratios), max(ratios)
    bound = (hi - lo) / (hi + lo)
    signs = [
        [a[0], b[0]]
        for a, b in pairwise(records)
        if (a[1] - b[1]) * (sum(a[1:]) - sum(b[1:])) < 0
    ]
    return {
        "upper": u,
        "whole": u + lower,
        "min_share": str(lo),
        "max_share": str(hi),
        "minimax_error": str(bound),
        "sign_reversals": signs,
        "days": records,
        "audit": audit(records),
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("data_directory", type=Path)
    ap.add_argument("--json", type=Path)
    args = ap.parse_args()
    out = {}
    for mode in ("items", "material_subtotals"):
        out[mode] = {
            site: summary(records)
            for site, records in observations(
                args.data_directory, mode == "material_subtotals"
            ).items()
        }
        for site, record in out[mode].items():
            print(
                mode,
                site,
                "upper,full",
                record["upper"],
                record["whole"],
                "reversals",
                len(record["sign_reversals"]),
            )
            print(
                "audit k/total and exact coverage (within 20%)",
                [(k, x["within_pct"]["20"]) for k, x in record["audit"].items()],
            )
    if args.json:
        args.json.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
