"""Independent endpoint-selection and count-sensitivity analysis of NOAA exports."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from io import TextIOWrapper
from math import comb, fsum
from statistics import mean
from zipfile import ZipFile
import csv


def design_probabilities():
    # Conditional on four distinct ordered draws from the 96-integer rule.
    z = [comb(2, e)*comb(18, 4-e)*3**e*5**(4-e) for e in range(3)]
    whole = sum(F(e*w, 2*sum(z)) for e, w in enumerate(z))
    # Reject repeated positions individually and continue from remaining ones.
    dist = {0: F(1)}
    for seen in range(4):
        nxt = Counter()
        for endpoints, p in dist.items():
            x, y = 3*(2-endpoints), 5*(18-(seen-endpoints))
            if x:
                nxt[endpoints+1] += p*F(x, x+y)
            if y:
                nxt[endpoints] += p*F(y, x+y)
        dist = nxt
    seq = sum(e*p for e, p in dist.items())/2
    pairs = {k: (x, (4-2*x)/18) for k, x in (("whole", whole), ("sequential", seq))}
    assert all(2*x + 18*y == 4 for x, y in pairs.values())
    assert seq == F(257570377,1993493502) and whole == F(89,669)
    return pairs


def load(archives):
    visits = defaultdict(list)
    dates = defaultdict(set)
    source_rows = 0
    for p in archives:
        with ZipFile(p) as z:
            [main] = [n for n in z.namelist() if n.endswith(".csv") and "backbarrier" not in n]
            with TextIOWrapper(z.open(main), encoding="utf-8-sig", newline="") as f:
                for row in csv.DictReader(f):
                    site, survey, day = row["shoreline_site_id"], row["survey_id"], row["survey_date"]
                    visits[(site,survey,day)].append(row)
                    dates[(site,day)].add(survey)
                    source_rows += 1
    kept = []
    flow = Counter()
    for (site, survey, day), rows in visits.items():
        what = {r["survey_protocol"] for r in rows}
        if what != {"MDMAP 2.0 Protocol"}:
            flow["other protocol"] += 1
            continue
        if len(dates[site,day]) != 1:
            flow["ambiguous site/date"] += 1
            continue
        if len(rows) != 4:
            flow["other visit size"] += 1
            continue
        if any(not r["total_debris_items"].strip() for r in rows):
            flow["missing outcome"] += 1
            continue
        try:
            strip = [int(r["transect_id"]) for r in rows]
            y = [int(r["total_debris_items"]) for r in rows]
            widths = {float(r["transect_width"]) for r in rows}
        except (ValueError, TypeError):
            flow["missing or non-integer positions/counts or invalid width"] += 1
            continue
        if widths != {5} or len(set(strip)) != 4 or any(x not in range(0,100,5) for x in strip):
            flow["incompatible positions or width"] += 1
            continue
        assert min(y) >= 0
        try:
            lengths = [float(r["site_length"]) for r in rows]
            band = all(90 <= x <= 110 for x in lengths)
        except (ValueError, TypeError):
            band = False
        flow["included"] += 1
        kept.append((site,dict(zip(strip,y)),band))
    assert sum(flow.values()) == len(visits)
    return kept, dict(rows=source_rows, sites=len({k[0] for k in visits}), visits=len(visits),
                      flow=dict(sorted(flow.items())))


def site_totals(data):
    groups = defaultdict(list)
    ps = design_probabilities()
    for site, ys, _ in data:
        p0, p95 = int(0 in ys), int(95 in ys)
        count = sum(ys.values())/4
        ht = [fsum(float(F(y,20) / (pe if x in (0,95) else pi)) for x,y in ys.items())
              for pe,pi in ps.values()]
        groups[site].append(((p0+p95)/2, p0, p95, count, *ht))
    return [
        {"site_id": int(site), "visits": len(rows),
         "endpoint_counts": [sum(row[j] for row in rows) for j in (1, 2)],
         "items_per_strip_means": list(map(mean, zip(*(row[3:] for row in rows))))}
        for site, rows in sorted(groups.items())
    ]


def prepare(archives):
    data, audit = load(archives)
    summary = {
        "audit": audit,
        "nominal": site_totals(data),
        "length_90_110": site_totals([row for row in data if row[2]]),
        "design_endpoint_probs": {name: str(pair[0]) for name, pair in design_probabilities().items()},
    }
    return summary, {path.name: sha256(path.read_bytes()).hexdigest() for path in archives}
