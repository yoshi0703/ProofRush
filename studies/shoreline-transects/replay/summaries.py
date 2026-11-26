"""Freeze only the per-site sufficient statistics used in the reports."""

from collections import defaultdict
from fractions import Fraction
from math import fsum
from random import Random
from statistics import mean


def pilot_cluster(entries):
    groups = defaultdict(list)
    for site, value in entries:
        groups[site].append(float(value))
    total = sum((Fraction(value) for _, value in entries), Fraction(0))
    return {
        "site_clusters": [
            [len(values), mean(values)] for values in groups.values()
        ],
        "event_sum": [total.numerator, total.denominator],
        "event_sum_float": any(isinstance(value, float) for _, value in entries),
    }


def pilot_cluster_report(cluster):
    groups = cluster["site_clusters"]
    if not groups:
        return {"visits": 0, "sites": 0}
    visits = sum(count for count, _ in groups)
    values = [avg for _, avg in groups]
    count = len(values)
    site_sum = fsum(values)
    rng = Random(638591)
    boot = sorted(mean(rng.choices(values, k=count)) for _ in range(4000))
    per_visit = Fraction(*cluster["event_sum"]) / visits
    event_mean = float(per_visit) if cluster["event_sum_float"] or per_visit.denominator != 1 else per_visit.numerator
    return {
        "visits": visits,
        "sites": count,
        "site_mean": mean(values),
        "event_mean": event_mean,
        "site_bootstrap_95": [boot[100], boot[3899]],
        "leave_one_site_out_range": (
            [
                min((site_sum - value) / (count - 1) for value in values),
                max((site_sum - value) / (count - 1) for value in values),
            ] if count > 1 else None
        ),
    }


def pilot_report(node):
    if not isinstance(node, dict):
        return node
    if "site_clusters" in node:
        return pilot_cluster_report(node)
    return {name: pilot_report(value) for name, value in node.items()}


def holdout_section(rows):
    if not rows:
        return {"sites": 0, "visits": 0}
    values = []
    for row in rows:
        visits = row["visits"]
        n0, n95 = row["endpoint_counts"]
        position = [n // visits if n % visits == 0 else n / visits for n in (n0, n95)]
        values.append(((n0 + n95) / (2 * visits), *position, *row["items_per_strip_means"]))
    site_means = list(map(mean, zip(*values)))
    appearances = [sum(row["endpoint_counts"][j] for row in rows) for j in (0, 1)]
    visits = sum(row["visits"] for row in rows)
    rng = Random(20261127)
    boot = sorted(mean(rng.choice(values)[0] for _ in values) for _ in range(10000))
    return {
        "sites": len(rows),
        "visits": visits,
        "endpoint_appearances": sum(appearances),
        "endpoint_appearances_by_position": appearances,
        "per_site_endpoint": site_means[0],
        "per_visit_endpoint": sum(appearances) / (2 * visits),
        "per_site_endpoint_bootstrap95": [boot[249], boot[9749]],
        "per_site_position0_95": site_means[1:3],
        "per_site_items_per_strip_unweighted_whole_HT_sequential_HT": site_means[3:],
        "site_endpoint_range": [min(row[0] for row in values), max(row[0] for row in values)],
        "site_visit_counts": {str(row["site_id"]): row["visits"] for row in rows},
    }


def reports(pilot, holdout):
    return {
        "pilot": pilot_report(pilot["report"]),
        "holdout": {
            **holdout,
            "nominal": holdout_section(holdout["nominal"]),
            "length_90_110": holdout_section(holdout["length_90_110"]),
        },
    }
