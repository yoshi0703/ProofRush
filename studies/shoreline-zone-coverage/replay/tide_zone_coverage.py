#!/usr/bin/env python3
"""Replay tide-zone coverage from the Cefas/UKZN September 2019 daily removals."""

from collections import Counter, defaultdict
import csv
from datetime import date
from decimal import Decimal
from fractions import Fraction
from hashlib import sha256
from io import StringIO
from itertools import pairwise
import json
from pathlib import Path
import argparse


FILES = {
    "cefas-data.csv": "3bff081e2864704db2e355c72cb51391116dc41c9bfcef446b8977fe3f49604a",
    "cefas-metadata.csv": "2c5891f7f1aa8c16e135e47ff4de9cb1e183e9377d144245d761baaa87411c22",
}
ABOVE = "From high tide line to back of the beach"
BELOW = "From below high tide line to water"
SITES = {"Amanzimtoti", "Umhlanga"}


def checked_csv(directory, filename):
    payload = (directory / filename).read_bytes()
    digest = sha256(payload).hexdigest()
    if digest != FILES[filename]:
        raise ValueError(
            f"{filename} differs from the pinned Cefas CSV (SHA-256 {digest})"
        )
    return list(csv.DictReader(StringIO(payload.decode("utf-8-sig"), newline="")))


def zone_key(row):
    return row["Event_ID"], row["Type"]


def sample_description(row):
    return row["Location"], date(int(row["Year"]), int(row["Month"]), int(row["Day"]))


def daily_zones(metadata):
    events = defaultdict(dict)
    for row in metadata:
        event, zone = zone_key(row)
        assert zone not in events[event]
        events[event][zone] = row
    records = defaultdict(list)
    for event, zones in events.items():
        assert set(zones) == {ABOVE, BELOW}
        a, b = zones[ABOVE], zones[BELOW]
        site, day = sample_description(a)
        assert site in SITES and (site, day) == sample_description(b)
        assert a["Last_Clean"] == b["Last_Clean"]
        assert {
            Decimal(r["Total_Beach_Cleaned_Lenght_(m)"]) for r in zones.values()
        } == {100}
        records[site].append((day, event, a["Last_Clean"]))
    expected = set()
    for values in records.values():
        for (earlier, _, _), (later, event, previous_clearance) in pairwise(
            sorted(values)
        ):
            if previous_clearance == "day before survey":
                assert (later - earlier).days == 1
                expected.update((event, zone) for zone in (ABOVE, BELOW))
    return events, expected


def count_cell(value):
    amount = Decimal(value)
    assert amount == amount.to_integral_value() and amount >= 0
    return int(amount)


def extract_counts(data, events, selected):
    item_counts = Counter()
    subtotals = Counter()
    nonnumeric_pellets = Counter()
    anomalies = []
    unique = set()
    for row in data:
        key = zone_key(row)
        event, zone = key
        assert sample_description(row) == sample_description(events[event][zone])
        category = row["Category"].strip()
        value = row["Value"].strip()
        entry = (*key, category)
        assert entry not in unique
        unique.add(entry)
        if key not in selected or category.endswith("_description"):
            continue
        if category.startswith("Wgt_"):
            if category == "Wgt_Other_wood_more50cm" and value and Decimal(value) > 100:
                anomalies.append(
                    {
                        "event": event,
                        "zone": zone,
                        "category": category,
                        "value_kg_as_exported": value,
                    }
                )
            continue
        if category == "Pellets/nurdles" and value in {"", "present"}:
            nonnumeric_pellets[value or "blank"] += 1
        elif category.startswith("Total_"):
            subtotals[key] += count_cell(value)
        else:
            item_counts[key] += count_cell(value)
    assert item_counts.keys() == subtotals.keys() == selected
    return item_counts, subtotals, nonnumeric_pellets, anomalies


def observations(events, counts):
    records = defaultdict(list)
    dates = {event: sample_description(zones[ABOVE]) for event, zones in events.items()}
    for event, (site, day) in dates.items():
        if (event, ABOVE) in counts:
            upper, lower = (counts[event, zone] for zone in (ABOVE, BELOW))
            records[site].append((day, upper, upper + lower))
    return {site: sorted(series) for site, series in sorted(records.items())}


def minimax(series):
    shares = [Fraction(upper, whole) for _, upper, whole in series]
    low, high = min(shares), max(shares)
    multiplier = 2 / (low + high)
    worst_error = (high - low) / (high + low)
    assert max(abs(multiplier * share - 1) for share in shares) == worst_error
    return {
        "min_share": float(low),
        "max_share": float(high),
        "best_constant_multiplier": float(multiplier),
        "worst_relative_daily_error": float(worst_error),
        "exact_best_multiplier": str(multiplier),
        "exact_worst_error": str(worst_error),
    }


def chronological_calibration(first, second):
    early_upper = sum(upper for _, upper, _ in first)
    early_total = sum(whole for _, _, whole in first)
    late_upper = sum(upper for _, upper, _ in second)
    late_total = sum(whole for _, _, whole in second)
    fitted = Fraction(early_total, early_upper)
    return {
        "days_training": len(first),
        "days_later": len(second),
        "calibrated_multiplier": float(fitted),
        "early_observed_upper_share": early_upper / early_total,
        "later_observed_upper_share": late_upper / late_total,
        "later_pooled_relative_error": float(fitted * late_upper / late_total - 1),
    }


def growth_reversals(series):
    return [
        {
            "dates": [str(a[0]), str(b[0])],
            "upper_counts": [a[1], b[1]],
            "whole_counts": [a[2], b[2]],
        }
        for a, b in pairwise(series)
        if (b[1] - a[1]) * (b[2] - a[2]) < 0
    ]


def site_results(series):
    n = len(series)
    whole = sum(total for _, _, total in series)
    upper = sum(count for _, count, _ in series)
    cutoff = next(i for i, (day, _, _) in enumerate(series) if day.day == 26)
    splits = [
        chronological_calibration(series[:k], series[k:])["later_pooled_relative_error"]
        for k in range(3, n - 2)
    ]
    return {
        "daily_visits": n,
        "whole_items": whole,
        "upper_items": upper,
        "pooled_upper_share": upper / whole,
        "mean_whole_items_per_day": whole / n,
        "mean_upper_items_per_day": upper / n,
        "mean_lower_items_per_day": (whole - upper) / n,
        "fixed_multiplier": minimax(series),
        "adjacent_sign_reversals": growth_reversals(series),
        "train_before_sept_26": chronological_calibration(
            series[:cutoff], series[cutoff:]
        ),
        "earlier_later_error_range_with_at_least_three_visits_per_side": [
            min(splits),
            max(splits),
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    directory = parser.parse_args().directory
    data = checked_csv(directory, "cefas-data.csv")
    metadata = checked_csv(directory, "cefas-metadata.csv")
    assert (len(data), len(metadata)) == (19596, 46)
    events, selected = daily_zones(metadata)
    counts, subtotals, pellets, anomalies = extract_counts(data, events, selected)
    series = observations(events, counts)
    sensitivity = observations(events, subtotals)
    assert len(selected) == 38
    assert sorted(len(daily) for daily in series.values()) == [9, 10]
    observed_range = [
        f(row[2] for daily in series.values() for row in daily) for f in (min, max)
    ]
    assert observed_range == [134, 719]
    assert {
        site: round(sum(v[2] for v in daily) / len(daily))
        for site, daily in series.items()
    } == {
        "Amanzimtoti": 543,
        "Umhlanga": 340,
    }
    assert len(anomalies) == 1 and anomalies[0]["value_kg_as_exported"] == "15000"
    output = {
        "dataset_doi": "10.14466/CefasDataHub.95",
        "analysis_rows_before_filtering": len(data),
        "daily_field_visits": len(selected) // 2,
        "known_count_whole_range": observed_range,
        "item_rows": {site: site_results(daily) for site, daily in series.items()},
        "reported_material_subtotals": {
            site: site_results(daily) for site, daily in sensitivity.items()
        },
        "daily_zone_totals_disagreeing": sum(
            counts[key] != subtotals[key] for key in selected
        ),
        "daily_unquantified_pellet_cells": dict(pellets),
        "unresolved_weight_record": anomalies,
    }
    print(json.dumps(output, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
