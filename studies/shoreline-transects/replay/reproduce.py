#!/usr/bin/env python3
"""Replay frozen numerical summaries or refresh via NOAA's public export."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from urllib.request import Request, urlopen
from zipfile import ZipFile

import holdout
import pilot
from summaries import reports


ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
SITES = "https://portal.diver.orr.noaa.gov/pentaho/mdmap/sites"
EXPORT = SITES + "/export"
SELECTION_SALT = "proofrush-environment-20261126:"


def digest(data):
    return sha256(data).hexdigest()


def report_digest(report):
    # Normalize JSON object keys, including position and histogram integers.
    normalized = json.loads(json.dumps(report, allow_nan=False))
    return digest(json.dumps(normalized, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def frozen_inputs(manifest):
    result = {}
    for cohort in ("pilot", "holdout"):
        raw = (DATA / f"{cohort}.json").read_bytes()
        if digest(raw) != manifest["frozen_file_sha256"][f"{cohort}.json"]:
            raise ValueError(f"The frozen {cohort} file does not match its manifest")
        result[cohort] = json.loads(raw)
    return result


def from_archives(manifest, directories):
    result = {}
    hashes = {}
    for cohort, directory, prepare in zip(
        ("pilot", "holdout"), directories, (pilot.prepare, holdout.prepare)
    ):
        archives = [
            directory / batch["file"]
            for batch in manifest["cohorts"][cohort]["batches"]
        ]
        result[cohort], hashes[cohort] = prepare(archives)
    return result, hashes


def fetch_batch(directory, batch):
    request = Request(
        EXPORT,
        data=json.dumps({"site_ids": batch["site_ids"]}).encode("utf-8"),
        headers={"Content-Type": "application/json", "Accept": "application/zip"},
    )
    with urlopen(request, timeout=150) as response:
        data = response.read()
    with ZipFile(BytesIO(data)) as archive:
        if archive.testzip() is not None:
            raise ValueError(f"Corrupt export for {batch['file']}")
    (directory / batch["file"]).write_bytes(data)


def refresh(manifest):
    with TemporaryDirectory(prefix="shoreline-noaa-") as directory:
        temp = Path(directory)
        batches = [
            batch for cohort in manifest["cohorts"].values() for batch in cohort["batches"]
        ]
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(lambda batch: fetch_batch(temp, batch), batches))
        return from_archives(manifest, (temp, temp))


def check_index(manifest):
    with urlopen(SITES, timeout=90) as response:
        payload = response.read()
    eligible = [
        row["id"] for row in json.loads(payload)
        if row.get("verified")
        and len(row.get("surveys") or []) >= 8
        and (row.get("location") or {}).get("country") == "United States"
    ]
    ranked = sorted(eligible, key=lambda site: digest(f"{SELECTION_SALT}{site}".encode("utf-8")))
    same_ranks = {}
    for name, cohort in manifest["cohorts"].items():
        low, high = cohort["one_based_ranks"]
        frozen = [value for batch in cohort["batches"] for value in batch["site_ids"]]
        same_ranks[name] = ranked[low - 1:high] == frozen
    return {
        "site_index_hash_matches": digest(payload) == manifest["site_index_sha256"],
        "current_eligible_sites": len(eligible),
        "same_sites_at_these_ranks": same_ranks,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--refresh", action="store_true", help="download the fixed cohorts anonymously")
    mode.add_argument("--archives", nargs=2, type=Path, metavar=("PILOT_DIR", "HOLDOUT_DIR"))
    parser.add_argument("--check-index", action="store_true", help="also compare today's NOAA index")
    parser.add_argument("--require-original", action="store_true", help="fail if local archives differ")
    parser.add_argument("--json", action="store_true", help="print all reconstructed statistics")
    args = parser.parse_args()
    if args.check_index and not args.refresh:
        parser.error("--check-index requires --refresh")
    if args.require_original and args.archives is None:
        parser.error("--require-original requires --archives")

    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    archive_matches = None
    if args.refresh or args.archives:
        prepared, raw_hashes = refresh(manifest) if args.refresh else from_archives(manifest, args.archives)
        archive_matches = {
            name: all(
                raw_hashes[name][batch["file"]] == batch["sha256"]
                for batch in cohort["batches"]
            )
            for name, cohort in manifest["cohorts"].items()
        }
    else:
        prepared = frozen_inputs(manifest)
    result = reports(prepared["pilot"], prepared["holdout"])
    matches = {name: report_digest(body) == manifest["original_report_sha256"][name]
               for name, body in result.items()}
    index_info = check_index(manifest) if args.check_index else None
    if args.json:
        print(json.dumps({
            "reports_match_original": matches,
            "raw_archive_hashes_match": archive_matches,
            "site_index_check": index_info,
            "pilot_adjacent_pair_flow": prepared["pilot"]["pair_flow"],
            "complete_repeats_by_public_site_id": prepared["pilot"]["complete_repeats_by_public_site_id"],
            **result,
        }, indent=2, allow_nan=False))
    else:
        for name in result:
            print(f"{name}: reconstructed numerical report matches original = {matches[name]}")
            if archive_matches is not None:
                print(f"{name}: raw archive hashes match = {archive_matches[name]}")
        print(f"pilot adjacent pairs: {prepared['pilot']['pair_flow']}")
        if index_info is not None:
            print(f"site-index check: {index_info}")
    if archive_matches is None and not all(matches.values()):
        raise SystemExit("The frozen replay differs from an independent original report.")
    if args.require_original and (not all(archive_matches.values()) or not all(matches.values())):
        raise SystemExit("The supplied archives or numerical reports differ from the original.")


if __name__ == "__main__":
    main()
