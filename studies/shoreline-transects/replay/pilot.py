"""Build pilot sufficient statistics from NOAA's public main-beach export."""
import csv
import hashlib
import io
import re
import statistics
import zipfile
from collections import Counter, defaultdict
from datetime import date
from math import fsum

from finite_design import contrast
from rounding import whole_redraw, successive, moments
from summaries import pilot_cluster

GRID = frozenset(range(0,100,5))
EDGE = {0,95}
METHODS = {"uniform": whole_redraw((1,1)), "whole_redraw": whole_redraw(), "successive": successive()}
FLAG = re.compile(r"non[ -]?random|not (?:be |appear to be |appear |truly |selected )?random|same (?:four |4 )?transects?|fixed transects?|same as what was used", re.I)


def removal_scope(value):
    scope = (value or "").strip().lower()
    return scope if scope in {"all", "none", "some"} else "unknown"


def eligible_integer(x):
    try:
        v = float(x)
        return int(v) if v.is_integer() else None
    except ValueError:
        return None


def shrink(zips):
    records = []
    hashes = {}
    for path in zips:
        hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        with zipfile.ZipFile(path) as archive:
            names = [n for n in archive.namelist() if n.endswith(".csv") and "backbarrier" not in n.lower()]
            assert len(names)==1
            with archive.open(names[0]) as raw:
                for r in csv.DictReader(io.TextIOWrapper(raw,encoding="utf-8-sig")):
                    flag = bool(FLAG.search(" ".join(r.get(x,"") or "" for x in ("survey_notes","transect_notes"))))
                    records.append({
                        "site":r["shoreline_site_id"], "survey":r["survey_id"], "date":r["survey_date"],
                        "protocol":r["survey_protocol"], "position":r["transect_id"],
                        "width":r["transect_width"], "length":r["site_length"],
                        "removal_site":removal_scope(r["debris_removal_site"]),
                        "removal_strip":removal_scope(r["debris_removal_transect"]),
                        "count":r["total_debris_items"], "flag":int(flag)
                    })
    return records,hashes


def event(rs, unique_date):
    first=rs[0]
    def fail(reason):
        return {"site":first["site"],"id":first["survey"],"date":first["date"],"valid":False,"reason":reason}
    if not unique_date: return fail("same_site_date")
    if first["protocol"]!='MDMAP 2.0 Protocol': return fail("earlier_protocol")
    if len(rs)!=4: return fail("row_count_other_than_four")
    positions=[eligible_integer(r['position']) for r in rs]
    if len(set(positions))!=4 or any(i not in GRID for i in positions): return fail("invalid_positions")
    if any(eligible_integer(r['width'])!=5 for r in rs): return fail("strip_width")
    counts=[eligible_integer(r["count"]) for r in rs]
    if any(v is None or v<0 for v in counts): return fail("missing_or_invalid_count")
    site_clean = {r["removal_site"].lower() for r in rs}
    strip_clean = {r["removal_strip"].lower() for r in rs}
    return {"site":first["site"],"id":first["survey"],"date":first["date"],"valid":True,
            "length":eligible_integer(first["length"]), "ys":dict(zip(positions,counts)),
            "flag":any(int(r["flag"]) for r in rs),"site_scope":next(iter(site_clean)) if len(site_clean)==1 else "mixed",
            "strip_scope":next(iter(strip_clean)) if len(strip_clean)==1 else "mixed",
            "J":sum(i in EDGE for i in positions)}


def count_audit(valid):
    result={"events":len(valid),"sites":len({e["site"] for e in valid}),
            "J_hist":dict(sorted(Counter(e["J"] for e in valid).items())),
            "position_hist":{i:sum(i in e["ys"] for e in valid) for i in sorted(GRID)},
            "observed_edge_inclusion":pilot_cluster([(e["site"],e["J"]/2) for e in valid]),
            "flagged_events":sum(e["flag"] for e in valid),
            "items":sum(sum(e["ys"].values()) for e in valid),
            "metadata_lengths":[min((e["length"] for e in valid if e["length"] is not None),default=None),
                                max((e["length"] for e in valid if e["length"] is not None),default=None)]}
    result["assignment_uncertainty"]={}
    for name, dist in METHODS.items():
        pi_e,pi_i=moments(dist)
        ys=[]
        for e in valid:
            v=fsum(y/float(pi_e if i in EDGE else pi_i) for i,y in e["ys"].items())/20
            ys.append((e["site"],v))
        result["assignment_uncertainty"][name]=pilot_cluster(ys)
    return result


def pair_record(a,b):
    previous=set(a["ys"]); current=set(b["ys"])
    rep=previous & current
    uniform = float(contrast(b["ys"],previous))
    out={"site":a["site"],"gap":abs((date.fromisoformat(a["date"])-date.fromisoformat(b["date"])).days),
         "old_site_scope":a["site_scope"],"old_strips":a["strip_scope"],"overlap":len(rep),
         "flag":a["flag"] or b["flag"], "length":b["length"],
         "mixed_diff":(statistics.mean(b["ys"][i] for i in rep)-
                       statistics.mean(b["ys"][i] for i in current-rep)) if 0<len(rep)<4 else None}
    for name, dist in METHODS.items():
        ratio = METHODS["uniform"][a["J"]]*METHODS["uniform"][b["J"]]/(dist[a["J"]]*dist[b["J"]])
        out[name]=uniform*float(ratio)
    return out


def pair_summary(rows):
    return {"overlap_hist":dict(sorted(Counter(r["overlap"] for r in rows).items())),
            "previous_site_scope":dict(Counter(r["old_site_scope"] for r in rows)),
            **{name:pilot_cluster([(r["site"],r[name]) for r in rows]) for name in METHODS},
            "mixed_only_unweighted":pilot_cluster([(r['site'],r['mixed_diff']) for r in rows if r['mixed_diff'] is not None])}


def analyze(rows):
    groups=defaultdict(list)
    for r in rows: groups[(r["site"],r["date"],r["survey"])].append(r)
    mult=Counter((s,d) for s,d,i in groups)
    sites=defaultdict(list)
    for (s,d,i),rs in sorted(groups.items()):
        sites[s].append(event(rs,mult[s,d]==1))
    all_events=[e for es in sites.values() for e in es]
    valid=[e for e in all_events if e['valid']]
    pairs=[]; placebos=[]
    for es in sites.values():
        for old,new in zip(es,es[1:]):
            if old['valid'] and new['valid']:
                pairs.append(pair_record(old,new))
                placebos.append(pair_record(new,old))
    primary=[r for r in pairs if 21<=r["gap"]<=42]
    report = {"rows":len(rows),"events":len(all_events),"sites_in_export":len(sites),
            "exclusions":dict(Counter(e["reason"] for e in all_events if not e["valid"])),
            "assignments":count_audit(valid),
            "assignments_clean_notes_90_110":count_audit([e for e in valid if not e["flag"] and 90<=(e["length"] or 0)<=110]),
            "previous_21_42":pair_summary(primary),
            "previous_7_60":pair_summary([r for r in pairs if 7<=r["gap"]<=60]),
            "previous_notes_length":pair_summary([r for r in primary if not r["flag"] and 90<=(r["length"] or 0)<=110]),
            "future_21_42":pair_summary([r for r in placebos if 21<=r["gap"]<=42]),
            "removal_strata":{scope:pair_summary([r for r in primary if r["old_site_scope"]==scope])
                              for scope in sorted({r['old_site_scope'] for r in primary})},
            "maximum_exposure_strata":{scope:pair_summary([r for r in primary if r["old_site_scope"]==scope and r["old_strips"]=="all"])
                               for scope in sorted({r['old_site_scope'] for r in primary})}}
    pair_flow = {
        "all_adjacent_pairs": sum(max(0, len(visits) - 1) for visits in sites.values()),
        "both_visits_eligible": len(pairs),
        "gap_21_42_days": len(primary),
        "gap_7_60_days": sum(7 <= pair["gap"] <= 60 for pair in pairs),
        "gap_21_42_with_notes_length_filter": sum(
            not pair["flag"] and 90 <= (pair["length"] or 0) <= 110 for pair in primary
        ),
    }
    repeat_sites = Counter(int(pair["site"]) for pair in primary if pair["overlap"] == 4)
    return {
        "pair_flow": pair_flow,
        "complete_repeats_by_public_site_id": dict(sorted(repeat_sites.items())),
        "report": report,
    }


def prepare(archives):
    rows, hashes = shrink(archives)
    return analyze(rows), hashes
