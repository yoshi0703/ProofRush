#!/usr/bin/env python3
"""Rebuild the spelling-BPE proof bundles and check their exported terms with nanoda."""
import argparse
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BUNDLES = {
    'six-phase': (
        ['SpellingBPE', 'DecoyRows', 'CombComparator', 'Phases', 'Ratio', 'PairRoster',
         'Attachment', 'Incidence', 'IncidenceAggregate', 'CoreTable', 'Separators', 'Forcing',
         'Limit', 'OriginalSix'],
        ['OriginalSix.six_phase_ratio', 'OriginalSix.asymptotic_upper', 'OriginalSix.input_nonempty',
         'OriginalSix.input_not_unique', 'OriginalSix.greedy_exists', 'OriginalSix.all_ties',
         'OriginalSix.comparator_optimum']),
    'diamond': (
        ['SpellingBPE', 'DecoyRows', 'CombComparator', 'PairRoster', 'Common', 'Separators',
         'Forcing', 'DiamondFamily', 'EdgeCases', 'EdgeCodes', 'DistinctRows', 'InitialDomain',
         'DiamondCount', 'DiamondComparator', 'Witness', 'DiamondConclusion', 'DiamondBudget',
         'Asymptotic', 'LimitRatio', 'RawDiamond', 'DiamondResult'],
        ['DiamondResult.replacement_limit_zero', 'DiamondResult.overlapping_limit_zero',
         'DiamondResult.below_one_sixth', 'DiamondGuarantee.all_ties',
         'DiamondGuarantee.comparator_lower', 'DiamondLimit.le_best',
         'RawDiamond.rawGreedy_all_ties', 'DiamondResult.input_allowed']),
    'finite': (
        ['SpellingBPE', 'FourMerges'],
        ['SpellingWitness.refutes_extension', 'SpellingWitness.histories',
         'SpellingWitness.ambiguous', 'SpellingBPE.optimum_attained']),
    'forced': (
        ['SpellingBPE', 'DecoyRows', 'ForcedFour'],
        ['SpellingDecoy.force', 'SpellingDecoy.pick_list', 'SpellingForced.forced_failure',
         'SpellingForced.available_greedy']),
    'phases': (
        ['Phases', 'Ratio', 'CombAuxiliaries'],
        ['CombPhases.bounded_every_gap', 'CombRatio.ratio_bound', 'CombRatio.ratio_near_sixth']),
    'comparator': (
        ['SpellingBPE', 'DecoyRows', 'CombComparator'],
        ['CombComparator.doubling_single_row', 'CombComparator.doubling_step',
         'CombComparator.doubling_single_row_feasible', 'CombComparator.doubling_table',
         'CombComparator.twice_doubling_table', 'CombComparator.twice_doubling_augmented_lower']),
}

BUNDLES['rate-and-vocabulary'] = (
    BUNDLES['diamond'][0] + [
        'Matching', 'ForestTypes', 'MergeForest', 'ForestCounts', 'ForestGaps', 'ForestLabels',
        'ForestPaths', 'ForestArithmetic', 'ForestMass', 'ForestChronology', 'ForestEdges',
        'ForestChronoCount', 'ForestShortMass', 'WorstRate', 'UniversalRate',
        'BoundedInitial', 'Isolation', 'FinitePairs', 'ShortCount', 'SingleWord', 'Uniform',
        'SourceGreedy', 'Approximation',
    ],
    ['SpellingApproximation.sharp_rates', 'SpellingUniversalRate.replacement_run_bound',
     'SpellingUniversalRate.overlapping_run_bound', 'BoundedInitial.uniform_source_approximation',
     'BoundedInitial.uniform_approximation', 'BoundedInitial.bounded_initial_replacement_greedy',
     'BoundedInitial.bounded_initial_raw_greedy'],
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', required=True, type=Path)
    parser.add_argument('--nanoda', required=True, type=Path)
    parser.add_argument('--run-dir', required=True, type=Path)
    parser.add_argument('--docker-image')
    parser.add_argument('--bundle', action='append', choices=list(BUNDLES))
    args = parser.parse_args()
    for key in args.bundle or BUNDLES:
        modules, targets = BUNDLES[key]
        cmd = [sys.executable, str(HERE.parents[1] / 'lean/verify.py'),
               '--sources', str(HERE / 'lean'), '--mathlib', str(args.mathlib),
               '--nanoda', str(args.nanoda), '--run-dir', str(args.run_dir / key)]
        for module in modules:
            cmd.extend(['--module', module])
        for target in targets:
            cmd.extend(['--target', target])
        if args.docker_image:
            cmd.extend(['--docker-image', args.docker_image])
        subprocess.run(cmd, check=True)


if __name__ == '__main__':
    main()
