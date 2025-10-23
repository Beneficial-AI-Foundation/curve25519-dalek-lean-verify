#!/usr/bin/env python3
"""
Plot verification progress over time from git history.

This script:
1. Checks all commits to master branch
2. Extracts status.csv from each commit
3. Counts total functions and verified functions
4. Plots progress over time
"""

import subprocess
import csv
import io
from datetime import datetime
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

def get_commit_history():
    """Get list of commits on master branch with timestamps."""
    result = subprocess.run(
        ['git', 'log', 'master', '--format=%H|%at', '--reverse'],
        capture_output=True,
        text=True,
        check=True
    )

    commits = []
    for line in result.stdout.strip().split('\n'):
        if line:
            commit_hash, timestamp = line.split('|')
            commits.append({
                'hash': commit_hash,
                'timestamp': int(timestamp),
                'datetime': datetime.fromtimestamp(int(timestamp))
            })
    return commits

def get_file_from_commit(commit_hash, filepath):
    """Extract a file's contents from a specific commit."""
    try:
        result = subprocess.run(
            ['git', 'show', f'{commit_hash}:{filepath}'],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError:
        # File doesn't exist in this commit
        return None

def count_verification_status(csv_content):
    """Parse CSV and count total, verified, specified, and draft spec functions."""
    if not csv_content:
        return None, None, None, None

    reader = csv.DictReader(io.StringIO(csv_content))
    total = 0
    verified = 0
    specified = 0
    draft_spec = 0

    for row in reader:
        total += 1
        status = row.get('verified', '').strip().lower()
        spec_theorem = row.get('spec_theorem', '').strip()

        if status == 'verified':
            verified += 1
        elif status == 'specified':
            specified += 1
        elif spec_theorem:  # Has spec_theorem but not verified/specified = draft
            draft_spec += 1

    return total, verified, specified, draft_spec

def main():
    print("Fetching commit history...")
    commits = get_commit_history()
    print(f"Found {len(commits)} commits on master")

    # Data points for plotting
    dates = []
    totals = []
    verifieds = []
    specifieds = []
    draft_specs = []

    print("\nAnalyzing status.csv from each commit...")
    for i, commit in enumerate(commits):
        if i % 10 == 0:
            print(f"  Processing commit {i+1}/{len(commits)}", end='\r')

        csv_content = get_file_from_commit(commit['hash'], 'status.csv')
        total, verified, specified, draft_spec = count_verification_status(csv_content)

        if total is not None:
            dates.append(commit['datetime'])
            totals.append(total)
            verifieds.append(verified)
            specifieds.append(specified)
            draft_specs.append(draft_spec)

    print(f"\n\nFound {len(dates)} commits with status.csv")

    if not dates:
        print("No data to plot!")
        return

    # Create the plot
    fig, ax = plt.subplots(figsize=(14, 7))

    # Calculate cumulative values for stacked area plot
    import numpy as np
    verified_arr = np.array(verifieds)
    specified_arr = np.array(specifieds)
    draft_spec_arr = np.array(draft_specs)

    # Calculate the remaining unspecified functions
    unspecified = [t - v - s - d for t, v, s, d in zip(totals, verifieds, specifieds, draft_specs)]

    # Create stacked area plot
    ax.fill_between(dates, 0, verified_arr,
                     alpha=0.7, color='#2ecc71', label='Verified')
    ax.fill_between(dates, verified_arr, verified_arr + specified_arr,
                     alpha=0.7, color='#3498db', label='Specified (spec written)')
    ax.fill_between(dates, verified_arr + specified_arr,
                     verified_arr + specified_arr + draft_spec_arr,
                     alpha=0.7, color='#f39c12', label='Draft Spec (WIP)')
    ax.fill_between(dates, verified_arr + specified_arr + draft_spec_arr, totals,
                     alpha=0.5, color='#95a5a6', label='No Spec Yet')

    # Add line plots on top for clarity
    ax.plot(dates, verifieds, 'o-', color='darkgreen', linewidth=1.5, markersize=4)
    ax.plot(dates, totals, 'o-', color='darkblue', linewidth=1.5, markersize=4)

    # Formatting
    ax.set_xlabel('Date', fontsize=12)
    ax.set_ylabel('Number of Functions', fontsize=12)
    ax.set_title('Curve25519-Dalek Verification Progress Over Time',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10, framealpha=0.9)
    ax.grid(True, alpha=0.3, linestyle='--')

    # Format x-axis dates
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%Y-%m-%d'))
    ax.xaxis.set_major_locator(mdates.AutoDateLocator())
    plt.xticks(rotation=45, ha='right')

    # Add annotation for latest point with all categories
    if verifieds:
        latest_verified = verifieds[-1]
        latest_specified = specifieds[-1]
        latest_draft = draft_specs[-1]
        latest_total = totals[-1]
        latest_unspecified = unspecified[-1]

        verified_pct = (latest_verified / latest_total * 100) if latest_total > 0 else 0
        with_spec_pct = ((latest_verified + latest_specified) / latest_total * 100) if latest_total > 0 else 0

        annotation_text = (
            f'Verified: {latest_verified} ({verified_pct:.1f}%)\n'
            f'Specified: {latest_specified}\n'
            f'Draft Spec: {latest_draft}\n'
            f'No Spec: {latest_unspecified}\n'
            f'Total: {latest_total}'
        )

        ax.text(0.98, 0.98, annotation_text,
                transform=ax.transAxes,
                fontsize=10, fontweight='bold',
                verticalalignment='top', horizontalalignment='right',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    plt.tight_layout()

    # Save the plot
    output_file = 'verification_progress.png'
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    print(f"\nPlot saved to {output_file}")

    # Show the plot
    plt.show()

    # Print summary statistics
    print("\nSummary:")
    print(f"  First commit with status.csv: {dates[0].strftime('%Y-%m-%d')}")
    print(f"  Latest commit: {dates[-1].strftime('%Y-%m-%d')}")
    print(f"\n  Initial state ({dates[0].strftime('%Y-%m-%d')}):")
    print(f"    Verified:   {verifieds[0]:2d} ({verifieds[0]/totals[0]*100:5.1f}%)")
    print(f"    Specified:  {specifieds[0]:2d} ({specifieds[0]/totals[0]*100:5.1f}%)")
    print(f"    Draft Spec: {draft_specs[0]:2d} ({draft_specs[0]/totals[0]*100:5.1f}%)")
    print(f"    Total:      {totals[0]:2d}")
    print(f"\n  Current state ({dates[-1].strftime('%Y-%m-%d')}):")
    print(f"    Verified:   {verifieds[-1]:2d} ({verifieds[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Specified:  {specifieds[-1]:2d} ({specifieds[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Draft Spec: {draft_specs[-1]:2d} ({draft_specs[-1]/totals[-1]*100:5.1f}%)")
    print(f"    No Spec:    {unspecified[-1]:2d} ({unspecified[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Total:      {totals[-1]:2d}")
    print(f"\n  Progress:")
    print(f"    Verified:   +{verifieds[-1] - verifieds[0]}")
    print(f"    Specified:  +{specifieds[-1] - specifieds[0]}")
    print(f"    Draft Spec: +{draft_specs[-1] - draft_specs[0]}")
    print(f"    Total:      +{totals[-1] - totals[0]}")

if __name__ == '__main__':
    main()