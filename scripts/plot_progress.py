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
    """Get list of commits on current branch with timestamps."""
    result = subprocess.run(
        ['git', 'log', '--format=%H|%at', '--reverse'],
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
    """Parse CSV and count total, verified, specified, draft spec, and extracted functions."""
    if not csv_content:
        return None, None, None, None, None

    reader = csv.DictReader(io.StringIO(csv_content))
    total = 0
    verified = 0
    specified = 0
    draft_spec = 0
    extracted = 0

    for row in reader:
        total += 1
        status = row.get('verified', '').strip().lower()
        spec_theorem = row.get('spec_theorem', '').strip()
        extracted_status = row.get('extracted', '').strip().lower()

        if status == 'verified':
            verified += 1
        elif status == 'specified':
            specified += 1
        elif spec_theorem:  # Has spec_theorem but not verified/specified = draft
            draft_spec += 1

        if extracted_status == 'extracted':
            extracted += 1

    return total, verified, specified, draft_spec, extracted

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
    extracteds = []

    print("\nAnalyzing status.csv from each commit...")
    for i, commit in enumerate(commits):
        if i % 10 == 0:
            print(f"  Processing commit {i+1}/{len(commits)}", end='\r')

        csv_content = get_file_from_commit(commit['hash'], 'status.csv')
        total, verified, specified, draft_spec, extracted = count_verification_status(csv_content)

        if total is not None:
            dates.append(commit['datetime'])
            totals.append(total)
            verifieds.append(verified)
            specifieds.append(specified)
            draft_specs.append(draft_spec)
            extracteds.append(extracted)

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

    # Create stacked area plot with step behavior (reverse order for legend)
    ax.fill_between(dates, verified_arr + specified_arr + draft_spec_arr, totals,
                     alpha=0.5, color='#95a5a6', label='Not started', step='post')
    ax.fill_between(dates, verified_arr + specified_arr,
                     verified_arr + specified_arr + draft_spec_arr,
                     alpha=0.7, color='#f9e79f', label='Draft', step='post')
    ax.fill_between(dates, verified_arr, verified_arr + specified_arr,
                     alpha=0.7, color='#5dade2', label='Specified', step='post')
    ax.fill_between(dates, 0, verified_arr,
                     alpha=0.7, color='#2ecc71', label='Verified', step='post')

    # Add step-style plots (horizontal lines with vertical jumps)
    ax.plot(dates, verifieds, color='darkgreen', linewidth=2, alpha=0.8, drawstyle='steps-post')
    ax.plot(dates, totals, color='darkblue', linewidth=2, alpha=0.8, drawstyle='steps-post')

    # Add dotted line for extracted (no points)
    ax.plot(dates, extracteds, ':', color='purple', linewidth=2, alpha=0.7, label='Extracted', drawstyle='steps-post')

    # Formatting
    ax.set_ylabel('Number of Functions', fontsize=12)
    ax.set_title('Curve25519-Dalek Verification Progress Over Time',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10, framealpha=0.9)
    ax.grid(True, alpha=0.3, linestyle='--')

    # Format x-axis dates
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%d-%m-%y'))
    ax.xaxis.set_major_locator(mdates.AutoDateLocator())
    plt.xticks(rotation=0)

    # Add "Verified: X/Y (Z%)" text anchored at the final verified point
    if verifieds:
        latest_verified = verifieds[-1]
        latest_total = totals[-1]
        verified_pct = (latest_verified / latest_total * 100) if latest_total > 0 else 0

        # Position text slightly higher and to the left of the final verified point
        # Add a small offset in data coordinates
        date_offset = mdates.date2num(dates[-1]) - mdates.date2num(dates[0])
        text_date_num = mdates.date2num(dates[-1]) - 0.02 * date_offset
        text_date = mdates.num2date(text_date_num)

        ax.text(text_date, latest_verified + 1,
                f'Verified: {latest_verified}/{latest_total} ({verified_pct:.1f}%)',
                fontsize=11, fontweight='bold',
                verticalalignment='bottom', horizontalalignment='right',
                color='black')

    plt.tight_layout()

    # Save the plot in both PNG and SVG formats
    output_png = 'verification_progress.png'
    output_svg = 'verification_progress.svg'
    plt.savefig(output_png, dpi=300, bbox_inches='tight')
    plt.savefig(output_svg, format='svg', bbox_inches='tight')
    print(f"\nPlots saved to {output_png} and {output_svg}")

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
    print(f"    Extracted:  {extracteds[0]:2d} ({extracteds[0]/totals[0]*100:5.1f}%)")
    print(f"    Total:      {totals[0]:2d}")
    print(f"\n  Current state ({dates[-1].strftime('%Y-%m-%d')}):")
    print(f"    Verified:   {verifieds[-1]:2d} ({verifieds[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Specified:  {specifieds[-1]:2d} ({specifieds[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Draft Spec: {draft_specs[-1]:2d} ({draft_specs[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Extracted:  {extracteds[-1]:2d} ({extracteds[-1]/totals[-1]*100:5.1f}%)")
    print(f"    No Spec:    {unspecified[-1]:2d} ({unspecified[-1]/totals[-1]*100:5.1f}%)")
    print(f"    Total:      {totals[-1]:2d}")
    print(f"\n  Progress:")
    print(f"    Verified:   +{verifieds[-1] - verifieds[0]}")
    print(f"    Specified:  +{specifieds[-1] - specifieds[0]}")
    print(f"    Draft Spec: +{draft_specs[-1] - draft_specs[0]}")
    print(f"    Extracted:  +{extracteds[-1] - extracteds[0]}")
    print(f"    Total:      +{totals[-1] - totals[0]}")

if __name__ == '__main__':
    main()