"""Verify the nine-letter minimum and the ten-letter upper and lower bounds."""

import argparse

from proofs.nine import check_nine
from proofs.ten import replay_branch, witness_and_four


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "branch",
        nargs="?",
        default="all",
        choices=("all", "nine", "four", "five", "seven", "six"),
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=4,
        help="worker processes for the ten-letter checks (default: 4)",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.branch in ("all", "nine"):
        check_nine.replay()
    if args.branch in ("all", "four"):
        witness_and_four.replay(args.jobs)
    for branch in ("five", "seven", "six"):
        if args.branch in ("all", branch):
            replay_branch.replay(branch, args.jobs)
    if args.branch == "all":
        print("Both bounds verified. The ten-letter minimum is 83.")


if __name__ == "__main__":
    main()
