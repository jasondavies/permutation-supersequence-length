"""Verify the nine-letter minimum and the ten-letter upper and lower bounds."""

import argparse
from importlib.metadata import version
import json
import platform
import subprocess
import sys

from proofs.nine import check_nine
from proofs.shared.progress import elapsed, log
from proofs.ten import replay_branch, witness_and_four


def command_output(*command):
    try:
        return subprocess.check_output(command, text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def environment():
    compiler = command_output("c++", "--version")
    return {
        "commit": command_output("git", "rev-parse", "HEAD"),
        "uncommitted_changes": bool(
            command_output("git", "status", "--porcelain", "--untracked-files=no")
        ),
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "compiler": compiler.splitlines()[0] if compiler else None,
        "packages": {p: version(p) for p in ("python-sat", "numpy", "cbor2")},
    }


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
    parser.add_argument(
        "--summary", metavar="FILE", help="also write a JSON summary of the run to FILE"
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")

    # Record the environment before the run writes any output files.
    setup = environment()
    results = {}
    if args.branch in ("all", "nine"):
        results["nine"] = check_nine.replay()
    if args.branch == "all":
        witness_and_four.check_witness()
        results["witness"] = {"permutations": 3628800}
    elif args.branch == "four":
        witness_and_four.replay(args.jobs)
        results["four"] = {"cuts": 88}
    for branch in ("five", "seven", "six"):
        if args.branch in ("all", branch):
            results[branch] = replay_branch.replay(branch, args.jobs)

    summary = {
        "branch": args.branch,
        "jobs": args.jobs,
        "elapsed": elapsed(),
        "environment": setup,
        "results": results,
    }
    print(json.dumps(summary, indent=2))
    if args.summary:
        with open(args.summary, "w") as out:
            json.dump(summary, out, indent=2)
            out.write("\n")
    if args.branch == "all":
        log(
            "All computational cases verified. Together with the Lean-checked "
            "four-copy lemma, the ten-letter minimum is 83."
        )


if __name__ == "__main__":
    main()
