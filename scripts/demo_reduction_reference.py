"""Run finite #303 examples; optionally write separate target/candidate JSON files."""

import argparse
import json
from pathlib import Path

from reduction_fixtures import examples
from reduction_reference import check


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", type=Path, metavar="DIRECTORY")
    args = parser.parse_args()
    reports = {}
    for title, (target, candidate) in examples().items():
        reports[title] = check(target, candidate)
        if args.write_fixtures:
            args.write_fixtures.mkdir(parents=True, exist_ok=True)
            for kind, value in (("target", target), ("candidate", candidate)):
                path = args.write_fixtures / f"{title}.{kind}.json"
                path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"scope": "finite reference only; no Lean/Core/native connection",
                      "examples": reports}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
