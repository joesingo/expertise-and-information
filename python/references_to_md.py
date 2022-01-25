#!/usr/bin/env python3
import json
from pathlib import Path
import sys

PATH_PREFIX = Path("lean/src")

def usage(exit_code):
    s = sys.stdout if exit_code == 0 else sys.stderr
    print(
        f"usage: {sys.argv[0]}\n",
        "read output from get_lean_references.py on stdin and write a list\n"
        " of links in GitHub Markdown format to stdout",
        file=s
    )
    sys.exit(exit_code)

def get_href(ref):
    path = PATH_PREFIX.joinpath(Path(ref["path"]))
    return str(path) + "#L" + str(ref["lineno"])

def main():
    args = sys.argv[1:]
    if len(args) > 0 and args[0] in ("-h", "--help"):
        usage(0)

    try:
        inp = json.load(sys.stdin)
    except json.decoder.JSONDecodeError:
        print("invalid JSON input", file=sys.stderr)

    # NOTE: no error checking that JSON input has the correct keys
    for obj in inp:
        name = obj["name"]
        if len(obj["references"]) == 1:
            ref = obj["references"][0]
            href = get_href(ref)
            print(f"* [{name}]({href})")
        else:
            links = []
            for i, ref in enumerate(obj["references"]):
                href = get_href(ref)
                links.append(f"[{i + 1}]({href})")
            slinks = ", ".join(links)
            print(f"* {name}: {slinks}")

if __name__ == "__main__":
    main()
