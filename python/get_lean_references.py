#!/usr/bin/env python3
import json
from pathlib import Path
import sys

LABEL_PREFIX = "--% latex_label: "

def usage(exit_code):
    s = sys.stdout if exit_code == 0 else sys.stderr
    print(
        f"usage: {sys.argv[0]} DIR AUX\n",
        "scan *.lean files in DIR and match latex labels in comments with "
        "those in the *.aux file AUX\n"
        " labels are given by comments of the form\n"
        f"    {LABEL_PREFIX}<label>\n",
        " output is a JSON list of objects of the form\n"
        "     {\n"
        "       \"name\": \"<theorem/def/lemma/etc name>\", \n"
        "       \"references\": [\n"
        "         {\"path\": \"<lean path>\", \"lineno\": <lineno>}\n"
        "         ...\n"
        "         ]\n"
        "     }\n"
        " note that a label may have several lean references. paths are given"
        " relative to DIR",
        file=s
    )
    sys.exit(exit_code)

def parse_brackets(s):
    """
    parse a string of the form {s1}{s2}...{sn}
    """
    while s:
        if not s.startswith("{"):
            raise ValueError
        s = s[1:]
        part = ""
        brackets = 0
        # read up to the matching '}' (not necessarily the *first* one, if the
        # substring contains a bracket pair)
        while s:
            c = s[0]
            s = s[1:]
            if c == "}" and brackets == 0:
                break

            if c == "{":
                brackets += 1
            elif c == "}":
                brackets -= 1
            part += c
        yield part

def main():
    args = sys.argv[1:]
    try:
        if not args or args[0] in ("-h", "--help"):
            usage(0)
        lean_dir, aux_file = args
    except ValueError:
        usage(1)

    output = []

    # first, collect lean references grouped by label
    refs = {}
    lean_path = Path(lean_dir)
    for p in lean_path.glob("**/*.lean"):
        with p.open("r") as f:
            for lineno, line in enumerate(f.readlines()):
                line = line.strip()
                if not line.startswith(LABEL_PREFIX):
                    continue
                label = line[len(LABEL_PREFIX):]
                path = p.relative_to(lean_path)
                if label not in refs:
                    refs[label] = []
                refs[label].append({"path": str(path), "lineno": lineno + 2})

    # now go through aux file
    aux_path = Path(aux_file)
    with aux_path.open("r") as f:
        for line in f.readlines():
            line = line.strip()
            newlabel_marker = r"\newlabel{"
            if not line.startswith(newlabel_marker):
                continue
            line = line[len(newlabel_marker):]
            # get label
            label = ""
            for char in line:
                if char == "}":
                    break
                label += char
            if label not in refs:
                continue
            line = line[len(label) + 1:]  # + 1 for closing '}'
            line = line[1:-1]             # remove surrounding brackets
            # name is 4th component
            try:
                name = list(parse_brackets(line))[3]
            except (ValueError, IndexError):
                continue
            # sanitise name
            name = name.replace(".", " ").title()
            output.append({
                "name": name,
                "references": refs[label]
            })

    json.dump(output, sys.stdout, indent=2)

if __name__ == "__main__":
    main()
