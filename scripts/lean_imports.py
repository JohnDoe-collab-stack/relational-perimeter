"""Read Lean import headers for local checks; no theorem or source rewriting.

Nested comments, split commands and imports on the same line are handled.
The supported module names are the ASCII dotted names used by this repository.
Unsupported import syntax fails closed instead of silently dropping an edge.
"""
import argparse
from functools import lru_cache
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


class ImportSyntaxError(ValueError):
    pass


def lean_code(text):
    output, index, depth, quoted = [], 0, 0, False
    while index < len(text):
        pair, char = text[index:index + 2], text[index]
        if depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            if char == "\\":
                output.extend("  ")
                index += 2
            else:
                quoted = char != '"'
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            output.extend(" " * (end - index))
            index = end
        elif char == '"':
            quoted = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    if depth or quoted:
        raise ImportSyntaxError("IMPORT_PARSE: unclosed comment/string")
    return "".join(output).lstrip("\ufeff")


@lru_cache(maxsize=512)
def imports(text):
    lexemes = list(re.finditer(NAME.pattern + r"|[^\s]", lean_code(text)))
    tokens = [lexeme.group() for lexeme in lexemes]
    result, index = [], 0
    for prefix in ("module", "prelude"):
        if index < len(tokens) and tokens[index] == prefix:
            index += 1
    while index < len(tokens):
        start = index
        for qualifier in ("public", "meta"):
            if index < len(tokens) and tokens[index] == qualifier:
                index += 1
        if index >= len(tokens) or tokens[index] != "import":
            break
        index += 1
        if index < len(tokens) and tokens[index] == "all":
            index += 1
        if index >= len(tokens) or not NAME.fullmatch(tokens[index]) or tokens[index] in (
                "import", "module", "prelude", "public", "meta", "all", "namespace", "def"):
            raise ImportSyntaxError(f"IMPORT_PARSE: missing module at token {start}")
        result.append(tokens[index])
        index += 1
        if index < len(tokens) and (tokens[index] in (".", "«") or
                                  lexemes[index].start() == lexemes[index - 1].end()):
            raise ImportSyntaxError(f"IMPORT_PARSE: unsupported module at token {start}")
    return result


def main():
    # Machine-readable module names must have LF separators on every platform.
    sys.stdout.reconfigure(newline="\n")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path)
    parser.add_argument("--stdin", action="store_true")
    args = parser.parse_args()
    if args.stdin == (args.source is not None):
        parser.error("provide a source file or --stdin")
    source = sys.stdin.buffer.read() if args.stdin else args.source.read_bytes()
    for module in imports(source.decode("utf-8-sig")):
        print(module)


if __name__ == "__main__":
    try:
        main()
    except (OSError, UnicodeError, ImportSyntaxError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
