#!/usr/bin/env python3
"""Compiled sharing checks for a bounded adaptive turn and its actual trace.

Policy/environment closures and the completion engine are explicit boundaries.
Direct closure-call sites are counted separately from path applications.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def sites(functions, caller, target, expected=1):
    count = len(re.findall(r"\b" + re.escape(target) + r"\s*\(", functions[caller]))
    if count != expected:
        raise ValueError(f"{caller}: expected {expected} direct {target} sites, found {count}")


def closure_site(functions, caller, arity, field):
    count = len(re.findall(r"lean_apply_" + str(arity) + r"\(v_" + field + r"_\d+_\s*,", functions[caller]))
    if count != 1:
        raise ValueError(f"{caller}: expected one {field} application site, found {count}")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    program = runpy.run_path(str(ROOT / "scripts/check-documentary-program-codegen.py"))
    functions, texts = {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        source = program["scalar_literals"](path.read_text(encoding="utf-8"))
        texts.append(source)
        functions.update(agent["bodies_with_objects"](source))
    params = agent["parameters"](texts)
    select = agent["shared"]["select"]
    Value = agent["Value"]

    class AdaptiveAnalysis(agent["AgentAnalysis"]):
        def global_value(self, name):
            body = self.functions.get(name, "")
            target = re.search(r"\.m_fun\s*=\s*\(void\*\)\s*((?:l|lp)_\w+)", body)
            fixed = re.search(r"\.m_num_fixed\s*=\s*(\d+)", body)
            if target and fixed and int(fixed[1]):
                # Exactly one captured boolean immediate, never a symbolic field.
                fields = re.search(r"\.m_objs\s*=\s*\{(.*?)\}", body, re.S)
                literal = re.fullmatch(r"\(\(lean_object\*\)\(\(\(size_t\)\(([01])\) << 1\) \| 1\)\)",
                                       fields[1].strip() if fields else "")
                arity = re.search(r"\.m_arity\s*=\s*(\d+)", body)
                if int(fixed[1]) != 1 or not literal or not arity or int(arity[1]) != 2 or target[1] not in self.functions:
                    raise ValueError("Unsupported adaptive static capture: " + name)
                return Value(function=target[1], fixed=1, fields={0: Value(number=int(literal[1]))})
            return super().global_value(name)

    def applications(current, compiled_params, entry, target, maximum, *, boundaries=()):
        normalized = {name: re.sub(r"\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)", r"\1", body)
                      for name, body in current.items()}
        analysis = AdaptiveAnalysis(normalized, compiled_params, agent["shared"]["reachable"],
                                    target=target, boundaries=boundaries)
        _, low, high = analysis.run(entry, [Value() for _ in compiled_params[entry]])
        if low != maximum or high != maximum:
            raise ValueError(f"{entry}: expected {maximum} applications of {target}, found [{low},{high}]")
        print(f"ADAPTIVE_APPLICATIONS_OK {entry}: {target}=[{low},{high}]; explicit scope")
    base = "Agent_Local_Documentary_Adaptive_"
    worker = select(functions, base + "run___redArg")
    turn = select(functions, base + "takeTurn___redArg")
    selection = select(functions, base + "selection___redArg")
    dispatch = select(functions, base + "dispatch___redArg")
    fallback = select(functions, base + "fallback___redArg")
    diverted = select(functions, base + "diverted")
    single = select(functions, base + "single___redArg")
    step = select(functions, "Agent_Local_Documentary_Program_step___redArg")
    completion = select(functions, base + "Execution_complete___redArg")
    certificate = select(functions, "Agent_Local_Documentary_AdaptiveCases_hostileComplete")
    actuals = [name for name in functions if name.startswith("_init_") and
               name.endswith("Agent_Local_Documentary_AdaptiveCases_hostile___closed__1")]
    if len(actuals) != 1:
        raise ValueError("Expected one actual hostile-run initializer")
    actual = actuals[0]

    def check(current):
        applications(current, params, turn, selection, 1, boundaries=(dispatch,))
        applications(current, params, turn, dispatch, 1, boundaries=(selection,))
        applications(current, params, fallback, step, 1)
        applications(current, params, diverted, step, 2)
        applications(current, params, single, step, 0)
        applications(current, params, certificate, worker, 0, boundaries=(completion,))
        applications(current, params, actual, worker, 1)
        sites(current, worker, turn)
        sites(current, worker, worker)
        closure_site(current, worker, 1, "feed")
        closure_site(current, selection, 3, "choose")

    check(functions)
    mutations = [(turn, selection), (turn, dispatch), (fallback, step), (diverted, step),
                 (worker, turn), (worker, worker), (worker, "lean_apply_1"), (selection, "lean_apply_3")]
    for caller, target in mutations:
        pattern = re.compile(r"\b(v_\w+)\s*=\s*" + re.escape(target) + r"\([^;]*\);")
        matches = list(pattern.finditer(functions[caller]))
        expected = 2 if caller == diverted else 1
        if len(matches) != expected:
            raise ValueError("Unexpected compiled mutation site: " + target)
        site = matches[0]
        duplicate = site.group(0).replace(site.group(1), "v_adaptive_duplicate", 1)
        current = dict(functions)
        current[caller] = current[caller][:site.start()] + duplicate + "\n" + current[caller][site.start():]
        try:
            with redirect_stdout(io.StringIO()):
                check(current)
        except ValueError as error:
            if not any(fragment in str(error) for fragment in ("found [2,2]", "found [3,3]", "found 2")):
                raise ValueError("Unexpected mutation rejection: " + str(error)) from error
        else:
            raise ValueError("Duplicate adaptive call accepted: " + target)
    current = dict(functions)
    current[certificate] = "v_adaptive_replay = " + worker + "(" + ",".join(
        "lean_box(0)" for _ in params[worker]) + ");\n" + current[certificate]
    try:
        with redirect_stdout(io.StringIO()):
            check(current)
    except ValueError as error:
        if "found [1,1]" not in str(error):
            raise ValueError("Unexpected replay rejection: " + str(error)) from error
    else:
        raise ValueError("Certificate replay accepted")
    for field in ("((lean_object*)(((size_t)(2) << 1) | 1))", worker):
        current = dict(functions)
        captures = [name for name, body in current.items() if
                    "AdaptiveCases_repeatedRead___closed__1" in name and ".m_fun" in body]
        if not captures:
            raise ValueError("Missing exact boolean-capture regression site")
        for name in captures:
            current[name] = re.sub(r"\.m_objs\s*=\s*\{.*?\}", ".m_objs = {" + field + "}", current[name], flags=re.S)
        try:
            with redirect_stdout(io.StringIO()):
                check(current)
        except ValueError as error:
            if "Unsupported adaptive static capture" not in str(error):
                raise ValueError("Unexpected capture rejection: " + str(error)) from error
        else:
            raise ValueError("Unsupported symbolic or nonboolean capture accepted")
    print("DOCUMENTARY_ADAPTIVE_CODEGEN_OK: seven application checks, four direct call-site checks; "
          "nine call mutations and two unsupported captures rejected; explicit policy/environment/completion scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_ADAPTIVE_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
