#!/usr/bin/env python3
"""Named C checks for the controlled original frontier normalizer.

Checks reject native producer replay and loss of actual retained routing data.
Mutation fixtures alter textual checker inputs, not compiled executions.
Deferred routing invocations, the bound bootstrap and global costs stay open.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_"
MODULES = ("ControlFrontierNormalizationSyntax_", "ControlFrontierNormalizationSearch_",
           "ControlFrontierNormalization_", "ControlMaster_expandedSearchCode")
NATIVE_SUFFIXES = (
    "ConstitutiveSearch_normalizeAcceptedFrontier",
    "ConstitutiveSearch_insertAcceptedIntoIrreducible",
    "ConstitutiveSearch_RelationSearch_classifyPairCertified",
    "ConstitutiveSearch_SAT_normalizeGeneratedStructuralFrontierByFlip",
    "ConstitutiveSearch_SAT_generatedStructuralFlipAtSearch",
    "ConstitutiveSearch_SAT_Cnf_flipAt",
    "ConstitutiveSearch_SAT_Clause_flipAt",
    "ConstitutiveSearch_SAT_Literal_flipAt",
    "ConstitutiveSearch_SAT_StructuralBranchDecision_flipAt",
    "ConstitutiveSearch_SAT_flipStructuralDecisionsAt",
    "ConstitutiveSearch_AcceptedFrontierCode_eval",
    "ConstitutiveSearch_Agent_Local_Documentary_Control_execute",
    "ConstitutiveSearch_Agent_Local_Documentary_Control_runCtl",
)
NATIVE = r"\b\w*(?:" + "|".join(map(re.escape, NATIVE_SUFFIXES)) + r")(?:___\w+)?\s*\("
NATIVE_EQUALITY = (r"\b(?:lean_nat_dec_eq|\w*(?:SAT_(?:instDecidableEqLiteral|"
                   r"instDecidableEqStructuralBranchDecision|decEqLiteral|decEqStructuralBranchDecision)|"
                   r"List_(?:instDecidableEq|decidableEq)))(?:___\w+)?\s*\(")


def make_check(functions, select):
    scope = [name for name in functions if any(BASE + module in name for module in MODULES)
             and not name.endswith("___boxed") and "closed__" not in name]
    if not scope:
        raise ValueError("Controlled normalization compiled bodies missing")
    # Allowance bootstraps are outside the paid execution scope. In particular,
    # Lean lowers their Nat recursion to a native zero test. Native producers
    # remain forbidden there, while comparison replay is checked in code paths.
    execution_scope = [name for name in scope if BASE + "ControlMaster_expandedSearchCode" in name or
                       re.search(BASE + r"ControlFrontierNormalization(?:Syntax|Search)?_"
                                 r"(?:listCode|cnfCode|boolCode|decisionCode|historyCode|mapCode|"
                                 r"flipLiteralCode|flipClauseCode|flipCnfCode|flipDecisionCode|flipHistoryCode|"
                                 r"findCode|fromFound|classifyCode|insertCode|code)(?:_|$)", name)]
    entry = select(functions, BASE + "ControlFrontierNormalization_code___redArg")
    consumers = [name for name in scope if BASE + "ControlMaster_expandedSearchCode" in name]
    producer_consumers = [name for name in consumers if re.search(re.escape(entry) + r"\s*\(", functions[name])]
    if len(producer_consumers) != 1:
        raise ValueError("Normalization must have one actual expanded-search consumer")
    owner = producer_consumers[0]
    data_paths = (
        ("ControlFrontierNormalizationSyntax_mapCode___redArg___lam__0",
         r"lean_ctor_set\([^,]+, 0, v_produced_\d+_\)"),
        ("ControlFrontierNormalizationSyntax_mapCode___redArg___lam__0",
         r"lean_ctor_set\([^,]+, 1, v_tail_\d+_\)"),
        ("ControlFrontierNormalizationSearch_findCode___redArg___lam__4",
         r"ControlFrontierNormalizationSyntax_cnfCode\(v_formula_\d+_, v_flipped_\d+_\)"),
        ("ControlFrontierNormalizationSearch_findCode___redArg___lam__3",
         r"ControlFrontierNormalizationSyntax_historyCode\(v_decisions_\d+_, v_history_\d+_\)"),
        ("ControlFrontierNormalizationSearch_classifyCode___redArg___lam__0",
         r"ControlFrontierNormalizationSearch_fromFound___redArg\(v_forward_\d+_, v_backward_\d+_\)"),
        ("ControlFrontierNormalizationSearch_classifyCode___redArg",
         r"ControlFrontierNormalizationSearch_findCode___redArg\(v_selected_\d+_, v_left_\d+_, v_right_\d+_\)"),
        ("ControlFrontierNormalizationSearch_classifyCode___redArg___lam__3",
         r"ControlFrontierNormalizationSearch_findCode___redArg\(v_selected_\d+_, v_right_\d+_, v_left_\d+_\)"),
        ("ControlFrontierNormalizationSearch_classifyCode___redArg___lam__2",
         r"lean_closure_set\([^,]+, 0, v_forward_\d+_\)"),
        ("ControlFrontierNormalizationSearch_classifyCode___redArg___lam__2",
         r"lean_closure_set\([^,]+, 1, v_backward_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__7",
         r"v_retained_\d+_ = lean_ctor_get\(v_tailReduction_\d+_, 0\)"),
        ("ControlFrontierNormalization_code___redArg___lam__7",
         r"v_code_\d+_ = lean_ctor_get\(v_tailReduction_\d+_, 1\)"),
        ("ControlFrontierNormalization_code___redArg___lam__7",
         r"ControlFrontierNormalization_insertCode___redArg\(v_selected_\d+_, v_head_\d+_, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__7",
         r"lean_closure_set\([^,]+, 3, v_code_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__5",
         r"v_prepended_\d+_ = lean_alloc_ctor\(4, 4, 0\)"),
        ("ControlFrontierNormalization_code___redArg___lam__5",
         r"lean_ctor_set\(v_prepended_\d+_, 1, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__5",
         r"lean_ctor_set\(v_prepended_\d+_, 3, v_code_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"v_retained_\d+_ = lean_ctor_get\(v_inserted_\d+_, 0\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"v_code_\d+_ = lean_ctor_get\(v_inserted_\d+_, 1\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"v_route_\d+_ = lean_alloc_ctor\(5, 5, 0\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"lean_ctor_set\(v_route_\d+_, 2, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"lean_ctor_set\(v_route_\d+_, 3, v_prepended_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__4",
         r"lean_ctor_set\(v_route_\d+_, 4, v_code_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__3",
         r"lean_ctor_set\([^,]+, 0, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_code___redArg___lam__3",
         r"lean_ctor_set\([^,]+, 1, v_route_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__8",
         r"v_route_\d+_ = lean_alloc_ctor\(2, 4, 0\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__8",
         r"lean_ctor_set\(v_route_\d+_, 3, v_forward_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__10",
         r"v_absorption_\d+_ = lean_alloc_ctor\(3, 4, 0\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__10",
         r"lean_ctor_set\(v_absorption_\d+_, 3, v_backward_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__9",
         r"v_retained_\d+_ = lean_ctor_get\(v_recursive_\d+_, 0\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__9",
         r"v_code_\d+_ = lean_ctor_get\(v_recursive_\d+_, 1\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__9",
         r"lean_ctor_set\(v_route_\d+_, 2, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__9",
         r"lean_ctor_set\(v_route_\d+_, 3, v_absorption_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__9",
         r"lean_ctor_set\(v_route_\d+_, 4, v_code_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__11",
         r"lean_ctor_set\([^,]+, 0, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__11",
         r"lean_ctor_set\([^,]+, 1, v_route_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__3",
         r"v_retained_\d+_ = lean_ctor_get\(v_recursive_\d+_, 0\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__3",
         r"v_code_\d+_ = lean_ctor_get\(v_recursive_\d+_, 1\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__3",
         r"lean_ctor_set\(v_prepended_\d+_, 1, v_retained_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__3",
         r"lean_ctor_set\(v_prepended_\d+_, 3, v_code_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__4",
         r"lean_ctor_set\(v_route_\d+_, 3, v_swap_\d+_\)"),
        ("ControlFrontierNormalization_insertCode___redArg___lam__4",
         r"lean_ctor_set\(v_route_\d+_, 4, v_prepended_\d+_\)"),
        ("ControlMaster_expandedSearchCode___lam__2",
         r"v_frontier_\d+_ = lean_ctor_get\(v_actualOpening_\d+_, 0\)"),
        ("ControlMaster_expandedSearchCode___lam__2",
         r"ControlFrontierNormalization_code___redArg\(v___x_\d+_, v_frontier_\d+_\)"),
        ("ControlMaster_expandedSearchCode___lam__1",
         r"lean_closure_set\([^,]+, 4, v_actualReduction_\d+_\)"),
        ("ControlMaster_expandedSearchCode___lam__0",
         r"lean_ctor_set\([^,]+, 3, v_actualOpening_\d+_\)"),
        ("ControlMaster_expandedSearchCode___lam__0",
         r"lean_ctor_set\([^,]+, 4, v_actualReduction_\d+_\)"),
    )
    data_paths = [(select(functions, BASE + suffix), pattern) for suffix, pattern in data_paths]
    classified = select(functions, BASE + "ControlFrontierNormalizationSearch_fromFound___redArg")

    def check(current):
        for name in scope:
            if re.search(NATIVE, current[name]):
                raise ValueError("Native normalization producer replayed: " + name)
        for name in execution_scope:
            if re.search(NATIVE_EQUALITY, current[name]):
                raise ValueError("Native normalization comparison replayed: " + name)
        calls = sum(len(re.findall(re.escape(entry) + r"\s*\(", current[name])) for name in consumers)
        if calls != 1 or not re.search(re.escape(entry) + r"\s*\(", current[owner]):
            raise ValueError("Actual controlled normalizer omitted, duplicated or moved")
        for name, pattern in data_paths:
            if not re.search(pattern, current[name]):
                raise ValueError("Actual normalization data path dropped: " + name)
        body = current[classified]
        forwards = re.findall(r"(v_\w+) = lean_ctor_get\(v_forward_\d+_, 0\)", body)
        backwards = re.findall(r"(v_\w+) = lean_ctor_get\(v_backward_\d+_, 0\)", body)
        packet = re.search(r"(v_\w+) = lean_alloc_ctor\(0, 2, 0\)", body)
        if not forwards or not backwards or not packet or any(not re.search(
                r"lean_ctor_set\(" + re.escape(packet[1]) + ", " + str(field) + ", " +
                re.escape(value) + r"\)", body) for field, value in ((0, forwards[-1]), (1, backwards[-1]))):
            raise ValueError("Bidirectional classification loses an actual relation witness")

    mutations = [(name, functions[name] + " lp_forbidden_" + suffix + "();")
                 for name in scope for suffix in NATIVE_SUFFIXES]
    mutations.extend((name, functions[name] + " lean_nat_dec_eq();") for name in execution_scope)
    mutations.extend(((owner, functions[owner] + entry + "();"),
                      (owner, functions[owner].replace(entry, "lp_substituted_normalizer"))))
    mutations.extend((name, re.sub(pattern, "lp_dropped_data_path", functions[name]))
                     for name, pattern in data_paths)
    for variable in ("forward", "backward"):
        mutations.append((classified, re.sub(r"lean_ctor_get\(v_" + variable + r"_\d+_, 0\)",
                                             "lp_substituted_relation()", functions[classified])))
    return check, mutations, scope, execution_scope


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(agent["bodies_with_objects"](path.read_text(encoding="utf-8")))
    check, mutations, scope, execution_scope = make_check(functions, agent["shared"]["select"])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError("Normalization mutation accepted: " + name)
    native_sites = sum(len(re.findall(NATIVE, functions[name])) for name in scope) + sum(
        len(re.findall(NATIVE_EQUALITY, functions[name])) for name in execution_scope)
    print("DOCUMENTARY_FRONTIER_NORMALIZATION_CODEGEN_OK: " + str(len(mutations)) +
          " textual mutations rejected; " + str(native_sites) +
          " native normalizer/helper/comparison sites in named scope; actual flips and both found directions; "
          "actual retained routing and whole Stage; one controlled normalizer consumer; "
          "deferred routing and bootstrap costs remain open")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_FRONTIER_NORMALIZATION_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
