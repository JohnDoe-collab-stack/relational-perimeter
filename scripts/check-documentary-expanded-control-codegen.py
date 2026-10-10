#!/usr/bin/env python3
"""Named checks of actual master packets and assemblies; full D2 stays open.

Mutation fixtures modify checker inputs, not compiled executions. Metadata
reads, inner constitutive generation, role opening and callbacks remain open.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_"
MODULES = ("ControlConstitutiveResources_", "ControlMasterData_", "ControlMasterGeneration_",
           "ControlMasterCandidates_", "ControlMasterDiscovery_", "ControlMasterHead_",
           "ControlMeasuredComparison_", "ControlMeasuredTransformation_",
           "ControlMeasuredState_", "ControlMeasuredDiscovery_",
           "ControlMeasuredSchedule_", "ControlMeasuredTransport_", "ControlSequentialStage_",
           "ControlNextState_", "ControlMasterApplication_", "ControlProducedImage_", "ControlMasterDecomposition_",
           "ControlProvenance_", "ControlQuotationAssembly_", "ControlMissingAssembly_",
           "ControlDeferred_", "ControlAdministration_", "ControlMaster_expanded", "ControlStep_expanded")
FORBIDDEN = (r"\b\w*(?:EndogenousDecomposition_VariableMaster_(?:masterHead|nextCursor)|"
             r"EndogenousDecomposition_(?:runThreadedNextDiscovery|measuredGeneratedExtractionFromSeed|"
             r"exploreRecordedCandidates|tryMeasuredCandidate|searchMeasuredRelation(?:FromData)?|"
             r"compareUnary|compareMeasured(?:List|Literal|Cnf|Bool|Decision|History)|"
             r"flipMeasured(?:Literal|Clause|Cnf|Decision|History)|checkMeasuredFreshness|"
             r"containsMeasuredLiteral|constructMeasured(?:Residual|Child|DecoyClause|Formula|OperationalRoot)|"
             r"childFromMeasuredResidual)|"
             r"EndogenousDecomposition_(?:buildFromExecutedDiscovery|prefixLocalOperationalProducer|"
             r"buildThreadedConstitutiveStage|executeSequentialStageFromActiveRecorded|realizeNextOperationalState|"
             r"validateStoredSchedule|executeStoredSchedule|applyDiscoveryExecution|applyMeasuredTransportCode|"
             r"executedStageDecomposition|executedRoleReductionLicense|producedRoleOutputRegime|producedRoleOutput|"
             r"validationFromMeasuredSearch|executionFromMeasuredSearch)|"
             r"Extensive_(?:deduplicate|containsWith|ProducedOutputImage_(?:regime|imageRegime))|"
             r"SAT_(?:runCandidateExtraction|extractClauseCandidateRun|extractCnfCandidateRun)|"
             r"Documentary_Program_(?:quotationStep|missingStep)|Documentary_Deduction_quote)"
             r"(?:___redArg)?\s*\(")

def make_check(functions, select):
    scope = [name for name in functions if any(BASE + module in name for module in MODULES)
             and not name.endswith("___boxed") and "closed__" not in name]
    if not scope:
        raise ValueError("Expanded compiled functions missing")
    engines = (
        ("EndogenousDecomposition_generateCanonicalStageFromSource___redArg", "ControlNextState_generationCode", 96),
        ("EndogenousDecomposition_relationalConstitutiveRoleStage", "ControlMasterDecomposition_roleCode", 39))
    boundaries = []
    for suffix, owner, label in engines:
        target = select(functions, suffix)
        candidates = [name for name in scope if BASE + owner in name and
                      re.search(re.escape(target) + r"\s*\(", functions[name])]
        if len(candidates) != 1:
            raise ValueError("Engine outside its single named callback: " + suffix)
        actual = candidates[0]
        parents = [name for name in scope if
                   re.search(r"lean_alloc_closure\(\(void\*\)\(" + re.escape(actual) + r"(?:___boxed)?\)", functions[name])]
        paid = [name for name in parents if re.search(r"= " + str(label) + r";", functions[name])]
        if len(paid) != 1:
            raise ValueError("Engine callback lacks its named paid parent: " + suffix)
        boundaries.append((target, actual, paid[0], label))
    head = select(functions, BASE + "ControlMasterHead_fromParts___redArg")
    formation = select(functions, BASE + "ControlConstitutiveResources_extendCode___redArg___lam__2")
    expanded = select(functions, BASE + "ControlMaster_expandedSearchCode")
    expanded_head = select(functions, BASE + "ControlMasterHead_code")
    candidate = select(functions, BASE + "ControlMeasuredDiscovery_candidateCode___redArg")
    endpoints = select(functions, BASE + "ControlMeasuredDiscovery_candidateCode___redArg___lam__1")
    candidate_owners = [name for name in scope if BASE + "ControlMasterCandidates_code" in name]
    retained_fields = (
        ("ControlSequentialStage_fromParts___redArg", ((3, "stored"), (4, "validation"), (5, "measured"),
            (7, "validated"), (8, "execution"), (9, "source"), (10, "application"), (11, "next"))),
        ("ControlMasterApplication_fromParts___redArg", ((0, "stage"), (2, "next"))),
        ("ControlMasterDecomposition_licenseFromParts___redArg", ((0, "left"), (1, "leftConstitution"),
            (2, "right"), (3, "rightConstitution"))),
        ("ControlMasterDecomposition_decompositionFromParts___redArg", ((0, "role"), (1, "license"), (2, "image"))),
        ("ControlProducedImage_fromFrontier___redArg", ((1, "frontier"),)))
    retained_fields = [(select(functions, BASE + owner), fields) for owner, fields in retained_fields]

    def check(current):
        for name in scope:
            if re.search(FORBIDDEN, current[name]):
                raise ValueError("Original whole production or traversal replayed: " + name)
            if BASE + "ControlAdministration_" in name and re.search(
                    r"\b\w*Documentary_Control_execute(?:___redArg)?\s*\(", current[name]):
                raise ValueError("Metered evaluator delegates to the native source evaluator")
        for target, actual, parent, label in boundaries:
            calls = sum(len(re.findall(re.escape(target) + r"\s*\(", current[name])) for name in scope)
            if calls != 1 or not re.search(re.escape(target) + r"\s*\(", current[actual]):
                raise ValueError("Named engine is replayed or moved")
            if not re.search(r"= " + str(label) + r";", current[parent]):
                raise ValueError("Paid engine label missing")
            if not re.search(r"lean_alloc_closure\(\(void\*\)\(" + re.escape(actual) + r"(?:___boxed)?\)", current[parent]):
                raise ValueError("Actual engine continuation dropped")
        for field, variable in ((0, "head"), (1, "next")):
            if not re.search(r"lean_ctor_set\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", current[head]):
                raise ValueError("Whole head factory drops actual " + variable)
        if not re.search(r"lean_ctor_set\([^,]+, 0, v_computed_\d+_\)", current[formation]):
            raise ValueError("Formation drops the actual paid value")
        if len(re.findall(re.escape(expanded_head) + r"\s*\(", current[expanded])) != 1:
            raise ValueError("Expanded search does not consume one controlled head")
        if sum(len(re.findall(re.escape(candidate) + r"\s*\(", current[name])) for name in candidate_owners) != 1:
            raise ValueError("Candidate traversal does not consume one controlled attempt")
        for field, variable in ((1, "left"), (2, "right")):
            if not re.search(r"lean_ctor_set\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", current[endpoints]):
                raise ValueError("Candidate factory drops actual endpoint " + variable)
        for owner, fields in retained_fields:
            for field, variable in fields:
                if not re.search(r"lean_ctor_set\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", current[owner]):
                    raise ValueError("Constitutive packet drops actual " + variable + ": " + owner)

    mutations = [(name, functions[name] + " lp_forbidden_EndogenousDecomposition_VariableMaster_masterHead();")
                 for name in scope]
    for target, actual, parent, label in boundaries:
        mutations += [(actual, functions[actual] + target + "();"),
                      (parent, functions[parent].replace("= " + str(label) + ";", "= 0;")),
                      (parent, functions[parent].replace(actual, "lp_substituted"))]
    for owner, variable in ((head, "head"), (head, "next"), (formation, "computed")):
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    mutations.append((expanded, functions[expanded] + expanded_head + "();"))
    candidate_owner = next(name for name in candidate_owners if re.search(re.escape(candidate) + r"\s*\(", functions[name]))
    mutations += [(candidate_owner, functions[candidate_owner] + candidate + "();"),
                  (candidate_owner, functions[candidate_owner].replace(candidate, "lp_substituted"))]
    for variable in ("left", "right"):
        mutations.append((endpoints, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[endpoints])))
    for owner, fields in retained_fields:
        for _, variable in fields:
            mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    native_attempts = ("tryMeasuredCandidate", "searchMeasuredRelation", "searchMeasuredRelationFromData",
                       "compareUnary", "compareMeasuredList", "compareMeasuredLiteral", "compareMeasuredCnf",
                       "compareMeasuredBool", "compareMeasuredDecision", "compareMeasuredHistory",
                       "flipMeasuredLiteral", "flipMeasuredClause", "flipMeasuredCnf", "flipMeasuredDecision",
                       "flipMeasuredHistory", "checkMeasuredFreshness", "containsMeasuredLiteral",
                       "constructMeasuredResidual", "constructMeasuredChild", "childFromMeasuredResidual",
                       "buildFromExecutedDiscovery", "prefixLocalOperationalProducer", "buildThreadedConstitutiveStage",
                       "executeSequentialStageFromActiveRecorded", "realizeNextOperationalState", "validateStoredSchedule",
                       "executeStoredSchedule", "applyDiscoveryExecution", "applyMeasuredTransportCode",
                       "executedStageDecomposition", "executedRoleReductionLicense", "producedRoleOutputRegime",
                       "producedRoleOutput", "validationFromMeasuredSearch", "executionFromMeasuredSearch")
    mutations.extend((endpoints, functions[endpoints] + " lp_forbidden_EndogenousDecomposition_" + name + "();")
                     for name in native_attempts)
    return check, mutations, scope

def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(agent["bodies_with_objects"](path.read_text(encoding="utf-8")))
    check, mutations, scope = make_check(functions, agent["shared"]["select"])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError("Expanded-control mutation accepted: " + name)
    metadata = sum(len(re.findall(r"\b\w*Resources_(?:Producer_arguments|Support_read|read)(?:___redArg)?\s*\(",
                                 functions[name])) for name in scope if BASE + "ControlMasterHead_" in name)
    schedule_metadata = sum(len(re.findall(r"\b\w*SAT_DiscoverySchedule_entry(?:___redArg)?\s*\(", functions[name]))
                            for name in scope)
    print("DOCUMENTARY_EXPANDED_CONTROL_CODEGEN_OK: " + str(len(mutations)) +
          " textual mutations rejected; actual head and formation retained; " + str(metadata) +
          " native head metadata-read sites and " + str(schedule_metadata) +
          " native schedule-entry sites remain open; constitutive generation, role opening and deferred callbacks remain open")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_EXPANDED_CONTROL_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
