#!/usr/bin/env python3
"""Named checks of actual master packets and assemblies; full D2 stays open.

Mutation fixtures modify checker inputs, not compiled executions. Native head
argument/value reads are rejected; other executable indices and deferred callbacks remain open. Generation and role formation are
expanded; the bootstrap must not call the generator or the source evaluator.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_"
MODULES = ("ControlConstitutiveResources_", "ControlMasterData_", "ControlMasterGeneration_",
           "ControlConstitutiveGeneration_", "ControlGenerationBudget_", "ControlRoleFormation_",
           "ControlMasterCandidates_", "ControlMasterDiscovery_", "ControlMasterHead_",
           "ControlMeasuredComparison_", "ControlMeasuredTransformation_",
           "ControlMeasuredState_", "ControlMeasuredDiscovery_",
           "ControlMeasuredSchedule_", "ControlScheduleCache_", "ControlMeasuredTransport_", "ControlSequentialStage_",
           "ControlNextState_", "ControlMasterApplication_", "ControlProducedImage_", "ControlMasterDecomposition_",
           "ControlProvenance_", "ControlFrontierSyntax_", "ControlFrontierOpening_",
           "ControlQuotationAssembly_", "ControlMissingAssembly_",
           "ControlDeferred_", "ControlAdministration_", "ControlMaster_expanded", "ControlStep_expanded")
FORBIDDEN = (r"\b\w*(?:EndogenousDecomposition_VariableMaster_(?:masterHead|nextCursor|openFrontier)|"
             r"EndogenousDecomposition_(?:runThreadedNextDiscovery|measuredGeneratedExtractionFromSeed|"
             r"exploreRecordedCandidates|tryMeasuredCandidate|searchMeasuredRelation(?:FromData)?|"
             r"compareUnary|compareMeasured(?:List|Literal|Cnf|Bool|Decision|History)|"
             r"flipMeasured(?:Literal|Clause|Cnf|Decision|History)|checkMeasuredFreshness|"
             r"containsMeasuredLiteral|constructMeasured(?:Residual|Child|DecoyClause|Formula|OperationalRoot)|"
             r"childFromMeasuredResidual)|"
             r"EndogenousDecomposition_(?:buildFromExecutedDiscovery|prefixLocalOperationalProducer|"
             r"generateCanonicalStageFromSource|relationalConstitutiveRoleStage|roleConstitutedOccurrenceAt|"
             r"roleOpeningOccurrenceAt|roleConstitutionEvidence|"
             r"buildThreadedConstitutiveStage|executeSequentialStageFromActiveRecorded|realizeNextOperationalState|"
             r"validateStoredSchedule|executeStoredSchedule|applyDiscoveryExecution|applyMeasuredTransportCode|"
             r"executedStageDecomposition|executedRoleReductionLicense|producedRoleOutputRegime|producedRoleOutput|"
             r"validationFromMeasuredSearch|executionFromMeasuredSearch)|"
             r"Extensive_(?:deduplicate|containsWith|ProducedOutputImage_(?:regime|imageRegime))|"
             r"SAT_(?:runCandidateExtraction|extractClauseCandidateRun|extractCnfCandidateRun)|"
             r"SAT_(?:generatedStructuralSplit|structuralContextSplit|DiscoverySchedule_entry)|"
             r"StrongPerimetralTurning_(?:generate|canonicalTarget|canonicalFreeLayer|generatedStepOfFreeK|"
             r"BoundaryDifferenceCode_inheritedClosureObstruction|successorCompatibleExplicitation)|"
             r"Documentary_Program_(?:quotationStep|missingStep)|Documentary_Deduction_quote)"
             r"(?:___redArg)?\s*\(")
NATIVE_METADATA = r"\b\w*Resources_(?:Producer_arguments|Support_read|read)(?:___redArg)?\s*\("
OPENING_NATIVE = (r"\b\w*SAT_(?:GeneratedStructuralBranchContext_child|structuralChildContext|"
                  r"structuralDecisionsAvoidCheck|branchResidual|branchWeakening|branchSyntax|"
                  r"branchReduction|Clause_containsLiteral)"
                  r"(?:___redArg)?\s*\(")

def make_check(functions, select):
    scope = [name for name in functions if any(BASE + module in name for module in MODULES)
             and not name.endswith("___boxed") and "closed__" not in name]
    if not scope:
        raise ValueError("Expanded compiled functions missing")
    engines = ()
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
    cached_packet = select(functions, BASE + "ControlConstitutiveResources_cachedCode___redArg___lam__0")
    cached_values = select(functions, BASE + "ControlConstitutiveResources_cachedCode___redArg___lam__2")
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
        ("ControlRoleFormation_endpointsFromThreaded___redArg", ((0, "source"), (1, "target"))),
        ("ControlRoleFormation_roleFromOpening___redArg", ((0, "opening"), (1, "relation"),
            (2, "sourceContinuation"), (3, "outputContinuation"))),
        ("ControlRoleFormation_realizationFromState___redArg", ((0, "state"),)),
        ("ControlRoleFormation_identityFromRealization___redArg", ((0, "realized"),)),
        ("ControlConstitutiveGeneration_layerCode___redArg___lam__1", ((0, "successor"),
            (1, "obstruction"), (2, "provenance"))),
        ("ControlConstitutiveGeneration_targetCode___redArg___lam__1", ((3, "layer"),)),
        ("ControlConstitutiveGeneration_lawsCode___redArg___lam__0", ((0, "compatible"), (1, "layer"),
            (2, "closure"), (3, "continuation"), (4, "fresh"))),
        ("ControlConstitutiveGeneration_canonicalFromProduced___redArg", ((0, "fst"), (1, "snd"))),
        ("ControlProducedImage_fromFrontier___redArg", ((1, "frontier"),)))
    retained_fields = [(select(functions, BASE + owner), fields) for owner, fields in retained_fields]
    opening_fields = (
        ("ControlFrontierOpening_fromFresh___redArg", ((0, "left"), (0, "right"),
            (1, "frontier"), (1, "preservation"))),
        ("ControlFrontierOpening_childCode___redArg___lam__0", ((0, "context"), (1, "generated"))),
        ("ControlFrontierOpening_splitCode___redArg___lam__1", ((0, "split"), (1, "merge"))),
        ("ControlFrontierOpening_prependCode___redArg___lam__2", ((0, "forward"), (1, "backward"))),
        ("ControlFrontierOpening_transCode___redArg___lam__2", ((0, "forward"), (1, "backward"))),
        ("ControlFrontierOpening_identityCode___lam__1", ((0, "forward"), (1, "forward"))))
    opening_fields = [(select(functions, BASE + owner), fields) for owner, fields in opening_fields]
    opening_code = select(functions, BASE + "ControlFrontierOpening_code___redArg")
    expanded_opening_owners = [name for name in scope if BASE + "ControlMaster_expandedSearchCode" in name]
    opening_context = select(functions, BASE + "ControlFrontierOpening_childCode___redArg___lam__2")
    residual_packets = [(select(functions, BASE + "ControlFrontierSyntax_residualCode___lam__" + str(index)), tag)
                        for index, tag in ((1, 1), (2, 2))]
    metadata_owners = [name for name in scope if any(BASE + owner in name for owner in
                       ("ControlMasterHead_", "ControlConstitutiveResources_"))]
    opening_owners = [name for name in scope if any(BASE + owner in name for owner in
                      ("ControlFrontierSyntax_", "ControlFrontierOpening_", "ControlMaster_expanded"))]
    paid_kinds = [(select(functions, BASE + "ControlMasterHead_" + kind + "Kind___redArg"),
                   select(functions, BASE + "ControlMasterHead_" + kind + "Kind___redArg___lam__0"))
                  for kind in ("discovery", "application", "decomposition", "assembly", "prefix", "source", "fresh")]

    def check(current):
        for name in opening_owners:
            if re.search(OPENING_NATIVE, current[name]):
                raise ValueError("Native frontier opening helper replayed: " + name)
        for name in metadata_owners:
            if re.search(NATIVE_METADATA, current[name]):
                raise ValueError("Unpaid native producer metadata/value read: " + name)
        for parent, callback in paid_kinds:
            if not re.search(r"= 15;", current[parent]) or not re.search(
                    r"lean_alloc_closure\(\(void\*\)\(" + re.escape(callback) + r"(?:___boxed)?\)", current[parent]):
                raise ValueError("Paid output-kind continuation dropped: " + parent)
        for name in scope:
            if re.search(FORBIDDEN, current[name]):
                raise ValueError("Original whole production or traversal replayed: " + name)
            if BASE + "ControlAdministration_" in name and re.search(
                    r"\b\w*Documentary_Control_execute(?:___redArg)?\s*\(", current[name]):
                raise ValueError("Metered evaluator delegates to the native source evaluator")
            if BASE + "ControlGenerationBudget_" in name and re.search(
                    r"\b\w*(?:ControlConstitutiveGeneration_(?:code|canonicalCode)|"
                    r"Documentary_Control_(?:execute|runCtl))(?:___redArg)?\s*\(", current[name]):
                raise ValueError("Bootstrap executes the generator instead of reading its source")
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
        if not re.search(r"lean_ctor_set\([^,]+, 0, v_computed_\d+_\)", current[cached_values]):
            raise ValueError("Cached formation drops the actual paid value")
        for field, variable in ((0, "args"), (1, "kind")):
            if not re.search(r"lean_ctor_set\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", current[cached_packet]):
                raise ValueError("Cached support drops actual " + variable)
        support = re.search(r"lean_ctor_set\((v_\w+), 0, v_values_\d+_\)", current[cached_packet])
        if not support or not re.search(r"lean_ctor_set\(" + re.escape(support[1]) +
                r", 1, v_formation_\d+_\)", current[cached_packet]) or not re.search(
                r"lean_ctor_set\([^,]+, 2, " + re.escape(support[1]) + r"\)", current[cached_packet]):
            raise ValueError("Cached packet drops its full produced support or formation")
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
        for owner, fields in opening_fields:
            for field, variable in fields:
                if not re.search(r"lean_ctor_set\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", current[owner]):
                    raise ValueError("Frontier packet drops actual " + variable + ": " + owner)
        projected = re.search(r"(v_\w+) = lean_ctor_get\(v_residual_\d+_, 0\)", current[opening_context])
        if not projected or not re.search(r"lean_ctor_set\(v_context_\d+_, 0, " +
                                         re.escape(projected[1]) + r"\)", current[opening_context]):
            raise ValueError("Child context does not consume the actual controlled residual")
        for owner, tag in residual_packets:
            body = current[owner]
            syntax = re.search(r"(v_\w+) = lean_ctor_get\((v_tail_\d+_), 0\)", body)
            weakening = re.search(r"(v_\w+) = lean_ctor_get\((v_tail_\d+_), 1\)", body)
            witness = re.search(r"(v_\w+) = lean_alloc_ctor\(" + str(tag) + r", 4, 0\)", body)
            if (not syntax or not weakening or not witness or syntax[2] != weakening[2] or
                not re.search(r"lean_ctor_set\(" + re.escape(witness[1]) + r", 1, " +
                              re.escape(syntax[1]) + r"\)", body) or
                not re.search(r"lean_ctor_set\(" + re.escape(witness[1]) + r", 3, " +
                              re.escape(weakening[1]) + r"\)", body) or
                len(re.findall(r"lean_ctor_set\([^,]+, 1, " + re.escape(witness[1]) + r"\)", body)) != 2):
                raise ValueError("Residual packet drops its actual syntax/weakening or positive formation: " + owner)
        if sum(len(re.findall(re.escape(opening_code) + r"\s*\(", current[name]))
               for name in expanded_opening_owners) != 1:
            raise ValueError("Expanded search does not consume one controlled opening")

    mutations = [(name, functions[name] + " lp_forbidden_EndogenousDecomposition_VariableMaster_masterHead();")
                 for name in scope]
    mutations.extend((name, functions[name] + " lp_forbidden_Resources_" + reader + "();")
                     for name in metadata_owners for reader in ("Producer_arguments", "Support_read", "read"))
    opening_helpers = ("GeneratedStructuralBranchContext_child", "structuralChildContext",
                       "structuralDecisionsAvoidCheck", "branchResidual", "branchWeakening",
                       "branchSyntax", "branchReduction", "Clause_containsLiteral")
    mutations.extend((name, functions[name] + " lp_forbidden_SAT_" + helper + "();")
                     for name in opening_owners for helper in opening_helpers)
    mutations.extend((name, functions[name] + " lp_forbidden_EndogenousDecomposition_VariableMaster_openFrontier();")
                     for name in opening_owners)
    for parent, callback in paid_kinds:
        mutations += [(parent, functions[parent].replace("= 15;", "= 0;")),
                      (parent, functions[parent].replace(callback, "lp_substituted"))]
    for target, actual, parent, label in boundaries:
        mutations += [(actual, functions[actual] + target + "();"),
                      (parent, functions[parent].replace("= " + str(label) + ";", "= 0;")),
                      (parent, functions[parent].replace(actual, "lp_substituted"))]
    for owner, variable in ((head, "head"), (head, "next"), (formation, "computed")):
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    for owner, variable in ((cached_values, "computed"), (cached_packet, "args"),
                            (cached_packet, "kind"), (cached_packet, "values"), (cached_packet, "formation")):
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    mutations.append((cached_packet, re.sub(r"(lean_ctor_set\([^,]+, 2, )v_\w+(\))",
                                          r"\1v_substituted\2", functions[cached_packet])))
    mutations.append((expanded, functions[expanded] + expanded_head + "();"))
    candidate_owner = next(name for name in candidate_owners if re.search(re.escape(candidate) + r"\s*\(", functions[name]))
    mutations += [(candidate_owner, functions[candidate_owner] + candidate + "();"),
                  (candidate_owner, functions[candidate_owner].replace(candidate, "lp_substituted"))]
    for variable in ("left", "right"):
        mutations.append((endpoints, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[endpoints])))
    for owner, fields in retained_fields:
        for _, variable in fields:
            mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    for owner, fields in opening_fields:
        for _, variable in fields:
            mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    mutations.append((opening_context, re.sub(r"v_residual_\d+_", "v_substituted", functions[opening_context])))
    mutations.append((opening_context, re.sub(r"(lean_ctor_set\(v_context_\d+_, 0, )v_\w+(\))",
                                            r"\1v_substituted\2", functions[opening_context])))
    for owner, tag in residual_packets:
        body = functions[owner]
        for field in (0, 1):
            mutations.append((owner, re.sub(r"(lean_ctor_get\(v_tail_\d+_, )" + str(field) + r"(\))",
                                           r"\g<1>9\2", body)))
        witness = re.search(r"(v_\w+) = lean_alloc_ctor\(" + str(tag) + r", 4, 0\)", body)[1]
        mutations.extend(((owner, body.replace("lean_alloc_ctor(" + str(tag) + ", 4, 0)", "lean_alloc_ctor(9, 4, 0)")),
                          (owner, re.sub(r"(lean_ctor_set\([^,]+, 1, )" + re.escape(witness) + r"(\))",
                                         r"\1v_substituted\2", body))))
    opening_consumer = next(name for name in expanded_opening_owners
                            if re.search(re.escape(opening_code) + r"\s*\(", functions[name]))
    mutations.extend(((opening_consumer, functions[opening_consumer] + opening_code + "();"),
                      (opening_consumer, functions[opening_consumer].replace(opening_code, "lp_substituted"))))
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
    native_attempts += ("generateCanonicalStageFromSource", "relationalConstitutiveRoleStage",
                        "roleConstitutedOccurrenceAt", "roleOpeningOccurrenceAt", "roleConstitutionEvidence")
    mutations.extend((endpoints, functions[endpoints] + " lp_forbidden_EndogenousDecomposition_" + name + "();")
                     for name in native_attempts)
    bootstrap = select(functions, BASE + "ControlGenerationBudget_canonicalBoundCode___redArg")
    mutations += [(bootstrap, functions[bootstrap] + " lp_forbidden_" + BASE +
                   "ControlConstitutiveGeneration_canonicalCode();"),
                  (bootstrap, functions[bootstrap] + " lp_forbidden_Documentary_Control_execute();"),
                  (endpoints, functions[endpoints] + " lp_forbidden_SAT_DiscoverySchedule_entry();")]
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
    metadata = sum(len(re.findall(NATIVE_METADATA,
                                 functions[name])) for name in scope if BASE + "ControlMasterHead_" in name)
    schedule_metadata = sum(len(re.findall(r"\b\w*SAT_DiscoverySchedule_entry(?:___redArg)?\s*\(", functions[name]))
                            for name in scope)
    opening_native_sites = sum(len(re.findall(OPENING_NATIVE, functions[name])) + len(re.findall(
        r"\b\w*EndogenousDecomposition_VariableMaster_openFrontier(?:___redArg)?\s*\(", functions[name]))
        for name in scope if any(BASE + owner in name for owner in
        ("ControlFrontierSyntax_", "ControlFrontierOpening_", "ControlMaster_expanded")))
    print("DOCUMENTARY_EXPANDED_CONTROL_CODEGEN_OK: " + str(len(mutations)) +
          " textual mutations rejected; actual head and formation retained; " + str(metadata) +
          " native head metadata-read sites and " + str(schedule_metadata) +
          " native schedule-entry sites; head argument reads use retained productions; other executable indices and deferred callbacks remain open")
    print("DOCUMENTARY_FRONTIER_OPENING_CODEGEN_OK: " + str(opening_native_sites) +
          " native opening/helper sites in named scope; actual children, positive weakening and preservation retained")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_EXPANDED_CONTROL_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
