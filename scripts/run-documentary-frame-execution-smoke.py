#!/usr/bin/env python3
"""Shared semantic fixtures for actual returned frames, readers and evidence.

Values, source origins, events and query traces are fixed independently. The
public terminal client preserves these fixtures and replaces the diagnostic
source probe with one paid execution of each large step. The command-line entry
delegates to that public regression; there is one qualified execution route.
"""
import hashlib
from pathlib import Path
import re
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r'''
import Tests.LocalAlignment.DocumentaryControlFrameExecution
import Tests.LocalAlignment.DocumentaryControlCompactExecution
import Tests.LocalAlignment.DocumentaryControlInterpreterCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 65536
set_option maxHeartbeats 100000000
namespace FrameExecutionSmoke
open ConstitutiveSearch ConstitutiveSearch.Resources ConstitutiveSearch.SAT
open ConstitutiveSearch.Agent.Local.Documentary
open Program Snapshot Control ControlBindings ControlMasterData ControlDeferred

__FULL_TAG__
def eventTag : Program.Event → Nat
  | .quoted => 0 | .derived => 1 | .refused => 2 | .missing => 3

def isMaster : Label → Bool | .masterHeadPacket => true | _ => false
def isPayload : Label → Bool | .executionPayload => true | _ => false
def isRestore : Label → Bool | .frameRestore => true | _ => false

def observe {slots spec}
    {before : FrameData Cases.sources Cases.contract DeductionCases.policy slots}
    {instruction : Instruction Cases.context DeductionCases.policy slots spec}
    (produced : ControlFrameExecution.Produced before instruction)
    (event : Program.Event) (value : Option Int) (origins : Option (List Nat))
    (depth size : Nat) (success : Bool) : Bool :=
  let table := produced.next.1
  let found := table.bindings.read (.here : Ref (spec :: slots) spec)
  eventTag produced.step.1.event == eventTag event &&
    ProgramCases.bindingValue table.store found == value &&
    found.map (fun occurrence => occurrence.1.origins) == origins &&
    table.dossier.cursor.depth == depth && table.store.1.length == size &&
    Program.succeeded table.restore == success

def probe {slots spec}
    (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (instruction : Instruction Cases.context DeductionCases.policy slots spec)
    (realized : ControlFrameExecution.Realized before)
    (event : Program.Event) (value : Option Int) (origins : Option (List Nat))
    (depth size heads : Nat) (success : Bool) :
    Option (ControlFrameExecution.Produced before instruction) :=
  let code := ControlFrameExecution.code before instruction realized
  match execute 500000 code with
  | none => none
  | some actual =>
    let fuel := actual.labels.length
    match execute fuel code, execute (fuel - 1) code, execute (fuel + 17) code,
        execute 0 code with
    | some exact, none, some more, none =>
      if actual.labels.map fullTag != exact.labels.map fullTag ||
          actual.labels.map fullTag != more.labels.map fullTag ||
          (actual.labels.filter isMaster).length != heads ||
          (actual.labels.filter isRestore).length != 1 ||
          (actual.labels.filter isPayload).length < 2 ||
          !(observe actual.value event value origins depth size success) ||
          !(observe exact.value event value origins depth size success) ||
          !(observe more.value event value origins depth size success) then none
      else some actual.value
    | _, _, _, _ => none

def initial : FrameData Cases.sources Cases.contract DeductionCases.policy [] :=
  Snapshot.frame ProgramCases.start
theorem initialCorrect : AssignmentCapture.Correct initial.dossier.cursor := by rfl

def formed : Option (ControlFrameExecution.Realized initial) :=
  let code := ControlFrameExecution.formCode initial initialCorrect .empty
  match execute 1000 code with
  | none => none
  | some actual =>
    let fuel := actual.labels.length
    match execute fuel code, execute (fuel - 1) code, execute (fuel + 17) code with
    | some exact, none, some more =>
      if actual.labels.map fullTag == exact.labels.map fullTag &&
          actual.labels.map fullTag == more.labels.map fullTag then some actual.value
      else none
    | _, _, _ => none

structure QueryFixture where
  stage : Nat
  query : Var
  bit : Bool
  nodes : Nat
  steps : Nat
  labels : List Nat

def queryTag : Label → Nat
  | .assignmentQueryCell => 0 | .assignmentQueryReturn => 1
  | .naturalComparison => 2 | .masterConstructionReturn => 3
  | .integerNaturalCell => 4 | .integerNaturalReturn => 5
  | .masterWorkPacket => 6 | _ => 999

__QUERY_FIXTURES__

def queryProbe {slots}
    {frame : FrameData Cases.sources Cases.contract DeductionCases.policy slots}
    (realized : ControlFrameExecution.Realized frame) (stage : Nat) : Bool :=
  (queryFixtures.filter (fun fixture => fixture.stage == stage)).all (fun fixture =>
    let code := realized.masterReader.queryCode fixture.query
    let fuel := fixture.labels.length
    match execute fuel code, execute (fuel - 1) code, execute (fuel + 17) code with
    | some actual, none, some more =>
      actual.labels.map queryTag == fixture.labels && more.labels.map queryTag == fixture.labels &&
      actual.value.1.value == fixture.bit && more.value.1.value == fixture.bit &&
      actual.value.1.work.nodes == fixture.nodes && more.value.1.work.nodes == fixture.nodes &&
      actual.value.1.work.labelSteps == fixture.steps && more.value.1.work.labelSteps == fixture.steps
    | _, _, _ => false)

def retained {slots spec}
    (frame : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (slot : Ref slots spec) (position : Nat) (value : Int) (origins : List Nat) : Bool :=
  let found := frame.bindings.read slot
  ProgramCases.bindingPosition frame.store found == some position &&
    ProgramCases.bindingValue frame.store found == some value &&
    found.map (fun occurrence => occurrence.1.origins) == some origins

def evidence {slots spec}
    (frame : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (realized : ControlFrameExecution.Realized frame)
    (slot : Ref slots spec) (origins : List Nat) : Bool :=
  match frame.bindings.read slot with
  | none => false
  | some occurrence =>
    let code := recipeReader realized.knowledgeRecipe occurrence.2
    match execute 100000 code with
    | none => false
    | some actual =>
      let fuel := actual.labels.length
      match execute fuel code, execute (fuel - 1) code, execute (fuel + 17) code with
      | some exact, none, some more =>
        actual.labels.map fullTag == exact.labels.map fullTag &&
          actual.labels.map fullTag == more.labels.map fullTag &&
          actual.value.1.sources.map (fun output => output.item.position) == origins &&
          exact.value.1.sources.map (fun output => output.item.position) == origins &&
          more.value.1.sources.map (fun output => output.item.position) == origins
      | _, _, _ => false

def check : Bool :=
  match formed with
  | none => false
  | some initialRealized =>
    match probe initial (.quotation ProgramCases.baselineTask) initialRealized
        .quoted (some 42) (some [1]) 1 1 1 true with
    | none => false
    | some first =>
      if !queryProbe first.realized 1 then false
      else match probe first.next.1 (.quotation ProgramCases.revisedTask) first.realized
          .quoted (some 43) (some [2]) 2 2 1 true with
      | none => false
      | some second =>
        if !queryProbe second.realized 2 then false
        else
          let difference := probe second.next.1
            (.conclusion DeductionCases.differenceRequest (.prior .here) .here DeductionCases.deltaDemand)
            second.realized .derived (some 1) (some [1, 2]) 2 3 0 true
          let forbidden := probe second.next.1
            (.conclusion DeductionCases.duplicateRequest (.prior .here) .here DeductionCases.forbiddenDemand)
            second.realized .refused none none 2 2 0 false
          let wrong := probe second.next.1
            (.conclusion DeductionCases.differenceRequest (.prior .here) .here ProgramCases.wrongDemand)
            second.realized .derived (some 1) (some [1, 2]) 2 3 0 false
          let blocked := probe initial
            (.quotation ⟨Cases.pinnedDemand, Cases.privateOrigin, Cases.publicOrigin⟩)
            initialRealized .refused none none 1 0 1 false
          match difference, forbidden, wrong, blocked with
          | some delta, some refused, some wrongOutput, some sourceBlocked =>
            let leftMissing := probe refused.next.1
              (.conclusion DeductionCases.sumRequest .here .here DeductionCases.sumDemand)
              refused.realized .missing none none 2 2 0 false
            let rightMissing := probe refused.next.1
              (.conclusion DeductionCases.sumRequest (.prior .here) .here DeductionCases.sumDemand)
              refused.realized .missing none none 2 2 0 false
            let continued := probe delta.next.1 (.quotation ProgramCases.baselineTask)
              delta.realized .quoted (some 42) (some [1]) 3 4 1 true
            let wrongDownstream := probe wrongOutput.next.1
              (.conclusion DeductionCases.sumRequest .here .here ProgramCases.downstreamDemand)
              wrongOutput.realized .derived (some 2) (some [1, 2, 1, 2]) 2 4 0 false
            let recovery := probe sourceBlocked.next.1 (.quotation ProgramCases.baselineTask)
              sourceBlocked.realized .quoted (some 42) (some [1]) 2 1 1 false
            match leftMissing, rightMissing, continued, wrongDownstream, recovery with
            | some left, some right, some fourth, some wrongFinal, some recovered =>
              if !queryProbe delta.realized 2 || !queryProbe refused.realized 2 ||
                  !queryProbe left.realized 2 || !queryProbe right.realized 2 ||
                  !queryProbe fourth.realized 3 || !queryProbe wrongFinal.realized 2 ||
                  !queryProbe recovered.realized 2 then false
              else match probe fourth.next.1
                  (.conclusion DeductionCases.sumRequest (.prior .here) (.prior .here) DeductionCases.sumDemand)
                  fourth.realized .derived (some 2) (some [1, 2, 1, 2]) 3 5 0 true with
              | none => false
              | some final =>
                queryProbe final.realized 3 &&
                retained final.next.1 .here 0 2 [1, 2, 1, 2] &&
                retained final.next.1 (.prior .here) 1 42 [1] &&
                retained final.next.1 (.prior (.prior .here)) 2 1 [1, 2] &&
                retained final.next.1 (.prior (.prior (.prior .here))) 3 43 [2] &&
                retained final.next.1 (.prior (.prior (.prior (.prior .here)))) 4 42 [1] &&
                evidence final.next.1 final.realized .here [1, 2, 1, 2]
            | _, _, _, _, _ => false
          | _, _, _, _ => false

def run : IO Unit := do
  if queryFixtures.length != 12 || !check then
    throw (IO.userError "Actual frame execution mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_FRAME_EXECUTION_SMOKE_DONE\n").toArray⟩
end FrameExecutionSmoke
def main : IO Unit := FrameExecutionSmoke.run
__AUDITS__
'''


def client():
    model = runpy.run_path(str(ROOT / 'scripts/run-documentary-measured-reader-smoke.py'))
    rows = []
    for stage, recipe in enumerate(((10,), (12, 10), (14, 12, 10)), start=1):
        for query in (0, 10, 12, 14):
            bit, nodes, steps, trace = model['golden'](recipe, query)
            labels = ', '.join(map(str, trace))
            rows.append(f'  ⟨{stage}, {query}, {str(bit).lower()}, {nodes}, {steps}, [{labels}]⟩')
    labels_source = (ROOT / 'Tests/LocalAlignment/DocumentaryControlBindings.lean').read_text(encoding='utf-8')
    enumeration = labels_source.split('inductive Label where', 1)[1].split('\nvariable ', 1)[0]
    names = re.findall(r'^\s*\|\s*(\w+)\s*$', enumeration, re.M)
    full_tag = 'def fullTag : Label → Nat\n' + '\n'.join(
        f'  | .{name} => {index}' for index, name in enumerate(names))
    audits = '\n'.join('#print axioms FrameExecutionSmoke.' + name for name in (
        'fullTag', 'eventTag', 'isMaster', 'isPayload', 'isRestore', 'observe', 'probe',
        'initial', 'initialCorrect', 'formed', 'QueryFixture', 'queryTag', 'queryFixtures',
        'queryProbe', 'retained', 'evidence', 'check', 'run')) + '\n#print axioms main\n'
    audits += '#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact\n'
    return (re.sub(r'\bexecute\b', 'ControlCompactExecution.sourceExecute', CLIENT).replace('__FULL_TAG__', full_tag)
            .replace('__QUERY_FIXTURES__', 'def queryFixtures : List QueryFixture := [\n' + ',\n'.join(rows) + ']')
            .replace('__AUDITS__', audits))


def main():
    runpy.run_path(str(ROOT / 'scripts/run-documentary-terminal-smoke.py'))['main']()


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print('DOCUMENTARY_FRAME_EXECUTION_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
