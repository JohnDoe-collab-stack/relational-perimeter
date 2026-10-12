#!/usr/bin/env python3
"""Actual public initialization and successors, preserving all semantic fixtures.

Large steps execute once. Fuel variants remain in the independent 140-coupon
suite and a separately frozen large citation. The positive Path and full compact
Tape are checked against the declared catalogue, without source replay or label
flattening. The fixture ceiling is not a D3 envelope or a bootstrap bound.
"""
import hashlib
from pathlib import Path
import runpy
import types
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


PINNED_NATIVE_HELPER_SHA256 = '1d912561c86ed8bcf9697a83fe33a84693c5ddfd70b52800edebc7fd2a5b88ed'


def _load_native_helper():
    path = (ROOT / 'scripts/documentary_native_client.py').resolve()
    source = path.read_bytes()
    if hashlib.sha256(source).hexdigest() != PINNED_NATIVE_HELPER_SHA256:
        raise ValueError('Native helper source differs from the reviewed pin')
    helper = types.ModuleType('_rp_documentary_native_client_from_pinned_source')
    helper.__file__ = str(path)
    exec(compile(source, helper.__file__, 'exec', dont_inherit=True), helper.__dict__)
    return helper
FIXTURE_FINAL_CEILING = 1_000_000_000_000
HELPERS = r'''
universe u

def wordMatches : List Label → List Label → Bool
  | [], [] => true
  | first :: rest, other :: remaining =>
      fullTag first == fullTag other && wordMatches rest remaining
  | _, _ => false

def suffixMatches (business successful : Bool) : ControlRunner.Tape → Bool
  | .word labels =>
      wordMatches labels (if successful then
        if business then [.controlFrame, .controlTrace, .controlWitness, .controlResult]
        else [.controlFrame, .controlWitness, .controlResult]
        else [.controlResult])
  | _ => false

def adminPrefixMatches (event : Control.Event) (forwards : Nat) : ControlRunner.Tape → Bool
  | .word labels => forwards == 0 &&
      wordMatches labels [.controlInspect, ControlRunner.eventLabel event, .controlCall, .controlFrame]
  | .adminBlock other layers => forwards != 0 && forwards == layers &&
      fullTag (ControlRunner.eventLabel event) == fullTag (ControlRunner.eventLabel other)
  | _ => false

def traceMatches (successful : Bool) :
    ControlCompactData.Path → ControlRunner.Tape → Bool
  | .done, .word labels =>
      successful && wordMatches labels [.controlInspect, .controlTrace, .controlWitness, .controlResult]
  | .stop, .word labels =>
      !successful && wordMatches labels [.controlInspect, .controlResult]
  | .business label childPath, .join (.word entryWord) (.join childTape suffix) =>
      if wordMatches entryWord [.controlInspect, label, .controlCall, .controlFrame] &&
          suffixMatches true successful suffix then traceMatches successful childPath childTape else false
  | .administrative event forwards childPath, .join entryTape (.join childTape suffix) =>
      if adminPrefixMatches event forwards entryTape && suffixMatches false successful suffix
      then traceMatches successful childPath childTape else false
  | _, _ => false

def pathCost (successful : Bool) (path : ControlCompactData.Path) (total : Nat) : Nat :=
  match path with
  | .done => total + 4
  | .stop => total + 2
  | .business _ child => pathCost successful child (total + (if successful then 8 else 5))
  | .administrative _ forwards child =>
      pathCost successful child (total + 4 + 3 * forwards + (if successful then 3 else 1))

def retainRun {Value : Type u} {code : Code Label Value} {fuel budget : Nat}
    (actual : ControlCompactExecution.Run code fuel budget) :
    Option (ControlCompactExecution.SourceResult code fuel) :=
  match received : actual.output with
  | none => none
  | some output =>
    if traceMatches true actual.path actual.tape &&
        pathCost true actual.path 0 + actual.remaining == budget then
      some ⟨output, actual.path, actual.tape, received ▸ actual.realized⟩
    else none

def paidExecute {Value : Type u} (fuel : Nat) (code : Code Label Value) :
    Option (ControlCompactExecution.SourceResult code fuel) :=
  (ControlCompactExecution.execute fuel __FIXTURE_CEILING__ code).bind retainRun

def terminalExecute {slots spec} (sourceFuel : Nat)
    (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (instruction : Instruction Cases.context DeductionCases.policy slots spec)
    (realized : ControlFrameExecution.Realized before) :
    Option (ControlCompactExecution.SourceResult
      (ControlDocumentaryExecution.Source before instruction realized) sourceFuel) :=
  (ControlDocumentaryExecution.execute sourceFuel __FIXTURE_CEILING__ before instruction realized).bind retainRun
'''
PROBE = r'''
def probe {slots spec}
    (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (instruction : Instruction Cases.context DeductionCases.policy slots spec)
    (realized : ControlFrameExecution.Realized before)
    (event : Program.Event) (value : Option Int) (origins : Option (List Nat))
    (depth size heads : Nat) (success : Bool) :
    Option (ControlFrameExecution.Produced before instruction) :=
  match terminalExecute 500000 before instruction realized with
  | none => none
  | some actual =>
    if (actual.labels.filter isMaster).length != heads ||
        (actual.labels.filter isRestore).length != 1 ||
        (actual.labels.filter isPayload).length < 2 ||
        !(observe actual.value event value origins depth size success) then none
    else some actual.value
'''
INITIAL = r'''
def initialState := EndogenousDecomposition.initialThreadedConstitutiveStateFromInitialization
  (EndogenousDecomposition.initializeConstitutiveHistory 0)

def initialPast := EndogenousDecomposition.initialOperationalPrefix 0

theorem initialFresh : EndogenousDecomposition.ThreadedStateFreshForNext initialState :=
  EndogenousDecomposition.initialThreadedConstitutiveStateFromInitialization_fresh
  (EndogenousDecomposition.initializeConstitutiveHistory 0)

def initial : FrameData Cases.sources Cases.contract DeductionCases.policy [] :=
  ControlDocumentaryExecution.initial initialState initialPast initialFresh
    Cases.sources Cases.contract DeductionCases.policy

def initialResult (budget : Nat) :=
  ControlDocumentaryExecution.initialExecute 1000 budget initialState initialPast initialFresh
    Cases.sources Cases.contract DeductionCases.policy

def formed : Option (ControlFrameExecution.Realized initial) :=
  match ControlCompactExecution.sourceExecute 1000
      (ControlDocumentaryExecution.initialCode initialState initialPast initialFresh
        Cases.sources Cases.contract DeductionCases.policy) with
  | none => none
  | some source =>
    let cost := pathCost true source.path 0
    match initialResult cost, initialResult (cost - 1), initialResult (cost + 17), initialResult 0 with
    | some exact, none, some more, none =>
      if !traceMatches true exact.path exact.tape || !traceMatches true more.path more.tape ||
          pathCost true exact.path 0 != cost || pathCost true more.path 0 != cost ||
          exact.remaining != 0 || more.remaining != 17 ||
          exact.output.map (fun result => result.labels.map fullTag) != some (source.labels.map fullTag) ||
          more.output.map (fun result => result.labels.map fullTag) != some (source.labels.map fullTag) then none
      else match exact.output with
        | none => none
        | some result => some (by
          obtain ⟨⟨frame, same⟩, realized⟩ := result.value
          cases same
          exact realized)
    | _, _, _, _ => none
'''


def client():
    factory = runpy.run_path(str(ROOT / 'scripts/run-documentary-frame-execution-smoke.py'))
    source = factory['client']().replace('FrameExecutionSmoke', 'TerminalSmoke')
    source = source.replace('DOCUMENTARY_FRAME_EXECUTION_SMOKE_DONE', 'DOCUMENTARY_TERMINAL_SMOKE_DONE')
    source = source.replace('import Tests.LocalAlignment.DocumentaryControlFrameExecution',
                            'import Tests.LocalAlignment.DocumentaryControlDocumentaryExecution')
    source = source.replace('def eventTag', HELPERS.replace('__FIXTURE_CEILING__', str(FIXTURE_FINAL_CEILING)) +
                            '\ndef eventTag', 1)
    start = source.index('def probe {slots spec}')
    end = source.index('structure QueryFixture', start)
    source = source[:start] + PROBE + '\n' + INITIAL + '\n' + source[end:]
    # Only non-documentary reader/reference/evidence calls use the generic paid
    # API. The large step itself calls the public documentary entry directly.
    source = source.replace('ControlCompactExecution.sourceExecute', 'paidExecute')
    # The small initial source oracle is an explicitly external test observation.
    source = source.replace('match paidExecute 1000\n      (ControlDocumentaryExecution.initialCode',
                            'match ControlCompactExecution.sourceExecute 1000\n      (ControlDocumentaryExecution.initialCode')
    source = source.replace('#print axioms TerminalSmoke.initialCorrect\n', '')
    source += '\n'.join('#print axioms TerminalSmoke.' + name for name in (
        'wordMatches', 'suffixMatches', 'adminPrefixMatches', 'traceMatches', 'pathCost',
        'retainRun', 'paidExecute', 'terminalExecute', 'initialState', 'initialPast',
        'initialFresh', 'initialResult')) + '\n'
    return source


def main():
    source = client().encode('utf-8')
    native = _load_native_helper()
    names = ('TerminalSmoke.fullTag', 'TerminalSmoke.eventTag', 'TerminalSmoke.isMaster', 'TerminalSmoke.isPayload', 'TerminalSmoke.isRestore', 'TerminalSmoke.observe', 'TerminalSmoke.probe', 'TerminalSmoke.initial', 'TerminalSmoke.formed', 'TerminalSmoke.QueryFixture', 'TerminalSmoke.queryTag', 'TerminalSmoke.queryFixtures', 'TerminalSmoke.queryProbe', 'TerminalSmoke.retained', 'TerminalSmoke.evidence', 'TerminalSmoke.check', 'TerminalSmoke.run', 'main', 'ConstitutiveSearch.Agent.Local.Documentary.ControlCompactExecution.source_exact', 'TerminalSmoke.wordMatches', 'TerminalSmoke.suffixMatches', 'TerminalSmoke.adminPrefixMatches', 'TerminalSmoke.traceMatches', 'TerminalSmoke.pathCost', 'TerminalSmoke.retainRun', 'TerminalSmoke.paidExecute', 'TerminalSmoke.terminalExecute', 'TerminalSmoke.initialState', 'TerminalSmoke.initialPast', 'TerminalSmoke.initialFresh', 'TerminalSmoke.initialResult')
    expected = ["'" + name + "' does not depend on any axioms" for name in names]
    result = native.run_native_client(ROOT, source, expected,
                                      b'DOCUMENTARY_TERMINAL_SMOKE_DONE\n', runtime_timeout=7200)
    print('DOCUMENTARY_TERMINAL_SMOKE_OK: public initialExecute and execute; '
          'five actual successive steps and all refused/missing/wrong-demand/recovery branches; '
          'same retained readers, references and source evidence tree; '
          'every positive Path event/forward and whole compact Tape checked against catalogue; '
          'initial exact/short/surplus/zero and independent 140-coupon fuel variants; '
          'each large fixture executed once; 31 clean audits; '
          'fixture ceiling and path observations are not D3 bounds; client_sha256=' + hashlib.sha256(source).hexdigest() +
          '; native runtime DONE; raw_artifacts=' + result['raw_artifacts'])


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print('DOCUMENTARY_TERMINAL_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
