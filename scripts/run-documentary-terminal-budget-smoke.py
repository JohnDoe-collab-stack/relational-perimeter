#!/usr/bin/env python3
"""Frozen large citation checks through the actual public terminal API.

The independently received current source observation is 44,545 business,
1,425,994 administration and 11,883,467 forwarding layers, giving cost
45,988,723 and exactly44 payload labels. Whole values, identities, readers and
positive Path/Tape checks remain unchanged; this fixture is not a D3 envelope.
"""
import hashlib
from pathlib import Path
import runpy
import types
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
EXPECTED_COST = 45_988_723
CHECK = r'''
def citation (budget : Nat) :=
  match formed with
  | none => false
  | some realized =>
    match ControlDocumentaryExecution.execute 500000 budget initial
        (.quotation ProgramCases.baselineTask) realized with
    | none => false
    | some actual =>
      match retainRun actual with
      | none => false
      | some result =>
        pathCost true result.path 0 == __EXPECTED_COST__ &&
        actual.remaining == budget - __EXPECTED_COST__ &&
        (result.labels.filter isMaster).length == 1 &&
        (result.labels.filter isRestore).length == 1 &&
        (result.labels.filter isPayload).length == 44 &&
        observe result.value .quoted (some 42) (some [1]) 1 1 true &&
        queryProbe result.value.realized 1

def insufficient : Bool :=
  match formed with
  | none => false
  | some realized =>
    (ControlDocumentaryExecution.execute 500000 (__EXPECTED_COST__ - 1) initial
      (.quotation ProgramCases.baselineTask) realized).isNone &&
    (ControlDocumentaryExecution.execute 500000 0 initial
      (.quotation ProgramCases.baselineTask) realized).isNone

def check : Bool := citation __EXPECTED_COST__ && insufficient && citation (__EXPECTED_COST__ + 17)

def run : IO Unit := do
  if !check then throw (IO.userError "Public terminal citation budget mismatch")
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_TERMINAL_BUDGET_SMOKE_DONE\n").toArray⟩
end TerminalBudgetSmoke
def main : IO Unit := TerminalBudgetSmoke.run
'''


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

def client():
    factory = runpy.run_path(str(ROOT / 'scripts/run-documentary-terminal-smoke.py'))
    source = factory['client']().replace('TerminalSmoke', 'TerminalBudgetSmoke')
    source = source[:source.index('def check : Bool :=')]
    source += CHECK.replace('__EXPECTED_COST__', str(EXPECTED_COST))
    names = ('fullTag', 'eventTag', 'isMaster', 'isPayload', 'isRestore', 'observe',
             'wordMatches', 'suffixMatches', 'adminPrefixMatches', 'traceMatches', 'pathCost',
             'retainRun', 'paidExecute', 'terminalExecute', 'initialState', 'initialPast',
             'initialFresh', 'initial', 'initialResult', 'formed', 'probe', 'QueryFixture',
             'queryTag', 'queryFixtures', 'queryProbe', 'retained', 'evidence',
             'citation', 'insufficient', 'check', 'run')
    source += '\n'.join('#print axioms TerminalBudgetSmoke.' + name for name in names)
    source += '\n#print axioms main\n'
    return source


def main():
    source = client().encode('utf-8')
    native = _load_native_helper()
    names = ('TerminalBudgetSmoke.fullTag', 'TerminalBudgetSmoke.eventTag', 'TerminalBudgetSmoke.isMaster', 'TerminalBudgetSmoke.isPayload', 'TerminalBudgetSmoke.isRestore', 'TerminalBudgetSmoke.observe', 'TerminalBudgetSmoke.wordMatches', 'TerminalBudgetSmoke.suffixMatches', 'TerminalBudgetSmoke.adminPrefixMatches', 'TerminalBudgetSmoke.traceMatches', 'TerminalBudgetSmoke.pathCost', 'TerminalBudgetSmoke.retainRun', 'TerminalBudgetSmoke.paidExecute', 'TerminalBudgetSmoke.terminalExecute', 'TerminalBudgetSmoke.initialState', 'TerminalBudgetSmoke.initialPast', 'TerminalBudgetSmoke.initialFresh', 'TerminalBudgetSmoke.initial', 'TerminalBudgetSmoke.initialResult', 'TerminalBudgetSmoke.formed', 'TerminalBudgetSmoke.probe', 'TerminalBudgetSmoke.QueryFixture', 'TerminalBudgetSmoke.queryTag', 'TerminalBudgetSmoke.queryFixtures', 'TerminalBudgetSmoke.queryProbe', 'TerminalBudgetSmoke.retained', 'TerminalBudgetSmoke.evidence', 'TerminalBudgetSmoke.citation', 'TerminalBudgetSmoke.insufficient', 'TerminalBudgetSmoke.check', 'TerminalBudgetSmoke.run', 'main')
    expected = ["'" + name + "' does not depend on any axioms" for name in names]
    result = native.run_native_client(ROOT, source, expected,
        b'DOCUMENTARY_TERMINAL_BUDGET_SMOKE_DONE\n', runtime_timeout=3600)
    print('DOCUMENTARY_TERMINAL_BUDGET_SMOKE_OK: actual public citation; frozen independent '
          f'cost={EXPECTED_COST}; exact, minus one, plus 17 and zero; whole value/origins/readers; '
          'positive Path/Tape catalogue; exact44 payloads; 32 clean audits; fixture is not a D3 envelope; '
          'client_sha256=' + hashlib.sha256(source).hexdigest() + '; native runtime DONE; raw_artifacts=' + result['raw_artifacts'])



if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print('DOCUMENTARY_TERMINAL_BUDGET_SMOKE_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
