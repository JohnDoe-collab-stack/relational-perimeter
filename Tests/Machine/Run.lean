import Tests.Machine.DirectMachine

/-! Development smoke demonstration only. It measures no total cost. -/
namespace ConstitutiveSearch.DirectMachine.Demo
open EndogenousDecomposition

def requests : List Request := [.sample, .tick, .sample, .tick, .sample, .tick, .sample]

def bitText (value : Bool) : String := if value then "true" else "false"

def eventText : Event → String
  | .produced bit => if bit then "produced true" else "produced false"
  | .sampled bit => if bit then "sampled true" else "sampled false"

/-- Use the constructive raw output path instead of standard println/append. -/
def line (text : String) : IO Unit := do
  IO.print text
  IO.print "\n"

def showEvents : List Event → IO Unit
  | [] => pure ()
  | head :: rest => do
      line (eventText head)
      showEvents rest

def runChannel (master : UnifiedMaster.Instance 0) (query : Nat) : IO Unit := do
  match Agent.receive [query] with
  | none => throw (IO.userError "nonempty received scope was rejected")
  | some requirement =>
      match connect requirement query with
      | none => throw (IO.userError "received channel was rejected")
      | some channel =>
          let booted := bootMaster channel master
          let savedPort := booted.1.wire
          let executed := execute channel booted.1 requests
          line "query"
          line (Nat.repr query)
          line (eventText booted.2)
          showEvents executed.2
          line "initial/final depth"
          line (Nat.repr booted.1.live.depth)
          line (Nat.repr executed.1.live.depth)
          line "saved/current port"
          line (bitText savedPort.read)
          line (bitText executed.1.wire.read)

def main : IO Unit := do
  -- Share the actual master value across the channel demonstrations.
  let master := UnifiedMaster.publicInstance 0
  runChannel master 0
  runChannel master 2
  runChannel master 5
  runChannel master 7

end ConstitutiveSearch.DirectMachine.Demo
def directMachineDemo : IO Unit := ConstitutiveSearch.DirectMachine.Demo.main
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.DirectMachine.Demo.requests
#print axioms ConstitutiveSearch.DirectMachine.Demo.bitText
#print axioms ConstitutiveSearch.DirectMachine.Demo.eventText
#print axioms ConstitutiveSearch.DirectMachine.Demo.line
#print axioms ConstitutiveSearch.DirectMachine.Demo.showEvents
#print axioms ConstitutiveSearch.DirectMachine.Demo.runChannel
#print axioms ConstitutiveSearch.DirectMachine.Demo.main
#print axioms directMachineDemo
/- AXIOM_AUDIT_END -/
