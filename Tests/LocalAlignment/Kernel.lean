import Tests.LocalAlignment.ModelLoop

/-! Executable ASCII-line transport; the proposer supplies data, never authorization.
Byte-based parsing and output avoid the axioms of the standard JSON/string
iterator libraries. Receipts read the same actual production as the next state. -/
set_option genInjectivity false
namespace LocalAlignmentKernel
open ConstitutiveSearch.Agent ConstitutiveSearch.Agent.Local
open ConstitutiveSearch.Resources ConstitutiveSearch.EndogenousDecomposition

abbrev Bytes := List UInt8
def bytes (text : String) : Bytes := text.toUTF8.data.toList
def number (value : Nat) : Bytes := bytes (Nat.repr value)
def boolean (value : Bool) : Bytes := if value then bytes "true" else bytes "false"

def tokenize : Bytes → Bytes → List Bytes → List Bytes
  | [], current, prior => (if current.isEmpty then prior else current.reverse :: prior).reverse
  | head :: tail, current, prior =>
      if head.toNat == 32 || head.toNat == 10 || head.toNat == 13 then
        tokenize tail [] (if current.isEmpty then prior else current.reverse :: prior)
      else tokenize tail (head :: current) prior

def digits : Bytes → Nat → Option Nat
  | [], value => some value
  | head :: tail, value =>
      if 48 ≤ head.toNat && head.toNat ≤ 57 then digits tail (10 * value + head.toNat - 48)
      else none

def natural (token : Bytes) (limit : Nat) : Option Nat :=
  if token.isEmpty then none else
    (digits token 0).bind (fun value => if value ≤ limit then some value else none)

def bit : Bytes → Option Bool
  | [] => none
  | head :: rest => match rest with
      | [] => if head.toNat == 48 then some false else if head.toNat == 49 then some true else none
      | _ :: _ => none

def exactlyOne : List Bytes → Option Bytes
  | [] => none
  | head :: tail => if tail.isEmpty then some head else none

def exactlyTwo : List Bytes → Option (Bytes × Bytes)
  | [] => none
  | head :: tail => (exactlyOne tail).map (fun next => (head, next))

def exactlyThree : List Bytes → Option (Bytes × Bytes × Bytes)
  | [] => none
  | head :: tail => (exactlyTwo tail).map (fun next => (head, next))

def parseRequest (memory : Memory) : List Bytes → Option Request
  | [] => none
  | op :: args =>
      if op == bytes "advance" then do
        let count ← exactlyOne args
        let steps ← natural count 16
        if memory.register.length + steps ≤ 128 then some (.advance steps) else none
      else if op == bytes "inspect" || op == bytes "obtain" then do
        let (handle, var) ← exactlyTwo args
        let handle ← natural handle 127
        let var ← natural var 256
        if op == bytes "inspect" then some (.inspect handle var) else some (.obtain handle var)
      else if op == bytes "propose" then do
        let (handle, var, value) ← exactlyThree args
        let handle ← natural handle 127
        let var ← natural var 256
        let value ← bit value
        some (.propose handle var value)
      else none

def decode (memory : Memory) (raw : String) : Option Request :=
  if raw.utf8ByteSize > 65536 then none else parseRequest memory (tokenize (bytes raw) [] [])

def refusalBytes : Refusal → Bytes
  | .outsideScope => bytes "\"outside_scope\""
  | .missingHandle => bytes "\"missing_handle\""
  | .incorrectValue => bytes "\"incorrect_value\""

def messageBytes : Message → Bytes
  | .advanced count => bytes "{\"kind\":\"advanced\",\"steps\":" ++ number count ++ bytes "}"
  | .answer handle var value => bytes "{\"kind\":\"answer\",\"handle\":" ++ number handle ++
      bytes ",\"var\":" ++ number var ++ bytes ",\"value\":" ++ boolean value ++ bytes "}"
  | .refused handle var reason => bytes "{\"kind\":\"refused\",\"handle\":" ++ number handle ++
      bytes ",\"var\":" ++ number var ++ bytes ",\"reason\":" ++ refusalBytes reason ++ bytes "}"

def originBytes {root context continuation} : TargetOrigin root context continuation → Bytes
  | .normalized _ => bytes "{\"kind\":\"executed_normalization\"}"
  | .resumed production => bytes "{\"kind\":\"executed_continuation\",\"next_depth\":" ++
      number production.next.depth ++ bytes "}"

def responseBytes {requirement register handle var candidate message}
    (evidence : ResponseEvidence requirement register handle var candidate message) : Bytes :=
  match evidence with
  | .answer _ authorization _ => bytes "{\"kind\":\"authorized_occurrence\",\"permission_position\":" ++
      number authorization.permission.position ++ bytes ",\"occurrence_position\":" ++
      number authorization.occurrence.2.position ++ bytes ",\"origin\":" ++
      originBytes authorization.occurrence.1.origin ++ bytes "}"
  | .outside _ => bytes "{\"kind\":\"absent_permission\"}"
  | .missing permission _ => bytes "{\"kind\":\"absent_occurrence\",\"permission_position\":" ++
      number permission.position ++ bytes "}"
  | .incorrect permission occurrence _ _ _ _ => bytes "{\"kind\":\"unequal_candidate\",\"permission_position\":" ++
      number permission.position ++ bytes ",\"occurrence_position\":" ++ number occurrence.2.position ++ bytes "}"

def evidenceBytes (memory : Memory) (request : Request) (result : Memory × Event)
    (evidence : RequestEvidence memory request result) : Bytes :=
  match request with
  | .advance count => bytes "{\"kind\":\"executed_advance\",\"steps\":" ++ number count ++ bytes "}"
  | .inspect _ _ => responseBytes evidence
  | .obtain _ _ => responseBytes evidence
  | .propose _ _ _ => responseBytes evidence

def arrayBytes : List Bytes → Bytes
  | [] => bytes "[]"
  | head :: tail => bytes "[" ++ head ++ tail.foldr (fun item rest => bytes "," ++ item ++ rest) (bytes "]")

def productionBytes (event : LiveContinuation.Event) : Bytes :=
  bytes "{\"input_depth\":" ++ number event.1.depth ++ bytes ",\"output_depth\":" ++ number event.2.next.depth ++
    bytes ",\"input_seed\":" ++ number event.1.state.searchSeed ++ bytes ",\"output_seed\":" ++
    number event.2.next.state.searchSeed ++ bytes ",\"input_provenance\":" ++
    arrayBytes (event.1.state.provenance.map number) ++ bytes ",\"output_provenance\":" ++
    arrayBytes (event.2.next.state.provenance.map number) ++ bytes "}"

def receiptBytes (memory : Memory) : {proposal : Option Request} → {result : Memory × Option Event} →
    DispatchEvidence memory proposal result → Bytes
  | _, _, .rejected => bytes "{\"kind\":\"protocol_refusal\",\"register_before\":" ++
      number memory.register.length ++ bytes ",\"register_after\":" ++ number memory.register.length ++ bytes "}"
  | _, _, .executed request result evidence => bytes "{\"kind\":\"executed\",\"register_before\":" ++
      number memory.register.length ++ bytes ",\"register_after\":" ++ number result.1.register.length ++
      bytes ",\"message\":" ++ messageBytes result.2.message ++ bytes ",\"evidence\":" ++
      evidenceBytes memory request result evidence ++ bytes ",\"productions\":" ++
      arrayBytes (result.2.productions.map productionBytes) ++ bytes "}"

def observationBytes (memory : Memory) : Bytes :=
  bytes "{\"scope\":" ++ arrayBytes (memory.requirement.realizedScope.map number) ++
    bytes ",\"available\":" ++ number memory.register.length ++ bytes "}"

def process (memory : Memory) (raw : String) : Memory × Bytes :=
  let proposal := decode memory raw
  let produced := dispatchCertified memory proposal
  (produced.1.1, bytes "{\"receipt\":" ++ receiptBytes memory produced.2 ++
    bytes ",\"observation\":" ++ observationBytes produced.1.1 ++ bytes "}")

theorem process_requirement (memory : Memory) (raw : String) :
    (process memory raw).1.requirement = memory.requirement :=
  dispatch_requirement memory (decode memory raw)

theorem decode_failure_no_effect (memory : Memory) (raw : String)
    (rejected : decode memory raw = none) : (process memory raw).1 = memory := by
  unfold process
  rw [rejected]
  rfl

def processLines : Memory → List String → Memory × List Bytes
  | memory, [] => (memory, [])
  | memory, raw :: rest =>
      let head := process memory raw
      let tail := processLines head.1 rest
      (tail.1, head.2 :: tail.2)

theorem all_raw_inputs_requirement (memory : Memory) (inputs : List String) :
    (processLines memory inputs).1.requirement = memory.requirement := by
  induction inputs generalizing memory with
  | nil => rfl
  | cons raw rest ih => exact (ih (process memory raw).1).trans (process_requirement memory raw)

theorem all_raw_inputs_old_reads (memory : Memory) (inputs : List String) (handle var : Nat)
    (within : handle < memory.register.length) :
    readRegister (processLines memory inputs).1.register handle var = readRegister memory.register handle var := by
  induction inputs generalizing memory with
  | nil => rfl
  | cons raw rest ih =>
      have continued : handle < (process memory raw).1.register.length :=
        Nat.lt_of_lt_of_le within (dispatch_monotone memory (decode memory raw))
      exact (ih (process memory raw).1 continued).trans (dispatch_old_read memory (decode memory raw) handle var within)

def codeBits : Bytes → Option (List Bool)
  | [] => some []
  | head :: tail => do
      let head ← bit [head]
      let tail ← codeBits tail
      some (head :: tail)

def bootData : List Bytes → Option (Nat × Nat × List Bool)
  | [] => none
  | op :: args => do
      if op != bytes "init" then none else do
        let (input, var, code) ← exactlyThree args
        let input ← natural input 8
        let var ← natural var 256
        if code.length > 9 then none else do
          let code ← codeBits code
          some (input, var, code)

def initializeMemory (raw : String) : Option Memory :=
  match bootData (tokenize (bytes raw) [] []) with
  | none => none
  | some (input, var, code) => match prepare input [var] code with
      | .error _ => none
      | .ok prepared => some prepared.memory

def writeLine (value : Bytes) : IO Unit := do
  let output ← IO.getStdout
  output.write ⟨(value ++ [10]).toArray⟩
  output.flush

def loop : Nat → Memory → IO Unit
  | 0, _ => pure ()
  | fuel + 1, memory => do
      let input ← IO.getStdin
      let raw ← input.getLine
      if raw.isEmpty then return
      let produced := process memory raw
      writeLine produced.2
      loop fuel produced.1

def main : IO Unit := do
  let input ← IO.getStdin
  let raw ← input.getLine
  match initializeMemory raw with
  | none => writeLine (bytes "{\"initialization_error\":true}")
  | some memory =>
      writeLine (bytes "{\"initialized\":" ++ observationBytes memory ++ bytes "}")
      loop 10000 memory

end LocalAlignmentKernel
def main : IO Unit := LocalAlignmentKernel.main
/- AXIOM_AUDIT_BEGIN -/
#print axioms LocalAlignmentKernel.bytes
#print axioms LocalAlignmentKernel.number
#print axioms LocalAlignmentKernel.boolean
#print axioms LocalAlignmentKernel.tokenize
#print axioms LocalAlignmentKernel.digits
#print axioms LocalAlignmentKernel.natural
#print axioms LocalAlignmentKernel.bit
#print axioms LocalAlignmentKernel.exactlyOne
#print axioms LocalAlignmentKernel.exactlyTwo
#print axioms LocalAlignmentKernel.exactlyThree
#print axioms LocalAlignmentKernel.parseRequest
#print axioms LocalAlignmentKernel.decode
#print axioms LocalAlignmentKernel.refusalBytes
#print axioms LocalAlignmentKernel.messageBytes
#print axioms LocalAlignmentKernel.originBytes
#print axioms LocalAlignmentKernel.responseBytes
#print axioms LocalAlignmentKernel.evidenceBytes
#print axioms LocalAlignmentKernel.arrayBytes
#print axioms LocalAlignmentKernel.productionBytes
#print axioms LocalAlignmentKernel.receiptBytes
#print axioms LocalAlignmentKernel.observationBytes
#print axioms LocalAlignmentKernel.process
#print axioms LocalAlignmentKernel.process_requirement
#print axioms LocalAlignmentKernel.decode_failure_no_effect
#print axioms LocalAlignmentKernel.processLines
#print axioms LocalAlignmentKernel.all_raw_inputs_requirement
#print axioms LocalAlignmentKernel.all_raw_inputs_old_reads
#print axioms LocalAlignmentKernel.codeBits
#print axioms LocalAlignmentKernel.bootData
#print axioms LocalAlignmentKernel.initializeMemory
#print axioms LocalAlignmentKernel.writeLine
#print axioms LocalAlignmentKernel.loop
#print axioms LocalAlignmentKernel.main
#print axioms main
/- AXIOM_AUDIT_END -/
