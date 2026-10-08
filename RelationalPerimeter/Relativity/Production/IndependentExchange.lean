import RelationalPerimeter.Relativity.Production.ReferenceRenaming
import RelationalPerimeter.Relativity.Production.UsedDependencies

/-!
# Two independent productions, with their actual dependencies

Both instructions read the same already formed source. The second is weakened
only by old-reference inclusion: it cannot consume the first output. The local
law adds a resource and preserves old ones, so shared old read ports are allowed.
The two histories remain different. The exchange transports their occurrences,
values and positive used-port edges; it does not equate the intermediate cursors.
This is a local candidate law, not yet a spacetime or physical grouping theorem.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def InputPort.rename {source target : List Kind}
    (references : {kind : Kind} → Ref source kind → Ref target kind)
    {outputKind inputKind} {instruction : Instruction source outputKind}
    {ref : Ref source inputKind} (port : InputPort instruction ref) :
    InputPort (instruction.rename references) (references ref) := by
  cases port with
  | emissionReading reading payload => exact .emissionReading _ _
  | emissionPayload reading payload => exact .emissionPayload _ _
  | relaySignal signal calibration => exact .relaySignal _ _
  | relayCalibration signal calibration => exact .relayCalibration _ _
  | receptionSignal signal => exact .receptionSignal _

/-- Every port of a weakened instruction positively returns to an old port.
No port of this instruction can designate the other production's fresh output. -/
def InputPort.priorOrigin {context : List Kind} {added outputKind inputKind}
    (instruction : Instruction context outputKind) (ref : Ref (added :: context) inputKind)
    (port : InputPort (instruction.rename Ref.prior) ref) :
    (old : Ref context inputKind) ×' (InputPort instruction old ×' (ref = .prior old)) := by
  cases instruction with
  | emit reading payload =>
    cases port with
    | emissionReading => exact ⟨reading, .emissionReading reading payload, rfl⟩
    | emissionPayload => exact ⟨payload, .emissionPayload reading payload, rfl⟩
  | relay signal calibration =>
    cases port with
    | relaySignal => exact ⟨signal, .relaySignal signal calibration, rfl⟩
    | relayCalibration => exact ⟨calibration, .relayCalibration signal calibration, rfl⟩
  | receive signal =>
    cases port with
    | receptionSignal => exact ⟨signal, .receptionSignal signal, rfl⟩

theorem independent_second_output (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) :
    (perform (perform source first).successor (second.rename Ref.prior)).determination.1 =
      (perform source second).determination.1 :=
  (perform_output_exact _ _).trans
    ((second.rename_interpret Ref.prior source.values (perform source first).successor.values
      (fun _ => rfl)).trans (perform_output_exact source second).symm)

structure IndependentPairProduction (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) where
  firstDetermination : Determination source first
  secondDetermination : Determination (source.extend firstDetermination) (second.rename Ref.prior)

/-- Two executions only, with their positive outputs retained for consumers. -/
def produceIndependentPair (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) :
    IndependentPairProduction source first second :=
  let firstDetermination := execute source.values first
  let secondDetermination := execute (source.extend firstDetermination).values (second.rename Ref.prior)
  ⟨firstDetermination, secondDetermination⟩

def IndependentPairProduction.cursor {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (produced : IndependentPairProduction source first second) : Cursor :=
  (source.extend produced.firstDetermination).extend produced.secondDetermination

/-- Assemble the history from the stored outputs, without executing again. -/
def IndependentPairProduction.execution {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (produced : IndependentPairProduction source first second) : Execution source :=
  ⟨produced.cursor, .extend
    (.extend .root ⟨firstKind, first, produced.firstDetermination, rfl⟩)
    ⟨secondKind, second.rename Ref.prior, produced.secondDetermination, rfl⟩⟩

def independentPair (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) :
    Execution source := (produceIndependentPair source first second).execution

theorem independentPair_runner_exact (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) :
    independentPair source first second = run source (.step first (.step (second.rename Ref.prior) .done)) := rfl

theorem independentPair_history_length (source : Cursor) {firstKind secondKind}
    (first : Instruction source.kinds firstKind) (second : Instruction source.kinds secondKind) :
    StrongPerimetralTurning.History.length (independentPair source first second).history = 2 :=
  rfl

theorem IndependentPairProduction.second_output_exact {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (produced : IndependentPairProduction source first second) :
    produced.secondDetermination.1 = second.interpret source.values :=
  produced.secondDetermination.2.output_exact.trans
    (second.rename_interpret Ref.prior source.values (source.extend produced.firstDetermination).values
      (fun _ => rfl))

def independentPairRaccord {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first) : ReadRaccord original.cursor reversed.cursor where
  references := swapTransport source.kinds firstKind secondKind
  reads := by
    intro kind ref
    cases ref with
    | here => exact reversed.firstDetermination.2.output_exact.trans original.second_output_exact.symm
    | prior rest => cases rest with
      | here => exact reversed.second_output_exact.trans original.firstDetermination.2.output_exact.symm
      | prior old => rfl

/-- Transport of actual edges. The fresh second edge becomes an inherited
first edge, and vice versa. Earlier edges retain their original role witnesses. -/
def independentPairUsed {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first)
    {one two : Occurrence original.cursor.kinds}
    (edge : Used original.cursor.formation one two) :
    Used reversed.cursor.formation
      ((independentPairRaccord original reversed).references.occurrences.forward one)
      ((independentPairRaccord original reversed).references.occurrences.forward two) := by
  cases edge with
  | produced past role ref port =>
    obtain ⟨old, oldPort, exactRef⟩ := port.priorOrigin second ref
    cases exactRef
    exact .inherited reversed.secondDetermination.2
      (.produced source.formation reversed.firstDetermination.2 old oldPort)
  | inherited role prior =>
    cases prior with
    | produced past priorRole ref port =>
      exact .produced (source.extend reversed.firstDetermination).formation
        reversed.secondDetermination.2 (.prior ref) (port.rename Ref.prior)
    | inherited priorRole oldEdge =>
      exact .inherited reversed.secondDetermination.2
        (.inherited reversed.firstDetermination.2 oldEdge)

theorem InputPort.prior_not_fresh {context : List Kind} {added outputKind}
    (instruction : Instruction context outputKind)
    (port : InputPort (instruction.rename Ref.prior)
      (Ref.here : Ref (added :: context) added)) : False := by
  obtain ⟨old, _, same⟩ := port.priorOrigin instruction .here
  exact fresh_position_distinct old (congrArg Ref.position same)

theorem dependent_port_cannot_be_independent {context : List Kind}
    (signal : Ref context .signal) (calibration : Ref context .calibration)
    (port : InputPort ((Instruction.relay signal calibration).rename
      (Ref.prior : {kind : Kind} → Ref context kind → Ref (.signal :: context) kind))
      (Ref.here : Ref (.signal :: context) .signal)) : False := by
  obtain ⟨old, _, same⟩ := port.priorOrigin (.relay signal calibration) .here
  exact fresh_position_distinct old (congrArg Ref.position same)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InputPort.rename
#print axioms RelationalPerimeter.Relativity.Production.InputPort.priorOrigin
#print axioms RelationalPerimeter.Relativity.Production.independent_second_output
#print axioms RelationalPerimeter.Relativity.Production.IndependentPairProduction
#print axioms RelationalPerimeter.Relativity.Production.produceIndependentPair
#print axioms RelationalPerimeter.Relativity.Production.IndependentPairProduction.cursor
#print axioms RelationalPerimeter.Relativity.Production.IndependentPairProduction.execution
#print axioms RelationalPerimeter.Relativity.Production.independentPair
#print axioms RelationalPerimeter.Relativity.Production.independentPair_runner_exact
#print axioms RelationalPerimeter.Relativity.Production.independentPair_history_length
#print axioms RelationalPerimeter.Relativity.Production.IndependentPairProduction.second_output_exact
#print axioms RelationalPerimeter.Relativity.Production.independentPairRaccord
#print axioms RelationalPerimeter.Relativity.Production.independentPairUsed
#print axioms RelationalPerimeter.Relativity.Production.InputPort.prior_not_fresh
#print axioms RelationalPerimeter.Relativity.Production.dependent_port_cannot_be_independent
/- AXIOM_AUDIT_END -/
