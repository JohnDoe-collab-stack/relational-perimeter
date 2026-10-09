import RelationalPerimeter.Constitution.FormationTransport

set_option linter.checkUnivs false

/-! Witness relabelling, complete step payloads, and preserved structural order. -/

namespace RelationalPerimeter.Constitution.FormationTransportExamples

open StrongPerimetralTurning

abbrev signature : ConstitutiveSignature :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Bool
    Difference := Bool
    Provenance := fun _ => Bool }

def boolFlip : ExactTypeTransport Bool Bool :=
  { forward := Bool.not
    backward := Bool.not
    forwardBackward := fun value => by cases value <;> rfl
    backwardForward := fun value => by cases value <;> rfl }

def witnessFlip : ConstitutiveSignatureTransport signature signature :=
  { explicit := .reflexive _
    implicit := .reflexive _
    difference := .reflexive _
    compatibility := fun _ _ => boolFlip
    provenance := fun _ => boolFlip }

def node : signature.Node :=
  { explicit := ()
    implicit := ()
    difference := false
    provenance := true
    internallyCompatible := true }

abbrev formation : PositiveFormation :=
  { Explicit := signature.Explicit
    Implicit := signature.Implicit
    Compatible := signature.Compatible
    Difference := signature.Difference
    Provenance := signature.Provenance
    State := Unit
    node := fun _ => node
    Step := fun _ _ => Bool × Bool
    compatibility := fun step => step.1 }

abbrev transportedFormation : PositiveFormation := formation.transport witnessFlip

def firstHistory : PositiveHistory formation () () :=
  .cons (middle := ()) (true, false) .nil

def secondHistory : PositiveHistory formation () () :=
  .cons (middle := ()) (true, true) .nil

def firstPayload : PositiveHistory formation () () → Option Bool
  | .nil => .none
  | .cons step _ => .some step.2

def transportedPayload : PositiveHistory transportedFormation () () → Option Bool
  | .nil => .none
  | .cons step _ => .some step.2

theorem equal_spines_with_distinct_step_data : firstHistory.deploy = secondHistory.deploy := rfl

theorem histories_distinct : firstHistory ≠ secondHistory := by
  intro equality
  have payloadExact := congrArg firstPayload equality
  cases payloadExact

def transportedHistory : PositiveHistory transportedFormation () () :=
  firstHistory.transportSignature witnessFlip

theorem selected_readout_flipped :
    (transportedHistory.linkAt .here).compatibility = false := rfl

theorem internal_readout_flipped :
    (transportedFormation.node ()).internallyCompatible = false := rfl

theorem provenance_flipped : (transportedFormation.node ()).provenance = false := rfl

theorem complete_payload_preserved : transportedPayload transportedHistory = .some false := rfl

theorem complete_history_return :
    PositiveHistory.restoreSignature witnessFlip transportedHistory = firstHistory :=
  firstHistory.transport_restore witnessFlip

def threeSteps : PositiveHistory formation () () :=
  .cons (middle := ()) (true, false)
    (.cons (middle := ()) (false, true) (.cons (middle := ()) (true, true) .nil))

def firstOccurrence : PositiveHistory.Occurrence threeSteps := .here
def secondOccurrence : PositiveHistory.Occurrence threeSteps := .later .here
def thirdOccurrence : PositiveHistory.Occurrence threeSteps := .later (.later .here)

abbrev threeStepsTransported : PositiveHistory transportedFormation () () :=
  threeSteps.transportSignature witnessFlip

theorem repeated_nodes :
    (threeSteps.linkAt firstOccurrence).source = (threeSteps.linkAt thirdOccurrence).source := rfl

theorem preserved_first_next_second :
    NonClosingNext threeStepsTransported.deploy
      (threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip firstOccurrence))
      (threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip secondOccurrence)) :=
  (threeSteps.transport_next_iff witnessFlip firstOccurrence secondOccurrence).mpr .here_next

theorem preserved_first_precedes_third :
    NonClosingPrecedes threeStepsTransported.deploy
      (threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip firstOccurrence))
      (threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip thirdOccurrence)) :=
  (threeSteps.transport_precedes_iff witnessFlip firstOccurrence thirdOccurrence).mpr
    (.here_later (.later .here))

theorem separated_transported_positions :
    threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip firstOccurrence) ≠
      threeStepsTransported.toPosition (threeSteps.transportOccurrence witnessFlip thirdOccurrence) :=
  preserved_first_precedes_third.ne

def firstPrefix : PositiveHistory formation () () := firstHistory

def lastSuffix : PositiveHistory formation () () :=
  .cons (middle := ()) (false, true) .nil

theorem composed_history_commutes :
    (firstPrefix.append lastSuffix).transportSignature witnessFlip =
      (firstPrefix.transportSignature witnessFlip).append
        (lastSuffix.transportSignature witnessFlip) :=
  firstPrefix.transport_append witnessFlip lastSuffix

theorem deployed_history_commutes :
    threeStepsTransported.deploy = witnessFlip.mapSpine threeSteps.deploy :=
  threeSteps.transport_deploy witnessFlip

def choice : ChosenPositiveContinuation formation :=
  { successor := fun _ => ()
    step := fun _ => (true, false) }

theorem chosen_walk_commutes :
    (choice.transportSignature witnessFlip).walk () 2 =
      let original := choice.walk () 2
      ⟨original.1, original.2.transportSignature witnessFlip⟩ :=
  choice.transport_walk witnessFlip () 2

end RelationalPerimeter.Constitution.FormationTransportExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.signature
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.boolFlip
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.witnessFlip
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.node
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.formation
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.transportedFormation
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.firstHistory
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.secondHistory
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.firstPayload
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.transportedPayload
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.equal_spines_with_distinct_step_data
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.histories_distinct
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.transportedHistory
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.selected_readout_flipped
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.internal_readout_flipped
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.provenance_flipped
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.complete_payload_preserved
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.complete_history_return
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.threeSteps
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.firstOccurrence
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.secondOccurrence
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.thirdOccurrence
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.threeStepsTransported
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.repeated_nodes
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.preserved_first_next_second
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.preserved_first_precedes_third
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.separated_transported_positions
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.firstPrefix
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.lastSuffix
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.composed_history_commutes
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.deployed_history_commutes
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.choice
#print axioms RelationalPerimeter.Constitution.FormationTransportExamples.chosen_walk_commutes
/- AXIOM_AUDIT_END -/
