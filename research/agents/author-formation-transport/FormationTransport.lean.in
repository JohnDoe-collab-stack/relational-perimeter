import RelationalPerimeter.Constitution.SpineTransport

set_option linter.checkUnivs false

/-!
# Reconstruction of a positive formation along its primitive signature

The state and full step data are retained. Nodes and step compatibility readouts
are transported using the exact maps of every primitive fibre. This construction
does not provide an inverse for an arbitrary map between pre-existing step types.
-/

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

universe uE uI uK uD uP uS uStep vE vI vK vD vP

namespace PositiveFormation

abbrev signature (F : PositiveFormation) : ConstitutiveSignature :=
  { Explicit := F.Explicit
    Implicit := F.Implicit
    Compatible := F.Compatible
    Difference := F.Difference
    Provenance := F.Provenance }

abbrev transport (F : PositiveFormation) {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target) : PositiveFormation :=
  { Explicit := target.Explicit
    Implicit := target.Implicit
    Compatible := target.Compatible
    Difference := target.Difference
    Provenance := target.Provenance
    State := F.State
    node := fun state => change.mapNode (F.node state)
    Step := F.Step
    compatibility := fun {source target} step =>
      (change.compatibility (F.node source).implicit (F.node target).explicit).forward
        (F.compatibility step) }

theorem transport_node (F : PositiveFormation) {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target) (state : F.State) :
    (F.transport change).node state = change.mapNode (F.node state) := rfl

theorem transport_step_readout (F : PositiveFormation) {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (step : F.Step source terminal) :
    (F.transport change).compatibility step =
      (change.compatibility (F.node source).implicit (F.node terminal).explicit).forward
        (F.compatibility step) := rfl

end PositiveFormation

namespace PositionReindex

theorem cast_here {S : ConstitutiveSignature} {node nextNode : S.Node}
    {witness : S.Compatible node.implicit nextNode.explicit}
    {first second : PerimeterSpine S.Compatible nextNode} (exactTail : first = second) :
    (congrArg (PerimeterSpine.advance (node := node) witness) exactTail) ▸
        (NonClosingPosition.here : NonClosingPosition (.advance witness first)) =
      (NonClosingPosition.here : NonClosingPosition (.advance witness second)) := by
  cases exactTail
  rfl

theorem cast_later {S : ConstitutiveSignature} {node nextNode : S.Node}
    {witness : S.Compatible node.implicit nextNode.explicit}
    {first second : PerimeterSpine S.Compatible nextNode} (exactTail : first = second)
    (position : NonClosingPosition first) :
    (congrArg (PerimeterSpine.advance (node := node) witness) exactTail) ▸
        (NonClosingPosition.later position : NonClosingPosition (.advance witness first)) =
      (NonClosingPosition.later (exactTail ▸ position) : NonClosingPosition (.advance witness second)) := by
  cases exactTail
  rfl

theorem precedes_cast {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second)
    (a b : NonClosingPosition first) :
    NonClosingPrecedes second (exactSpine ▸ a) (exactSpine ▸ b) ↔
      NonClosingPrecedes first a b := by
  cases exactSpine
  exact Iff.rfl

theorem next_cast {S : ConstitutiveSignature} {node : S.Node}
    {first second : PerimeterSpine S.Compatible node} (exactSpine : first = second)
    (a b : NonClosingPosition first) :
    NonClosingNext second (exactSpine ▸ a) (exactSpine ▸ b) ↔
      NonClosingNext first a b := by
  cases exactSpine
  exact Iff.rfl

end PositionReindex

namespace PositiveHistory

variable {F : PositiveFormation} {target : ConstitutiveSignature}

def transportSignature (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} : PositiveHistory F source terminal →
      PositiveHistory (F.transport change) source terminal
  | .nil => .nil
  | .cons step tail => .cons step (tail.transportSignature change)

def restoreSignature (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} : PositiveHistory (F.transport change) source terminal →
      PositiveHistory F source terminal
  | .nil => .nil
  | .cons step tail => .cons step (restoreSignature change tail)

theorem transport_restore (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    restoreSignature change (history.transportSignature change) = history := by
  induction history with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons step) inductionHypothesis

theorem restore_transport (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State}
    (history : PositiveHistory (F.transport change) source terminal) :
    (restoreSignature change history).transportSignature change = history := by
  exact PositiveHistory.rec
    (F := F.transport change)
    (motive := fun _ _ history =>
      (restoreSignature change history).transportSignature change = history)
    (fun {_} => rfl)
    (fun {_ _ _} step _ inductionHypothesis =>
      congrArg (PositiveHistory.cons (F := F.transport change) step) inductionHypothesis)
    history

def signatureTransport (change : ConstitutiveSignatureTransport F.signature target)
    (source terminal : F.State) :
    ExactTypeTransport (PositiveHistory F source terminal)
      (PositiveHistory (F.transport change) source terminal) :=
  { forward := transportSignature change
    backward := restoreSignature change
    forwardBackward := transport_restore change
    backwardForward := restore_transport change }

theorem transport_append (change : ConstitutiveSignatureTransport F.signature target)
    {source middle terminal : F.State} (first : PositiveHistory F source middle)
    (second : PositiveHistory F middle terminal) :
    (first.append second).transportSignature change =
      (first.transportSignature change).append (second.transportSignature change) := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons (F := F.transport change) step)
        (inductionHypothesis second)

theorem transport_deploy (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    (history.transportSignature change).deploy = change.mapSpine history.deploy := by
  induction history with
  | nil => rfl
  | @cons source middle terminal step tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance
        (node := (F.transport change).node source)
        (nextNode := (F.transport change).node middle)
        ((change.compatibility (F.node source).implicit (F.node middle).explicit).forward
          (F.compatibility step))) inductionHypothesis

def transportOccurrence (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} : (history : PositiveHistory F source terminal) →
      Occurrence history → Occurrence (history.transportSignature change)
  | .nil, occurrence => nomatch occurrence
  | .cons _ _, .here => .here
  | .cons _ tail, .later occurrence => .later (tail.transportOccurrence change occurrence)

def restoreOccurrence (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} : (history : PositiveHistory F source terminal) →
      Occurrence (history.transportSignature change) → Occurrence history
  | .nil => fun occurrence => nomatch occurrence
  | .cons step tail => fun occurrence =>
      match occurrence with
      | .here => Occurrence.here (step := step) (tail := tail)
      | .later occurrence => Occurrence.later (step := step) (tail.restoreOccurrence change occurrence)

theorem transport_restore_occurrence
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (occurrence : Occurrence history) :
    history.restoreOccurrence change (history.transportOccurrence change occurrence) =
      occurrence := by
  induction occurrence with
  | here => rfl
  | later occurrence inductionHypothesis =>
      exact congrArg Occurrence.later inductionHypothesis

theorem restore_transport_occurrence
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (occurrence : Occurrence (history.transportSignature change)) :
    history.transportOccurrence change (history.restoreOccurrence change occurrence) =
      occurrence := by
  induction history with
  | nil =>
      change Occurrence (.nil : PositiveHistory (F.transport change) _ _) at occurrence
      exact nomatch occurrence
  | cons step tail inductionHypothesis =>
      change Occurrence (PositiveHistory.cons (F := F.transport change)
        step (tail.transportSignature change)) at occurrence
      exact match occurrence with
      | .here => rfl
      | .later occurrence => congrArg (Occurrence.later (F := F.transport change))
          (inductionHypothesis occurrence)

def occurrenceSignatureTransport
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    ExactTypeTransport (Occurrence history) (Occurrence (history.transportSignature change)) :=
  { forward := history.transportOccurrence change
    backward := history.restoreOccurrence change
    forwardBackward := history.transport_restore_occurrence change
    backwardForward := history.restore_transport_occurrence change }

theorem transport_position
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (occurrence : Occurrence history) :
    history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change occurrence) =
      change.mapPosition history.deploy (history.toPosition occurrence) := by
  induction occurrence with
  | @here source middle terminal step tail =>
      exact PositionReindex.cast_here (S := target) (tail.transport_deploy change)
  | @later source middle terminal step tail occurrence inductionHypothesis =>
      change (congrArg (PerimeterSpine.advance
        (node := (F.transport change).node source)
        (nextNode := (F.transport change).node middle)
        ((change.compatibility (F.node source).implicit (F.node middle).explicit).forward
          (F.compatibility step))) (tail.transport_deploy change)) ▸
          (NonClosingPosition.later ((tail.transportSignature change).toPosition
            (tail.transportOccurrence change occurrence))) =
        NonClosingPosition.later (change.mapPosition tail.deploy (tail.toPosition occurrence))
      exact (PositionReindex.cast_later (S := target) (tail.transport_deploy change)
        ((tail.transportSignature change).toPosition
          (tail.transportOccurrence change occurrence))).trans
        (congrArg NonClosingPosition.later inductionHypothesis)

theorem transport_precedes_iff
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (first second : Occurrence history) :
    NonClosingPrecedes (history.transportSignature change).deploy
        ((history.transportSignature change).toPosition (history.transportOccurrence change first))
        ((history.transportSignature change).toPosition (history.transportOccurrence change second)) ↔
      NonClosingPrecedes history.deploy (history.toPosition first) (history.toPosition second) := by
  calc
    _ ↔ NonClosingPrecedes (change.mapSpine history.deploy)
      (history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change first))
      (history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change second)) :=
          (PositionReindex.precedes_cast (history.transport_deploy change) _ _).symm
    _ ↔ _ := by
      rw [history.transport_position, history.transport_position]
      exact change.precedes_iff history.deploy _ _

theorem transport_next_iff
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (first second : Occurrence history) :
    NonClosingNext (history.transportSignature change).deploy
        ((history.transportSignature change).toPosition (history.transportOccurrence change first))
        ((history.transportSignature change).toPosition (history.transportOccurrence change second)) ↔
      NonClosingNext history.deploy (history.toPosition first) (history.toPosition second) := by
  calc
    _ ↔ NonClosingNext (change.mapSpine history.deploy)
      (history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change first))
      (history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change second)) :=
          (PositionReindex.next_cast (history.transport_deploy change) _ _).symm
    _ ↔ _ := by
      rw [history.transport_position, history.transport_position]
      exact change.next_iff history.deploy _ _

theorem transport_link
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (occurrence : Occurrence history) :
    (history.transportSignature change).linkAt (history.transportOccurrence change occurrence) =
      change.mapLink (history.linkAt occurrence) := by
  induction occurrence with
  | here => rfl
  | later occurrence inductionHypothesis => exact inductionHypothesis

end PositiveHistory

namespace ChosenPositiveContinuation

def transportSignature {F : PositiveFormation} {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    (choice : ChosenPositiveContinuation F) : ChosenPositiveContinuation (F.transport change) :=
  { successor := choice.successor
    step := choice.step }

theorem transport_successor {F : PositiveFormation} {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    (choice : ChosenPositiveContinuation F) (state : F.State) :
    (choice.transportSignature change).successor state = choice.successor state := rfl

theorem transport_selected_step {F : PositiveFormation} {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    (choice : ChosenPositiveContinuation F) (state : F.State) :
    (choice.transportSignature change).step state = choice.step state := rfl

theorem transport_walk {F : PositiveFormation} {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    (choice : ChosenPositiveContinuation F) (source : F.State) (count : Nat) :
    (choice.transportSignature change).walk source count =
      let original := choice.walk source count
      ⟨original.1, original.2.transportSignature change⟩ := by
  induction count generalizing source with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [walk]
      rw [inductionHypothesis]
      rfl

end ChosenPositiveContinuation
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.PositiveFormation.signature
#print axioms RelationalPerimeter.Constitution.PositiveFormation.transport
#print axioms RelationalPerimeter.Constitution.PositiveFormation.transport_node
#print axioms RelationalPerimeter.Constitution.PositiveFormation.transport_step_readout
#print axioms RelationalPerimeter.Constitution.PositionReindex.cast_here
#print axioms RelationalPerimeter.Constitution.PositionReindex.cast_later
#print axioms RelationalPerimeter.Constitution.PositionReindex.precedes_cast
#print axioms RelationalPerimeter.Constitution.PositionReindex.next_cast
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transportSignature
#print axioms RelationalPerimeter.Constitution.PositiveHistory.restoreSignature
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_restore
#print axioms RelationalPerimeter.Constitution.PositiveHistory.restore_transport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.signatureTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_append
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_deploy
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transportOccurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.restoreOccurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_restore_occurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.restore_transport_occurrence
#print axioms RelationalPerimeter.Constitution.PositiveHistory.occurrenceSignatureTransport
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_position
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_precedes_iff
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_next_iff
#print axioms RelationalPerimeter.Constitution.PositiveHistory.transport_link
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.transportSignature
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.transport_successor
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.transport_selected_step
#print axioms RelationalPerimeter.Constitution.ChosenPositiveContinuation.transport_walk
/- AXIOM_AUDIT_END -/
