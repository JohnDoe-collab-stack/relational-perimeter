import Tests.LocalAlignment.DocumentaryControlFrontierApplicationSplit
import Tests.LocalAlignment.DocumentaryControlFrontierApplicationAbsorption

/-! Named entire historical execution payloads, formed solely from the actual
preservation, actual directed transport, children and their shared order.
The Eval laws below relate every field, including metadata and stored executors,
to the original producer. They do not execute or replay those producers. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 18000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

@[inline] def assembled {formula : Cnf} {selected : Var}
    {source target : List (GeneratedStructuralBranchContext formula)} :=
  @ControlFrontierApplication.ExecutablePreservation.mk formula selected source target

def identity (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source)) :
    ControlFrontierApplication.ExecutablePreservation formula selected source source :=
  ⟨actual.1, fun _ => 2, fun _ => 2, id, id, ControlFrontierApplication.identityForward selected source actual,
      ControlFrontierApplication.identityBackward selected source actual,
              ControlFrontierApplication.identity_forward_bounded selected source actual,
              ControlFrontierApplication.identity_backward_bounded selected source actual⟩

def swap (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest))) :
    ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (second :: first :: rest) :=
  ⟨actual.1, fun _ => 3, fun _ => 3, id, id, ControlFrontierApplication.swapApplication selected
      ⟨actual.1.forward, congrArg AcceptedFrontierPreservation.forward actual.2⟩,
      ControlFrontierApplication.swapApplication selected
      ⟨actual.1.backward, congrArg AcceptedFrontierPreservation.backward actual.2⟩,
            ControlFrontierApplication.swap_application_bounded selected _, ControlFrontierApplication.swap_application_bounded selected _⟩

def absorbFirst {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport.1)) :
    ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (second :: rest) :=
  ⟨actual.1, fun _ => 7, fun _ => 2, flipEnvelope selected, id, ControlFrontierApplication.absorbFirstForward selected relation transport actual,
      ControlFrontierApplication.absorbFirstBackward selected transport.1 actual,
              ControlFrontierApplication.absorb_first_forward_bounded selected relation transport actual, ControlFrontierApplication.absorb_first_backward_bounded selected transport.1 actual⟩

def absorbSecond {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport.1)) :
    ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (first :: rest) :=
  ⟨actual.1, fun _ => 8, fun _ => 2, flipEnvelope selected, id, ControlFrontierApplication.absorbSecondForward selected relation transport actual,
      ControlFrontierApplication.absorbSecondBackward selected transport.1 actual,
              ControlFrontierApplication.absorb_second_forward_bounded selected relation transport actual, ControlFrontierApplication.absorb_second_backward_bounded selected transport.1 actual⟩

def expand {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1)) :
    ControlFrontierApplication.ExecutablePreservation formula selected
              (parent :: rest) (left.1 :: right.1 :: rest) :=
  ⟨actual.1, fun budget => (budget + 3) + 1, fun _ => 4, id, id, ControlFrontierApplication.expandForward selected parent fresh left right splitter actual,
      ControlFrontierApplication.expandBackward selected parent fresh left right splitter actual,
            ControlFrontierApplication.expand_forward_bounded selected parent fresh left right splitter actual,
            ControlFrontierApplication.expand_backward_bounded selected parent fresh left right splitter actual⟩

def prepend {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head))) :
    ControlFrontierApplication.ExecutablePreservation formula selected (head :: source) (head :: target) :=
  ⟨actual.1, fun budget => (child.forwardCost budget + 1) + 1,
              fun budget => (child.backwardCost budget + 1) + 1,
              fun budget => max budget (child.forwardReaderBound budget),
              fun budget => max budget (child.backwardReaderBound budget),
              ControlFrontierApplication.prependForward child actual,
      ControlFrontierApplication.prependBackward child actual,
              ControlFrontierApplication.prepend_forward_bounded child actual,
              ControlFrontierApplication.prepend_backward_bounded child actual⟩

def trans {formula : Cnf} {selected : Var} {source middle target}
    (left : ControlFrontierApplication.ExecutablePreservation formula selected source middle)
    (right : ControlFrontierApplication.ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation)) :
    ControlFrontierApplication.ExecutablePreservation formula selected source target :=
  ⟨actual.1,
              fun budget => (left.forwardCost budget +
                (right.forwardCost (left.forwardReaderBound budget) + 1)) + 1,
              fun budget => (right.backwardCost budget +
                (left.backwardCost (right.backwardReaderBound budget) + 1)) + 1,
              fun budget => right.forwardReaderBound (left.forwardReaderBound budget),
              fun budget => left.backwardReaderBound (right.backwardReaderBound budget),
              ControlFrontierApplication.transForward left right actual,
      ControlFrontierApplication.transBackward left right actual,
              ControlFrontierApplication.trans_forward_bounded left right actual,
              ControlFrontierApplication.trans_backward_bounded left right actual⟩

def identity_eval (formula : Cnf) (selected : Var) (source : List (GeneratedStructuralBranchContext formula))
    (actual : Actual (AcceptedFrontierPreservation.identity (generatedStructuralBranchSystem formula) source))
    {labels : List Label}
    (trace : Eval (ControlFrontierOpening.identityCode (generatedStructuralBranchSystem formula) source) labels actual) :
    Eval (ControlFrontierApplication.identityCode formula selected source)
      (labels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources])
      ⟨identity formula selected source actual, actual.2⟩ := by
  exact trace.bind (.step (.step (.step (.step .done))))

def swap_eval (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest)))
    {labels : List Label}
    (trace : Eval (ControlFrontierEvaluation.swapCode (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest)) labels actual) :
    Eval (ControlFrontierApplication.swapCode formula selected (first := first) (second := second) (rest := rest))
      (labels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources])
      ⟨swap formula selected actual, actual.2⟩ := by
  exact trace.bind (.step (.step (.step (.step .done))))

def absorb_first_eval {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport.1))
    {transportLabels preservationLabels : List Label}
    (transportTrace : Eval (ControlFrontierEvaluation.transportCode selected relation) transportLabels transport)
    (preservationTrace : Eval (ControlFrontierEvaluation.absorbFirstCode (rest := rest) transport.1) preservationLabels actual) :
    Eval (ControlFrontierApplication.absorbFirstCode selected (rest := rest) relation)
      (transportLabels ++ (preservationLabels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources]))
      ⟨absorbFirst selected relation transport actual,
        actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest)) transport.2)⟩ := by
  exact transportTrace.bind (preservationTrace.bind (.step (.step (.step (.step .done)))))

def absorb_second_eval {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport.1))
    {transportLabels preservationLabels : List Label}
    (transportTrace : Eval (ControlFrontierEvaluation.transportCode selected relation) transportLabels transport)
    (preservationTrace : Eval (ControlFrontierEvaluation.absorbSecondCode (rest := rest) transport.1) preservationLabels actual) :
    Eval (ControlFrontierApplication.absorbSecondCode selected (rest := rest) relation)
      (transportLabels ++ (preservationLabels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources]))
      ⟨absorbSecond selected relation transport actual,
        actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest)) transport.2)⟩ := by
  exact transportTrace.bind (preservationTrace.bind (.step (.step (.step (.step .done)))))

def expand_eval {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1))
    {labels : List Label}
    (trace : Eval (ControlFrontierOpening.expandCode (rest := rest) splitter.1) labels actual) :
    Eval (ControlFrontierApplication.expandCode selected parent fresh left right splitter (rest := rest))
      (labels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources])
      ⟨expand selected parent fresh left right splitter actual, actual.2⟩ := by
  exact trace.bind (.step (.step (.step (.step .done))))

def prepend_eval {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ControlFrontierApplication.ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head)))
    {labels : List Label}
    (trace : Eval (ControlFrontierOpening.prependCode (head := head) child.preservation) labels actual) :
    Eval (ControlFrontierApplication.prependCode (head := head) child)
      (labels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources])
      ⟨prepend child actual, actual.2⟩ := by
  exact trace.bind (.step (.step (.step (.step .done))))

def trans_eval {formula : Cnf} {selected : Var} {source middle target}
    (left : ControlFrontierApplication.ExecutablePreservation formula selected source middle)
    (right : ControlFrontierApplication.ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation))
    {labels : List Label}
    (trace : Eval (ControlFrontierOpening.transCode left.preservation right.preservation) labels actual) :
    Eval (ControlFrontierApplication.transCode left right)
      (labels ++ [.executionPayload, .controlClosure, .controlClosure, .formationResources])
      ⟨trans left right actual, actual.2⟩ := by
  exact trace.bind (.step (.step (.step (.step .done))))

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.assembled
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.identity
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.swap
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.absorbFirst
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.absorbSecond
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.expand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.prepend
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.trans
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.identity_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.swap_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.absorb_first_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.absorb_second_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.expand_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.prepend_eval
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingOriginal.trans_eval
/- AXIOM_AUDIT_END -/
