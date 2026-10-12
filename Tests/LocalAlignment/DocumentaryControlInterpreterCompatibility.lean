import Tests.LocalAlignment.DocumentaryControlInterpreter
import Tests.LocalAlignment.DocumentaryControlHistoricalInterpreter

/-! Whole-code simulation, preserving business fuel, labels and values.
The historical interpreter is an exact copy with only its namespace renamed. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility
universe u v

def erase {Label : Type} {Value : Type u} : ConstitutiveSearch.Agent.Local.Documentary.Control.Code Label Value → ConstitutiveSearch.Agent.Local.Documentary.ControlHistorical.Code Label Value
  | .done value => .done value
  | .step label next => .step label (fun _ => erase (next ()))
  | .admin _ next _ => erase (next ())

 def traceOut {Label : Type} {Value : Type u} {code : ConstitutiveSearch.Agent.Local.Documentary.Control.Code Label Value} {labels value}
    (trace : ConstitutiveSearch.Agent.Local.Documentary.Control.Eval code labels value) : ConstitutiveSearch.Agent.Local.Documentary.ControlHistorical.Eval (erase code) labels value :=
  match trace with
  | .done => .done
  | .step rest => .step (traceOut rest)
  | @ConstitutiveSearch.Agent.Local.Documentary.Control.Eval.admin _ _ event next forwards labels value rest => traceOut (code := next ()) rest

def traceIn {Label : Type} {Value : Type u} : (code : ConstitutiveSearch.Agent.Local.Documentary.Control.Code Label Value) →
    {labels : List Label} → {value : Value} → ConstitutiveSearch.Agent.Local.Documentary.ControlHistorical.Eval (erase code) labels value → ConstitutiveSearch.Agent.Local.Documentary.Control.Eval code labels value
  | .done _, _, _, trace => by cases trace; exact .done
  | .step _ next, _, _, trace => by cases trace with
    | step rest => exact .step (traceIn (next ()) rest)
  | .admin _ next _, _, _, trace => .admin (traceIn (next ()) trace)
termination_by structural code => code

theorem run_equivalent {Label : Type} {Value : Type u} (code : ConstitutiveSearch.Agent.Local.Documentary.Control.Code Label Value) (fuel : Nat) :
    ConstitutiveSearch.Agent.Local.Documentary.Control.runCtl fuel code = ConstitutiveSearch.Agent.Local.Documentary.ControlHistorical.runCtl fuel (erase code) := by
  induction code generalizing fuel with
  | done value => cases fuel <;> rfl
  | step label next previous =>
    cases fuel with
    | zero => rfl
    | succ remaining =>
      rw [ConstitutiveSearch.Agent.Local.Documentary.Control.runCtl_step]
      dsimp only [erase]
      rw [ConstitutiveSearch.Agent.Local.Documentary.ControlHistorical.runCtl_step]
      rw [previous ()]
  | admin event next forwards previous =>
    rw [ConstitutiveSearch.Agent.Local.Documentary.Control.runCtl_admin fuel event next forwards]
    exact previous () fuel

end ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility.erase
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility.traceOut
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility.traceIn
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompatibility.run_equivalent
/- AXIOM_AUDIT_END -/
