import Tests.LocalAlignment.DocumentaryFoundationPortable

/-! Full rooted-history constructor serialization. Each retained endpoint is
encoded explicitly. Restoration consumes these fields and validates their
composability; it never invokes a free generation or historical executor. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable
open StrongPerimetralTurning FoundationPortable ControlCodec

theorem freeKCore_unique
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {code : BoundaryDifferenceCode P cursor}
    (first second : FreeKCore P cursor code) : first = second := by
  cases first with
  | mk formationTerm formationExact obstruction obstructionExact
      provenance provenanceExact =>
    cases second with
    | mk formationTerm' formationExact' obstruction' obstructionExact'
        provenance' provenanceExact' =>
      cases formationExact
      cases formationExact'
      cases obstructionExact
      cases obstructionExact'
      cases provenanceExact
      cases provenanceExact'
      rfl

theorem freeK_unique
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (first second : FreeK P previous difference) : first = second := by
  cases first with
  | mk core =>
    cases second with
    | mk core' =>
      exact congrArg FreeK.mk
        (freeKCore_unique core core')

theorem integrates_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : Integrates source) : first = second := by
  cases first with
  | mk firstLayer firstExact =>
    cases second with
    | mk secondLayer secondExact =>
      have layerExact : firstLayer = secondLayer :=
        freeK_unique firstLayer secondLayer
      cases layerExact
      rfl

theorem preservesProvenance_unique
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : PreservesProvenance source target) : first = second := by
  cases first with
  | mk firstTarget firstIntegrated =>
    cases second with
    | mk secondTarget secondIntegrated =>
      cases firstTarget
      cases secondTarget
      exact congrArg (PreservesProvenance.mk rfl)
        (integrates_unique firstIntegrated secondIntegrated)

theorem integratesClosureObstruction_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : IntegratesClosureObstruction source) : first = second := by
  cases first
  cases second
  rfl

theorem continuesDifference_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : ContinuesDifference source) : first = second := by
  cases first
  cases second
  rfl

theorem freshBoundaryDifference_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : FreshBoundaryDifference source) : first = second := by
  cases first with
  | mk firstContinuation firstRecord firstRecordExact firstFresh =>
    cases second with
    | mk secondContinuation secondRecord secondRecordExact secondFresh =>
      have continuationExact : firstContinuation = secondContinuation :=
        continuesDifference_unique
          firstContinuation secondContinuation
      have recordExact : firstRecord = secondRecord :=
        firstRecordExact.trans secondRecordExact.symm
      cases continuationExact
      cases recordExact
      rfl

theorem canonicalGeneratedLaws_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : CanonicalGeneratedLaws source) : first = second := by
  cases first with
  | mk firstCompatibility firstCompatibilityExact firstProvenance
      firstObstruction firstDifference firstFresh =>
    cases second with
    | mk secondCompatibility secondCompatibilityExact secondProvenance
      secondObstruction secondDifference secondFresh =>
      have compatibilityExact : firstCompatibility = secondCompatibility :=
        firstCompatibilityExact.trans secondCompatibilityExact.symm
      have provenanceExact : firstProvenance = secondProvenance :=
        preservesProvenance_unique
          firstProvenance secondProvenance
      have obstructionExact : firstObstruction = secondObstruction :=
        integratesClosureObstruction_unique
          firstObstruction secondObstruction
      have differenceExact : firstDifference = secondDifference :=
        continuesDifference_unique
          firstDifference secondDifference
      have freshExact : firstFresh = secondFresh :=
        freshBoundaryDifference_unique firstFresh secondFresh
      cases compatibilityExact
      cases provenanceExact
      cases obstructionExact
      cases differenceExact
      cases freshExact
      rfl

theorem generatedStep_unique
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : GeneratedStep source target) : first = second := by
  cases first with
  | mk firstTarget firstLaws =>
    cases second with
    | mk secondTarget secondLaws =>
      exact congrArg (GeneratedStep.mk firstTarget)
        (canonicalGeneratedLaws_unique
          firstLaws secondLaws)

def stepFields {P : CircularPresentation} (source : PositiveConstitution P) :
    GeneratedStep source (extendFields source) :=
  { formedByFreeLayer := rfl
    laws :=
      { compatibility := stepCompatibleAt source.1
        compatibilityIsCanonical := rfl
        preservesProvenance :=
          { targetIsCanonical := rfl
            integrated :=
              { layer :=
                  { core :=
                      { formationTerm := .admissible (successorCompatibleExplicitation source.1)
                        formationTermIsSuccessor := rfl
                        integratedClosureObstruction := source.2.1.1.inheritedClosureObstruction
                        integratedClosureObstructionIsCurrent := rfl
                        integratedProvenance := provenanceAtCursor source.1
                        integratedProvenanceIsCurrent := rfl } }
                targetIsFormation := rfl } }
        integratesClosureObstruction :=
          { integratedByFormation := rfl, inheritedByTarget := rfl }
        continuesDifference := { targetBoundaryIsNext := rfl }
        freshBoundaryDifference :=
          { continuation := { targetBoundaryIsNext := rfl }
            freshRecord := .current
            freshRecordIsCurrent := rfl
            notPreservedOld := by intro old same; cases same } } }

inductive Code where
  | root
  | step (prior : Code) (endpoint : Tree)
deriving DecidableEq

def captureHistory {P : CircularPresentation} :
    {target : PositiveConstitution P} →
      GeneratedHistory (initialPositive P) target → Code
  | _, .root => .root
  | target, .extend prior _step => .step (captureHistory prior) (FoundationPortable.capture target)

def capture {P : CircularPresentation} (value : RootedGeneratedHistory P) : Code :=
  captureHistory value.history

def restoreCode (P : CircularPresentation) : Code → Option (RootedGeneratedHistory P)
  | .root => some ⟨initialPositive P, .root⟩
  | .step prior endpoint => do
      let before ← restoreCode P prior
      if same : endpoint = .formed (FoundationPortable.capture before.endpoint) then
        let target := FoundationPortable.materialize P endpoint
        have targetExact : target = extendFields before.endpoint := by
          unfold target
          rw [same]
          change extendFields (materialize P (FoundationPortable.capture before.endpoint)) = _
          rw [FoundationPortable.capture_exact]
        return ⟨target, .extend before.history (targetExact.symm ▸ stepFields before.endpoint)⟩
      else none

theorem appended_exact {P : CircularPresentation} (before : RootedGeneratedHistory P)
    (stored target : PositiveConstitution P)
    (fields : stored = extendFields before.endpoint)
    (original : GeneratedStep before.endpoint target) (same : stored = target) :
    (⟨stored, .extend before.history (fields.symm ▸ stepFields before.endpoint)⟩ :
      RootedGeneratedHistory P) = ⟨target, .extend before.history original⟩ := by
  cases same
  exact congrArg (fun step => (⟨stored, .extend before.history step⟩ : RootedGeneratedHistory P))
    (generatedStep_unique _ original)

theorem history_exact {P : CircularPresentation} {target : PositiveConstitution P}
    (history : GeneratedHistory (initialPositive P) target) :
    restoreCode P (captureHistory history) = some ⟨target, history⟩ := by
  induction history with
  | root => rfl
  | @extend source target prior step ih =>
      rw [captureHistory, restoreCode, ih]
      dsimp only [Bind.bind, Option.bind]
      have fields : target = extendFields source := step.formedByFreeLayer
      cases fields
      have codeExact : FoundationPortable.capture (extendFields source) =
          Tree.formed (FoundationPortable.capture source) := rfl
      rw [dif_pos codeExact]
      apply congrArg some
      exact appended_exact ⟨source, prior⟩ _ _
        (FoundationPortable.capture_exact (extendFields source)) step
        (FoundationPortable.capture_exact (extendFields source))

theorem capture_exact {P : CircularPresentation} (value : RootedGeneratedHistory P) :
    restoreCode P (capture value) = some value := history_exact value.history

def words : Code → Words
  | .root => [0]
  | .step prior endpoint => 1 :: (words prior ++ treeCodec.words endpoint)

def read : Words → Option (Code × Words)
  | [] => none
  | word :: tail => match word with
    | .negSucc _ => none
    | .ofNat tag => match tag with
      | 0 => some (.root, tail)
      | 1 => do
          let (prior, rest) ← read tail
          let (endpoint, last) ← treeCodec.read rest
          return (.step prior endpoint, last)
      | _ + 2 => none

theorem words_exact (code : Code) (tail : Words) :
    read (words code ++ tail) = some (code, tail) := by
  induction code generalizing tail with
  | root => rfl
  | step prior endpoint ih =>
      rw [words, List.cons_append, PortableCheckpoint.append_associative]
      change (do let (prior, rest) ← read (words prior ++ (treeCodec.words endpoint ++ tail))
                 let (endpoint, last) ← treeCodec.read rest
                 pure (Code.step prior endpoint, last)) = _
      rw [ih]
      change (do let (endpoint, last) ← treeCodec.read (treeCodec.words endpoint ++ tail)
                 pure (Code.step prior endpoint, last)) = _
      rw [treeCodec.exact]
      rfl

def codec : Codec Code := ⟨words, read, words_exact⟩
def envelope : Codec Code :=
  (natural.product (natural.product codec)).via
    (fun value => (91, 1, value))
    (fun data => match data.1 with
      | 91 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none) (fun _ => rfl)

def save {P : CircularPresentation} (value : RootedGeneratedHistory P) : List UInt8 :=
  bytes (envelope.words (capture value))
def load (input : List UInt8) : Option Code := do
  let words ← fromBytes input
  let (value, tail) ← envelope.read words
  match tail with | [] => some value | _ :: _ => none
def restore (P : CircularPresentation) (input : List UInt8) : Option (RootedGeneratedHistory P) :=
  (load input).bind (restoreCode P)

theorem byte_roundtrip {P : CircularPresentation} (value : RootedGeneratedHistory P) :
    load (save value) = some (capture value) := by
  unfold load save
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact (capture value) []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

theorem restored_exact {P : CircularPresentation} (value : RootedGeneratedHistory P) :
    restore P (save value) = some value := by
  unfold restore
  rw [byte_roundtrip]
  exact capture_exact value

theorem all_consumers {P : CircularPresentation} (value : RootedGeneratedHistory P)
    {Result : Type u} (future : RootedGeneratedHistory P → Result) :
    (restore P (save value)).map future = some (future value) := by
  rw [restored_exact]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.freeKCore_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.freeK_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.integrates_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.preservesProvenance_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.integratesClosureObstruction_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.continuesDifference_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.freshBoundaryDifference_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.canonicalGeneratedLaws_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.generatedStep_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.stepFields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.Code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.captureHistory
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.restoreCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.appended_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.history_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.capture_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.words
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.words_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.codec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.HistoryPortable.all_consumers
/- AXIOM_AUDIT_END -/
