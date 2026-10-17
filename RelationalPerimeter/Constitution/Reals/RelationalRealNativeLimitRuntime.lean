import RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Constitutive limits of native families

The rich context owns one archive per native term. A request executes its
diagonal once, groups that owned Step, installs the action's target, and updates
only that diagonal's archive. The numeric live contract forgets this bank and
history by fixed-precision uniformity, not by identifying archives. Its kernel
executes compact term environments from explicitly projected initial memory;
it never calls the rich executor or a presentation/readout.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy
open StrongPerimetralTurning ConstitutiveRuntime ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy

variable {P : CircularPresentation} {baseDepth : Nat}

structure NativeTermKernel where
  environment : LiveEnvironment
  initial : environment.Memory

/- The two generators are separate executable inputs. Kernel callbacks expose
only LiveEnvironment and projected memory, not a Service/Real/archive. No
physical claim is made about hidden captures of an arbitrary received callback. -/
structure NativeCauchyFamily (P : CircularPresentation) (baseDepth : Nat) where
  terms : Nat → Real P baseDepth
  kernels : Nat → NativeTermKernel
  kernelExact : (n p : Nat) → {archive : (environment (terms n)).Archive} →
    (step : Step (environment (terms n)) archive p) →
    step.code = (kernels n).environment.answer
      (((kernels n).environment.step (kernels n).initial p).event)
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q →
    PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) →
    {aa : (environment (terms n)).Archive} → {ba : (environment (terms m)).Archive} →
    (first : Step (environment (terms n)) aa r) →
    (second : Step (environment (terms m)) ba s) →
    PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension p r → PrecisionExtension p s → Near p first.code second.code

abbrev ContextBank (family : NativeCauchyFamily P baseDepth) :=
  (n : Nat) → (environment (family.terms n)).Archive

def initialBank (family : NativeCauchyFamily P baseDepth) : ContextBank family :=
  fun n => (environment (family.terms n)).initialArchive

/-- Only transport along equality of the term index; no archive is identified. -/
def updateBank {family : NativeCauchyFamily P baseDepth} (bank : ContextBank family)
    (n : Nat) (next : (environment (family.terms n)).Archive) : ContextBank family :=
  fun k => if h : k = n then h ▸ next else bank k

theorem updateBank_hit {family : NativeCauchyFamily P baseDepth} (bank : ContextBank family)
    (n : Nat) (next : (environment (family.terms n)).Archive) : updateBank bank n next n = next := by
  unfold updateBank
  exact dif_pos rfl

theorem updateBank_other {family : NativeCauchyFamily P baseDepth} (bank : ContextBank family)
    (n k : Nat) (next : (environment (family.terms n)).Archive) (h : k ≠ n) :
    updateBank bank n next k = bank k := by
  unfold updateBank
  exact dif_neg h

structure NativeSourceAction {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {p : Nat} (searched : Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p) where
  private mk ::
  step : Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p
  stepExact : step = searched

structure NativeSourceStored {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {p : Nat} {searched : Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p}
    (acted : NativeSourceAction searched) where
  private mk ::
  action : NativeSourceAction searched
  actionExact : action = acted

structure NativeSourceContext (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family) (p : Nat) where
  private mk ::
  archive : (environment (family.terms (family.modulus p))).Archive
  archiveExact : archive = bank (family.modulus p)

/-- The equality only reindexes the Step's archive parameter. Execution reads
the received archive field, not a separately captured bank entry. -/
def searchNativeSource {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family} {p : Nat}
    (context : NativeSourceContext family bank p) :
    Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p :=
  let step := executeAt (family.terms (family.modulus p)) context.archive p
  context.archiveExact ▸ step

/-- Search, rather than a numerical projection, produces the native resource. -/
def nativeSourceProgram (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family)
    (p : Nat) : Program Unit where
  ReceivedContext _ := NativeSourceContext family bank p
  SearchResult _ := Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p
  ActionResult _ searched := NativeSourceAction searched
  Accepted _ _ _ := Unit
  Authorization _ _ _ _ := Unit
  Decomposition _ searched acted _ _ := NativeSourceAction searched
  Continuation _ searched _ _ _ _ := NativeSourceAction searched
  Stored _ _ acted := NativeSourceStored acted
  stamp _ := .source (family.modulus p) p
  receive _ := ⟨bank (family.modulus p), rfl⟩
  search _ context := searchNativeSource context
  act _ searched := ⟨searched, rfl⟩
  preserves _ _ _ := ()
  authorize _ _ _ _ := ()
  decompose _ _ acted _ _ := acted
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.step.code
  read stored := stored.action.step.code
  readStoredExact stored := congrArg (fun action => action.step.code) stored.actionExact

abbrev NativeSourceExecution (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family)
    (journal : Journal P baseDepth) (p : Nat) := ExecutedRequest (nativeSourceProgram family bank p) P journal ()

def NativeSourceExecution.diagonal {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    Step (environment (family.terms (family.modulus p))) (bank (family.modulus p)) p :=
  source.memory.stored.action.step

theorem NativeSourceExecution.diagonalExact {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    source.diagonal = executeAt (family.terms (family.modulus p)) (bank (family.modulus p)) p := by
  change source.memory.stored.action.step = _
  rw [source.memory.stored.actionExact]
  change source.action.step = _
  rw [source.action.stepExact]
  rw [source.searchResult_is_receivedContextOutput, source.receivedContext_is_produced]
  rfl

def nativeSpecification {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    LocalGrouping.Specification where
  Source := Unit
  precision := p
  sourceCode _ := source.diagonal.code
  targetCode := source.diagonal.code
  sourceNearTarget _ := family.cauchy p (family.modulus p) (family.modulus p) p p
    source.diagonal source.diagonal (.refl _) (.refl _) (.refl _) (.refl _)

def nativeNormalizationTrace {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    ConstitutiveSearch.Grouping.Trace (LocalGrouping.Step (nativeSpecification source)) (.source ()) .target := by
  rw [← LocalGrouping.normal_source (nativeSpecification source) ()]
  exact ((LocalGrouping.rules (nativeSpecification source)).normalize (.source ())).trace

def nativeNormalized {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    LocalGrouping.GroupedCharge p source.diagonal.code :=
  (LocalGrouping.acceptanceAction (nativeSpecification source)).transport
    (nativeNormalizationTrace source) (LocalGrouping.sourceCharge (nativeSpecification source) ())

theorem nativeNormalized_code {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) :
    (nativeNormalized source).outputCode = source.diagonal.code := by
  have exactCharge := LocalGrouping.action_coherent (nativeSpecification source)
    (nativeNormalizationTrace source) (ConstitutiveSearch.Grouping.Trace.one
      (LocalGrouping.Step.group (specification := nativeSpecification source) ()))
    (LocalGrouping.sourceCharge (nativeSpecification source) ())
  change (nativeNormalized source).outputCode = _
  unfold nativeNormalized
  rw [exactCharge]
  rfl

structure NativeTarget {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) where
  private mk ::
  normalized : LocalGrouping.GroupedCharge p source.diagonal.code
  normalizedExact : normalized = nativeNormalized source

def NativeTarget.code {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} {source : NativeSourceExecution family bank journal p}
    (target : NativeTarget source) : SignedDyadicCode := target.normalized.outputCode

theorem NativeTarget.codeExact {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} {source : NativeSourceExecution family bank journal p}
    (target : NativeTarget source) : target.code = source.diagonal.code := by
  unfold code
  rw [target.normalizedExact]
  exact nativeNormalized_code source

structure NativeGroupingAction {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (searched : NativeSourceExecution family bank journal p) where
  private mk ::
  source : NativeSourceExecution family bank journal p
  sourceExact : source = searched
  target : NativeTarget source

structure NativeGroupingStored {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} {searched : NativeSourceExecution family bank journal p}
    (acted : NativeGroupingAction searched) where
  private mk ::
  action : NativeGroupingAction searched
  actionExact : action = acted

/-- The action consumes the searched execution itself; request carries no target. -/
def nativeGroupingProgram {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (source : NativeSourceExecution family bank journal p) : Program Unit where
  ReceivedContext _ := NativeSourceExecution family bank journal p
  SearchResult _ := NativeSourceExecution family bank journal p
  ActionResult _ searched := NativeGroupingAction searched
  Accepted _ _ acted := Near p acted.source.diagonal.code acted.target.code
  Authorization _ _ _ _ := Unit
  Decomposition _ searched _ _ _ := NativeGroupingAction searched
  Continuation _ searched _ _ _ _ := NativeGroupingAction searched
  Stored _ _ acted := NativeGroupingStored acted
  stamp _ := .limit p
  receive _ := source
  search _ received := received
  act _ searched := ⟨searched, rfl, ⟨nativeNormalized searched, rfl⟩⟩
  preserves _ _ acted := LimitGrouping.transportNear
    (by rw [acted.target.normalizedExact]; unfold nativeNormalized
        have h := LocalGrouping.action_coherent (nativeSpecification acted.source)
          (nativeNormalizationTrace acted.source) (ConstitutiveSearch.Grouping.Trace.one
            (LocalGrouping.Step.group (specification := nativeSpecification acted.source) ()))
          (LocalGrouping.sourceCharge (nativeSpecification acted.source) ())
        rw [h]; rfl)
    acted.target.codeExact.symm acted.target.normalized.consumedNearTarget
  authorize _ _ _ _ := ()
  decompose _ _ acted _ _ := acted
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.target.code
  read stored := stored.action.target.code
  readStoredExact stored := congrArg (fun action => action.target.code) stored.actionExact

structure NativeLimitProduction (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family)
    (journal : Journal P baseDepth) (p : Nat) where
  private mk ::
  source : NativeSourceExecution family bank journal p
  grouping : ExecutedRequest (nativeGroupingProgram source) P source.completedJournal ()

def produceNativeLimit (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family)
    (journal : Journal P baseDepth) (p : Nat) : NativeLimitProduction family bank journal p :=
  let source := execute (nativeSourceProgram family bank p) P journal ()
  let grouped := execute (nativeGroupingProgram source) P source.completedJournal ()
  ⟨source, grouped⟩

def NativeLimitProduction.diagonal {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (production : NativeLimitProduction family bank journal p) :=
  production.source.diagonal

def NativeLimitProduction.code {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (production : NativeLimitProduction family bank journal p) :=
  production.grouping.memory.stored.action.target.code

theorem NativeLimitProduction.groupedSourceExact {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (production : NativeLimitProduction family bank journal p) :
    production.grouping.memory.stored.action.source = production.source := by
  rw [production.grouping.memory.stored.actionExact]
  change production.grouping.action.source = _
  rw [production.grouping.action.sourceExact,
    production.grouping.searchResult_is_receivedContextOutput,
    production.grouping.receivedContext_is_produced]
  rfl

theorem NativeLimitProduction.codeExact {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (production : NativeLimitProduction family bank journal p) :
    production.code = production.diagonal.code := by
  change production.grouping.memory.stored.action.target.code = _
  rw [production.grouping.memory.stored.action.target.codeExact,
    production.grouping.memory.stored.actionExact]
  change production.grouping.action.source.diagonal.code = _
  rw [production.grouping.action.sourceExact,
    production.grouping.searchResult_is_receivedContextOutput,
    production.grouping.receivedContext_is_produced]
  rfl

abbrev RetainedNativeLimit (family : NativeCauchyFamily P baseDepth) :=
  (bank : ContextBank family) × (journal : Journal P baseDepth) × (p : Nat) × NativeLimitProduction family bank journal p

structure NativeArchive (family : NativeCauchyFamily P baseDepth) where
  private mk ::
  bank : ContextBank family
  journal : Journal P baseDepth
  retained : List (RetainedNativeLimit family)
  installed : Option (RetainedNativeLimit family)

/-- Receive an explicit native context bank without fabricating retained or
installed output. Every nonempty history must then be produced by nativeNext. -/
def seedNativeArchive (family : NativeCauchyFamily P baseDepth) (bank : ContextBank family) :
    NativeArchive family :=
  ⟨bank, Journal.root P baseDepth, [], none⟩

def readNativeInstalled {family : NativeCauchyFamily P baseDepth} (archive : NativeArchive family) : Option SignedDyadicCode :=
  archive.installed.map (fun retained => retained.2.2.2.code)

def nativeNext {family : NativeCauchyFamily P baseDepth} (archive : NativeArchive family) {p : Nat}
    (production : NativeLimitProduction family archive.bank archive.journal p) : NativeArchive family :=
  let retained : RetainedNativeLimit family := ⟨archive.bank, archive.journal, p, production⟩
  ⟨updateBank archive.bank (family.modulus p) production.diagonal.next,
    production.grouping.completedJournal, archive.retained ++ [retained], some retained⟩

theorem nativeNext_bank {family : NativeCauchyFamily P baseDepth} (archive : NativeArchive family) {p : Nat}
    (production : NativeLimitProduction family archive.bank archive.journal p) :
    (nativeNext archive production).bank (family.modulus p) = production.diagonal.next :=
  updateBank_hit _ _ _

theorem nativeNext_installed {family : NativeCauchyFamily P baseDepth} (archive : NativeArchive family) {p : Nat}
    (production : NativeLimitProduction family archive.bank archive.journal p) :
    (nativeNext archive production).installed = some ⟨archive.bank, archive.journal, p, production⟩ := rfl

theorem nativeNext_read {family : NativeCauchyFamily P baseDepth} (archive : NativeArchive family) {p : Nat}
    (production : NativeLimitProduction family archive.bank archive.journal p) :
    readNativeInstalled (nativeNext archive production) = some production.code := rfl

structure NativeRichEvent (family : NativeCauchyFamily P baseDepth) where
  archive : NativeArchive family
  precision : Nat
  production : NativeLimitProduction family archive.bank archive.journal precision

/-- A convenience adapter, not a guarantee about the physical captures of its
generator. The service's live closure receives kernels, never this adapter. -/
def nativeTermKernel (real : Real P baseDepth) : NativeTermKernel :=
  ⟨(environment real).liveEnvironment, (environment real).project (environment real).initialArchive⟩

def nativeLiveStep (kernels : Nat → NativeTermKernel) (modulus : Nat → Nat)
    (_memory : Option SignedDyadicCode) (p : Nat) : LiveStep (Option SignedDyadicCode) SignedDyadicCode :=
  let kernel := kernels (modulus p)
  let response := kernel.environment.step kernel.initial p
  let code := kernel.environment.answer response.event
  ⟨some code, code⟩

/-- Proposition-level uniformity may form a canonical reference. This is not
an additional native production of the rich route, nor a compiled-cost claim. -/
theorem nativeStep_liveCode (real : Real P baseDepth) (p : Nat)
    {archive : (environment real).Archive} (step : Step (environment real) archive p) :
    step.code = (nativeTermKernel real).environment.answer
      (((nativeTermKernel real).environment.step (nativeTermKernel real).initial p).event) := by
  have h := (canonicalStep (environment real) p).answerProjection
  rw [(canonicalStep (environment real) p).eventProjection] at h
  exact (currentReadout real archive p step).trans h.symm

/-- This derived adapter preserves every mathematical native family. Its
kernel-generator callback may capture terms; that boundary is explicit, not
a physical-compaction theorem. Concrete clients may supply separated kernels. -/
def NativeCauchyFamily.ofTerms (terms : Nat → Real P baseDepth) (modulus : Nat → Nat)
    (monotone : {p q : Nat} → PrecisionExtension p q → PrecisionExtension (modulus p) (modulus q))
    (law : (p n m r s : Nat) →
      {aa : (environment (terms n)).Archive} → {ba : (environment (terms m)).Archive} →
      (first : Step (environment (terms n)) aa r) → (second : Step (environment (terms m)) ba s) →
      PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
      PrecisionExtension p r → PrecisionExtension p s → Near p first.code second.code) : NativeCauchyFamily P baseDepth where
  terms := terms
  kernels n := nativeTermKernel (terms n)
  kernelExact n p := fun {archive} step => nativeStep_liveCode (terms n) p step
  modulus := modulus
  modulusMonotone := monotone
  cauchy := law

theorem NativeLimitProduction.liveCode {family : NativeCauchyFamily P baseDepth} {bank : ContextBank family}
    {journal : Journal P baseDepth} {p : Nat} (production : NativeLimitProduction family bank journal p) :
    production.code = (nativeLiveStep family.kernels family.modulus none p).event :=
  production.codeExact.trans (family.kernelExact _ p production.diagonal)

def nativeEnvironment (family : NativeCauchyFamily P baseDepth) : Service P baseDepth where
  Archive := NativeArchive family
  Memory := Option SignedDyadicCode
  Event := SignedDyadicCode
  RichEvent := NativeRichEvent family
  Read := Option SignedDyadicCode
  Resource archive p := NativeLimitProduction family archive.bank archive.journal p
  initialArchive := seedNativeArchive family (initialBank family)
  execute archive p := produceNativeLimit family archive.bank archive.journal p
  next := nativeNext _
  richEvent {archive} {precision} production := ⟨archive, precision, production⟩
  code production := production.code
  readArchive := readNativeInstalled
  project := readNativeInstalled
  projectEvent event := event.production.code
  readLive := id
  liveStep := nativeLiveStep family.kernels family.modulus
  answer := id
  nextExact archive p := congrArg some (produceNativeLimit family archive.bank archive.journal p).liveCode
  eventExact archive p := (produceNativeLimit family archive.bank archive.journal p).liveCode
  readExact _ := rfl
  answerExact _ := rfl
  separates _ _ _ readExact _ := readExact

def nativeCoherent (family : NativeCauchyFamily P baseDepth) : Coherent (nativeEnvironment family) where
  near := by
    intro aa ba p r s first second hr hs
    exact LimitGrouping.transportNear first.resource.codeExact.symm second.resource.codeExact.symm
      (family.cauchy p (family.modulus r) (family.modulus s) r s
        first.resource.diagonal second.resource.diagonal
        (family.modulusMonotone hr) (family.modulusMonotone hs) hr hs)

def nativeCertificate (family : NativeCauchyFamily P baseDepth) : CertifiedService P baseDepth where
  service := nativeEnvironment family
  coherence := nativeCoherent family
  uniform archive p step :=
    step.resource.liveCode.trans (canonicalStep (nativeEnvironment family) p).resource.liveCode.symm

def nativeLimit (family : NativeCauchyFamily P baseDepth) : Real P baseDepth := .certified (nativeCertificate family)

end RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeCauchyFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.ContextBank
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.initialBank
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.updateBank
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.updateBank_hit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.updateBank_other
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceAction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceStored
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceContext
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.searchNativeSource
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeSourceProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceExecution
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceExecution.diagonal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeSourceExecution.diagonalExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeSpecification
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNormalizationTrace
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNormalized
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNormalized_code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeTarget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeTarget.code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeTarget.codeExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeGroupingAction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeGroupingStored
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeGroupingProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.produceNativeLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction.diagonal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction.code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction.groupedSourceExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction.codeExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.RetainedNativeLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.seedNativeArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.readNativeInstalled
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNext
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNext_bank
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNext_installed
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeNext_read
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeTermKernel
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeTermKernel
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeStep_liveCode
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeCauchyFamily.ofTerms
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeLimitProduction.liveCode
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeCoherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeCertificate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeLimit
/- AXIOM_AUDIT_END -/
