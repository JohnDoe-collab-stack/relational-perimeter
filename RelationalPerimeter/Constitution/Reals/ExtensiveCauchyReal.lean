import RelationalPerimeter.Constitution.Reals.RegularDyadicNameOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals
namespace ExtensiveCauchyReal

/-- A saturated inhabited class. Its global inhabitance is deliberately truncated. -/
structure Value where
  Contains : RegularDyadicName → Type
  inhabited : Nonempty (Σ name, Contains name)
  saturated : {a b : RegularDyadicName} → NameEquivalent a b → Contains a → Contains b
  coherent : {a b : RegularDyadicName} → Contains a → Contains b → NameEquivalent a b

structure ExternalEquivalent (x y : Value) where
  forward : (name : RegularDyadicName) → x.Contains name → y.Contains name
  backward : (name : RegularDyadicName) → y.Contains name → x.Contains name

namespace ExternalEquivalent
def refl (x : Value) : ExternalEquivalent x x := ⟨fun _ h => h, fun _ h => h⟩
def symm {x y : Value} (h : ExternalEquivalent x y) : ExternalEquivalent y x :=
  ⟨h.backward, h.forward⟩
def trans {x y z : Value} (h : ExternalEquivalent x y) (k : ExternalEquivalent y z) :
    ExternalEquivalent x z :=
  ⟨fun n m => k.forward n (h.forward n m), fun n m => h.backward n (k.backward n m)⟩
end ExternalEquivalent

def classOf (name : RegularDyadicName) : Value where
  Contains := NameEquivalent name
  inhabited := ⟨⟨name, NameEquivalent.refl name⟩⟩
  saturated := fun h m => NameEquivalent.trans m h
  coherent := fun a b => NameEquivalent.trans (NameEquivalent.symm a) b

def classOfContains (name : RegularDyadicName) : (classOf name).Contains name :=
  NameEquivalent.refl name

def classOfPreserves {a b : RegularDyadicName} (same : NameEquivalent a b) :
    ExternalEquivalent (classOf a) (classOf b) :=
  ⟨fun _ m => NameEquivalent.trans (NameEquivalent.symm same) m,
   fun _ m => NameEquivalent.trans same m⟩

def classOfReflects {a b : RegularDyadicName}
    (same : ExternalEquivalent (classOf a) (classOf b)) : NameEquivalent a b :=
  same.backward b (classOfContains b)

def memberClassEquivalent (value : Value) (name : RegularDyadicName)
    (member : value.Contains name) : ExternalEquivalent (classOf name) value :=
  ⟨fun _ same => value.saturated same member, fun _ m => value.coherent member m⟩

theorem classOfSurjective (value : Value) :
    Nonempty (Σ name, ExternalEquivalent (classOf name) value) := by
  obtain ⟨⟨name, member⟩⟩ := value.inhabited
  exact ⟨⟨name, memberClassEquivalent value name member⟩⟩

def SetoidEquivalent (x y : Value) : Prop := Nonempty (ExternalEquivalent x y)

universe u v w z g h i j

structure PositiveSetoid where
  Carrier : Type u
  Equivalent : Carrier → Carrier → Type v
  equivalentRefl : (x : Carrier) → Equivalent x x
  equivalentSymm : {x y : Carrier} → Equivalent x y → Equivalent y x
  equivalentTrans : {x y z : Carrier} → Equivalent x y → Equivalent y z → Equivalent x z

structure RelationalMorphism (X : PositiveSetoid.{u,v}) (Y : PositiveSetoid.{w,z}) where
  Graph : X.Carrier → Y.Carrier → Type g
  total : (x : X.Carrier) → Nonempty (Σ y, Graph x y)
  stableSource : {x x' : X.Carrier} → {y : Y.Carrier} → X.Equivalent x x' → Graph x y → Graph x' y
  stableTarget : {x : X.Carrier} → {y y' : Y.Carrier} → Graph x y → Y.Equivalent y y' → Graph x y'
  singleValued : {x : X.Carrier} → {y z : Y.Carrier} → Graph x y → Graph x z → Y.Equivalent y z

namespace RelationalMorphism
def PointwiseEquivalent {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) (G : RelationalMorphism.{u,v,w,z,h} X Y) :
    Sort (max u w z g h + 1) :=
  (x : X.Carrier) → (y z : Y.Carrier) → F.Graph x y → G.Graph x z → Y.Equivalent y z

def identity (X : PositiveSetoid.{u,v}) : RelationalMorphism X X where
  Graph := X.Equivalent
  total := fun x => ⟨⟨x, X.equivalentRefl x⟩⟩
  stableSource := fun h m => X.equivalentTrans (X.equivalentSymm h) m
  stableTarget := X.equivalentTrans
  singleValued := fun a b => X.equivalentTrans (X.equivalentSymm a) b

def compose {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    {Z : PositiveSetoid.{i,j}} (F : RelationalMorphism.{u,v,w,z,g} X Y)
    (G : RelationalMorphism.{w,z,i,j,h} Y Z) : RelationalMorphism X Z where
  Graph := fun x z => Σ y, F.Graph x y × G.Graph y z
  total := by
    intro x
    obtain ⟨⟨y, fy⟩⟩ := F.total x
    obtain ⟨⟨z, gz⟩⟩ := G.total y
    exact ⟨⟨z, ⟨y, fy, gz⟩⟩⟩
  stableSource := fun same ⟨y, fy, gy⟩ => ⟨y, F.stableSource same fy, gy⟩
  stableTarget := fun ⟨y, fy, gy⟩ same => ⟨y, fy, G.stableTarget gy same⟩
  singleValued := fun ⟨y, fy, gy⟩ ⟨y', fy', gy'⟩ =>
    G.singleValued (G.stableSource (F.singleValued fy fy') gy) gy'

def identityLeft {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) : PointwiseEquivalent (compose (identity X) F) F :=
  fun _ _ _ ⟨_, same, graph⟩ other =>
    F.singleValued (F.stableSource (X.equivalentSymm same) graph) other

def identityRight {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) : PointwiseEquivalent (compose F (identity Y)) F :=
  fun _ _ _ ⟨_, graph, same⟩ other => F.singleValued (F.stableTarget graph same) other

def composeAssoc {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    {Z : PositiveSetoid.{i,j}} {W : PositiveSetoid}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) (G : RelationalMorphism.{w,z,i,j,h} Y Z)
    (H : RelationalMorphism Z W) : PointwiseEquivalent (compose (compose F G) H) (compose F (compose G H)) :=
  fun _ _ _ first ⟨middle, f, ⟨next, g, h⟩⟩ =>
    (compose (compose F G) H).singleValued first ⟨next, ⟨middle, f, g⟩, h⟩
end RelationalMorphism

def ValuePositiveSetoid : PositiveSetoid where
  Carrier := Value
  Equivalent := ExternalEquivalent
  equivalentRefl := ExternalEquivalent.refl
  equivalentSymm := ExternalEquivalent.symm
  equivalentTrans := ExternalEquivalent.trans

def ConventionalRegularCauchyReference : PositiveSetoid where
  Carrier := RegularDyadicName
  Equivalent := NameEquivalent
  equivalentRefl := NameEquivalent.refl
  equivalentSymm := NameEquivalent.symm
  equivalentTrans := NameEquivalent.trans

def ReferenceRealizes (name : RegularDyadicName) (value : Value) : Type := value.Contains name

def referenceCoverage (name : RegularDyadicName) : Σ value, ReferenceRealizes name value :=
  ⟨classOf name, classOfContains name⟩

theorem valueReferenceCoverage (value : Value) :
    Nonempty (Σ name, ReferenceRealizes name value) := value.inhabited

def referenceRealizesStable {a b : RegularDyadicName} {value : Value}
    (same : NameEquivalent a b) (member : ReferenceRealizes a value) : ReferenceRealizes b value :=
  value.saturated same member

def referenceCorrect {a b : RegularDyadicName} {x y : Value} (same : NameEquivalent a b)
    (ha : ReferenceRealizes a x) (hb : ReferenceRealizes b y) : ExternalEquivalent x y :=
  (memberClassEquivalent x a ha).symm.trans
    ((classOfPreserves same).trans (memberClassEquivalent y b hb))

def referenceFaithful {a b : RegularDyadicName} {x y : Value} (same : ExternalEquivalent x y)
    (ha : ReferenceRealizes a x) (hb : ReferenceRealizes b y) : NameEquivalent a b :=
  y.coherent (same.forward a ha) hb

def RespectsNameEquivalent {Y : PositiveSetoid.{u,v}} (f : RegularDyadicName → Y.Carrier) :=
  {a b : RegularDyadicName} → NameEquivalent a b → Y.Equivalent (f a) (f b)

structure ClassDescent {Y : PositiveSetoid.{u,v}} (f : RegularDyadicName → Y.Carrier)
    (value : Value) (y : Y.Carrier) where
  name : RegularDyadicName
  member : value.Contains name
  agrees : Y.Equivalent (f name) y

def classDescent {Y : PositiveSetoid.{u,v}} (f : RegularDyadicName → Y.Carrier)
    (respects : RespectsNameEquivalent f) : RelationalMorphism ValuePositiveSetoid Y where
  Graph := ClassDescent f
  total := by
    intro value
    obtain ⟨⟨name, member⟩⟩ := value.inhabited
    exact ⟨⟨f name, ⟨name, member, Y.equivalentRefl _⟩⟩⟩
  stableSource := fun same d => ⟨d.name, same.forward d.name d.member, d.agrees⟩
  stableTarget := fun d same => ⟨d.name, d.member, Y.equivalentTrans d.agrees same⟩
  singleValued := fun {value} {y} {z} a b => Y.equivalentTrans (Y.equivalentSymm a.agrees)
    (Y.equivalentTrans (respects (value.coherent a.member b.member)) b.agrees)

def ExtendsNameMap {Y : PositiveSetoid.{u,v}} (f : RegularDyadicName → Y.Carrier)
    (M : RelationalMorphism ValuePositiveSetoid Y) :=
  (name : RegularDyadicName) → M.Graph (classOf name) (f name)

def classDescentExtends {Y : PositiveSetoid.{u,v}} (f : RegularDyadicName → Y.Carrier)
    (respects : RespectsNameEquivalent f) : ExtendsNameMap f (classDescent f respects) :=
  fun name => ⟨name, classOfContains name, Y.equivalentRefl _⟩

def classDescentOnClass {Y : PositiveSetoid.{u,v}} {f : RegularDyadicName → Y.Carrier}
    (respects : RespectsNameEquivalent f) {name : RegularDyadicName} {y : Y.Carrier}
    (d : ClassDescent f (classOf name) y) : Y.Equivalent (f name) y :=
  Y.equivalentTrans (respects d.member) d.agrees

def classDescentOnClassBack {Y : PositiveSetoid.{u,v}} {f : RegularDyadicName → Y.Carrier}
    {name : RegularDyadicName} {y : Y.Carrier} (same : Y.Equivalent (f name) y) :
    ClassDescent f (classOf name) y := ⟨name, classOfContains name, same⟩

def classDescentUnique {Y : PositiveSetoid.{u,v}} {f : RegularDyadicName → Y.Carrier}
    (respects : RespectsNameEquivalent f) (M : RelationalMorphism ValuePositiveSetoid Y)
    (extension : ExtendsNameMap f M) :
    RelationalMorphism.PointwiseEquivalent (classDescent f respects) M :=
  fun value y z d graph => Y.equivalentTrans (Y.equivalentSymm d.agrees)
    (M.singleValued (M.stableSource (memberClassEquivalent value d.name d.member)
      (extension d.name)) graph)

structure UnaryMember (op : RegularDyadicName → RegularDyadicName) (x : Value)
    (name : RegularDyadicName) where
  source : RegularDyadicName
  member : x.Contains source
  agrees : NameEquivalent (op source) name

structure BinaryMember (op : RegularDyadicName → RegularDyadicName → RegularDyadicName)
    (x y : Value) (name : RegularDyadicName) where
  left : RegularDyadicName
  right : RegularDyadicName
  leftMember : x.Contains left
  rightMember : y.Contains right
  agrees : NameEquivalent (op left right) name

def unaryValue (op : RegularDyadicName → RegularDyadicName)
    (congr : {a b : RegularDyadicName} → NameEquivalent a b → NameEquivalent (op a) (op b))
    (x : Value) : Value where
  Contains := UnaryMember op x
  inhabited := by
    obtain ⟨⟨name, member⟩⟩ := x.inhabited
    exact ⟨⟨op name, ⟨name, member, NameEquivalent.refl _⟩⟩⟩
  saturated := fun same m => ⟨m.source, m.member, m.agrees.trans same⟩
  coherent := fun a b => a.agrees.symm.trans ((congr (x.coherent a.member b.member)).trans b.agrees)

def binaryValue (op : RegularDyadicName → RegularDyadicName → RegularDyadicName)
    (congr : {a b c d : RegularDyadicName} → NameEquivalent a c → NameEquivalent b d →
      NameEquivalent (op a b) (op c d)) (x y : Value) : Value where
  Contains := BinaryMember op x y
  inhabited := by
    obtain ⟨⟨a, ha⟩⟩ := x.inhabited
    obtain ⟨⟨b, hb⟩⟩ := y.inhabited
    exact ⟨⟨op a b, ⟨a, b, ha, hb, NameEquivalent.refl _⟩⟩⟩
  saturated := fun same m => ⟨m.left, m.right, m.leftMember, m.rightMember, m.agrees.trans same⟩
  coherent := fun a b => a.agrees.symm.trans
    ((congr (x.coherent a.leftMember b.leftMember) (y.coherent a.rightMember b.rightMember)).trans b.agrees)

def unaryValueCongr (op : RegularDyadicName → RegularDyadicName)
    (congr : {a b : RegularDyadicName} → NameEquivalent a b → NameEquivalent (op a) (op b))
    {x y : Value} (same : ExternalEquivalent x y) :
    ExternalEquivalent (unaryValue op congr x) (unaryValue op congr y) :=
  ⟨fun _ m => ⟨m.source, same.forward _ m.member, m.agrees⟩,
   fun _ m => ⟨m.source, same.backward _ m.member, m.agrees⟩⟩

def binaryValueCongr (op : RegularDyadicName → RegularDyadicName → RegularDyadicName)
    (congr : {a b c d : RegularDyadicName} → NameEquivalent a c → NameEquivalent b d →
      NameEquivalent (op a b) (op c d)) {a b c d : Value}
    (left : ExternalEquivalent a c) (right : ExternalEquivalent b d) :
    ExternalEquivalent (binaryValue op congr a b) (binaryValue op congr c d) :=
  ⟨fun _ m => ⟨m.left, m.right, left.forward _ m.leftMember, right.forward _ m.rightMember, m.agrees⟩,
   fun _ m => ⟨m.left, m.right, left.backward _ m.leftMember, right.backward _ m.rightMember, m.agrees⟩⟩

def classOfUnary (op : RegularDyadicName → RegularDyadicName)
    (congr : {a b : RegularDyadicName} → NameEquivalent a b → NameEquivalent (op a) (op b))
    (a : RegularDyadicName) : ExternalEquivalent (classOf (op a)) (unaryValue op congr (classOf a)) :=
  ⟨fun _ same => ⟨a, classOfContains a, same⟩,
   fun _ m => (congr m.member).trans m.agrees⟩

def classOfBinary (op : RegularDyadicName → RegularDyadicName → RegularDyadicName)
    (congr : {a b c d : RegularDyadicName} → NameEquivalent a c → NameEquivalent b d →
      NameEquivalent (op a b) (op c d)) (a b : RegularDyadicName) :
    ExternalEquivalent (classOf (op a b)) (binaryValue op congr (classOf a) (classOf b)) :=
  ⟨fun _ same => ⟨a, b, classOfContains a, classOfContains b, same⟩,
   fun _ m => (congr m.leftMember m.rightMember).trans m.agrees⟩

open RegularDyadicName

def dyadicValue (code : SignedDyadicCode) : Value := classOf (constantName code)
def zero : Value := classOf zeroName
def one : Value := classOf oneName
def negValue : Value → Value := unaryValue negName negNameCongr
def addValue : Value → Value → Value := binaryValue addName addNameCongr
def mulValue : Value → Value → Value := binaryValue mulName mulNameCongr

def negCongr {a b : Value} : ExternalEquivalent a b → ExternalEquivalent (negValue a) (negValue b) :=
  unaryValueCongr negName negNameCongr
def addCongr {a b c d : Value} : ExternalEquivalent a c → ExternalEquivalent b d →
    ExternalEquivalent (addValue a b) (addValue c d) := binaryValueCongr addName addNameCongr
def mulCongr {a b c d : Value} : ExternalEquivalent a c → ExternalEquivalent b d →
    ExternalEquivalent (mulValue a b) (mulValue c d) := binaryValueCongr mulName mulNameCongr

def classOfDyadic (code : SignedDyadicCode) :
    ExternalEquivalent (classOf (constantName code)) (dyadicValue code) := ExternalEquivalent.refl _
def classOfNeg (a : RegularDyadicName) :
    ExternalEquivalent (classOf (negName a)) (negValue (classOf a)) := classOfUnary negName negNameCongr a
def classOfAdd (a b : RegularDyadicName) :
    ExternalEquivalent (classOf (addName a b)) (addValue (classOf a) (classOf b)) :=
  classOfBinary addName addNameCongr a b
def classOfMul (a b : RegularDyadicName) :
    ExternalEquivalent (classOf (mulName a b)) (mulValue (classOf a) (classOf b)) :=
  classOfBinary mulName mulNameCongr a b

/-- A finite algebraic expression. Its interpretation never chooses a class member. -/
inductive Expression where
  | first | second | third | zero | one
  | neg : Expression → Expression
  | add : Expression → Expression → Expression
  | mul : Expression → Expression → Expression

def Expression.onNames (a b c : RegularDyadicName) : Expression → RegularDyadicName
  | .first => a
  | .second => b
  | .third => c
  | .zero => zeroName
  | .one => oneName
  | .neg t => negName (t.onNames a b c)
  | .add t s => addName (t.onNames a b c) (s.onNames a b c)
  | .mul t s => mulName (t.onNames a b c) (s.onNames a b c)

def Expression.onValues (a b c : Value) : Expression → Value
  | .first => a
  | .second => b
  | .third => c
  | .zero => ExtensiveCauchyReal.zero
  | .one => ExtensiveCauchyReal.one
  | .neg t => negValue (t.onValues a b c)
  | .add t s => addValue (t.onValues a b c) (s.onValues a b c)
  | .mul t s => mulValue (t.onValues a b c) (s.onValues a b c)

def Expression.exact {a b c : Value} {an bn cn : RegularDyadicName}
    (ha : a.Contains an) (hb : b.Contains bn) (hc : c.Contains cn) (t : Expression) :
    ExternalEquivalent (classOf (t.onNames an bn cn)) (t.onValues a b c) :=
  match t with
  | .first => memberClassEquivalent a an ha
  | .second => memberClassEquivalent b bn hb
  | .third => memberClassEquivalent c cn hc
  | .zero => ExternalEquivalent.refl _
  | .one => ExternalEquivalent.refl _
  | .neg t => (classOfNeg _).trans (negCongr (t.exact ha hb hc))
  | .add t s => (classOfAdd _ _).trans (addCongr (t.exact ha hb hc) (s.exact ha hb hc))
  | .mul t s => (classOfMul _ _).trans (mulCongr (t.exact ha hb hc) (s.exact ha hb hc))

/-- Finite algebraic descent eliminates global inhabitance only into `Prop`. -/
theorem expressionLaw (left right : Expression)
    (law : (a b c : RegularDyadicName) → NameEquivalent (left.onNames a b c) (right.onNames a b c))
    (a b c : Value) : SetoidEquivalent (left.onValues a b c) (right.onValues a b c) := by
  obtain ⟨⟨an, ha⟩⟩ := a.inhabited
  obtain ⟨⟨bn, hb⟩⟩ := b.inhabited
  obtain ⟨⟨cn, hc⟩⟩ := c.inhabited
  exact ⟨(left.exact ha hb hc).symm.trans
    ((classOfPreserves (law an bn cn)).trans (right.exact ha hb hc))⟩

theorem setoidEquivalentRefl (x : Value) : SetoidEquivalent x x := ⟨ExternalEquivalent.refl x⟩
theorem setoidEquivalentSymm {x y : Value} (h : SetoidEquivalent x y) : SetoidEquivalent y x := by
  obtain ⟨h⟩ := h
  exact ⟨h.symm⟩
theorem setoidEquivalentTrans {x y z : Value} (h : SetoidEquivalent x y)
    (k : SetoidEquivalent y z) : SetoidEquivalent x z := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨h.trans k⟩

theorem setoidAddCongr {a b c d : Value} (h : SetoidEquivalent a c) (k : SetoidEquivalent b d) :
    SetoidEquivalent (addValue a b) (addValue c d) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨addCongr h k⟩
theorem setoidNegCongr {a b : Value} (h : SetoidEquivalent a b) :
    SetoidEquivalent (negValue a) (negValue b) := by
  obtain ⟨h⟩ := h
  exact ⟨negCongr h⟩
theorem setoidMulCongr {a b c d : Value} (h : SetoidEquivalent a c) (k : SetoidEquivalent b d) :
    SetoidEquivalent (mulValue a b) (mulValue c d) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨mulCongr h k⟩

theorem setoidAddComm (a b : Value) : SetoidEquivalent (addValue a b) (addValue b a) :=
  expressionLaw (.add .first .second) (.add .second .first) (fun a b _ => addNameComm a b) a b zero
theorem setoidAddAssoc (a b c : Value) :
    SetoidEquivalent (addValue (addValue a b) c) (addValue a (addValue b c)) :=
  expressionLaw (.add (.add .first .second) .third) (.add .first (.add .second .third)) addNameAssoc a b c
theorem setoidZeroLeft (a : Value) : SetoidEquivalent (addValue zero a) a :=
  expressionLaw (.add .zero .first) .first (fun a _ _ => zeroNameLeft a) a zero zero
theorem setoidZeroRight (a : Value) : SetoidEquivalent (addValue a zero) a :=
  expressionLaw (.add .first .zero) .first (fun a _ _ => zeroNameRight a) a zero zero
theorem setoidNegInvolutive (a : Value) : SetoidEquivalent (negValue (negValue a)) a :=
  expressionLaw (.neg (.neg .first)) .first (fun a _ _ => negNameInvolutive a) a zero zero
theorem setoidAddInverseLeft (a : Value) : SetoidEquivalent (addValue (negValue a) a) zero :=
  expressionLaw (.add (.neg .first) .first) .zero (fun a _ _ => addNameInverseLeft a) a zero zero
theorem setoidAddInverseRight (a : Value) : SetoidEquivalent (addValue a (negValue a)) zero :=
  expressionLaw (.add .first (.neg .first)) .zero (fun a _ _ => addNameInverseRight a) a zero zero
theorem setoidNegSum (a b : Value) :
    SetoidEquivalent (negValue (addValue a b)) (addValue (negValue a) (negValue b)) :=
  expressionLaw (.neg (.add .first .second)) (.add (.neg .first) (.neg .second))
    (fun a b _ => negNameSum a b) a b zero

structure ExternalOrder (x y : Value) where
  leftName : RegularDyadicName
  rightName : RegularDyadicName
  leftMember : x.Contains leftName
  rightMember : y.Contains rightName
  accuracy : Nat
  response : Nat
  beyond : PrecisionExtension (accuracy + 3) response
  separation : StrictSeparation accuracy (leftName.approximation response) (rightName.approximation response)

def ExternalOrder.toNameOrder {x y : Value} (order : ExternalOrder x y) :
    NameOrder order.leftName order.rightName :=
  ⟨order.accuracy, order.response, order.beyond, order.separation⟩

def externalOrderFromMembers {x y : Value} {a b : RegularDyadicName}
    (left : x.Contains a) (right : y.Contains b) (order : NameOrder a b) : ExternalOrder x y :=
  ⟨a, b, left, right, order.accuracy, order.response, order.beyond, order.separation⟩

def nameOrderToExternal {a b : RegularDyadicName} (order : NameOrder a b) :
    ExternalOrder (classOf a) (classOf b) :=
  externalOrderFromMembers (classOfContains a) (classOfContains b) order

def ExternalApartness (x y : Value) : Type := ExternalOrder x y ⊕ ExternalOrder y x
def SetoidOrder (x y : Value) : Prop := Nonempty (ExternalOrder x y)
def SetoidApartness (x y : Value) : Prop := Nonempty (ExternalApartness x y)

def nameApartnessToExternal {a b : RegularDyadicName} (apart : NameApartness a b) :
    ExternalApartness (classOf a) (classOf b) :=
  match apart with
  | .inl order => .inl (nameOrderToExternal order)
  | .inr order => .inr (nameOrderToExternal order)

def transportExternalOrder {a b c d : Value} (order : ExternalOrder a b)
    (left : ExternalEquivalent a c) (right : ExternalEquivalent b d) : ExternalOrder c d :=
  { order with leftMember := left.forward _ order.leftMember, rightMember := right.forward _ order.rightMember }

def transportExternalApartness {a b c d : Value} (apart : ExternalApartness a b)
    (left : ExternalEquivalent a c) (right : ExternalEquivalent b d) : ExternalApartness c d :=
  match apart with
  | .inl order => .inl (transportExternalOrder order left right)
  | .inr order => .inr (transportExternalOrder order right left)

def externalOrderToNames {x y : Value} {a b : RegularDyadicName} (order : ExternalOrder x y)
    (ha : x.Contains a) (hb : y.Contains b) : NameOrder a b :=
  transportNameOrder order.toNameOrder (x.coherent order.leftMember ha) (y.coherent order.rightMember hb)

def externalApartnessToNames {x y : Value} {a b : RegularDyadicName} (apart : ExternalApartness x y)
    (ha : x.Contains a) (hb : y.Contains b) : NameApartness a b :=
  match apart with
  | .inl order => .inl (externalOrderToNames order ha hb)
  | .inr order => .inr (externalOrderToNames order hb ha)

def naturalValue (n : Nat) : Value := dyadicValue (DyadicDensity.naturalCode n)
def negativeNaturalValue (n : Nat) : Value := dyadicValue (DyadicDensity.negativeNaturalCode n)

structure ExternalDensityWitness (x y : Value) where
  code : SignedDyadicCode
  left : ExternalOrder x (dyadicValue code)
  right : ExternalOrder (dyadicValue code) y

def externalDensity {x y : Value} (origin : ExternalOrder x y) : ExternalDensityWitness x y :=
  let produced := nameDensity origin.toNameOrder
  ⟨produced.code,
   externalOrderFromMembers origin.leftMember (classOfContains _) produced.left,
   externalOrderFromMembers (classOfContains _) origin.rightMember produced.right⟩

structure ExternalNaturalBounds (x : Value) where
  lower : Nat
  upper : Nat
  lowerOrder : ExternalOrder (negativeNaturalValue lower) x
  upperOrder : ExternalOrder x (naturalValue upper)

def externalNaturalBoundsFromMember (value : Value) (name : RegularDyadicName)
    (member : value.Contains name) : ExternalNaturalBounds value :=
  let produced := nameNaturalBounds name
  ⟨produced.lower, produced.upper,
   externalOrderFromMembers (classOfContains _) member produced.lowerOrder,
   externalOrderFromMembers member (classOfContains _) produced.upperOrder⟩

theorem externalNaturalBounds (value : Value) : Nonempty (ExternalNaturalBounds value) := by
  obtain ⟨⟨name, member⟩⟩ := value.inhabited
  exact ⟨externalNaturalBoundsFromMember value name member⟩

theorem densityCodeExact {a b : RegularDyadicName} (origin : NameOrder a b) :
    (externalDensity (nameOrderToExternal origin)).code = (nameDensity origin).code := rfl
theorem lowerBoundExact (name : RegularDyadicName) :
    (externalNaturalBoundsFromMember (classOf name) name (classOfContains name)).lower =
      (nameNaturalBounds name).lower := rfl
theorem upperBoundExact (name : RegularDyadicName) :
    (externalNaturalBoundsFromMember (classOf name) name (classOfContains name)).upper =
      (nameNaturalBounds name).upper := rfl

theorem setoidMulComm (a b : Value) : SetoidEquivalent (mulValue a b) (mulValue b a) :=
  expressionLaw (.mul .first .second) (.mul .second .first) (fun a b _ => mulNameComm a b) a b zero
theorem setoidMulAssoc (a b c : Value) :
    SetoidEquivalent (mulValue (mulValue a b) c) (mulValue a (mulValue b c)) :=
  expressionLaw (.mul (.mul .first .second) .third) (.mul .first (.mul .second .third)) mulNameAssoc a b c
theorem setoidOneLeft (a : Value) : SetoidEquivalent (mulValue one a) a :=
  expressionLaw (.mul .one .first) .first (fun a _ _ => mulNameOneLeft a) a zero zero
theorem setoidOneRight (a : Value) : SetoidEquivalent (mulValue a one) a :=
  expressionLaw (.mul .first .one) .first (fun a _ _ => mulNameOneRight a) a zero zero
theorem setoidMulZeroLeft (a : Value) : SetoidEquivalent (mulValue zero a) zero :=
  expressionLaw (.mul .zero .first) .zero (fun a _ _ => mulNameZeroLeft a) a zero zero
theorem setoidMulZeroRight (a : Value) : SetoidEquivalent (mulValue a zero) zero :=
  expressionLaw (.mul .first .zero) .zero (fun a _ _ => mulNameZeroRight a) a zero zero
theorem setoidDistributeLeft (a b c : Value) :
    SetoidEquivalent (mulValue a (addValue b c)) (addValue (mulValue a b) (mulValue a c)) :=
  expressionLaw (.mul .first (.add .second .third)) (.add (.mul .first .second) (.mul .first .third))
    mulNameDistributeLeft a b c
theorem setoidDistributeRight (a b c : Value) :
    SetoidEquivalent (mulValue (addValue a b) c) (addValue (mulValue a c) (mulValue b c)) :=
  expressionLaw (.mul (.add .first .second) .third) (.add (.mul .first .third) (.mul .second .third))
    mulNameDistributeRight a b c
theorem setoidMulNegLeft (a b : Value) :
    SetoidEquivalent (mulValue (negValue a) b) (negValue (mulValue a b)) :=
  expressionLaw (.mul (.neg .first) .second) (.neg (.mul .first .second))
    (fun a b _ => mulNameNegLeft a b) a b zero
theorem setoidMulNegRight (a b : Value) :
    SetoidEquivalent (mulValue a (negValue b)) (negValue (mulValue a b)) :=
  expressionLaw (.mul .first (.neg .second)) (.neg (.mul .first .second))
    (fun a b _ => mulNameNegRight a b) a b zero

open DyadicReciprocal

/-- The zero class member is normalized by three separately retained fine links. -/
def zeroMemberNear (name : RegularDyadicName) (member : zero.Contains name)
    (fine response : Nat) (beyond : PrecisionExtension fine response) :
    Σ auxiliary : Nat, Near fine (name.approximation response) (name.approximation auxiliary) ×
      (Near fine (name.approximation auxiliary) (zeroName.approximation auxiliary) ×
       Near fine (zeroName.approximation auxiliary) SignedDyadicCode.zero) :=
  let same := member.symm
  let auxiliary := fine + same.responseThreshold fine
  ⟨auxiliary,
   name.coherent fine response auxiliary beyond (.first _ _),
   same.near fine auxiliary auxiliary (.second _ _) (.second _ _),
   (constantNameSameValue SignedDyadicCode.zero auxiliary).toNear fine⟩

def externalNegativeDomain {x : Value} (order : ExternalOrder x zero) :
    ReciprocalNameDomain order.leftName where
  direction := .negative
  away := order.accuracy + 2
  nonzero p :=
    let links := zeroMemberNear order.rightName order.rightMember (order.accuracy + 3)
      order.response order.beyond
    fromNegativeMargin (strengthenSeparationThreeLinks order.separation
      (order.leftName.coherent _ _ _ order.beyond (inverseSourceBeyond order.accuracy p))
      (Near.refl _ _) (Near.refl _ _)
      links.2.1 links.2.2.1 links.2.2.2)

def externalPositiveDomain {x : Value} (order : ExternalOrder zero x) :
    ReciprocalNameDomain order.rightName where
  direction := .positive
  away := order.accuracy + 2
  nonzero p :=
    let links := zeroMemberNear order.leftName order.leftMember (order.accuracy + 3)
      order.response order.beyond
    fromPositiveMargin (strengthenSeparationThreeLinks order.separation
      links.2.1 links.2.2.1 links.2.2.2
      (order.rightName.coherent _ _ _ order.beyond (inverseSourceBeyond order.accuracy p))
      (Near.refl _ _) (Near.refl _ _))

structure ExternalInversePresentation (x : Value) where
  name : RegularDyadicName
  member : x.Contains name
  domain : ReciprocalNameDomain name

def externalInversePresentation {x : Value} (apart : ExternalApartness x zero) :
    ExternalInversePresentation x :=
  match apart with
  | .inl order => ⟨order.leftName, order.leftMember, externalNegativeDomain order⟩
  | .inr order => ⟨order.rightName, order.rightMember, externalPositiveDomain order⟩

def externalInverse (x : Value) (apart : ExternalApartness x zero) : Value :=
  let produced := externalInversePresentation apart
  classOf (reciprocalName produced.name produced.domain)

def SetoidInverse (x y : Value) : Prop :=
  Nonempty (Σ' witness : ExternalApartness x zero, SetoidEquivalent (externalInverse x witness) y)

def addMember {x y : Value} {a b : RegularDyadicName} (ha : x.Contains a) (hb : y.Contains b) :
    (addValue x y).Contains (addName a b) := ⟨a, b, ha, hb, .refl _⟩
def mulMember {x y : Value} {a b : RegularDyadicName} (ha : x.Contains a) (hb : y.Contains b) :
    (mulValue x y).Contains (mulName a b) := ⟨a, b, ha, hb, .refl _⟩
def negMember {x : Value} {a : RegularDyadicName} (ha : x.Contains a) :
    (negValue x).Contains (negName a) := ⟨a, ha, .refl _⟩

theorem setoidUnitPositive : SetoidOrder zero one := ⟨nameOrderToExternal unitNamePositive⟩

theorem setoidIrreflexive {x : Value} (order : SetoidOrder x x) : False := by
  obtain ⟨order⟩ := order
  exact (order.toNameOrder.refutesEquivalent (x.coherent order.leftMember order.rightMember)).elim

theorem setoidAsymmetric {x y : Value} (first : SetoidOrder x y) (reverse : SetoidOrder y x) : False := by
  obtain ⟨first⟩ := first
  obtain ⟨reverse⟩ := reverse
  exact (first.toNameOrder.asymmetric
    (externalOrderToNames reverse first.rightMember first.leftMember)).elim

theorem setoidTransitive {x y z : Value} (first : SetoidOrder x y) (second : SetoidOrder y z) :
    SetoidOrder x z := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨externalOrderFromMembers first.leftMember second.rightMember
    (first.toNameOrder.transitive (externalOrderToNames second first.rightMember second.rightMember))⟩

theorem setoidCotransitive {x y : Value} (origin : SetoidOrder x y) (middle : Value) :
    SetoidOrder x middle ∨ SetoidOrder middle y := by
  obtain ⟨origin⟩ := origin
  obtain ⟨⟨name, member⟩⟩ := middle.inhabited
  cases origin.toNameOrder.cotransitive name with
  | inl order => exact .inl ⟨externalOrderFromMembers origin.leftMember member order⟩
  | inr order => exact .inr ⟨externalOrderFromMembers member origin.rightMember order⟩

theorem setoidTransportOrder {a b c d : Value} (order : SetoidOrder a b)
    (left : SetoidEquivalent a c) (right : SetoidEquivalent b d) : SetoidOrder c d := by
  obtain ⟨order⟩ := order
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨transportExternalOrder order left right⟩

theorem setoidTranslateRight {a b : Value} (origin : SetoidOrder a b) (shift : Value) :
    SetoidOrder (addValue a shift) (addValue b shift) := by
  obtain ⟨origin⟩ := origin
  obtain ⟨⟨name, member⟩⟩ := shift.inhabited
  exact ⟨externalOrderFromMembers (addMember origin.leftMember member)
    (addMember origin.rightMember member) (translateNameOrderRight origin.toNameOrder name)⟩

theorem setoidTranslateLeft {a b : Value} (origin : SetoidOrder a b) (shift : Value) :
    SetoidOrder (addValue shift a) (addValue shift b) :=
  setoidTransportOrder (setoidTranslateRight origin shift) (setoidAddComm a shift) (setoidAddComm b shift)

theorem setoidReflectTranslationRight {a b shift : Value}
    (origin : SetoidOrder (addValue a shift) (addValue b shift)) : SetoidOrder a b := by
  obtain ⟨origin⟩ := origin
  obtain ⟨⟨an, ha⟩⟩ := a.inhabited
  obtain ⟨⟨bn, hb⟩⟩ := b.inhabited
  obtain ⟨⟨sn, hs⟩⟩ := shift.inhabited
  exact ⟨externalOrderFromMembers ha hb
    (reflectNameTranslationRight (externalOrderToNames origin (addMember ha hs) (addMember hb hs)))⟩

theorem setoidReflectTranslationLeft {a b shift : Value}
    (origin : SetoidOrder (addValue shift a) (addValue shift b)) : SetoidOrder a b :=
  setoidReflectTranslationRight
    (setoidTransportOrder origin (setoidAddComm shift a) (setoidAddComm shift b))

theorem setoidPositiveProduct {a b : Value} (left : SetoidOrder zero a) (right : SetoidOrder zero b) :
    SetoidOrder zero (mulValue a b) := by
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨externalOrderFromMembers (classOfContains zeroName) (mulMember left.rightMember right.rightMember)
    (positiveNameProduct (externalOrderToNames left (classOfContains zeroName) left.rightMember)
      (externalOrderToNames right (classOfContains zeroName) right.rightMember))⟩

theorem setoidMultiplyPositiveRight {a b c : Value} (origin : SetoidOrder a b) (positive : SetoidOrder zero c) :
    SetoidOrder (mulValue a c) (mulValue b c) := by
  obtain ⟨origin⟩ := origin
  obtain ⟨positive⟩ := positive
  exact ⟨externalOrderFromMembers (mulMember origin.leftMember positive.rightMember)
    (mulMember origin.rightMember positive.rightMember)
    (multiplyNamePositiveRight origin.toNameOrder
      (externalOrderToNames positive (classOfContains zeroName) positive.rightMember))⟩

theorem setoidMultiplyPositiveLeft {a b c : Value} (origin : SetoidOrder a b) (positive : SetoidOrder zero c) :
    SetoidOrder (mulValue c a) (mulValue c b) :=
  setoidTransportOrder (setoidMultiplyPositiveRight origin positive) (setoidMulComm a c) (setoidMulComm b c)

theorem setoidApartnessSymm {x y : Value} (apart : SetoidApartness x y) : SetoidApartness y x := by
  obtain ⟨apart⟩ := apart
  exact ⟨match apart with | .inl order => .inr order | .inr order => .inl order⟩

theorem setoidTransportApartness {a b c d : Value} (apart : SetoidApartness a b)
    (left : SetoidEquivalent a c) (right : SetoidEquivalent b d) : SetoidApartness c d := by
  obtain ⟨apart⟩ := apart
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨transportExternalApartness apart left right⟩

theorem setoidApartnessToOrder {x y : Value} (apart : SetoidApartness x y) :
    SetoidOrder x y ∨ SetoidOrder y x := by
  obtain ⟨apart⟩ := apart
  cases apart with
  | inl order => exact .inl ⟨order⟩
  | inr order => exact .inr ⟨order⟩

theorem setoidOrderToApartness {x y : Value} (orders : SetoidOrder x y ∨ SetoidOrder y x) :
    SetoidApartness x y := by
  cases orders with
  | inl order => obtain ⟨order⟩ := order; exact ⟨.inl order⟩
  | inr order => obtain ⟨order⟩ := order; exact ⟨.inr order⟩

theorem setoidDensityExists {x y : Value} (order : SetoidOrder x y) :
    Nonempty (Σ' code : SignedDyadicCode, SetoidOrder x (dyadicValue code) ∧ SetoidOrder (dyadicValue code) y) := by
  obtain ⟨order⟩ := order
  let produced := externalDensity order
  exact ⟨⟨produced.code, ⟨⟨produced.left⟩, ⟨produced.right⟩⟩⟩⟩

theorem setoidNaturalBoundsExist (x : Value) :
    Nonempty (Σ' lower upper : Nat, SetoidOrder (negativeNaturalValue lower) x ∧ SetoidOrder x (naturalValue upper)) := by
  obtain ⟨produced⟩ := externalNaturalBounds x
  exact ⟨⟨produced.lower, produced.upper, ⟨⟨produced.lowerOrder⟩, ⟨produced.upperOrder⟩⟩⟩⟩

def externalInverseCongr {x y : Value} (same : ExternalEquivalent x y)
    (first : ExternalApartness x zero) (second : ExternalApartness y zero) :
    ExternalEquivalent (externalInverse x first) (externalInverse y second) :=
  let a := externalInversePresentation first
  let b := externalInversePresentation second
  classOfPreserves (reciprocalNameCongr
    (y.coherent (same.forward a.name a.member) b.member) a.domain b.domain)

def externalInverseWitnessIndependent (x : Value) (first second : ExternalApartness x zero) :
    ExternalEquivalent (externalInverse x first) (externalInverse x second) :=
  externalInverseCongr (.refl x) first second

def externalInverseUnitRight (x : Value) (witness : ExternalApartness x zero) :
    ExternalEquivalent (mulValue x (externalInverse x witness)) one :=
  let produced := externalInversePresentation witness
  ((classOfMul produced.name (reciprocalName produced.name produced.domain)).trans
    (mulCongr (memberClassEquivalent x produced.name produced.member) (.refl _))).symm.trans
      (classOfPreserves (reciprocalNameUnitRight produced.name produced.domain))

def externalInverseUnitLeft (x : Value) (witness : ExternalApartness x zero) :
    ExternalEquivalent (mulValue (externalInverse x witness) x) one :=
  let produced := externalInversePresentation witness
  ((classOfMul (reciprocalName produced.name produced.domain) produced.name).trans
    (mulCongr (.refl _) (memberClassEquivalent x produced.name produced.member))).symm.trans
      (classOfPreserves (reciprocalNameUnitLeft produced.name produced.domain))

def classOfInverse {a : RegularDyadicName} (witness : NameApartness a zeroName) :
    ExternalEquivalent (classOf (inverseName a witness))
      (externalInverse (classOf a) (nameApartnessToExternal witness)) := by
  cases witness with
  | inl order => exact classOfPreserves (reciprocalNameWitnessIndependent a
      (inverseNameDomain a (.inl order)) (externalNegativeDomain (nameOrderToExternal order)))
  | inr order => exact classOfPreserves (reciprocalNameWitnessIndependent a
      (inverseNameDomain a (.inr order)) (externalPositiveDomain (nameOrderToExternal order)))

theorem setoidInverseFromWitness {x : Value} (w : ExternalApartness x zero) :
    SetoidInverse x (externalInverse x w) := ⟨⟨w, setoidEquivalentRefl _⟩⟩

theorem setoidInverseTotal {x : Value} (apart : SetoidApartness x zero) :
    Nonempty (Σ' y : Value, SetoidInverse x y) := by
  obtain ⟨w⟩ := apart
  exact ⟨⟨externalInverse x w, setoidInverseFromWitness w⟩⟩

theorem setoidInverseWitnessIndependent {x : Value} (first second : ExternalApartness x zero) :
    SetoidEquivalent (externalInverse x first) (externalInverse x second) :=
  ⟨externalInverseWitnessIndependent x first second⟩

theorem setoidInverseSingleValued {x y z : Value} (first : SetoidInverse x y) (second : SetoidInverse x z) :
    SetoidEquivalent y z := by
  obtain ⟨⟨a, ha⟩⟩ := first
  obtain ⟨⟨b, hb⟩⟩ := second
  exact setoidEquivalentTrans (setoidEquivalentSymm ha)
    (setoidEquivalentTrans (setoidInverseWitnessIndependent a b) hb)

theorem setoidInverseCongr {x x' y y' : Value} (same : SetoidEquivalent x x')
    (first : SetoidInverse x y) (second : SetoidInverse x' y') : SetoidEquivalent y y' := by
  obtain ⟨same⟩ := same
  obtain ⟨⟨a, ha⟩⟩ := first
  obtain ⟨⟨b, hb⟩⟩ := second
  exact setoidEquivalentTrans (setoidEquivalentSymm ha)
    (setoidEquivalentTrans ⟨externalInverseCongr same a b⟩ hb)

theorem setoidInverseUnitRight {x y : Value} (inverse : SetoidInverse x y) :
    SetoidEquivalent (mulValue x y) one := by
  obtain ⟨⟨w, same⟩⟩ := inverse
  exact setoidEquivalentTrans
    (setoidMulCongr (setoidEquivalentRefl x) (setoidEquivalentSymm same)) ⟨externalInverseUnitRight x w⟩

theorem setoidInverseUnitLeft {x y : Value} (inverse : SetoidInverse x y) :
    SetoidEquivalent (mulValue y x) one := by
  obtain ⟨⟨w, same⟩⟩ := inverse
  exact setoidEquivalentTrans
    (setoidMulCongr (setoidEquivalentSymm same) (setoidEquivalentRefl x)) ⟨externalInverseUnitLeft x w⟩

def valueSetoid : Setoid Value where
  r := SetoidEquivalent
  iseqv := ⟨setoidEquivalentRefl, setoidEquivalentSymm, setoidEquivalentTrans⟩

/-- Every law of the extensive ordered readout is propositionally truncated. -/
structure SetoidOrderedArchimedeanReadout : Prop where
  equivalentRefl : (x : Value) → SetoidEquivalent x x
  equivalentSymm : {x y : Value} → SetoidEquivalent x y → SetoidEquivalent y x
  equivalentTrans : {x y z : Value} → SetoidEquivalent x y → SetoidEquivalent y z → SetoidEquivalent x z
  addCongr : {a b c d : Value} → SetoidEquivalent a c → SetoidEquivalent b d →
    SetoidEquivalent (addValue a b) (addValue c d)
  addComm : (a b : Value) → SetoidEquivalent (addValue a b) (addValue b a)
  addAssoc : (a b c : Value) → SetoidEquivalent (addValue (addValue a b) c) (addValue a (addValue b c))
  zeroLeft : (a : Value) → SetoidEquivalent (addValue zero a) a
  zeroRight : (a : Value) → SetoidEquivalent (addValue a zero) a
  negCongr : {a b : Value} → SetoidEquivalent a b → SetoidEquivalent (negValue a) (negValue b)
  negInvolutive : (a : Value) → SetoidEquivalent (negValue (negValue a)) a
  addInverseLeft : (a : Value) → SetoidEquivalent (addValue (negValue a) a) zero
  addInverseRight : (a : Value) → SetoidEquivalent (addValue a (negValue a)) zero
  negSum : (a b : Value) → SetoidEquivalent (negValue (addValue a b)) (addValue (negValue a) (negValue b))
  mulCongr : {a b c d : Value} → SetoidEquivalent a c → SetoidEquivalent b d →
    SetoidEquivalent (mulValue a b) (mulValue c d)
  mulComm : (a b : Value) → SetoidEquivalent (mulValue a b) (mulValue b a)
  mulAssoc : (a b c : Value) → SetoidEquivalent (mulValue (mulValue a b) c) (mulValue a (mulValue b c))
  oneLeft : (a : Value) → SetoidEquivalent (mulValue one a) a
  oneRight : (a : Value) → SetoidEquivalent (mulValue a one) a
  mulZeroLeft : (a : Value) → SetoidEquivalent (mulValue zero a) zero
  mulZeroRight : (a : Value) → SetoidEquivalent (mulValue a zero) zero
  distributeLeft : (a b c : Value) →
    SetoidEquivalent (mulValue a (addValue b c)) (addValue (mulValue a b) (mulValue a c))
  distributeRight : (a b c : Value) →
    SetoidEquivalent (mulValue (addValue a b) c) (addValue (mulValue a c) (mulValue b c))
  mulNegLeft : (a b : Value) → SetoidEquivalent (mulValue (negValue a) b) (negValue (mulValue a b))
  mulNegRight : (a b : Value) → SetoidEquivalent (mulValue a (negValue b)) (negValue (mulValue a b))
  unitPositive : SetoidOrder zero one
  irreflexive : {x : Value} → SetoidOrder x x → False
  asymmetric : {x y : Value} → SetoidOrder x y → SetoidOrder y x → False
  transitive : {x y z : Value} → SetoidOrder x y → SetoidOrder y z → SetoidOrder x z
  cotransitive : {x y : Value} → SetoidOrder x y → (middle : Value) →
    SetoidOrder x middle ∨ SetoidOrder middle y
  transportOrder : {a b c d : Value} → SetoidOrder a b → SetoidEquivalent a c →
    SetoidEquivalent b d → SetoidOrder c d
  translateRight : {a b : Value} → SetoidOrder a b → (shift : Value) →
    SetoidOrder (addValue a shift) (addValue b shift)
  translateLeft : {a b : Value} → SetoidOrder a b → (shift : Value) →
    SetoidOrder (addValue shift a) (addValue shift b)
  reflectTranslationRight : {a b shift : Value} →
    SetoidOrder (addValue a shift) (addValue b shift) → SetoidOrder a b
  positiveProduct : {a b : Value} → SetoidOrder zero a → SetoidOrder zero b → SetoidOrder zero (mulValue a b)
  multiplyPositiveRight : {a b c : Value} → SetoidOrder a b → SetoidOrder zero c →
    SetoidOrder (mulValue a c) (mulValue b c)
  multiplyPositiveLeft : {a b c : Value} → SetoidOrder a b → SetoidOrder zero c →
    SetoidOrder (mulValue c a) (mulValue c b)
  apartnessSymm : {x y : Value} → SetoidApartness x y → SetoidApartness y x
  transportApartness : {a b c d : Value} → SetoidApartness a b → SetoidEquivalent a c →
    SetoidEquivalent b d → SetoidApartness c d
  apartnessToOrder : {x y : Value} → SetoidApartness x y → SetoidOrder x y ∨ SetoidOrder y x
  orderToApartness : {x y : Value} → SetoidOrder x y ∨ SetoidOrder y x → SetoidApartness x y
  inverseFromWitness : {x : Value} → (w : ExternalApartness x zero) → SetoidInverse x (externalInverse x w)
  inverseTotal : {x : Value} → SetoidApartness x zero → Nonempty (Σ' y : Value, SetoidInverse x y)
  inverseSingleValued : {x y z : Value} → SetoidInverse x y → SetoidInverse x z → SetoidEquivalent y z
  inverseWitnessIndependent : {x : Value} → (first second : ExternalApartness x zero) →
    SetoidEquivalent (externalInverse x first) (externalInverse x second)
  inverseCongr : {x x' y y' : Value} → SetoidEquivalent x x' → SetoidInverse x y →
    SetoidInverse x' y' → SetoidEquivalent y y'
  inverseUnitRight : {x y : Value} → SetoidInverse x y → SetoidEquivalent (mulValue x y) one
  inverseUnitLeft : {x y : Value} → SetoidInverse x y → SetoidEquivalent (mulValue y x) one
  densityExists : {x y : Value} → SetoidOrder x y →
    Nonempty (Σ' code : SignedDyadicCode, SetoidOrder x (dyadicValue code) ∧ SetoidOrder (dyadicValue code) y)
  naturalBoundsExist : (x : Value) →
    Nonempty (Σ' lower upper : Nat,
      SetoidOrder (negativeNaturalValue lower) x ∧ SetoidOrder x (naturalValue upper))

namespace SetoidOrderedArchimedeanReadout
abbrev Equivalent := SetoidEquivalent
abbrev Order := SetoidOrder
abbrev Apartness := SetoidApartness
abbrev Inverse := SetoidInverse
end SetoidOrderedArchimedeanReadout

theorem setoidOrderedArchimedeanReadout : SetoidOrderedArchimedeanReadout where
  equivalentRefl := setoidEquivalentRefl
  equivalentSymm := setoidEquivalentSymm
  equivalentTrans := setoidEquivalentTrans
  addCongr := setoidAddCongr
  addComm := setoidAddComm
  addAssoc := setoidAddAssoc
  zeroLeft := setoidZeroLeft
  zeroRight := setoidZeroRight
  negCongr := setoidNegCongr
  negInvolutive := setoidNegInvolutive
  addInverseLeft := setoidAddInverseLeft
  addInverseRight := setoidAddInverseRight
  negSum := setoidNegSum
  mulCongr := setoidMulCongr
  mulComm := setoidMulComm
  mulAssoc := setoidMulAssoc
  oneLeft := setoidOneLeft
  oneRight := setoidOneRight
  mulZeroLeft := setoidMulZeroLeft
  mulZeroRight := setoidMulZeroRight
  distributeLeft := setoidDistributeLeft
  distributeRight := setoidDistributeRight
  mulNegLeft := setoidMulNegLeft
  mulNegRight := setoidMulNegRight
  unitPositive := setoidUnitPositive
  irreflexive := setoidIrreflexive
  asymmetric := setoidAsymmetric
  transitive := setoidTransitive
  cotransitive := setoidCotransitive
  transportOrder := setoidTransportOrder
  translateRight := setoidTranslateRight
  translateLeft := setoidTranslateLeft
  reflectTranslationRight := setoidReflectTranslationRight
  positiveProduct := setoidPositiveProduct
  multiplyPositiveRight := setoidMultiplyPositiveRight
  multiplyPositiveLeft := setoidMultiplyPositiveLeft
  apartnessSymm := setoidApartnessSymm
  transportApartness := setoidTransportApartness
  apartnessToOrder := setoidApartnessToOrder
  orderToApartness := setoidOrderToApartness
  inverseFromWitness := setoidInverseFromWitness
  inverseTotal := setoidInverseTotal
  inverseSingleValued := setoidInverseSingleValued
  inverseWitnessIndependent := setoidInverseWitnessIndependent
  inverseCongr := setoidInverseCongr
  inverseUnitRight := setoidInverseUnitRight
  inverseUnitLeft := setoidInverseUnitLeft
  densityExists := setoidDensityExists
  naturalBoundsExist := setoidNaturalBoundsExist

end ExtensiveCauchyReal
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.Value
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalEquivalent.refl
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalEquivalent.symm
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalEquivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOf
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfContains
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfPreserves
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfReflects
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.memberClassEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfSurjective
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.PositiveSetoid
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.PointwiseEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.identity
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.compose
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.identityLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.identityRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RelationalMorphism.composeAssoc
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ValuePositiveSetoid
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ConventionalRegularCauchyReference
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ReferenceRealizes
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceCoverage
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.valueReferenceCoverage
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceRealizesStable
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceCorrect
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceFaithful
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.RespectsNameEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ClassDescent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classDescent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExtendsNameMap
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classDescentExtends
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classDescentOnClass
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classDescentOnClassBack
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classDescentUnique
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.UnaryMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.BinaryMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.unaryValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.binaryValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.unaryValueCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.binaryValueCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfUnary
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfBinary
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.dyadicValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.zero
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.one
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.negValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.addValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.mulValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.negCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.addCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.mulCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfDyadic
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfNeg
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfAdd
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfMul
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.Expression
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.Expression.onNames
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.Expression.onValues
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.Expression.exact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.expressionLaw
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidEquivalentRefl
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidEquivalentSymm
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidEquivalentTrans
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAddCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidNegCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAddComm
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAddAssoc
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidZeroLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidZeroRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidNegInvolutive
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAddInverseLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAddInverseRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidNegSum
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalOrder.toNameOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalOrderFromMembers
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.nameOrderToExternal
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalApartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidApartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.nameApartnessToExternal
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.transportExternalOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.transportExternalApartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalOrderToNames
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalApartnessToNames
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.naturalValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.negativeNaturalValue
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalDensityWitness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalDensity
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalNaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalNaturalBoundsFromMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalNaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.densityCodeExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.lowerBoundExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.upperBoundExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulComm
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulAssoc
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidOneLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidOneRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulZeroLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulZeroRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidDistributeLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidDistributeRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulNegLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMulNegRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.zeroMemberNear
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalNegativeDomain
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalPositiveDomain
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalInversePresentation
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInversePresentation
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInverse
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidInverse
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.addMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.mulMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.negMember
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidUnitPositive
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidIrreflexive
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidAsymmetric
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidTransitive
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidCotransitive
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidTransportOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidTranslateRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidTranslateLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidReflectTranslationRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidReflectTranslationLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidPositiveProduct
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMultiplyPositiveRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidMultiplyPositiveLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidApartnessSymm
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidTransportApartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidApartnessToOrder
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidOrderToApartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidDensityExists
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidNaturalBoundsExist
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInverseCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInverseWitnessIndependent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInverseUnitRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalInverseUnitLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.classOfInverse
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseFromWitness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseTotal
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseWitnessIndependent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseSingleValued
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseCongr
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseUnitRight
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidInverseUnitLeft
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.valueSetoid
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrderedArchimedeanReadout
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrderedArchimedeanReadout.Equivalent
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrderedArchimedeanReadout.Order
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrderedArchimedeanReadout.Apartness
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.SetoidOrderedArchimedeanReadout.Inverse
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.setoidOrderedArchimedeanReadout
/- AXIOM_AUDIT_END -/
