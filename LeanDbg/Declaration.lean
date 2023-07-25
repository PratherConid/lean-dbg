import Lean.Util.CollectLevelParams
import Lean.Elab.DeclUtil
import Lean.Elab.DefView
import LeanDbg.Inductive
import Lean.Elab.Structure
import Lean.Elab.MutualDef
import Lean.Elab.DeclarationRange


open Lean Meta

namespace LeanDbg

open Elab Command in
/-
leading_parser "inductive " >> declId >> optDeclSig >> optional ":=" >> many ctor
leading_parser atomic (group ("class " >> "inductive ")) >> declId >> optDeclSig >> optional ":=" >> many ctor >> optDeriving
-/
private def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView := do
  checkValidInductiveModifier modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser optional docComment >> "\n| " >> declModifiers >> rawIdent >> optDeclSig
    let mut ctorModifiers ← elabModifiers ctor[2]
    if let some leadingDocComment := ctor[0].getOptional? then
      if ctorModifiers.docString?.isSome then
        logErrorAt leadingDocComment "duplicate doc string"
      ctorModifiers := { ctorModifiers with docString? := TSyntax.getDocString ⟨leadingDocComment⟩ }
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 3
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[3] <| applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[3]
    return { ref := ctor, modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let computedFields ← (decl[5].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
    return { ref := cf, modifiers := cf[0], fieldId := cf[1].getId, type := ⟨cf[3]⟩, matchAlts := ⟨cf[4]⟩ }
  let classes ← getOptDerivingClasses decl[6]
  return {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors
    computedFields
  }

open Elab Command in
def elabInductive (modifiers : Modifiers) (stx : Syntax) : Elab.Command.CommandElabM Unit := do
  let v ← inductiveSyntaxToView modifiers stx
  let ctors : Array LeanDbg.CtorView := v.ctors.map
    (fun x => {ref := x.ref, modifiers := x.modifiers, declName := x.declName, binders := x.binders, type? := x.type?})
  let cfvs : Array LeanDbg.ComputedFieldView := v.computedFields.map
    (fun x => {ref := x.ref, modifiers := x.modifiers, fieldId := x.fieldId, type := x.type, matchAlts := x.matchAlts})
  LeanDbg.elabInductiveViews
    #[{ref := v.ref, declId := v.declId, modifiers := v.modifiers,
       shortDeclName := v.shortDeclName, declName := v.declName,
       levelNames := v.levelNames, binders := v.binders, type?:=v.type?,
       ctors := ctors, derivingClasses := v.derivingClasses, computedFields := cfvs}]

open Elab Command in
private def ensureValidNamespace (name : Name) : MacroM Unit := do
  match name with
  | .str p s =>
    if s == "_root_" then
      Macro.throwError s!"invalid namespace '{name}', '_root_' is a reserved namespace"
    ensureValidNamespace p
  | .num .. => Macro.throwError s!"invalid namespace '{name}', it must not contain numeric parts"
  | .anonymous => return ()

open Elab Command in
private def setDeclIdName (declId : Syntax) (nameNew : Name) : Syntax :=
  let (id, _) := expandDeclIdCore declId
  -- We should not update the name of `def _root_.` declarations
  assert! !(`_root_).isPrefixOf id
  let idStx := mkIdent nameNew |>.raw.setInfo declId.getHeadInfo
  if declId.isIdent then
    idStx
  else
    declId.setArg 0 idStx

/-- Return `true` if `stx` is a `Command.declaration`, and it is a definition that always has a name. -/
private def isNamedDef (stx : Syntax) : Bool :=
  if !stx.isOfKind ``Lean.Parser.Command.declaration then
    false
  else
    let decl := stx[1]
    let k := decl.getKind
    k == ``Lean.Parser.Command.abbrev ||
    k == ``Lean.Parser.Command.def ||
    k == ``Lean.Parser.Command.theorem ||
    k == ``Lean.Parser.Command.opaque ||
    k == ``Lean.Parser.Command.axiom ||
    k == ``Lean.Parser.Command.inductive ||
    k == ``Lean.Parser.Command.classInductive ||
    k == ``Lean.Parser.Command.structure

/-- Return `true` if `stx` is an `instance` declaration command -/
private def isInstanceDef (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.declaration &&
  stx[1].getKind == ``Lean.Parser.Command.instance

open Elab Command in
/-- Return `some name` if `stx` is a definition named `name` -/
private def getDefName? (stx : Syntax) : Option Name := do
  if isNamedDef stx then
    let (id, _) := expandDeclIdCore stx[1][1]
    some id
  else if isInstanceDef stx then
    let optDeclId := stx[1][3]
    if optDeclId.isNone then none
    else
      let (id, _) := expandDeclIdCore optDeclId[0]
      some id
  else
    none

/--
Update the name of the given definition.
This function assumes `stx` is not a nameless instance.
-/
private def setDefName (stx : Syntax) (name : Name) : Syntax :=
  if isNamedDef stx then
    stx.setArg 1 <| stx[1].setArg 1 <| setDeclIdName stx[1][1] name
  else if isInstanceDef stx then
    -- We never set the name of nameless instance declarations
    assert! !stx[1][3].isNone
    stx.setArg 1 <| stx[1].setArg 3 <| stx[1][3].setArg 0 <| setDeclIdName stx[1][3][0] name
  else
    stx

/--
  Given declarations such as `@[...] def Foo.Bla.f ...` return `some (Foo.Bla, @[...] def f ...)`
  Remark: if the id starts with `_root_`, we return `none`.
-/
private def expandDeclNamespace? (stx : Syntax) : MacroM (Option (Name × Syntax)) := do
  let some name := getDefName? stx | return none
  if (`_root_).isPrefixOf name then
    ensureValidNamespace (name.replacePrefix `_root_ Name.anonymous)
    return none
  let scpView := extractMacroScopes name
  match scpView.name with
  | .str .anonymous _ => return none
  | .str pre shortName => return some (pre, setDefName stx { scpView with name := shortName }.review)
  | _ => return none

open Lean Parser Command in
def myinductiveparser := leading_parser
  "#myinductive " >> declId >> optDeclSig >> Parser.optional (symbol " :=" <|> " where") >>
  many ctor >> Parser.optional (ppDedent ppLine >> computedFields) >> optDeriving

syntax (name := myinductive) myinductiveparser : command

@[command_elab myinductive]
def elabMyInductive : Elab.Command.CommandElab := fun stx => do
  match (← Elab.liftMacroM <| expandDeclNamespace? stx) with
  | some (ns, newStx) => do
    let ns := mkIdentFrom stx ns
    let newStx ← `(namespace $ns $(⟨newStx⟩) end $ns)
    Elab.Command.withMacroExpansion stx newStx <| Elab.Command.elabCommand newStx
  | none => do
    let decl     := stx[1]
    let declKind := decl.getKind
    if declKind == ``LeanDbg.myinductive then
      let modifiers ← Elab.elabModifiers stx[0]
      elabInductive modifiers decl
    else
      throwError "unexpected declaration"