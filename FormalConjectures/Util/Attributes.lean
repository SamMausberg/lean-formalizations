import Lean

open Lean Parser

syntax (name := formalConjecturesCategoryAttr) "category" (ppSpace rawIdent)+ : attr
syntax (name := formalConjecturesAMSAttr) "AMS" (ppSpace (rawIdent <|> num))+ : attr

namespace FormalConjectures

open Lean

/-- Lightweight metadata attribute for problem tags such as `research` or `open`. -/
initialize categoryAttr : ParametricAttribute (Array String) ←
  registerParametricAttribute {
    name := Name.mkSimple "formalConjecturesCategoryAttr"
    descr := "tags a declaration with one or more problem categories"
    getParam := fun _ stx => do
      let cats := stx[1].getArgs
      if cats.isEmpty then
        throwError "Invalid `[category]` attribute syntax"
      pure <| cats.map fun cat =>
        if cat.isIdent then
          cat.getId.toString
        else
          cat.reprint.getD ""
  }

/-- Lightweight metadata attribute for AMS subject classifications. -/
initialize amsAttr : ParametricAttribute (Array String) ←
  registerParametricAttribute {
    name := Name.mkSimple "formalConjecturesAMSAttr"
    descr := "tags a declaration with one or more AMS classifications"
    getParam := fun _ stx => do
      let codes := stx[1].getArgs
      if codes.isEmpty then
        throwError "Invalid `[AMS]` attribute syntax"
      pure <| codes.map fun code =>
        if code.isIdent then
          code.getId.toString
        else
          match code.isNatLit? with
          | some n => toString n
          | none => code.reprint.getD ""
  }

def getCategories? (env : Environment) (declName : Name) : Option (Array String) :=
  categoryAttr.getParam? env declName

def getAMS? (env : Environment) (declName : Name) : Option (Array String) :=
  amsAttr.getParam? env declName

end FormalConjectures
