import PPAC.Migration.Internal.SyntaxCheckedFields

/-! 完整字段图上的公式/纯项/真实后继bound/原编号0符号类型检查；均为对象公式。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax
open SyntaxCheckedFieldSyntax MinimalPredicates
open StructuralTreeOperatorSyntax (shape)

def codeMatrix : Formula 4 := formulaCode (0 : Fin 3).castSucc (Fin.last 3) (1 : Fin 3).castSucc (2 : Fin 3).castSucc
def termMatrix : Formula 4 := term (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)
def advancedMatrix : Formula 4 := advancedCode (0 : Fin 3).castSucc (Fin.last 3) (1 : Fin 3).castSucc (2 : Fin 3).castSucc
def zeroMatrix : Formula 2 := zeroScalar (0 : Fin 1).castSucc (Fin.last 1)

def codeField {m} (w g : Fin m) (j : Nat) (b f : Fin m) : Formula m := checked codeMatrix (three w b f) g j
def termField {m} (w g : Fin m) (j : Nat) (b f : Fin m) : Formula m := checked termMatrix (three w b f) g j
def advancedField {m} (w g : Fin m) (j : Nat) (b f : Fin m) : Formula m := checked advancedMatrix (three w b f) g j
def zeroField {m} (w g : Fin m) (j : Nat) : Formula m := checked zeroMatrix (fun _ => w) g j

theorem code_pred {m} (w b f x : Fin m) :
    pred codeMatrix (three w b f) x = formulaCode w x b f := by
  simp only [pred, codeMatrix, formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem codeField_rename {m n} (w g : Fin m) (j : Nat) (b f : Fin m) (r : Fin m → Fin n) :
    (codeField w g j b f).rename r = codeField (r w) (r g) j (r b) (r f) := by
  simp only [codeField, checked_rename, three_map]

theorem code_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m)
    (xs : Fin k → Fin m) (n t p l g b f : Fin m) (j : Fin k)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((codeField w g j.val b f).iff (formulaCode w (xs j) b f)) := by
  have hh := SyntaxCheckedFields.iff_at_constructor hZ codeMatrix (three w b f) k tag w xs n t p l g j hw hc hs
  simpa only [codeField, code_pred] using hh

theorem term_pred {m} (w b f x : Fin m) :
    pred termMatrix (three w b f) x = term w b f x := by
  simp only [pred, termMatrix, term_rename, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem termField_rename {m n} (w g : Fin m) (j : Nat) (b f : Fin m) (r : Fin m → Fin n) :
    (termField w g j b f).rename r = termField (r w) (r g) j (r b) (r f) := by
  simp only [termField, checked_rename, three_map]

theorem term_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m)
    (xs : Fin k → Fin m) (n t p l g b f : Fin m) (j : Fin k)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((termField w g j.val b f).iff (term w b f (xs j))) := by
  have hh := SyntaxCheckedFields.iff_at_constructor hZ termMatrix (three w b f) k tag w xs n t p l g j hw hc hs
  simpa only [termField, term_pred] using hh

theorem advanced_pred {m} (w b f x : Fin m) :
    pred advancedMatrix (three w b f) x = advancedCode w x b f := by
  simp only [pred, advancedMatrix, advancedCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem advancedField_rename {m n} (w g : Fin m) (j : Nat) (b f : Fin m) (r : Fin m → Fin n) :
    (advancedField w g j b f).rename r = advancedField (r w) (r g) j (r b) (r f) := by
  simp only [advancedField, checked_rename, three_map]

theorem advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m)
    (xs : Fin k → Fin m) (n t p l g b f : Fin m) (j : Fin k)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((advancedField w g j.val b f).iff (advancedCode w (xs j) b f)) := by
  have hh := SyntaxCheckedFields.iff_at_constructor hZ advancedMatrix (three w b f) k tag w xs n t p l g j hw hc hs
  simpa only [advancedField, advanced_pred] using hh

theorem zero_pred {m} (w x : Fin m) : pred zeroMatrix (fun _ => w) x = zeroScalar w x := by
  simp only [pred, zeroMatrix, zeroScalar_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem zeroField_rename {m n} (w g : Fin m) (j : Nat) (r : Fin m → Fin n) :
    (zeroField w g j).rename r = zeroField (r w) (r g) j := by
  simp only [zeroField, checked_rename]

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m)
    (xs : Fin k → Fin m) (n t p l g : Fin m) (j : Fin k)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((zeroField w g j.val).iff (zeroScalar w (xs j))) := by
  have hh := SyntaxCheckedFields.iff_at_constructor hZ zeroMatrix (fun _ => w) k tag w xs n t p l g j hw hc hs
  simpa only [zeroField, zero_pred] using hh
end PPAC.Migration.Internal.FormulaCodeTypedFields
