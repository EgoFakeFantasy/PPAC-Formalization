import PPAC.Migration.Internal.OriginalFormulaApplicationNaturality

/-! 原十一公式的内部存在分支；仅子组件和量词后继深度由对象量词绑定。 -/
namespace PPAC.Migration.Internal.OriginalFormulaCaseSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def binaryBody {m} (tag kind : Nat) (w mode depth parameter n q : Fin m) : Formula (m+4) :=
  OriginalFormulaLocalData.binary tag kind (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
def binaryCase {m} (tag kind : Nat) (w mode depth parameter n q : Fin m) : Formula m := existsMany 4 (binaryBody tag kind w mode depth parameter n q)

def unaryBody {m} (tag : Nat) (w mode depth parameter n q : Fin m) : Formula (m+2) :=
  OriginalFormulaLocalData.unary tag (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1)
def unaryCase {m} (tag : Nat) (w mode depth parameter n q : Fin m) : Formula m := existsMany 2 (unaryBody tag w mode depth parameter n q)

def binderBody {m} (tag : Nat) (w mode depth parameter n q : Fin m) : Formula (m+1) :=
  (successor (Fin.last m) depth.castSucc).conj (unaryCase tag w.castSucc mode.castSucc (Fin.last m) parameter.castSucc n.castSucc q.castSucc)

def binderCase {m} (tag : Nat) (w mode depth parameter n q : Fin m) : Formula m := .ex (binderBody tag w mode depth parameter n q)

def applicationBody {m} (w mode depth parameter n q : Fin m) : Formula (m+3) :=
  OriginalFormulaLocalData.application (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 n) (old 3 q) (slot 3 0) (slot 3 1) (slot 3 2)
def applicationCase {m} (w mode depth parameter n q : Fin m) : Formula m := existsMany 3 (applicationBody w mode depth parameter n q)

theorem binaryBody_lift {m j} (tag kind : Nat) (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (binaryBody tag kind w mode depth parameter n q).rename (lift 4 ρ) = binaryBody tag kind (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [binaryBody, OriginalFormulaLocalData.binary_rename, lift_old, lift_slot]

theorem binaryCase_rename {m j} (tag kind : Nat) (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (binaryCase tag kind w mode depth parameter n q).rename ρ = binaryCase tag kind (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [binaryCase, existsMany_rename, binaryBody_lift]

theorem unaryBody_lift {m j} (tag : Nat) (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (unaryBody tag w mode depth parameter n q).rename (lift 2 ρ) = unaryBody tag (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [unaryBody, OriginalFormulaLocalData.unary_rename, lift_old, lift_slot]

theorem unaryCase_rename {m j} (tag : Nat) (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (unaryCase tag w mode depth parameter n q).rename ρ = unaryCase tag (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [unaryCase, existsMany_rename, unaryBody_lift]

theorem applicationBody_lift {m j} (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (applicationBody w mode depth parameter n q).rename (lift 3 ρ) = applicationBody (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [applicationBody, OriginalFormulaLocalData.application_rename, lift_old, lift_slot]

theorem applicationCase_rename {m j} (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (applicationCase w mode depth parameter n q).rename ρ = applicationCase (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [applicationCase, existsMany_rename, applicationBody_lift]

theorem binderCase_rename {m j} (tag : Nat) (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (binderCase tag w mode depth parameter n q).rename ρ = binderCase tag (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [binderCase, binderBody, Formula.rename, successor_rename, unaryCase_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_binary {m} {Γ : Context m} (tag kind : Nat) (w mode depth parameter n q x y X Y : Fin m)
    (hd : Derives Γ (OriginalFormulaLocalData.binary tag kind w mode depth parameter n q x y X Y)) : Derives Γ (binaryCase tag kind w mode depth parameter n q) := by
  apply HornBinderRules.intro_many 4 (binaryBody tag kind w mode depth parameter n q) (OriginalArgumentCaseSyntax.four x y X Y)
  exact of_eq (by simp only [binaryBody, OriginalFormulaLocalData.binary_rename, assign_old, assign_slot]; rfl) hd

theorem intro_unary {m} {Γ : Context m} (tag : Nat) (w mode depth parameter n q x X : Fin m)
    (hd : Derives Γ (OriginalFormulaLocalData.unary tag w mode depth parameter n q x X)) : Derives Γ (unaryCase tag w mode depth parameter n q) := by
  apply HornBinderRules.intro_many 2 (unaryBody tag w mode depth parameter n q) (SyntaxAtomSyntax.two x X)
  exact of_eq (by simp only [unaryBody, OriginalFormulaLocalData.unary_rename, assign_old, assign_slot]; rfl) hd

theorem intro_application {m} {Γ : Context m} (w mode depth parameter n q symbol args newArgs : Fin m)
    (hd : Derives Γ (OriginalFormulaLocalData.application w mode depth parameter n q symbol args newArgs)) : Derives Γ (applicationCase w mode depth parameter n q) := by
  apply HornBinderRules.intro_many 3 (applicationBody w mode depth parameter n q) (OriginalLookupExpr.rowFields symbol args newArgs)
  exact of_eq (by simp only [applicationBody, OriginalFormulaLocalData.application_rename, assign_old, assign_slot]; rfl) hd

theorem intro_binder {m} {Γ : Context m} (tag : Nat) (w mode depth parameter n q childDepth : Fin m)
    (hs : Derives Γ (successor childDepth depth)) (hu : Derives Γ (unaryCase tag w mode childDepth parameter n q)) : Derives Γ (binderCase tag w mode depth parameter n q) := by
  apply Derives.exI childDepth
  exact of_eq (by simp only [binderBody, Formula.instantiate, Formula.rename, successor_rename, unaryCase_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs hu)

end PPAC.Migration.Internal.OriginalFormulaCaseSyntax
