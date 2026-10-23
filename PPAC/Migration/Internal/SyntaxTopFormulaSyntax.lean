import PPAC.Migration.Internal.SyntaxTopFormulaAtCodes

/-! 首槽公式判断：两份实际唯一数值环境见证均为对象量词，不要求调用方提供环境码。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

def instantiateInput {m} (w a b A t n : Fin m) : Formula m :=
  (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t).conj (FormulaCodeSyntax.formulaCode w n A b)

def instantiateState {m} (w a b A t n q R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b a b n q)

def instantiateBody {m} (w a b A t n q : Fin m) : Formula (m+2) :=
  instantiateState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def instantiated {m} (w a b A t n q : Fin m) : Formula m := .ex (.ex (instantiateBody w a b A t n q))

def instantiateExists {m} (w a b A t n : Fin m) : Formula m := .ex
  (instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m))

def instantiateUnique {m} (w a b A t n q : Fin m) : Formula m := .all
  ((instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def instantiateFiber {m} (w a b A t n : Fin m) : Formula m := .ex
  ((instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)).conj (instantiateUnique w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)))

theorem instantiateInput_rename {m k} (w a b A t n : Fin m) (ρ : Fin m → Fin k) :
    (instantiateInput w a b A t n).rename ρ = instantiateInput (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) := by
  simp only [instantiateInput, Formula.rename, SyntaxTopEnvironmentSyntax.instantiateInput_rename, FormulaCodeSyntax.formulaCode_rename]

theorem instantiateState_rename {m k} (w a b A t n q R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateState w a b A t n q R S).rename ρ = instantiateState (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) (ρ q) (ρ R) (ρ S) := by
  simp only [instantiateState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

theorem instantiated_rename {m k} (w a b A t n q : Fin m) (ρ : Fin m → Fin k) :
    (instantiated w a b A t n q).rename ρ = instantiated (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) (ρ q) := by
  simp only [instantiated, instantiateBody, Formula.rename, instantiateState_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem instantiateExists_rename {m k} (w a b A t n : Fin m) (ρ : Fin m → Fin k) :
    (instantiateExists w a b A t n).rename ρ = instantiateExists (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) := by
  simp only [instantiateExists, Formula.rename, instantiated_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem instantiateUnique_rename {m k} (w a b A t n q : Fin m) (ρ : Fin m → Fin k) :
    (instantiateUnique w a b A t n q).rename ρ = instantiateUnique (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) (ρ q) := by
  simp only [instantiateUnique, Formula.rename, instantiated_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem instantiateFiber_rename {m k} (w a b A t n : Fin m) (ρ : Fin m → Fin k) :
    (instantiateFiber w a b A t n).rename ρ = instantiateFiber (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) := by
  simp only [instantiateFiber, Formula.rename, instantiated_rename, instantiateUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_instantiated {m} {Γ : Context m} (w a b A t n q R S : Fin m)
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b a b n q)) :
    Derives Γ (instantiated w a b A t n q) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [instantiateBody, Formula.instantiate, instantiateState_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (show Derives Γ (instantiateState w a b A t n q R S) from .conjI he hq)

theorem intro_instantiate_exists {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) : Derives Γ (instantiateExists w a b A t n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, instantiated_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem intro_instantiate_fiber {m} {Γ : Context m} (w a b A t n q : Fin m)
    (hq : Derives Γ (instantiated w a b A t n q)) (hu : Derives Γ (instantiateUnique w a b A t n q)) : Derives Γ (instantiateFiber w a b A t n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, instantiated_rename, instantiateUnique_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hu)

def abstractInput {m} (w a b A B n : Fin m) : Formula m :=
  (SyntaxTopEnvironmentSyntax.abstractInput w a b A B).conj (FormulaCodeSyntax.formulaCode w n a B)

def abstractState {m} (w a b A B n q R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a B A b n q)

def abstractBody {m} (w a b A B n q : Fin m) : Formula (m+2) :=
  abstractState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstracted {m} (w a b A B n q : Fin m) : Formula m := .ex (.ex (abstractBody w a b A B n q))

def abstractExists {m} (w a b A B n : Fin m) : Formula m := .ex
  (abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m))

def abstractUnique {m} (w a b A B n q : Fin m) : Formula m := .all
  ((abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def abstractFiber {m} (w a b A B n : Fin m) : Formula m := .ex
  ((abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)).conj (abstractUnique w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)))

theorem abstractInput_rename {m k} (w a b A B n : Fin m) (ρ : Fin m → Fin k) :
    (abstractInput w a b A B n).rename ρ = abstractInput (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) := by
  simp only [abstractInput, Formula.rename, SyntaxTopEnvironmentSyntax.abstractInput_rename, FormulaCodeSyntax.formulaCode_rename]

theorem abstractState_rename {m k} (w a b A B n q R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractState w a b A B n q R S).rename ρ = abstractState (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) (ρ R) (ρ S) := by
  simp only [abstractState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

theorem abstracted_rename {m k} (w a b A B n q : Fin m) (ρ : Fin m → Fin k) :
    (abstracted w a b A B n q).rename ρ = abstracted (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) := by
  simp only [abstracted, abstractBody, Formula.rename, abstractState_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstractExists_rename {m k} (w a b A B n : Fin m) (ρ : Fin m → Fin k) :
    (abstractExists w a b A B n).rename ρ = abstractExists (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) := by
  simp only [abstractExists, Formula.rename, abstracted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstractUnique_rename {m k} (w a b A B n q : Fin m) (ρ : Fin m → Fin k) :
    (abstractUnique w a b A B n q).rename ρ = abstractUnique (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) := by
  simp only [abstractUnique, Formula.rename, abstracted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem abstractFiber_rename {m k} (w a b A B n : Fin m) (ρ : Fin m → Fin k) :
    (abstractFiber w a b A B n).rename ρ = abstractFiber (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) := by
  simp only [abstractFiber, Formula.rename, abstracted_rename, abstractUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_abstracted {m} {Γ : Context m} (w a b A B n q R S : Fin m)
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a B A b n q)) :
    Derives Γ (abstracted w a b A B n q) := by
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [abstractBody, Formula.instantiate, abstractState_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (show Derives Γ (abstractState w a b A B n q R S) from .conjI he hq)

theorem intro_abstract_exists {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (abstractExists w a b A B n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, abstracted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem intro_abstract_fiber {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) (hu : Derives Γ (abstractUnique w a b A B n q)) : Derives Γ (abstractFiber w a b A B n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, abstracted_rename, abstractUnique_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hu)

end PPAC.Migration.Internal.SyntaxTopFormulaSyntax
