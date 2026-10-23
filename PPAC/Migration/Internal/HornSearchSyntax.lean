import PPAC.Migration.Internal.HornApplicationBounds

/-! 原S(row)搜索界的实际对象后继见证与完整原表的有界存在应用。 -/
namespace PPAC.Migration.Internal.HornSearchSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornApplicationBounds
open YesMetaZFC.Automation.ObjectHorn (Rule)

def boundedStep {m} : List Rule → Fin m → Fin m → Fin m → Fin m → Formula m
  | .nil, _, _, _, _ => .bot
  | rule :: rules, w, row, trace, s => (boundedAt rule w row trace s).disj (boundedStep rules w row trace s)

def searchBody {m} (rules : List Rule) (w row trace : Fin m) : Formula (m+1) :=
  (successor (Fin.last m) row.castSucc).conj (boundedStep rules w.castSucc row.castSucc trace.castSucc (Fin.last m))

def searchStep {m} (rules : List Rule) (w row trace : Fin m) : Formula m := .ex (searchBody rules w row trace)

def originalSearchStep {m} (w row trace : Fin m) : Formula m := searchStep YesMetaZFC.Automation.ObjectSyntaxTransform.rules w row trace

theorem boundedStep_rename {m k} (rules : List Rule) (w row trace s : Fin m) (ρ : Fin m → Fin k) :
    (boundedStep rules w row trace s).rename ρ = boundedStep rules (ρ w) (ρ row) (ρ trace) (ρ s) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih => simp only [boundedStep, Formula.rename, boundedAt_rename, ih]

theorem searchStep_rename {m k} (rules : List Rule) (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (searchStep rules w row trace).rename ρ = searchStep rules (ρ w) (ρ row) (ρ trace) := by
  simp only [searchStep, searchBody, Formula.rename, successor_rename, boundedStep_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem originalSearchStep_rename {m k} (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (originalSearchStep w row trace).rename ρ = originalSearchStep (ρ w) (ρ row) (ρ trace) := searchStep_rename _ _ _ _ _

theorem intro_search {m} {Γ : Context m} (rules : List Rule) (w row trace s : Fin m)
    (hs : Derives Γ (successor s row)) (hb : Derives Γ (boundedStep rules w row trace s)) :
    Derives Γ (searchStep rules w row trace) := by
  apply Derives.exI s
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [searchBody, Formula.instantiate, Formula.rename, successor_rename, boundedStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs hb)

end PPAC.Migration.Internal.HornSearchSyntax
