import PPAC.Migration.Internal.HornTraceExtension
import PPAC.Migration.Internal.HornExprConstructor
import PPAC.Migration.Internal.SyntaxConstructors
import YesMetaZFC.Automation.ObjectProjection

/-! 原ObjectProjection七规则的独立纯闭轨迹；不使用数值投影或类型结论定义接受。 -/
namespace PPAC.Migration.Internal.ProjectionTraceSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def tagRow {m} (w x y r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 2 0 w (SetLanguage.args2 x y) r

def getRow {m} (w x i y r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 1 w (SyntaxAtomSyntax.three x i y) r

def fieldRow {m} (w x i y r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 2 w (SyntaxAtomSyntax.three x i y) r

def closed {m} (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w.castSucc (Fin.last m) R.castSucc))

def witness {m} (w r R : Fin m) : Formula m := (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed w R))

def condition {m} (w r : Fin m) : Formula m := .ex (witness w.castSucc r.castSucc (Fin.last m))

def tag {m} (w x y : Fin m) : Formula m := .ex
  ((tagRow w.castSucc x.castSucc y.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

def get {m} (w x i y : Fin m) : Formula m := .ex
  ((getRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

def field {m} (w x i y : Fin m) : Formula m := .ex
  ((fieldRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj (condition w.castSucc (Fin.last m)))

theorem args2_map {α β : Type} (x y : α) (f : α → β) :
    (fun i => f (SetLanguage.args2 x y i)) = SetLanguage.args2 (f x) (f y) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun z => Fin.elim0 z) j) i

theorem tagRow_rename {m l} (w x y r : Fin m) (ρ : Fin m → Fin l) :
    (tagRow w x y r).rename ρ = tagRow (ρ w) (ρ x) (ρ y) (ρ r) := by
  simp only [tagRow, SyntaxNodeSyntax.constructor_rename, args2_map]

theorem getRow_rename {m l} (w x i y r : Fin m) (ρ : Fin m → Fin l) :
    (getRow w x i y r).rename ρ = getRow (ρ w) (ρ x) (ρ i) (ρ y) (ρ r) := by
  simp only [getRow, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem fieldRow_rename {m l} (w x i y r : Fin m) (ρ : Fin m → Fin l) :
    (fieldRow w x i y r).rename ρ = fieldRow (ρ w) (ρ x) (ρ i) (ρ y) (ρ r) := by
  simp only [fieldRow, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem closed_rename {m l} (w R : Fin m) (ρ : Fin m → Fin l) :
    (closed w R).rename ρ = closed (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, HornStepSyntax.step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m l} (w r R : Fin m) (ρ : Fin m → Fin l) :
    (witness w r R).rename ρ = witness (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, closed_rename]

theorem condition_rename {m l} (w r : Fin m) (ρ : Fin m → Fin l) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_at {m} {Γ : Context m} (w R r : Fin m) (hc : Derives Γ (closed w R)) (hr : Derives Γ (.mem r R)) :
    Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r R) := by
  have ht : Derives Γ ((Formula.mem r R).imp (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r R)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, HornStepSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE ht hr

theorem intro_condition {m} {Γ : Context m} (w r R : Fin m) (hw : Derives Γ (witness w r R)) : Derives Γ (condition w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hw

theorem tag_rename {m l} (w x y : Fin m) (ρ : Fin m → Fin l) :
    (tag w x y).rename ρ = tag (ρ w) (ρ x) (ρ y) := by
  simp only [tag, Formula.rename, tagRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem get_rename {m l} (w x i y : Fin m) (ρ : Fin m → Fin l) :
    (get w x i y).rename ρ = get (ρ w) (ρ x) (ρ i) (ρ y) := by
  simp only [get, Formula.rename, getRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem field_rename {m l} (w x i y : Fin m) (ρ : Fin m → Fin l) :
    (field w x i y).rename ρ = field (ρ w) (ρ x) (ρ i) (ρ y) := by
  simp only [field, Formula.rename, fieldRow_rename, condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem condition_natural {m} {Γ : Context m} (w r : Fin m)
    (hc : Derives Γ (condition w r)) : Derives Γ (.mem r w) := by
  let B := witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (RestrictionSyntax.subset_at _ _ _ (.conjL hB)) (.conjL (.conjR hB))

theorem condition_step {m} {Γ : Context m} (w r : Fin m)
    (hc : Derives Γ (condition w r)) :
    Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r w) := by
  let B := witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := closed_at _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ho := HornTraceMonotone.step YesMetaZFC.Automation.ObjectProjection.rules _ _ _ _ (.conjL hB) hs
  exact of_eq (HornStepSyntax.step_rename _ w r w Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectionTraceSyntax
