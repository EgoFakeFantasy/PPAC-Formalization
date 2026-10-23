import PPAC.Migration.Internal.PureSyntaxFormulaGraph

/-! 任意有限原赋值下的真实项前提行；用于等式与关系原子而非宿主项求值。 -/
namespace PPAC.Migration.Internal.PureSyntaxTermPremise
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def fields {a} (i j k : Fin a) : Fin 3 → Expr a := PureSyntaxFormulaGraph.fields i j (.var k)
def head {a} (i j k : Fin a) : Expr a := Expr.node (.literal 0) (List.ofFn (fields i j k))

theorem construct {m a} {Γ : Context m} (i j k : Fin a) (w p : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) (hp : Derives Γ (PureSyntaxTrace.termRow w (env i) (env j) (env k) p)) :
    Derives Γ (graph (head i j k) w env p) := by
  have hv (l : Fin a) : Derives Γ (graph (.var l) w env (env l)) := .conjI (environmentNat_at w env hn l) (.eqRefl _)
  apply HornExprForest.constructor_graph 3 0 (fields i j k) w p env (SyntaxAtomSyntax.three (env i) (env j) (env k)) _ hp
  intro l
  exact Fin.cases (hv i) (fun v => Fin.cases (hv j) (fun t => Fin.cases (hv k) (fun z => Fin.elim0 z) t) v) l

theorem checked {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j k : Fin a) (w R : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise (head i j k) w R env)) : Derives Γ (SyntaxTermSyntax.term w (env i) (env j) (env k)) := by
  let B := (graph (head i j k) w.castSucc (fun l => (env l).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat a w.castSucc (fun l => (env l).castSucc)) := of_eq (environmentNat_rename a w env Fin.castSucc) (under hn B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc B)
  have hv (l : Fin a) : Derives Δ (graph (.var l) w.castSucc (fun v => (env v).castSucc) (env l).castSucc) := .conjI (environmentNat_at _ _ hn1 l) (.eqRefl _)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornExprConstructor.constructor_iff hZ1 3 0 (fields i j k) w.castSucc (Fin.last m) (fun l => (env l).castSucc)
    (SyntaxAtomSyntax.three (env i).castSucc (env j).castSucc (env k).castSucc) hw1 hn1
    (fun l => Fin.cases (hv i) (fun v => Fin.cases (hv j) (fun t => Fin.cases (hv k) (fun z => Fin.elim0 z) t) v) l)
  have hr := Derives.impE (.conjL hi) (.conjL hB)
  have ht := PureSyntaxTermMatrix.step_sound hZ1 _ _ _ _ _ _ hw1 hr (PureSyntaxTrace.closed_at _ _ _ hc1 (.conjR hB))
  exact of_eq (SyntaxTermSyntax.term_rename w (env i) (env j) (env k) Fin.castSucc).symm ht

end PPAC.Migration.Internal.PureSyntaxTermPremise
