import PPAC.Migration.Internal.PureSyntaxFormulaInductionSyntax

/-! 真实子公式前提，绑定界可为实际表达式值；严格子码IH只在对象公式内实例化。 -/
namespace PPAC.Migration.Internal.PureSyntaxFormulaPremise
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def fields {a} (bound : Expr a) (free child : Fin a) : Fin 3 → Expr a := Fin.cases bound (Fin.cases (.var free) (Fin.cases (.var child) Fin.elim0))
def head {a} (bound : Expr a) (free child : Fin a) : Expr a := Expr.node (.literal 4) (List.ofFn (fields bound free child))

theorem construct {m a} {Γ : Context m} (bound : Expr a) (free child : Fin a) (w B p : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) (hb : Derives Γ (graph bound w env B))
    (hp : Derives Γ (PureSyntaxTrace.formulaRow w B (env free) (env child) p)) : Derives Γ (graph (head bound free child) w env p) := by
  have hv (i : Fin a) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  apply HornExprForest.constructor_graph 3 4 (fields bound free child) w p env (SyntaxAtomSyntax.three B (env free) (env child)) _ hp
  intro i
  exact Fin.cases hb (fun j => Fin.cases (hv free) (fun k => Fin.cases (hv child) (fun z => Fin.elim0 z) k) j) i

theorem checked {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Expr a) (free child : Fin a)
    (w B R : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hb : Derives Γ (graph bound w env B)) (hs : Derives Γ (RestrictionSyntax.subset R w))
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hp : Derives Γ (HornRuleSyntax.premise (head bound free child) w R env)) :
    Derives Γ (PureSyntaxTrace.formula w B (env free) (env child)) := by
  let A := (graph (head bound free child) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) hp
  have hZ1 := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hn1 : Derives Δ (environmentNat a w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename a w env Fin.castSucc) (under hn A)
  have hb1 : Derives Δ (graph bound w.castSucc (fun i => (env i).castSucc) B.castSucc) := of_eq (graph_rename bound w B env Fin.castSucc) (under hb A)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs A)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (PureSyntaxTrace.closed_rename w R Fin.castSucc) (under hc A)
  have hv (i : Fin a) : Derives Δ (graph (.var i) w.castSucc (fun j => (env j).castSucc) (env i).castSucc) := .conjI (environmentNat_at _ _ hn1 i) (.eqRefl _)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hi := HornExprConstructor.constructor_iff hZ1 3 4 (fields bound free child) w.castSucc (Fin.last m) (fun i => (env i).castSucc)
    (SyntaxAtomSyntax.three B.castSucc (env free).castSucc (env child).castSucc) hw1 hn1
    (fun i => Fin.cases hb1 (fun j => Fin.cases (hv free) (fun k => Fin.cases (hv child) (fun z => Fin.elim0 z) k) j) i)
  have hr := Derives.impE (.conjL hi) (.conjL hA)
  have hcond := PureSyntaxTrace.intro_condition _ _ _ (.conjI hs1 (.conjI (.conjR hA) hc1))
  have hout := PureSyntaxFormulaGraph.intro_formula _ _ _ _ _ hr hcond
  exact of_eq (PureSyntaxTrace.formula_rename w B (env free) (env child) Fin.castSucc).symm hout

theorem typed_from_induction {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Expr a) (free child : Fin a)
    (w n B R : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hi : Derives Γ (allIH w n)) (hl : Derives Γ (.mem (env child) n)) (hb : Derives Γ (graph bound w env B))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise (head bound free child) w R env)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w (env child) B (env free)) :=
  .impE (.conjL (correct_at w (env child) B (env free) (allIH_at w n (env child) hi hl)))
    (checked hZ bound free child w B R env hw hn hb hs hc hp)

end PPAC.Migration.Internal.PureSyntaxFormulaPremise
