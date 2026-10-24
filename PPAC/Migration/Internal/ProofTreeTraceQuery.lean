import PPAC.Migration.Internal.ProofTreeEntrySyntax

/-! 原递归前提的数值构造器查询；全部行见证在对象EX中取得和消去。 -/
namespace PPAC.Migration.Internal.ProofTreeTraceQuery
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def query {m a} (test : Formula 1) (e : Expr a) (w : Fin m) (env : Fin a → Fin m) : Formula m := .ex
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m)))

def rowQuery {m} (test : Formula 1) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m)))

theorem query_rename {m a l} (test : Formula 1) (e : Expr a) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (query test e w env).rename ρ = query test e (ρ w) (fun i => ρ (env i)) := by
  simp only [query, Formula.rename, graph_rename, ProofTreeTraceSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rowQuery_rename {m l} (test : Formula 1) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin l) :
    (rowQuery test k tag w xs).rename ρ = rowQuery test k tag (ρ w) (fun i => ρ (xs i)) := by
  simp only [rowQuery, Formula.rename, SyntaxNodeSyntax.constructor_rename, ProofTreeTraceSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem constructor_query_iff {m a} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (k tag : Nat) (es : Fin k → Expr a)
    (w : Fin m) (env : Fin a → Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hs : ∀ i, Derives Γ (graph (es i) w env (xs i))) :
    Derives Γ ((query test (Expr.node (.literal tag) (List.ofFn es)) w env).iff (rowQuery test k tag w xs)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := query test (Expr.node (.literal tag) (List.ofFn es)) w env
    let B := (graph (Expr.node (.literal tag) (List.ofFn es)) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (lift hn)
    have hs1 (i : Fin k) := of_eq (graph_rename (es i) w (xs i) env Fin.castSucc) (lift (hs i))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc := Derives.impE (.conjL (HornExprConstructor.constructor_iff (ZFContext.under (ZFContext.add hZ E) B) k tag es w.castSucc (Fin.last m) (fun i => (env i).castSucc) (fun i => (xs i).castSucc) hw1 hn1 hs1)) (.conjL hB)
    have hout : Derives Δ (rowQuery test k tag w.castSucc (fun i => (xs i).castSucc)) := by
      apply Derives.exI (Fin.last m)
      simpa only [rowQuery, Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, ProofTreeTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hc (.conjR hB)
    exact of_eq (rowQuery_rename test k tag w xs Fin.castSucc).symm hout
  · apply Derives.impI
    let E := rowQuery test k tag w xs
    let B := (SyntaxNodeSyntax.constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (lift hn)
    have hs1 (i : Fin k) := of_eq (graph_rename (es i) w (xs i) env Fin.castSucc) (lift (hs i))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hg := Derives.impE (.conjR (HornExprConstructor.constructor_iff (ZFContext.under (ZFContext.add hZ E) B) k tag es w.castSucc (Fin.last m) (fun i => (env i).castSucc) (fun i => (xs i).castSucc) hw1 hn1 hs1)) (.conjL hB)
    have hout : Derives Δ (query test (Expr.node (.literal tag) (List.ofFn es)) w.castSucc (fun i => (env i).castSucc)) := by
      apply Derives.exI (Fin.last m)
      simpa only [query, Formula.instantiate, Formula.rename, graph_rename, ProofTreeTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hg (.conjR hB)
    exact of_eq (query_rename test _ w env Fin.castSucc).symm hout

end PPAC.Migration.Internal.ProofTreeTraceQuery
