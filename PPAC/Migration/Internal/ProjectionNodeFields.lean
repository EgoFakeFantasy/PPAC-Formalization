import PPAC.Migration.Internal.HornNodeFields
import PPAC.Migration.Internal.ProjectionTraceSyntax

/-! 两字段实际头图反演及投影查询全部字段的内部自然性。 -/
namespace PPAC.Migration.Internal.ProjectionNodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem field_2 {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (es : Fin 2 → Expr n)
    (w r : Fin m) (env : Fin n → Fin m) (xs : Fin 2 → Fin m) (i : Fin 2)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (Expr.node (.literal tag) (List.ofFn es)) w env r))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 2 tag w xs r)) : Derives Γ (graph (es i) w env (xs i)) := by
  have he0 := HornExprExistence.exists_value hZ (es 0) w env hw hn
  let B0 := (Formula.mem (Fin.last m) w.castSucc).conj (graph (es 0) w.castSucc (fun a => (env a).castSucc) (Fin.last m))
  let Δ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) he0
  have hZ1 := ZFContext.under hZ B0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B0)
  have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B0)
  have hB0 : Derives Δ1 B0 := .hyp (Or.inl rfl)
  have he1 := HornExprExistence.exists_value hZ1 (es 1) w.castSucc (fun a => (env a).castSucc) hw1 hn1
  let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph (es 1) w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) (Fin.last (m+1)))
  let Δ2 := Context.add B1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := B1) he1
  have hZ2 := ZFContext.under hZ1 B1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
  have hn2 := of_eq (environmentNat_rename n w.castSucc (fun a => (env a).castSucc) Fin.castSucc) (under hn1 B1)
  have hB1 : Derives Δ2 B1 := .hyp (Or.inl rfl)
  have h0 : Derives Δ2 (graph (es 0) (old 2 w) (fun a => old 2 (env a)) (Fin.last m).castSucc) :=
    of_eq (by simp only [Formula.raise, graph_rename, old]) (under (.conjR hB0) B1)
  have h1 : Derives Δ2 (graph (es 1) (old 2 w) (fun a => old 2 (env a)) (Fin.last (m+1))) := of_eq (by simp only [old]) (.conjR hB1)
  let ys := SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1))
  have hs : ∀ j, Derives Δ2 (graph (es j) (old 2 w) (fun a => old 2 (env a)) (ys j)) := Fin.cases h0 (Fin.cases h1 (fun z => Fin.elim0 z))
  have hg2 : Derives Δ2 (graph (Expr.node (.literal tag) (List.ofFn es)) (old 2 w) (fun a => old 2 (env a)) (old 2 r)) :=
    of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under hg B0) B1)
  have hc2 : Derives Δ2 (SyntaxNodeSyntax.constructor 2 tag (old 2 w) (fun a => old 2 (xs a)) (old 2 r)) :=
    of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, old]) (under (under hc B0) B1)
  have hy := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ2 2 tag es (old 2 w) (old 2 r) (fun a => old 2 (env a)) ys hw2 hn2 hs)) hg2
  have heq := SyntaxNodeInjective.constructor_input_eq hZ2 2 tag tag (old 2 w) ys (fun a => old 2 (xs a)) (old 2 r) i hw2 hy hc2
  have ho := HornExprSyntax.output_subst (es i) (old 2 w) (ys i) (old 2 (xs i)) (fun a => old 2 (env a)) heq (hs i)
  exact of_eq (by simp only [Formula.raise, graph_rename, old]) ho

theorem constructor_field_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat)
    (w r : Fin m) (xs : Fin k → Fin m) (j : Fin k) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs r)) : Derives Γ (.mem (xs j) w) :=
  StructuralListTraceOrder.member_member hZ w (xs j) r hw (SyntaxNodeInjective.constructor_range hZ k tag w xs r hw hr)
    (SyntaxConstructors.child_member hZ k tag w xs r j hw hr)

theorem tag_natural_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m) (j : Fin 2)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.tag w x y)) :
    Derives Γ (.mem ((SetLanguage.args2 x y) j) w) := by
  let B := (ProjectionTraceSyntax.tagRow w.castSucc x.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := constructor_field_natural (ZFContext.under hZ B) 2 0 w.castSucc (Fin.last m) (SetLanguage.args2 x.castSucc y.castSucc) j hw1 (.conjL hB)
  exact of_eq (congrArg (fun a => Formula.mem a w.castSucc) (congrFun (ProjectionTraceSyntax.args2_map x y Fin.castSucc) j).symm) ho

theorem get_natural_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m) (j : Fin 3)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.get w x i y)) :
    Derives Γ (.mem ((SyntaxAtomSyntax.three x i y) j) w) := by
  let B := (ProjectionTraceSyntax.getRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := constructor_field_natural (ZFContext.under hZ B) 3 1 w.castSucc (Fin.last m) (SyntaxAtomSyntax.three x.castSucc i.castSucc y.castSucc) j hw1 (.conjL hB)
  exact of_eq (congrArg (fun a => Formula.mem a w.castSucc) (congrFun (SyntaxAtomSyntax.three_map x i y Fin.castSucc) j).symm) ho

theorem field_natural_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m) (j : Fin 3)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.field w x i y)) :
    Derives Γ (.mem ((SyntaxAtomSyntax.three x i y) j) w) := by
  let B := (ProjectionTraceSyntax.fieldRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := constructor_field_natural (ZFContext.under hZ B) 3 2 w.castSucc (Fin.last m) (SyntaxAtomSyntax.three x.castSucc i.castSucc y.castSucc) j hw1 (.conjL hB)
  exact of_eq (congrArg (fun a => Formula.mem a w.castSucc) (congrFun (SyntaxAtomSyntax.three_map x i y Fin.castSucc) j).symm) ho

end PPAC.Migration.Internal.ProjectionNodeFields
