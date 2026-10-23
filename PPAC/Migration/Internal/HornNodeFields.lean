import PPAC.Migration.Internal.HornRowFields

/-! 三／四字段原规则头的实际字段反演，所有表达式值在对象存在量词内取得。 -/
namespace PPAC.Migration.Internal.HornNodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem field_3 {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (es : Fin 3 → Expr n)
    (w r : Fin m) (env : Fin n → Fin m) (xs : Fin 3 → Fin m) (i : Fin 3)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (Expr.node (.literal tag) (List.ofFn es)) w env r))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 3 tag w xs r)) : Derives Γ (graph (es i) w env (xs i)) := by
  have he0 := HornExprExistence.exists_value hZ (es 0) w env hw hn
  let B0 := (Formula.mem (Fin.last (m+0)) w.castSucc).conj (graph (es 0) w.castSucc (fun a => (env a).castSucc) (Fin.last (m+0)))
  let Δ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) he0
  have hZ1 := ZFContext.under hZ B0
  have hw1 : Derives Δ1 (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B0)
  have hn1 : Derives Δ1 (environmentNat n w.castSucc (fun a => (env a).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B0)
  have hB0 : Derives Δ1 B0 := .hyp (Or.inl rfl)
  have he1 := HornExprExistence.exists_value hZ1 (es 1) w.castSucc (fun a => (env a).castSucc) hw1 hn1
  let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph (es 1) w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) (Fin.last (m+1)))
  let Δ2 := Context.add B1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := B1) he1
  have hZ2 := ZFContext.under hZ1 B1
  have hw2 : Derives Δ2 (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
  have hn2 : Derives Δ2 (environmentNat n w.castSucc.castSucc (fun a => (env a).castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc (fun a => (env a).castSucc) Fin.castSucc) (under hn1 B1)
  have hB1 : Derives Δ2 B1 := .hyp (Or.inl rfl)
  have he2 := HornExprExistence.exists_value hZ2 (es 2) w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) hw2 hn2
  let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (graph (es 2) w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Δ3 := Context.add B2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := B2) he2
  have hZ3 := ZFContext.under hZ2 B2
  have hw3 : Derives Δ3 (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
  have hn3 : Derives Δ3 (environmentNat n w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) Fin.castSucc) (under hn2 B2)
  have hB2 : Derives Δ3 B2 := .hyp (Or.inl rfl)
  have h0 : Derives Δ3 (graph (es 0) (old 3 w) (fun a => old 3 (env a)) (Fin.last (m+0)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under (.conjR hB0) B1) B2)
  have h1 : Derives Δ3 (graph (es 1) (old 3 w) (fun a => old 3 (env a)) (Fin.last (m+1)).castSucc) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (.conjR hB1) B2)
  have h2 : Derives Δ3 (graph (es 2) (old 3 w) (fun a => old 3 (env a)) (Fin.last (m+2))) := of_eq (by simp only [old]) (.conjR hB2)
  let ys : Fin 3 → Fin (m+3) := Fin.cases (Fin.last (m+0)).castSucc.castSucc (Fin.cases (Fin.last (m+1)).castSucc (Fin.cases (Fin.last (m+2)) (Fin.elim0)))
  have hs : ∀ j, Derives Δ3 (graph (es j) (old 3 w) (fun a => old 3 (env a)) (ys j)) := Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun z => Fin.elim0 z)))
  have hg3 : Derives Δ3 (graph (Expr.node (.literal tag) (List.ofFn es)) (old 3 w) (fun a => old 3 (env a)) (old 3 r)) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under (under hg B0) B1) B2)
  have hc3 : Derives Δ3 (SyntaxNodeSyntax.constructor 3 tag (old 3 w) (fun a => old 3 (xs a)) (old 3 r)) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, old]) (under (under (under hc B0) B1) B2)
  have hy := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ3 3 tag es (old 3 w) (old 3 r) (fun a => old 3 (env a)) ys hw3 hn3 hs)) hg3
  have heq := SyntaxNodeInjective.constructor_input_eq hZ3 3 tag tag (old 3 w) ys (fun a => old 3 (xs a)) (old 3 r) i hw3 hy hc3
  have ho := HornExprSyntax.output_subst (es i) (old 3 w) (ys i) (old 3 (xs i)) (fun a => old 3 (env a)) heq (hs i)
  exact of_eq (by simp only [Formula.raise, graph_rename, old]) ho

theorem field_4 {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (es : Fin 4 → Expr n)
    (w r : Fin m) (env : Fin n → Fin m) (xs : Fin 4 → Fin m) (i : Fin 4)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (Expr.node (.literal tag) (List.ofFn es)) w env r))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 4 tag w xs r)) : Derives Γ (graph (es i) w env (xs i)) := by
  have he0 := HornExprExistence.exists_value hZ (es 0) w env hw hn
  let B0 := (Formula.mem (Fin.last (m+0)) w.castSucc).conj (graph (es 0) w.castSucc (fun a => (env a).castSucc) (Fin.last (m+0)))
  let Δ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) he0
  have hZ1 := ZFContext.under hZ B0
  have hw1 : Derives Δ1 (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B0)
  have hn1 : Derives Δ1 (environmentNat n w.castSucc (fun a => (env a).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B0)
  have hB0 : Derives Δ1 B0 := .hyp (Or.inl rfl)
  have he1 := HornExprExistence.exists_value hZ1 (es 1) w.castSucc (fun a => (env a).castSucc) hw1 hn1
  let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph (es 1) w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) (Fin.last (m+1)))
  let Δ2 := Context.add B1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := B1) he1
  have hZ2 := ZFContext.under hZ1 B1
  have hw2 : Derives Δ2 (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
  have hn2 : Derives Δ2 (environmentNat n w.castSucc.castSucc (fun a => (env a).castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc (fun a => (env a).castSucc) Fin.castSucc) (under hn1 B1)
  have hB1 : Derives Δ2 B1 := .hyp (Or.inl rfl)
  have he2 := HornExprExistence.exists_value hZ2 (es 2) w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) hw2 hn2
  let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (graph (es 2) w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc) (Fin.last (m+2)))
  let Δ3 := Context.add B2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := B2) he2
  have hZ3 := ZFContext.under hZ2 B2
  have hw3 : Derives Δ3 (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
  have hn3 : Derives Δ3 (environmentNat n w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc.castSucc (fun a => (env a).castSucc.castSucc) Fin.castSucc) (under hn2 B2)
  have hB2 : Derives Δ3 B2 := .hyp (Or.inl rfl)
  have he3 := HornExprExistence.exists_value hZ3 (es 3) w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc) hw3 hn3
  let B3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (graph (es 3) w.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)))
  let Δ4 := Context.add B3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := B3) he3
  have hZ4 := ZFContext.under hZ3 B3
  have hw4 : Derives Δ4 (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 B3)
  have hn4 : Derives Δ4 (environmentNat n w.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc) Fin.castSucc) (under hn3 B3)
  have hB3 : Derives Δ4 B3 := .hyp (Or.inl rfl)
  have h0 : Derives Δ4 (graph (es 0) (old 4 w) (fun a => old 4 (env a)) (Fin.last (m+0)).castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under (under (.conjR hB0) B1) B2) B3)
  have h1 : Derives Δ4 (graph (es 1) (old 4 w) (fun a => old 4 (env a)) (Fin.last (m+1)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under (.conjR hB1) B2) B3)
  have h2 : Derives Δ4 (graph (es 2) (old 4 w) (fun a => old 4 (env a)) (Fin.last (m+2)).castSucc) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (.conjR hB2) B3)
  have h3 : Derives Δ4 (graph (es 3) (old 4 w) (fun a => old 4 (env a)) (Fin.last (m+3))) := of_eq (by simp only [old]) (.conjR hB3)
  let ys : Fin 4 → Fin (m+4) := Fin.cases (Fin.last (m+0)).castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+1)).castSucc.castSucc (Fin.cases (Fin.last (m+2)).castSucc (Fin.cases (Fin.last (m+3)) (Fin.elim0))))
  have hs : ∀ j, Derives Δ4 (graph (es j) (old 4 w) (fun a => old 4 (env a)) (ys j)) := Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun z => Fin.elim0 z))))
  have hg4 : Derives Δ4 (graph (Expr.node (.literal tag) (List.ofFn es)) (old 4 w) (fun a => old 4 (env a)) (old 4 r)) := of_eq (by simp only [Formula.raise, graph_rename, old]) (under (under (under (under hg B0) B1) B2) B3)
  have hc4 : Derives Δ4 (SyntaxNodeSyntax.constructor 4 tag (old 4 w) (fun a => old 4 (xs a)) (old 4 r)) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename, old]) (under (under (under (under hc B0) B1) B2) B3)
  have hy := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ4 4 tag es (old 4 w) (old 4 r) (fun a => old 4 (env a)) ys hw4 hn4 hs)) hg4
  have heq := SyntaxNodeInjective.constructor_input_eq hZ4 4 tag tag (old 4 w) ys (fun a => old 4 (xs a)) (old 4 r) i hw4 hy hc4
  have ho := HornExprSyntax.output_subst (es i) (old 4 w) (ys i) (old 4 (xs i)) (fun a => old 4 (env a)) heq (hs i)
  exact of_eq (by simp only [Formula.raise, graph_rename, old]) ho

end PPAC.Migration.Internal.HornNodeFields
