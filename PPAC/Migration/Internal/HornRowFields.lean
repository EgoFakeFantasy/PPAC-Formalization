import PPAC.Migration.Internal.HornNodeDisjoint

/-! 原五字段行表达式反向恢复所有内部字段；真实存在见证只在对象量词内消去。 -/
namespace PPAC.Migration.Internal.HornRowFields
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def five {α : Type} (a b c d e : α) : Fin 5 → α := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))

theorem field_graph {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (es : Fin 5 → Expr n)
    (w r : Fin m) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (Expr.node (.literal tag) (List.ofFn es)) w env r))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 tag w xs r)) : Derives Γ (graph (es i) w env (xs i)) := by
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
  have he4 := HornExprExistence.exists_value hZ4 (es 4) w.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc) hw4 hn4
  let B4 := (Formula.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc).conj (graph (es 4) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+4)))
  let Δ5 := Context.add B4 (Context.image Formula.raise Δ4)
  apply Derives.exE (p := B4) he4
  have hZ5 := ZFContext.under hZ4 B4
  have hw5 : Derives Δ5 (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw4 B4)
  have hn5 : Derives Δ5 (environmentNat n w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hn4 B4)
  have hB4 : Derives Δ5 B4 := .hyp (Or.inl rfl)
  have h0 : Derives Δ5 (graph (es 0) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (under (under (under (under (Derives.conjR hB0) B1) B2) B3) B4)
  have h1 : Derives Δ5 (graph (es 1) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (under (under (under (Derives.conjR hB1) B2) B3) B4)
  have h2 : Derives Δ5 (graph (es 2) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+2)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (under (under (Derives.conjR hB2) B3) B4)
  have h3 : Derives Δ5 (graph (es 3) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)).castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (under (Derives.conjR hB3) B4)
  have h4 : Derives Δ5 (graph (es 4) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+4))) := .conjR hB4
  have hs : ∀ a, Derives Δ5 (graph (es a) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun b => (env b).castSucc.castSucc.castSucc.castSucc.castSucc) ((five (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))) a)) :=
    fun a => Fin.cases h0 (fun b => Fin.cases h1 (fun c => Fin.cases h2 (fun d => Fin.cases h3 (fun e => Fin.cases h4 (fun z => Fin.elim0 z) e) d) c) b) a
  have hg5 : Derives Δ5 (graph (Expr.node (.literal tag) (List.ofFn es)) w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) r.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (under (under (under (under (under hg B0) B1) B2) B3) B4)
  have hc5 : Derives Δ5 (SyntaxNodeSyntax.constructor 5 tag w.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (xs a).castSucc.castSucc.castSucc.castSucc.castSucc) r.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename]) (under (under (under (under (under hc B0) B1) B2) B3) B4)
  have hy := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ5 5 tag es w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) (five (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))) hw5 hn5 hs)) hg5
  have eq := SyntaxNodeInjective.constructor_input_eq hZ5 5 tag tag w.castSucc.castSucc.castSucc.castSucc.castSucc (five (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))) (fun a => (xs a).castSucc.castSucc.castSucc.castSucc.castSucc) r.castSucc.castSucc.castSucc.castSucc.castSucc i hw5 hy hc5
  have ho := HornExprSyntax.output_subst (es i) w.castSucc.castSucc.castSucc.castSucc.castSucc ((five (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))) i) (xs i).castSucc.castSucc.castSucc.castSucc.castSucc (fun a => (env a).castSucc.castSucc.castSucc.castSucc.castSucc) eq (hs i)
  simpa only [Formula.raise, graph_rename] using ho

end PPAC.Migration.Internal.HornRowFields
