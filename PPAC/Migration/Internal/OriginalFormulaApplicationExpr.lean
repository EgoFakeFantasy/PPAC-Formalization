import PPAC.Migration.Internal.OriginalFormulaApplicationSyntax

/-! 原application输入／输出Expr与独立纯数值应用结构双向对应；所有中间码实际存在。 -/
namespace PPAC.Migration.Internal.OriginalFormulaApplicationExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax OriginalFormulaApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem graph_of_application {m a} {Γ : Context m} (i j : Fin a) (w n : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) (ha : Derives Γ (application w (env i) (env j) n)) :
    Derives Γ (graph (expr i j) w env n) := by
  let B := body w (env i) (env j) n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hn3 : Derives Δ (environmentNat a (old 3 w) (fun k => old 3 (env k))) := of_eq (environmentNat_rename a w env (old 3)) (HornBinderRules.under_body 3 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hS := OriginalFormulaScalarExpr.scalar_graph i (old 3 w) (slot 3 0) (fun k => old 3 (env k)) hn3 (.conjL hB)
  have hA : Derives Δ (graph (.var j) (old 3 w) (fun k => old 3 (env k)) (old 3 (env j))) := .conjI (environmentNat_at _ _ hn3 j) (.eqRefl _)
  have hP := HornExprStructural.cons_graph (Expr.node (.var i) []) (.var j) (old 3 w) (slot 3 0) (old 3 (env j)) (slot 3 1) (fun k => old 3 (env k)) hS hA (.conjL (.conjR hB))
  have ho := HornExprStructural.raw_graph (.literal 2) (YesMetaZFC.Automation.ObjectSyntaxTransform.cons (Expr.node (.var i) []) (.var j)) (old 3 w) (slot 3 2) (slot 3 1) (old 3 n) (fun k => old 3 (env k)) (.conjL (.conjR (.conjR hB))) hP (.conjR (.conjR (.conjR hB)))
  exact of_eq (graph_rename (expr i j) w n env (old 3)).symm ho

theorem application_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j : Fin a) (w n : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (expr i j) w env n).iff (application w (env i) (env j) n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (expr i j) w env n
    have heS := SyntaxNodes.exists_node (ZFContext.add hZ E) 0 w (env i) Fin.elim0 (add hw E) (add (environmentNat_at _ _ hn i) E) (.eqRefl w)
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.scalar w.castSucc (env i).castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := X) heS
    have hZ1 := ZFContext.under (ZFContext.add hZ E) X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) X)
    have hn1 : Derives Δ (environmentNat a w.castSucc (fun k => (env k).castSucc)) := of_eq (environmentNat_rename a w env Fin.castSucc) (under (add hn E) X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have heP := StructuralConsCore.exists_cons hZ1 w.castSucc (Fin.last m) (env j).castSucc hw1 (.conjL hX) (environmentNat_at _ _ hn1 j)
    let P := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last m).castSucc (env j).castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add P (Context.image Formula.raise Δ)
    apply Derives.exE (p := P) heP
    have hZ2 := ZFContext.under hZ1 P
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 P)
    have heT := SyntaxNumerals.exists_numeral hZ2 2 w.castSucc.castSucc hw2
    let T := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last (m+2)))
    let Xi3 := Context.add T (Context.image Formula.raise Ξ)
    apply Derives.exE (p := T) heT
    have hZ3 := ZFContext.under hZ2 T
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Xi3 p.raise.raise.raise := under (under (under (add hp E) X) P) T
    have hw3 : Derives Xi3 (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
    have hn3 : Derives Xi3 (environmentNat a w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hn)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hG : Derives Xi3 (graph (expr i j) w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc) := of_eq (by simp only [E, Formula.raise, graph_rename]) (under (under (under hE X) P) T)
    have hS3 : Derives Xi3 (SyntaxNodeSyntax.scalar w.castSucc.castSucc.castSucc (env i).castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.scalar_rename]) (under (under (.conjR hX) P) T)
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hP3 : Derives Xi3 (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (env j).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hP) T)
    have hT : Derives Xi3 T := .hyp (Or.inl rfl)
    have hSG := OriginalFormulaScalarExpr.scalar_graph i w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) hn3 hS3
    have hA : Derives Xi3 (graph (.var j) w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) (env j).castSucc.castSucc.castSucc) := .conjI (environmentNat_at _ _ hn3 j) (.eqRefl _)
    have hPG := HornExprStructural.cons_graph (Expr.node (.var i) []) (.var j) w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (env j).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (fun k => (env k).castSucc.castSucc.castSucc) hSG hA hP3
    have hRaw := Derives.impE (.conjL (HornExprStructural.raw_iff hZ3 (.literal 2) (YesMetaZFC.Automation.ObjectSyntaxTransform.cons (Expr.node (.var i) []) (.var j)) w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) hw3 hn3 (.conjR hT) hPG)) hG
    have ho := intro_application w.castSucc.castSucc.castSucc (env i).castSucc.castSucc.castSucc (env j).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hS3 hP3 (.conjR hT) hRaw
    simpa only [Formula.raise, application_rename] using ho
  · apply Derives.impI
    exact graph_of_application i j w n env (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalFormulaApplicationExpr
