import PPAC.Migration.Internal.PureSyntaxEqualityComplete
import PPAC.Migration.Internal.OriginalFormulaMemberApplication

/-! 原成员规则固定符号零的实际输入表达式与独立EX载荷；不执行宿主Expr.eval。 -/
namespace PPAC.Migration.Internal.PureSyntaxMembershipInput
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def input : Expr 3 := YesMetaZFC.Automation.ObjectTermSyntax.rawNode 2
  (YesMetaZFC.Automation.ObjectTermSyntax.cons (Expr.node (.literal 0) []) (.var 2))

def body {m} (w args n : Fin m) : Formula (m+3) :=
  (SyntaxAtomSyntax.zeroScalar (old 3 w) (slot 3 0)).conj
    ((StructuralListSyntax.consCode (old 3 w) (slot 3 0) (old 3 args) (slot 3 1)).conj
      ((SyntaxNumeralSyntax.numeral 2 (slot 3 2)).conj (StructuralNodeSyntax.raw (old 3 w) (slot 3 2) (slot 3 1) (old 3 n))))

def data {m} (w args n : Fin m) : Formula m := existsMany 3 (body w args n)

theorem body_lift {m j} (w args n : Fin m) (ρ : Fin m → Fin j) :
    (body w args n).rename (lift 3 ρ) = body (ρ w) (ρ args) (ρ n) := by
  simp only [body, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, StructuralListSyntax.consCode_rename, SyntaxNumeralSyntax.numeral_rename, StructuralNodeSyntax.raw_rename, lift_old, lift_slot]

theorem data_rename {m j} (w args n : Fin m) (ρ : Fin m → Fin j) :
    (data w args n).rename ρ = data (ρ w) (ρ args) (ρ n) := by
  simp only [data, existsMany_rename, body_lift]

theorem intro_data {m} {Γ : Context m} (w args n s p two : Fin m)
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s)) (hp : Derives Γ (StructuralListSyntax.consCode w s args p))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 two)) (hn : Derives Γ (StructuralNodeSyntax.raw w two p n)) : Derives Γ (data w args n) := by
  apply HornBinderRules.intro_many 3 (body w args n) (OriginalLookupExpr.rowFields s p two)
  exact of_eq (by simp only [body, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, StructuralListSyntax.consCode_rename, SyntaxNumeralSyntax.numeral_rename, StructuralNodeSyntax.raw_rename, assign_old, assign_slot]; rfl) (.conjI hs (.conjI hp (.conjI ht hn)))

theorem graph_of_data {m} {Γ : Context m} (w n : Fin m) (env : Fin 3 → Fin m)
    (hn : Derives Γ (environmentNat 3 w env)) (ha : Derives Γ (data w (env 2) n)) :
    Derives Γ (graph input w env n) := by
  let B := body w (env 2) n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hn3 : Derives Δ (environmentNat 3 (old 3 w) (fun k => old 3 (env k))) := of_eq (environmentNat_rename 3 w env (old 3)) (HornBinderRules.under_body 3 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hS : Derives Δ (graph (Expr.node (.literal 0) []) (old 3 w) (fun k => old 3 (env k)) (slot 3 0)) := by
    simpa only [List.ofFn_zero] using HornExprForest.constructor_graph 0 0 (Fin.elim0 : Fin 0 → Expr 3) (old 3 w) (slot 3 0) (fun k => old 3 (env k)) Fin.elim0 (fun i => Fin.elim0 i) (.conjL hB)
  have hA : Derives Δ (graph (.var (2 : Fin 3)) (old 3 w) (fun k => old 3 (env k)) (old 3 (env 2))) := .conjI (environmentNat_at _ _ hn3 (2 : Fin 3)) (.eqRefl _)
  have hP := HornExprStructural.cons_graph (Expr.node (.literal 0) []) (.var (2 : Fin 3)) (old 3 w) (slot 3 0) (old 3 (env 2)) (slot 3 1) (fun k => old 3 (env k)) hS hA (.conjL (.conjR hB))
  have ho := HornExprStructural.raw_graph (.literal 2) (YesMetaZFC.Automation.ObjectSyntaxTransform.cons (Expr.node (.literal 0) []) (.var (2 : Fin 3))) (old 3 w) (slot 3 2) (slot 3 1) (old 3 n) (fun k => old 3 (env k)) (.conjL (.conjR (.conjR hB))) hP (.conjR (.conjR (.conjR hB)))
  exact of_eq (graph_rename input w n env (old 3)).symm ho

theorem data_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((graph input w env n).iff (data w (env 2) n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph input w env n
    have heS := SyntaxConstructors.exists_constructor (ZFContext.add hZ E) 0 0 w Fin.elim0 (add hw E) (.eqRefl w)
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := X) heS
    have hZ1 := ZFContext.under (ZFContext.add hZ E) X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) X)
    have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun k => (env k).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under (add hn E) X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have heP := StructuralConsCore.exists_cons hZ1 w.castSucc (Fin.last m) (env 2).castSucc hw1 (.conjL hX) (environmentNat_at _ _ hn1 (2 : Fin 3))
    let P := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last m).castSucc (env 2).castSucc.castSucc (Fin.last (m+1)))
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
    have hn3 : Derives Xi3 (environmentNat 3 w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hn)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hG : Derives Xi3 (graph input w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc) := of_eq (by simp only [E, Formula.raise, graph_rename]) (under (under (under hE X) P) T)
    have hS3 : Derives Xi3 (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]) (under (under (.conjR hX) P) T)
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hP3 : Derives Xi3 (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (env 2).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hP) T)
    have hT : Derives Xi3 T := .hyp (Or.inl rfl)
    have hSG : Derives Xi3 (graph (Expr.node (.literal 0) []) w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc) := by
      simpa only [List.ofFn_zero] using HornExprForest.constructor_graph 0 0 (Fin.elim0 : Fin 0 → Expr 3) w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) Fin.elim0 (fun i => Fin.elim0 i) hS3
    have hA : Derives Xi3 (graph (.var (2 : Fin 3)) w.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) (env 2).castSucc.castSucc.castSucc) := .conjI (environmentNat_at _ _ hn3 (2 : Fin 3)) (.eqRefl _)
    have hPG := HornExprStructural.cons_graph (Expr.node (.literal 0) []) (.var (2 : Fin 3)) w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (env 2).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (fun k => (env k).castSucc.castSucc.castSucc) hSG hA hP3
    have hRaw := Derives.impE (.conjL (HornExprStructural.raw_iff hZ3 (.literal 2) (YesMetaZFC.Automation.ObjectSyntaxTransform.cons (Expr.node (.literal 0) []) (.var (2 : Fin 3))) w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (fun k => (env k).castSucc.castSucc.castSucc) hw3 hn3 (.conjR hT) hPG)) hG
    have ho := intro_data w.castSucc.castSucc.castSucc (env 2).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hS3 hP3 (.conjR hT) hRaw
    simpa only [Formula.raise, data_rename] using ho
  · apply Derives.impI
    exact graph_of_data w n env (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PureSyntaxMembershipInput
