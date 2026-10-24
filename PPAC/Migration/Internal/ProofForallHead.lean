import PPAC.Migration.Internal.ProofForallBounds
import PPAC.Migration.Internal.HornExprExistence

/-! 原forall头的实际嵌套node3[v0,node9[v1],v2]，中间全称公式码由对象EX取得／消去。 -/
namespace PPAC.Migration.Internal.ProofForallHead
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def quantified : Expr 4 := ObjectProofNode.node 9 [.var 1]

def fields {m} (env : Fin 4 → Fin m) (v : Fin m) : Fin 3 → Fin m :=
  Fin.cases (env 0) (Fin.cases v (Fin.cases (env 2) Fin.elim0))

theorem fields_map {m l} (env : Fin 4 → Fin m) (v : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields env v i)) = fields (fun j => ρ (env j)) (ρ v) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun t => Fin.elim0 t) k) j) i

def atQuantifier {m} (w row v : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (SyntaxNodeSyntax.constructor 1 9 w (fun _ : Fin 1 => env 1) v).conj
    (SyntaxNodeSyntax.constructor 3 3 w (fields env v) row)

def normalized {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  (atQuantifier w.castSucc row.castSucc (Fin.last m) (fun j => (env j).castSucc))

theorem atQuantifier_rename {m l} (w row v : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atQuantifier w row v env).rename ρ = atQuantifier (ρ w) (ρ row) (ρ v) (fun j => ρ (env j)) := by
  simp only [atQuantifier, Formula.rename, SyntaxNodeSyntax.constructor_rename, fields_map]

theorem normalized_rename {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (normalized w row env).rename ρ = normalized (ρ w) (ρ row) (fun j => ρ (env j)) := by
  simp only [normalized, Formula.rename, atQuantifier_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_normalized {m} {Γ : Context m} (w row v : Fin m) (env : Fin 4 → Fin m)
    (h : Derives Γ (atQuantifier w row v env)) : Derives Γ (normalized w row env) := by
  apply Derives.exI v
  simpa only [normalized, Formula.instantiate, atQuantifier_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph quantified w env v).iff (SyntaxNodeSyntax.constructor 1 9 w (fun _ : Fin 1 => env 1) v)) := by
  exact HornExprConstructor.constructor_iff hZ 1 9 (fun _ : Fin 1 => .var 1) w v env (fun _ : Fin 1 => env 1) hw hn
    (fun _ => .conjI (environmentNat_at w env hn 1) (.eqRefl _))

theorem outer_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hv : Derives Γ (graph quantified w env v)) :
    Derives Γ ((graph ObjectProofNode.forallShape.head w env row).iff
      (SyntaxNodeSyntax.constructor 3 3 w (fields env v) row)) := by
  let exprs : Fin 3 → Expr 4 := Fin.cases (.var 0) (Fin.cases quantified (Fin.cases (.var 2) Fin.elim0))
  have he : ObjectProofNode.forallShape.head = Expr.node (.literal 3) (List.ofFn exprs) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 3 3 exprs w row env (fields env v) hw hn
  intro i
  exact Fin.cases (.conjI (environmentNat_at w env hn 0) (.eqRefl _))
    (fun j => Fin.cases hv (fun k => Fin.cases (.conjI (environmentNat_at w env hn 2) (.eqRefl _)) (fun t => Fin.elim0 t) k) j) i

theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph ObjectProofNode.forallShape.head w env row).iff (normalized w row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph ObjectProofNode.forallShape.head w env row
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (graph quantified w.castSucc (fun j => (env j).castSucc) (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (HornExprExistence.exists_value (ZFContext.add hZ E) quantified w env (add hw E) (add hn E))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hE : Derives Δ (graph ObjectProofNode.forallShape.head w.castSucc (fun j => (env j).castSucc) row.castSucc) :=
      of_eq (graph_rename _ w row env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hq := Derives.impE (.conjL (quantified_iff hZ1 _ _ _ hw1 hn1)) (.conjR hB)
    have ho := Derives.impE (.conjL (outer_iff hZ1 _ _ _ _ hw1 hn1 (.conjR hB))) hE
    exact of_eq (normalized_rename w row env Fin.castSucc).symm (intro_normalized _ _ _ _ (.conjI hq ho))
  · apply Derives.impI
    let E := normalized w row env
    let B := atQuantifier w.castSucc row.castSucc (Fin.last m) (fun j => (env j).castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hq := Derives.impE (.conjR (quantified_iff hZ1 _ _ _ hw1 hn1)) (.conjL hB)
    have ho := Derives.impE (.conjR (outer_iff hZ1 _ _ _ _ hw1 hn1 hq)) (.conjR hB)
    exact of_eq (graph_rename ObjectProofNode.forallShape.head w row env Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofForallHead
