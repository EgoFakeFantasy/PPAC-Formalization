import PPAC.Migration.Internal.LogicalStaticQueries
import PPAC.Migration.Internal.HornExprExistence
import PPAC.Migration.Internal.HornApplicationBounds

/-! 原逻辑14嵌套数值头的完整构造子正规式；3个中间码均在对象EX取得／消去。 -/
namespace PPAC.Migration.Internal.LogicalRule14Head
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix SyntaxNodeSyntax.constructor

def part0 : Expr 3 := ObjectLogicalAxiom.node 14 [.var 1, .var 2]

def fields0 {m} (env : Fin 3 → Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (env 2) (Fin.elim0)))

theorem fields0_map {m l} (env : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields0 env i)) = fields0 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node0_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    : Derives Γ ((graph part0 w env v).iff (SyntaxNodeSyntax.constructor 2 14 w (fields0 env) v)) := by
  let es : Fin 2 → Expr 3 := (Fin.cases (.var 1) (Fin.cases (.var 2) (Fin.elim0)))
  have he : part0 = Expr.node (.literal 14) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 14 es w v env (fields0 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    · exact Fin.elim0 j1

def part1 : Expr 3 := ObjectLogicalAxiom.node 6 [.var 1, .var 2]

def fields1 {m} (env : Fin 3 → Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (env 2) (Fin.elim0)))

theorem fields1_map {m l} (env : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields1 env i)) = fields1 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node1_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    : Derives Γ ((graph part1 w env v).iff (SyntaxNodeSyntax.constructor 2 6 w (fields1 env) v)) := by
  let es : Fin 2 → Expr 3 := (Fin.cases (.var 1) (Fin.cases (.var 2) (Fin.elim0)))
  have he : part1 = Expr.node (.literal 6) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 6 es w v env (fields1 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    · exact Fin.elim0 j1

def part2 : Expr 3 := ObjectLogicalAxiom.node 7 [.var 1, part1]

def fields2 {m} (env : Fin 3 → Fin m) (c1 : Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (c1) (Fin.elim0)))

theorem fields2_map {m l} (env : Fin 3 → Fin m) (c1 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields2 env c1 i)) = fields2 (fun i => ρ (env i)) (ρ c1) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node2_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c1 : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hc1 : Derives Γ (graph part1 w env c1))
    : Derives Γ ((graph part2 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields2 env c1) v)) := by
  let es : Fin 2 → Expr 3 := (Fin.cases (.var 1) (Fin.cases (part1) (Fin.elim0)))
  have he : part2 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields2 env c1) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc1
    · exact Fin.elim0 j1

def part3 : Expr 3 := ObjectLogicalAxiom.rule14.head

def fields3 {m} (env : Fin 3 → Fin m) (c0 c2 : Fin m) : Fin 3 → Fin m := (Fin.cases (env 0) (Fin.cases (c0) (Fin.cases (c2) (Fin.elim0))))

theorem fields3_map {m l} (env : Fin 3 → Fin m) (c0 c2 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields3 env c0 c2 i)) = fields3 (fun i => ρ (env i)) (ρ c0) (ρ c2) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact rfl
      · exact Fin.elim0 j2

theorem node3_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c0 c2 : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hc0 : Derives Γ (graph part0 w env c0))
    (hc2 : Derives Γ (graph part2 w env c2))
    : Derives Γ ((graph part3 w env v).iff (SyntaxNodeSyntax.constructor 3 0 w (fields3 env c0 c2) v)) := by
  let es : Fin 3 → Expr 3 := (Fin.cases (.var 0) (Fin.cases (part0) (Fin.cases (part2) (Fin.elim0))))
  have he : part3 = Expr.node (.literal 0) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 3 0 es w v env (fields3 env c0 c2) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 0) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc0
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact hc2
      · exact Fin.elim0 j2

def atValues {m} (w row : Fin m) (env : Fin 3 → Fin m) (ys : Fin 3 → Fin m) : Formula m :=
  (SyntaxNodeSyntax.constructor 2 14 w (fields0 env) (ys 0)).conj ((SyntaxNodeSyntax.constructor 2 6 w (fields1 env) (ys 1)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields2 env (ys 1)) (ys 2)).conj (SyntaxNodeSyntax.constructor 3 0 w (fields3 env (ys 0) (ys 2)) row)))

theorem atValues_rename {m l} (w row : Fin m) (env : Fin 3 → Fin m) (ys : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (atValues w row env ys).rename ρ = atValues (ρ w) (ρ row) (fun i => ρ (env i)) (fun i => ρ (ys i)) := by
  simp only [atValues, Formula.rename, SyntaxNodeSyntax.constructor_rename, fields0_map, fields1_map, fields2_map, fields3_map]

def body {m} (w row : Fin m) (env : Fin 3 → Fin m) : Formula (m+3) :=
  atValues (old 3 w) (old 3 row) (fun i => old 3 (env i)) (slot 3)

def normalized {m} (w row : Fin m) (env : Fin 3 → Fin m) : Formula m := existsMany 3 (body w row env)

theorem body_lift {m l} (w row : Fin m) (env : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (body w row env).rename (lift 3 ρ) = body (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [body, atValues_rename, lift_old, lift_slot]

theorem normalized_rename {m l} (w row : Fin m) (env : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (normalized w row env).rename ρ = normalized (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [normalized, existsMany_rename, body_lift]

theorem intro_normalized {m} {Γ : Context m} (w row : Fin m) (env : Fin 3 → Fin m) (ys : Fin 3 → Fin m)
    (hc : Derives Γ (atValues w row env ys)) : Derives Γ (normalized w row env) := by
  apply HornBinderRules.intro_many 3 (body w row env) ys
  exact of_eq (by simp only [body, atValues_rename, assign_old, assign_slot]) hc

attribute [local irreducible] HornExprSyntax.graph
set_option maxHeartbeats 1200000 in
theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((graph ObjectLogicalAxiom.rule14.head w env row).iff (normalized w row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph ObjectLogicalAxiom.rule14.head w env row
    have hRoot0 : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hw0 := add hw E
    have hn0 := add hn E
    let B0 := (Formula.mem (Fin.last m) w.castSucc).conj (graph part0 w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ1 := Context.add B0 (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B0) (HornExprExistence.exists_value hZ0 part0 w (fun i => (env i)) hw0 hn0)
    have hZ1 := ZFContext.under hZ0 B0
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw0 B0)
    have hn1 := of_eq (environmentNat_rename 3 w (fun i => (env i)) Fin.castSucc) (under hn0 B0)
    have hRoot1 := of_eq (graph_rename ObjectLogicalAxiom.rule14.head w row (fun i => (env i)) Fin.castSucc) (under hRoot0 B0)
    have hB0 : Derives Δ1 B0 := .hyp (Or.inl rfl)
    have hV0_1 := Derives.conjR hB0
    let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph part1 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1)))
    let Δ2 := Context.add B1 (Context.image Formula.raise (Δ1))
    apply Derives.exE (p := B1) (HornExprExistence.exists_value hZ1 part1 w.castSucc (fun i => (env i).castSucc) hw1 hn1)
    have hZ2 := ZFContext.under hZ1 B1
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
    have hn2 := of_eq (environmentNat_rename 3 w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 B1)
    have hRoot2 := of_eq (graph_rename ObjectLogicalAxiom.rule14.head w.castSucc row.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hRoot1 B1)
    have hB1 : Derives Δ2 B1 := .hyp (Or.inl rfl)
    have hV1_2 := Derives.conjR hB1
    have hV0_2 := of_eq (graph_rename part0 w.castSucc (Fin.last m) (fun i => (env i).castSucc) Fin.castSucc) (under hV0_1 B1)
    let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (graph part2 w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.last (m+2)))
    let Δ3 := Context.add B2 (Context.image Formula.raise (Δ2))
    apply Derives.exE (p := B2) (HornExprExistence.exists_value hZ2 part2 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) hw2 hn2)
    have hZ3 := ZFContext.under hZ2 B2
    have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
    have hn3 := of_eq (environmentNat_rename 3 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hn2 B2)
    have hRoot3 := of_eq (graph_rename ObjectLogicalAxiom.rule14.head w.castSucc.castSucc row.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hRoot2 B2)
    have hB2 : Derives Δ3 B2 := .hyp (Or.inl rfl)
    have hV2_3 := Derives.conjR hB2
    have hV0_3 := of_eq (graph_rename part0 w.castSucc.castSucc (Fin.last m).castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hV0_2 B2)
    have hV1_3 := of_eq (graph_rename part1 w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hV1_2 B2)
    have hC0 := Derives.impE (.conjL (node0_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) hw3 hn3)) hV0_3
    have hC1 := Derives.impE (.conjL (node1_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (fun i => (env i).castSucc.castSucc.castSucc) hw3 hn3)) hV1_3
    have hC2 := Derives.impE (.conjL (node2_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc (fun i => (env i).castSucc.castSucc.castSucc) hw3 hn3 hV1_3)) hV2_3
    have hC3 := Derives.impE (.conjL (node3_iff hZ3 w.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (fun i => (env i).castSucc.castSucc.castSucc) hw3 hn3 hV0_3 hV2_3)) hRoot3
    have ho := intro_normalized w.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.cases ((Fin.last m).castSucc.castSucc) (Fin.cases ((Fin.last (m+1)).castSucc) (Fin.cases ((Fin.last (m+2))) (Fin.elim0)))) (.conjI hC0 (.conjI hC1 (.conjI hC2 hC3)))
    exact of_eq (by simp only [Formula.raise, normalized_rename]) ho
  · apply Derives.impI
    let E := normalized w row env
    let B := body w row env
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 (add hw E) B)
    have hn1 := of_eq (environmentNat_rename 3 w env (old 3)) (HornBinderRules.under_body 3 (add hn E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hG0 := Derives.impE (.conjR (node0_iff hZ1 (old 3 w) (slot 3 0) (fun i => old 3 (env i)) hw1 hn1)) (Derives.conjL hB)
    have hG1 := Derives.impE (.conjR (node1_iff hZ1 (old 3 w) (slot 3 1) (fun i => old 3 (env i)) hw1 hn1)) (Derives.conjL (Derives.conjR hB))
    have hG2 := Derives.impE (.conjR (node2_iff hZ1 (old 3 w) (slot 3 2) (slot 3 1) (fun i => old 3 (env i)) hw1 hn1 hG1)) (Derives.conjL (Derives.conjR (Derives.conjR hB)))
    have hG3 := Derives.impE (.conjR (node3_iff hZ1 (old 3 w) (old 3 row) (slot 3 0) (slot 3 2) (fun i => old 3 (env i)) hw1 hn1 hG0 hG2)) (Derives.conjR (Derives.conjR (Derives.conjR hB)))
    exact of_eq (graph_rename ObjectLogicalAxiom.rule14.head w row env (old 3)).symm hG3

end PPAC.Migration.Internal.LogicalRule14Head
