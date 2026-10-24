import PPAC.Migration.Internal.LogicalStaticQueries
import PPAC.Migration.Internal.HornExprExistence
import PPAC.Migration.Internal.HornApplicationBounds

/-! 原逻辑0嵌套数值头的完整构造子正规式；7个中间码均在对象EX取得／消去。 -/
namespace PPAC.Migration.Internal.LogicalRule0Head
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix SyntaxNodeSyntax.constructor

def part0 : Expr 4 := ObjectLogicalAxiom.node 0 [.var 1, .var 2, .var 3]

def fields0 {m} (env : Fin 4 → Fin m) : Fin 3 → Fin m := (Fin.cases (env 1) (Fin.cases (env 2) (Fin.cases (env 3) (Fin.elim0))))

theorem fields0_map {m l} (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields0 env i)) = fields0 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact rfl
      · exact Fin.elim0 j2

theorem node0_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    : Derives Γ ((graph part0 w env v).iff (SyntaxNodeSyntax.constructor 3 0 w (fields0 env) v)) := by
  let es : Fin 3 → Expr 4 := (Fin.cases (.var 1) (Fin.cases (.var 2) (Fin.cases (.var 3) (Fin.elim0))))
  have he : part0 = Expr.node (.literal 0) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 3 0 es w v env (fields0 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact (.conjI (environmentNat_at w env hn 3) (.eqRefl _))
      · exact Fin.elim0 j2

def part1 : Expr 4 := ObjectLogicalAxiom.node 7 [.var 2, .var 3]

def fields1 {m} (env : Fin 4 → Fin m) : Fin 2 → Fin m := (Fin.cases (env 2) (Fin.cases (env 3) (Fin.elim0)))

theorem fields1_map {m l} (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields1 env i)) = fields1 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node1_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    : Derives Γ ((graph part1 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields1 env) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (.var 2) (Fin.cases (.var 3) (Fin.elim0)))
  have he : part1 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields1 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 3) (.eqRefl _))
    · exact Fin.elim0 j1

def part2 : Expr 4 := ObjectLogicalAxiom.node 7 [.var 1, part1]

def fields2 {m} (env : Fin 4 → Fin m) (c1 : Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (c1) (Fin.elim0)))

theorem fields2_map {m l} (env : Fin 4 → Fin m) (c1 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields2 env c1 i)) = fields2 (fun i => ρ (env i)) (ρ c1) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node2_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c1 : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc1 : Derives Γ (graph part1 w env c1))
    : Derives Γ ((graph part2 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields2 env c1) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (.var 1) (Fin.cases (part1) (Fin.elim0)))
  have he : part2 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields2 env c1) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc1
    · exact Fin.elim0 j1

def part3 : Expr 4 := ObjectLogicalAxiom.node 7 [.var 1, .var 2]

def fields3 {m} (env : Fin 4 → Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (env 2) (Fin.elim0)))

theorem fields3_map {m l} (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields3 env i)) = fields3 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node3_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    : Derives Γ ((graph part3 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields3 env) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (.var 1) (Fin.cases (.var 2) (Fin.elim0)))
  have he : part3 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields3 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 2) (.eqRefl _))
    · exact Fin.elim0 j1

def part4 : Expr 4 := ObjectLogicalAxiom.node 7 [.var 1, .var 3]

def fields4 {m} (env : Fin 4 → Fin m) : Fin 2 → Fin m := (Fin.cases (env 1) (Fin.cases (env 3) (Fin.elim0)))

theorem fields4_map {m l} (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields4 env i)) = fields4 (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node4_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    : Derives Γ ((graph part4 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields4 env) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (.var 1) (Fin.cases (.var 3) (Fin.elim0)))
  have he : part4 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields4 env) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 1) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact (.conjI (environmentNat_at w env hn 3) (.eqRefl _))
    · exact Fin.elim0 j1

def part5 : Expr 4 := ObjectLogicalAxiom.node 7 [part3, part4]

def fields5 {m} (_env : Fin 4 → Fin m) (c3 c4 : Fin m) : Fin 2 → Fin m := (Fin.cases (c3) (Fin.cases (c4) (Fin.elim0)))

theorem fields5_map {m l} (env : Fin 4 → Fin m) (c3 c4 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields5 env c3 c4 i)) = fields5 (fun i => ρ (env i)) (ρ c3) (ρ c4) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node5_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c3 c4 : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc3 : Derives Γ (graph part3 w env c3))
    (hc4 : Derives Γ (graph part4 w env c4))
    : Derives Γ ((graph part5 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields5 env c3 c4) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (part3) (Fin.cases (part4) (Fin.elim0)))
  have he : part5 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields5 env c3 c4) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact hc3
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc4
    · exact Fin.elim0 j1

def part6 : Expr 4 := ObjectLogicalAxiom.node 7 [part2, part5]

def fields6 {m} (_env : Fin 4 → Fin m) (c2 c5 : Fin m) : Fin 2 → Fin m := (Fin.cases (c2) (Fin.cases (c5) (Fin.elim0)))

theorem fields6_map {m l} (env : Fin 4 → Fin m) (c2 c5 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields6 env c2 c5 i)) = fields6 (fun i => ρ (env i)) (ρ c2) (ρ c5) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · exact Fin.elim0 j1

theorem node6_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c2 c5 : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc2 : Derives Γ (graph part2 w env c2))
    (hc5 : Derives Γ (graph part5 w env c5))
    : Derives Γ ((graph part6 w env v).iff (SyntaxNodeSyntax.constructor 2 7 w (fields6 env c2 c5) v)) := by
  let es : Fin 2 → Expr 4 := (Fin.cases (part2) (Fin.cases (part5) (Fin.elim0)))
  have he : part6 = Expr.node (.literal 7) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 2 7 es w v env (fields6 env c2 c5) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact hc2
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc5
    · exact Fin.elim0 j1

def part7 : Expr 4 := ObjectLogicalAxiom.rule0.head

def fields7 {m} (env : Fin 4 → Fin m) (c0 c6 : Fin m) : Fin 3 → Fin m := (Fin.cases (env 0) (Fin.cases (c0) (Fin.cases (c6) (Fin.elim0))))

theorem fields7_map {m l} (env : Fin 4 → Fin m) (c0 c6 : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fields7 env c0 c6 i)) = fields7 (fun i => ρ (env i)) (ρ c0) (ρ c6) := by
  funext i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact rfl
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact rfl
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact rfl
      · exact Fin.elim0 j2

theorem node7_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v c0 c6 : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc0 : Derives Γ (graph part0 w env c0))
    (hc6 : Derives Γ (graph part6 w env c6))
    : Derives Γ ((graph part7 w env v).iff (SyntaxNodeSyntax.constructor 3 0 w (fields7 env c0 c6) v)) := by
  let es : Fin 3 → Expr 4 := (Fin.cases (.var 0) (Fin.cases (part0) (Fin.cases (part6) (Fin.elim0))))
  have he : part7 = Expr.node (.literal 0) (List.ofFn es) := rfl
  rw [he]
  apply HornExprConstructor.constructor_iff hZ 3 0 es w v env (fields7 env c0 c6) hw hn
  intro i
  refine Fin.cases ?_ (fun j0 => ?_) i
  · exact (.conjI (environmentNat_at w env hn 0) (.eqRefl _))
  · refine Fin.cases ?_ (fun j1 => ?_) j0
    · exact hc0
    · refine Fin.cases ?_ (fun j2 => ?_) j1
      · exact hc6
      · exact Fin.elim0 j2

def atValues {m} (w row : Fin m) (env : Fin 4 → Fin m) (ys : Fin 7 → Fin m) : Formula m :=
  (SyntaxNodeSyntax.constructor 3 0 w (fields0 env) (ys 0)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields1 env) (ys 1)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields2 env (ys 1)) (ys 2)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields3 env) (ys 3)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields4 env) (ys 4)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields5 env (ys 3) (ys 4)) (ys 5)).conj ((SyntaxNodeSyntax.constructor 2 7 w (fields6 env (ys 2) (ys 5)) (ys 6)).conj (SyntaxNodeSyntax.constructor 3 0 w (fields7 env (ys 0) (ys 6)) row)))))))

theorem atValues_rename {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ys : Fin 7 → Fin m) (ρ : Fin m → Fin l) :
    (atValues w row env ys).rename ρ = atValues (ρ w) (ρ row) (fun i => ρ (env i)) (fun i => ρ (ys i)) := by
  simp only [atValues, Formula.rename, SyntaxNodeSyntax.constructor_rename, fields0_map, fields1_map, fields2_map, fields3_map, fields4_map, fields5_map, fields6_map, fields7_map]

def body {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula (m+7) :=
  atValues (old 7 w) (old 7 row) (fun i => old 7 (env i)) (slot 7)

def normalized {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m := existsMany 7 (body w row env)

theorem body_lift {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (body w row env).rename (lift 7 ρ) = body (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [body, atValues_rename, lift_old, lift_slot]

theorem normalized_rename {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (normalized w row env).rename ρ = normalized (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [normalized, existsMany_rename, body_lift]

theorem intro_normalized {m} {Γ : Context m} (w row : Fin m) (env : Fin 4 → Fin m) (ys : Fin 7 → Fin m)
    (hc : Derives Γ (atValues w row env ys)) : Derives Γ (normalized w row env) := by
  apply HornBinderRules.intro_many 7 (body w row env) ys
  exact of_eq (by simp only [body, atValues_rename, assign_old, assign_slot]) hc

attribute [local irreducible] HornExprSyntax.graph
set_option maxHeartbeats 1200000 in
theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph ObjectLogicalAxiom.rule0.head w env row).iff (normalized w row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph ObjectLogicalAxiom.rule0.head w env row
    have hRoot0 : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hw0 := add hw E
    have hn0 := add hn E
    let B0 := (Formula.mem (Fin.last m) w.castSucc).conj (graph part0 w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ1 := Context.add B0 (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B0) (HornExprExistence.exists_value hZ0 part0 w (fun i => (env i)) hw0 hn0)
    have hZ1 := ZFContext.under hZ0 B0
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw0 B0)
    have hn1 := of_eq (environmentNat_rename 4 w (fun i => (env i)) Fin.castSucc) (under hn0 B0)
    have hRoot1 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w row (fun i => (env i)) Fin.castSucc) (under hRoot0 B0)
    have hB0 : Derives Δ1 B0 := .hyp (Or.inl rfl)
    have hV0_1 := Derives.conjR hB0
    let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph part1 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1)))
    let Δ2 := Context.add B1 (Context.image Formula.raise (Δ1))
    apply Derives.exE (p := B1) (HornExprExistence.exists_value hZ1 part1 w.castSucc (fun i => (env i).castSucc) hw1 hn1)
    have hZ2 := ZFContext.under hZ1 B1
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
    have hn2 := of_eq (environmentNat_rename 4 w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 B1)
    have hRoot2 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc row.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hRoot1 B1)
    have hB1 : Derives Δ2 B1 := .hyp (Or.inl rfl)
    have hV1_2 := Derives.conjR hB1
    have hV0_2 := of_eq (graph_rename part0 w.castSucc (Fin.last m) (fun i => (env i).castSucc) Fin.castSucc) (under hV0_1 B1)
    let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (graph part2 w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.last (m+2)))
    let Δ3 := Context.add B2 (Context.image Formula.raise (Δ2))
    apply Derives.exE (p := B2) (HornExprExistence.exists_value hZ2 part2 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) hw2 hn2)
    have hZ3 := ZFContext.under hZ2 B2
    have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
    have hn3 := of_eq (environmentNat_rename 4 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hn2 B2)
    have hRoot3 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc.castSucc row.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hRoot2 B2)
    have hB2 : Derives Δ3 B2 := .hyp (Or.inl rfl)
    have hV2_3 := Derives.conjR hB2
    have hV0_3 := of_eq (graph_rename part0 w.castSucc.castSucc (Fin.last m).castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hV0_2 B2)
    have hV1_3 := of_eq (graph_rename part1 w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hV1_2 B2)
    let B3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (graph part3 w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)))
    let Δ4 := Context.add B3 (Context.image Formula.raise (Δ3))
    apply Derives.exE (p := B3) (HornExprExistence.exists_value hZ3 part3 w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) hw3 hn3)
    have hZ4 := ZFContext.under hZ3 B3
    have hw4 := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 B3)
    have hn4 := of_eq (environmentNat_rename 4 w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) Fin.castSucc) (under hn3 B3)
    have hRoot4 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) Fin.castSucc) (under hRoot3 B3)
    have hB3 : Derives Δ4 B3 := .hyp (Or.inl rfl)
    have hV3_4 := Derives.conjR hB3
    have hV0_4 := of_eq (graph_rename part0 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) Fin.castSucc) (under hV0_3 B3)
    have hV1_4 := of_eq (graph_rename part1 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (fun i => (env i).castSucc.castSucc.castSucc) Fin.castSucc) (under hV1_3 B3)
    have hV2_4 := of_eq (graph_rename part2 w.castSucc.castSucc.castSucc (Fin.last (m+2)) (fun i => (env i).castSucc.castSucc.castSucc) Fin.castSucc) (under hV2_3 B3)
    let B4 := (Formula.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc).conj (graph part4 w.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+4)))
    let Δ5 := Context.add B4 (Context.image Formula.raise (Δ4))
    apply Derives.exE (p := B4) (HornExprExistence.exists_value hZ4 part4 w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) hw4 hn4)
    have hZ5 := ZFContext.under hZ4 B4
    have hw5 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw4 B4)
    have hn5 := of_eq (environmentNat_rename 4 w.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hn4 B4)
    have hRoot5 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hRoot4 B4)
    have hB4 : Derives Δ5 B4 := .hyp (Or.inl rfl)
    have hV4_5 := Derives.conjR hB4
    have hV0_5 := of_eq (graph_rename part0 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV0_4 B4)
    have hV1_5 := of_eq (graph_rename part1 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV1_4 B4)
    have hV2_5 := of_eq (graph_rename part2 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV2_4 B4)
    have hV3_5 := of_eq (graph_rename part3 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (fun i => (env i).castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV3_4 B4)
    let B5 := (Formula.mem (Fin.last (m+5)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (graph part5 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+5)))
    let Δ6 := Context.add B5 (Context.image Formula.raise (Δ5))
    apply Derives.exE (p := B5) (HornExprExistence.exists_value hZ5 part5 w.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) hw5 hn5)
    have hZ6 := ZFContext.under hZ5 B5
    have hw6 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw5 B5)
    have hn6 := of_eq (environmentNat_rename 4 w.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hn5 B5)
    have hRoot6 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc.castSucc.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hRoot5 B5)
    have hB5 : Derives Δ6 B5 := .hyp (Or.inl rfl)
    have hV5_6 := Derives.conjR hB5
    have hV0_6 := of_eq (graph_rename part0 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV0_5 B5)
    have hV1_6 := of_eq (graph_rename part1 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV1_5 B5)
    have hV2_6 := of_eq (graph_rename part2 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV2_5 B5)
    have hV3_6 := of_eq (graph_rename part3 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV3_5 B5)
    have hV4_6 := of_eq (graph_rename part4 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV4_5 B5)
    let B6 := (Formula.mem (Fin.last (m+6)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (graph part6 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+6)))
    let Δ7 := Context.add B6 (Context.image Formula.raise (Δ6))
    apply Derives.exE (p := B6) (HornExprExistence.exists_value hZ6 part6 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw6 hn6)
    have hZ7 := ZFContext.under hZ6 B6
    have hw7 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw6 B6)
    have hn7 := of_eq (environmentNat_rename 4 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hn6 B6)
    have hRoot7 := of_eq (graph_rename ObjectLogicalAxiom.rule0.head w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hRoot6 B6)
    have hB6 : Derives Δ7 B6 := .hyp (Or.inl rfl)
    have hV6_7 := Derives.conjR hB6
    have hV0_7 := of_eq (graph_rename part0 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV0_6 B6)
    have hV1_7 := of_eq (graph_rename part1 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV1_6 B6)
    have hV2_7 := of_eq (graph_rename part2 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV2_6 B6)
    have hV3_7 := of_eq (graph_rename part3 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV3_6 B6)
    have hV4_7 := of_eq (graph_rename part4 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV4_6 B6)
    have hV5_7 := of_eq (graph_rename part5 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)) (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) Fin.castSucc) (under hV5_6 B6)
    have hC0 := Derives.impE (.conjL (node0_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7)) hV0_7
    have hC1 := Derives.impE (.conjL (node1_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7)) hV1_7
    have hC2 := Derives.impE (.conjL (node2_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7 hV1_7)) hV2_7
    have hC3 := Derives.impE (.conjL (node3_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7)) hV3_7
    have hC4 := Derives.impE (.conjL (node4_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7)) hV4_7
    have hC5 := Derives.impE (.conjL (node5_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7 hV3_7 hV4_7)) hV5_7
    have hC6 := Derives.impE (.conjL (node6_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7 hV2_7 hV5_7)) hV6_7
    have hC7 := Derives.impE (.conjL (node7_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hw7 hn7 hV0_7 hV6_7)) hRoot7
    have ho := intro_normalized w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc row.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.cases ((Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.cases ((Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.cases ((Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc) (Fin.cases ((Fin.last (m+3)).castSucc.castSucc.castSucc) (Fin.cases ((Fin.last (m+4)).castSucc.castSucc) (Fin.cases ((Fin.last (m+5)).castSucc) (Fin.cases ((Fin.last (m+6))) (Fin.elim0)))))))) (.conjI hC0 (.conjI hC1 (.conjI hC2 (.conjI hC3 (.conjI hC4 (.conjI hC5 (.conjI hC6 hC7)))))))
    exact of_eq (by simp only [Formula.raise, normalized_rename]) ho
  · apply Derives.impI
    let E := normalized w row env
    let B := body w row env
    let Δ := Context.add B (raisedContext 7 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 7 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 7 (ZFContext.add hZ E) B
    have hw1 := of_eq (omega_rename w (old 7)) (HornBinderRules.under_body 7 (add hw E) B)
    have hn1 := of_eq (environmentNat_rename 4 w env (old 7)) (HornBinderRules.under_body 7 (add hn E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hG0 := Derives.impE (.conjR (node0_iff hZ1 (old 7 w) (slot 7 0) (fun i => old 7 (env i)) hw1 hn1)) (Derives.conjL hB)
    have hG1 := Derives.impE (.conjR (node1_iff hZ1 (old 7 w) (slot 7 1) (fun i => old 7 (env i)) hw1 hn1)) (Derives.conjL (Derives.conjR hB))
    have hG2 := Derives.impE (.conjR (node2_iff hZ1 (old 7 w) (slot 7 2) (slot 7 1) (fun i => old 7 (env i)) hw1 hn1 hG1)) (Derives.conjL (Derives.conjR (Derives.conjR hB)))
    have hG3 := Derives.impE (.conjR (node3_iff hZ1 (old 7 w) (slot 7 3) (fun i => old 7 (env i)) hw1 hn1)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hB))))
    have hG4 := Derives.impE (.conjR (node4_iff hZ1 (old 7 w) (slot 7 4) (fun i => old 7 (env i)) hw1 hn1)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB)))))
    have hG5 := Derives.impE (.conjR (node5_iff hZ1 (old 7 w) (slot 7 5) (slot 7 3) (slot 7 4) (fun i => old 7 (env i)) hw1 hn1 hG3 hG4)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB))))))
    have hG6 := Derives.impE (.conjR (node6_iff hZ1 (old 7 w) (slot 7 6) (slot 7 2) (slot 7 5) (fun i => old 7 (env i)) hw1 hn1 hG2 hG5)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB)))))))
    have hG7 := Derives.impE (.conjR (node7_iff hZ1 (old 7 w) (old 7 row) (slot 7 0) (slot 7 6) (fun i => old 7 (env i)) hw1 hn1 hG0 hG6)) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hB)))))))
    exact of_eq (graph_rename ObjectLogicalAxiom.rule0.head w row env (old 7)).symm hG7

end PPAC.Migration.Internal.LogicalRule0Head
