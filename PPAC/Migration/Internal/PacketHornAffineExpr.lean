import PPAC.Migration.Internal.PacketHornAffineSyntax

/-! Original affine heads, guard and premise are connected to their actual internal values. -/
namespace PPAC.Migration.Internal.PacketHornAffineExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketHornAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def baseFields : Fin 3 → Expr 1 := Fin.cases (.var 0) (Fin.cases (.literal 0) (Fin.cases (.var 0) Fin.elim0))

def stepFields (wide : Bool) : Fin 3 → Expr 3 :=
  Fin.cases (.var 0) (Fin.cases (.succ (.var 1)) (Fin.cases (ObjectPacket.Expr.addConst (PacketAffineRuleData.radix wide) (.var 2)) Fin.elim0))

theorem actual_base_head (wide : Bool) : (PacketAffineRuleData.baseRule wide).head =
    Expr.node (.literal (PacketAffineRuleData.relation wide)) (List.ofFn baseFields) := rfl

theorem actual_step_head (wide : Bool) : (PacketAffineRuleData.stepRule wide).head =
    Expr.node (.literal (PacketAffineRuleData.relation wide)) (List.ofFn (stepFields wide)) := rfl

theorem variable_row_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (indices : Fin 3 → Fin n)
    (w r : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((graph (ObjectPacket.node (PacketAffineRuleData.relation wide) (List.ofFn (fun i => Expr.var (indices i)))) w env r).iff
      (SyntaxNodeSyntax.constructor 3 (PacketAffineRuleData.relation wide) w (fun i => env (indices i)) r)) :=
  HornExprConstructor.constructor_iff hZ 3 (PacketAffineRuleData.relation wide) _ w r env _ hw hn
    (fun i => .conjI (environmentNat_at w env hn (indices i)) (.eqRefl _))

theorem base_head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w z r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((graph (PacketAffineRuleData.baseRule wide).head w env r).iff (row wide w (env 0) z (env 0) r)) := by
  have hv : Derives Γ (graph (.var (0 : Fin 1)) w env (env 0)) := .conjI (environmentNat_at w env hn 0) (.eqRefl _)
  have hs : ∀ i, Derives Γ (graph (baseFields i) w env (SyntaxAtomSyntax.three (env 0) z (env 0) i)) := by
    intro i
    exact Fin.cases hv (fun j => Fin.cases hz (fun l => Fin.cases hv (fun i => Fin.elim0 i) l) j) i
  rw [actual_base_head]
  exact HornExprConstructor.constructor_iff hZ 3 (PacketAffineRuleData.relation wide) baseFields w r env _ hw hn hs

theorem step_head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B s y r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hs : Derives Γ (successor s (env 1))) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 2) B y)) :
    Derives Γ ((graph (PacketAffineRuleData.stepRule wide).head w env r).iff (row wide w (env 0) s y r)) := by
  have hv (i : Fin 3) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hS := intro_succ (.var (1 : Fin 3)) w s (env 1) env (hv 1) hs
  have hY := HornExprAddConst.backward hZ (PacketAffineRuleData.radix wide) (.var (2 : Fin 3)) w (env 2) B y env hw hn (hv 2) hB hy
  have hf : ∀ i, Derives Γ (graph (stepFields wide i) w env (SyntaxAtomSyntax.three (env 0) s y i)) := by
    intro i
    exact Fin.cases (hv 0) (fun j => Fin.cases hS (fun l => Fin.cases hY (fun i => Fin.elim0 i) l) j) i
  rw [actual_step_head]
  exact HornExprConstructor.constructor_iff hZ 3 (PacketAffineRuleData.relation wide) (stepFields wide) w r env _ hw hn hf

theorem base_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ ((HornRuleSyntax.guard (.var 0) (.literal (PacketAffineRuleData.radix wide)) w env).iff (.mem (env 0) B)) :=
  HornRuleValue.guard_at hZ (.var (0 : Fin 1)) (.literal (PacketAffineRuleData.radix wide)) w (env 0) B env hw hn
    (.conjI (environmentNat_at w env hn 0) (.eqRefl _)) hB

theorem step_premise_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((HornRuleSyntax.premise (ObjectPacket.node (PacketAffineRuleData.relation wide) [.var 0,.var 1,.var 2]) w V env).iff
      (entry wide w V (env 0) (env 1) (env 2))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename 3 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (variable_row_iff (ZFContext.rename hZ Fin.castSucc) wide (SyntaxAtomSyntax.three 0 1 2) w.castSucc (Fin.last m)
      (fun i => (env i).castSucc) hw1 hn1)
    (SyntaxTypeLocalTransfer.iff_refl _)

end PPAC.Migration.Internal.PacketHornAffineExpr
