import PPAC.Migration.Internal.OriginalFormulaExpr

/-! 原十一公式子前提与真实数值子运行；量词深度是对象实际后继。 -/
namespace PPAC.Migration.Internal.OriginalFormulaChildren
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules OriginalFormulaExpr
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def applicationIndices : Fin 5 → Fin 6 := HornRowFields.five 0 1 2 4 5

def binderFields : Fin 5 → Expr 5 := HornRowFields.five (.var 0) (.succ (.var 1)) (.var 2) (.var 3) (.var 4)

theorem actual_binder_child : unaryChild true = Expr.node (.literal 3) (List.ofFn binderFields) := rfl

theorem binary_left_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat) (w : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((tracedPremise (binaryLeft kind) w env).iff (OriginalTransformRowSyntax.run kind w (env 0) (env 1) (env 2) (env 3) (env 5))) :=
  OriginalFormulaRowGraph.variable_child_iff hZ kind OriginalArgumentsExpr.headIndices w env hw hn

theorem binary_right_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat) (w : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((tracedPremise (binaryRight kind) w env).iff (OriginalTransformRowSyntax.run kind w (env 0) (env 1) (env 2) (env 4) (env 6))) :=
  OriginalFormulaRowGraph.variable_child_iff hZ kind OriginalArgumentsExpr.tailIndices w env hw hn

theorem application_child_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) :
    Derives Γ ((tracedPremise applicationChild w env).iff (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 5))) :=
  OriginalFormulaRowGraph.variable_child_iff hZ 2 applicationIndices w env hw hn

theorem nonbinder_child_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) :
    Derives Γ ((tracedPremise (unaryChild false) w env).iff (OriginalTransformRowSyntax.run 3 w (env 0) (env 1) (env 2) (env 3) (env 4))) :=
  OriginalFormulaRowGraph.variable_child_iff hZ 3 id w env hw hn

theorem binder_row_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w depth r : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hs : Derives Γ (successor depth (env 1))) :
    Derives Γ ((graph (unaryChild true) w env r).iff (OriginalTransformRowSyntax.row 3 w (env 0) depth (env 2) (env 3) (env 4) r)) := by
  have hv (i : Fin 5) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hd : Derives Γ (graph (.succ (.var (1 : Fin 5))) w env depth) := intro_succ (.var 1) w depth (env 1) env (hv 1) hs
  have hfields : ∀ i, Derives Γ (graph (binderFields i) w env (HornRowFields.five (env 0) depth (env 2) (env 3) (env 4) i)) :=
    fun i => Fin.cases (hv 0) (fun j => Fin.cases hd (fun k => Fin.cases (hv 2) (fun l => Fin.cases (hv 3) (fun _ => hv 4) l) k) j) i
  rw [actual_binder_child]
  exact HornExprConstructor.constructor_iff hZ 5 3 binderFields w r env _ hw hn hfields

theorem binder_child_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w depth : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hs : Derives Γ (successor depth (env 1))) :
    Derives Γ ((tracedPremise (unaryChild true) w env).iff (OriginalTransformRowSyntax.run 3 w (env 0) depth (env 2) (env 3) (env 4))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 : Derives (Context.image Formula.raise Γ) (environmentNat 5 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 5 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  have hs1 : Derives (Context.image Formula.raise Γ) (successor depth.castSucc (env 1).castSucc) := of_eq (successor_rename depth (env 1) Fin.castSucc) (Derives.rename Fin.castSucc hs)
  exact FormulaCodeCongruence.conj_congr
    (binder_row_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc depth.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hs1)
    (SyntaxTypeLocalTransfer.iff_refl _)

end PPAC.Migration.Internal.OriginalFormulaChildren
