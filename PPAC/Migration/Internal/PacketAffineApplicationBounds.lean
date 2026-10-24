import PPAC.Migration.Internal.ObjectPacketHornAffine

/-! Every actual affine parameter occurs in its original head, so the original search bound is proved. -/
namespace PPAC.Migration.Internal.PacketAffineApplicationBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornExprBounds
open PacketAffineRuleData (baseRule stepRule)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem base_variables (wide : Bool) : ∀ i : Fin 1, i ∈ (baseRule wide).head.variables := by
  have he : (baseRule wide).head.variables = ([0,0] : List (Fin 1)) := by
    simp only [baseRule, ObjectPacket.affineBase, ObjectPacket.node, Expr.node, Expr.list, Expr.variables, List.nil_append, List.append_nil, List.cons_append]
  rw [he]
  exact (by decide : ∀ i : Fin 1, i ∈ ([0,0] : List (Fin 1)))

theorem step_variables (wide : Bool) : ∀ i : Fin 3, i ∈ (stepRule wide).head.variables := by
  have he : (stepRule wide).head.variables = ([0,1,2] : List (Fin 3)) := by
    simp only [stepRule, ObjectPacket.affineStep, ObjectPacket.node, Expr.node, Expr.list, Expr.variables, ObjectPacket.Expr.addConst_variables, List.nil_append, List.append_nil, List.cons_append]
  rw [he]
  exact (by decide : ∀ i : Fin 3, i ∈ ([0,1,2] : List (Fin 3)))

theorem base_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hh : Derives Γ (graph (baseRule wide).head w env r)) : Derives Γ (environmentBound 1 r env) :=
  intro_environmentBound r env (fun i => variable_bound hZ (baseRule wide).head i (base_variables wide i) w r env hw hn hh)

theorem step_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph (stepRule wide).head w env r)) : Derives Γ (environmentBound 3 r env) :=
  intro_environmentBound r env (fun i => variable_bound hZ (stepRule wide).head i (step_variables wide i) w r env hw hn hh)

theorem base_intro {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w r V : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix (baseRule wide) w r V env)) :
    Derives Γ (HornApplicationSyntax.application (baseRule wide) w r V) :=
  HornApplicationRules.intro_application (baseRule wide) w r V env hn (base_bound hZ wide w r env hw hn (.conjL hm)) hm

theorem step_intro {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (HornRuleSyntax.matrix (stepRule wide) w r V env)) :
    Derives Γ (HornApplicationSyntax.application (stepRule wide) w r V) :=
  HornApplicationRules.intro_application (stepRule wide) w r V env hn (step_bound hZ wide w r env hw hn (.conjL hm)) hm

end PPAC.Migration.Internal.PacketAffineApplicationBounds
