import PPAC.Migration.Internal.ProjectionGetConstructors
import PPAC.Migration.Internal.RawCodeGetZero
import PPAC.Migration.Internal.RawCodeGetLaws

/-! 原get头的实际数值方程；递归分支的子数值前提明确保留，未伪称完整正确性。 -/
namespace PPAC.Migration.Internal.ProjectionGetLocal
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation
open ProjectionGetConstructors

theorem zero_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hh : Derives Γ (graph ObjectProjection.getZero.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row)) :
    Derives Γ (RawCodeGetSyntax.get w x i y) := by
  have hx := HornNodeFields.field_3 hZ 1 zeroFields w row env (SyntaxAtomSyntax.three x i y) 0 hw hn
    (of_eq (congrArg (fun e => graph e w env row) zero_head) hh) hr
  have hy := HornNodeFields.field_3 hZ 1 zeroFields w row env (SyntaxAtomSyntax.three x i y) 2 hw hn
    (of_eq (congrArg (fun e => graph e w env row) zero_head) hh) hr
  have hi := ProjectionNodeFields.constructor_field_natural hZ 3 1 w row (SyntaxAtomSyntax.three x i y) 1 hw hr
  exact .impE (.conjR (RawCodeGetZero.checked_iff hZ w x i y hw hx hi)) hy

theorem head_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph ObjectProjection.getHead.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row)) :
    Derives Γ (RawCodeGetSyntax.get w x i y) := by
  have hx := HornNodeFields.field_3 hZ 1 headFields w row env (SyntaxAtomSyntax.three x i y) 0 hw hn
    (of_eq (congrArg (fun e => graph e w env row) head_head) hh) hr
  have hi := HornNodeFields.field_3 hZ 1 headFields w row env (SyntaxAtomSyntax.three x i y) 1 hw hn
    (of_eq (congrArg (fun e => graph e w env row) head_head) hh) hr
  have hy := HornNodeFields.field_3 hZ 1 headFields w row env (SyntaxAtomSyntax.three x i y) 2 hw hn
    (of_eq (congrArg (fun e => graph e w env row) head_head) hh) hr
  have hp := ProjectionRawPairExpr.head_tail hZ true (0 : Fin 3) 1 2 w x env hw hn hx
  have hg := Derives.impE (.conjR (RawCodeGetLaws.zero_iff hZ w x i (env 1) hw hi)) hp
  exact RawCodeGetSyntax.output_subst w x i (env 1) y (eq_symm (.conjR hy)) hg

theorem tail_sound_from_child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hh : Derives Γ (graph ObjectProjection.getTail.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row))
    (hc : Derives Γ (RawCodeGetSyntax.get w (env 2) (env 3) (env 4))) : Derives Γ (RawCodeGetSyntax.get w x i y) := by
  have hx := HornNodeFields.field_3 hZ 1 tailFields w row env (SyntaxAtomSyntax.three x i y) 0 hw hn
    (of_eq (congrArg (fun e => graph e w env row) tail_head) hh) hr
  have hi := HornNodeFields.field_3 hZ 1 tailFields w row env (SyntaxAtomSyntax.three x i y) 1 hw hn
    (of_eq (congrArg (fun e => graph e w env row) tail_head) hh) hr
  have hy := HornNodeFields.field_3 hZ 1 tailFields w row env (SyntaxAtomSyntax.three x i y) 2 hw hn
    (of_eq (congrArg (fun e => graph e w env row) tail_head) hh) hr
  have ht := ProjectionRawPairExpr.head_tail hZ false (0 : Fin 5) 1 2 w x env hw hn hx
  have hs := Derives.impE (.conjL (ProjectionRawPairExpr.successor_variable_iff (3 : Fin 5) w i env hn)) hi
  have hg := RawCodeGetLaws.successor_backward hZ w x (env 2) (env 3) i (env 4) hw (environmentNat_at w env hn 3) hs ht hc
  exact RawCodeGetSyntax.output_subst w x i (env 4) y (eq_symm (.conjR hy)) hg

theorem tail_actual_child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hp : Derives Γ (HornRuleSyntax.premises ObjectProjection.getTail.premises w V env)) :
    Derives Γ (ProjectionTraceSyntax.get w (env 2) (env 3) (env 4)) := by
  have h1 : Derives Γ (HornRuleSyntax.premise tailPremise w V env) := .conjL hp
  have h2 := Derives.impE (.conjL (ProjectionTracePremises.premise_iff tailPremise w V env hv)) h1
  exact .impE (.conjL (ProjectionTracePremises.get_variables_iff hZ (2 : Fin 5) 3 4 w env hw hn)) h2

end PPAC.Migration.Internal.ProjectionGetLocal
