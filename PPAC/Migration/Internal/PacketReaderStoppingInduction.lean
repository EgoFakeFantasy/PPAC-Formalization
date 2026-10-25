import PPAC.Migration.Internal.PacketReaderStoppingAdvance

/-! Fixed Formula6 and original omega induction construct stopping-or-exact-prefix progress at every internal index. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStoppingSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (OmegaInductionSyntax.base PacketReaderStoppingSyntax.matrix (params5 w B z o n)) := by
  simp only [OmegaInductionSyntax.base,PacketReaderStoppingSyntax.matrix_pred,paramsUp,params5_0,params5_1,params5_2,params5_3,params5_4]
  apply Derives.allI
  apply Derives.impI
  let H := empty (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz H)
  have hc1 := of_eq (PacketReaderStateSyntax.carrier_rename w n Fin.castSucc) (under hc H)
  exact PacketReaderStoppingInitial.zero_point hZ1 _ _ _ _ _ _ hw1 hz1 hc1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.step PacketReaderStoppingSyntax.matrix (params5 w B z o n) w) := by
  simp only [OmegaInductionSyntax.step,PacketReaderStoppingSyntax.matrix_pred,paramsUp,params5_0,params5_1,params5_2,params5_3,params5_4]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (slot 2 0) (old 2 w)
  let P := progress (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 n) (slot 2 0)
  let S : Formula (m+2) := successor (slot 2 1) (slot 2 0)
  let Δ := Context.add S (Context.add P (Context.add I (raisedContext 2 Γ)))
  have lift2 {q : Formula m} (hq : Derives Γ q) : Derives Δ (q.rename (old 2)) := add (add (add (HornBinderRules.under_many 2 hq) I) P) S
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) I) P) S
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hP : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact PacketReaderStoppingAdvance.successor_point hZ2 _ _ _ _ _ _ _ hw2 hP hS

theorem all_progress {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (allProgress w B z o n) := by
  have hall := ZFArithmetic.induction hZ PacketReaderStoppingSyntax.matrix (params5 w B z o n) w hw
    (base hZ w B z o n hw hz hc) (step hZ w B z o n hw)
  simpa only [allProgress,OmegaInductionSyntax.holds,PacketReaderStoppingSyntax.matrix_pred,paramsUp,params5_0,params5_1,params5_2,params5_3,params5_4] using hall

end PPAC.Migration.Internal.PacketReaderStoppingInduction
