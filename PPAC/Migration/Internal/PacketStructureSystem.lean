import PPAC.Migration.Internal.PacketStructureSystemSyntax

/-! Original native ZF constructs the common accepting set and all three structural root laws from omega alone. -/
namespace PPAC.Migration.Internal.PacketStructureSystem
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureDispatchData PacketStructureDispatch PacketStructureSystemSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem root_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hc : Derives Γ (row (width f) (tag f) w xs r)) :
    Derives Γ (rootLaw f w V r) := by
  apply Derives.conjI
  · exact condition_iff_bounded hZ f w V r xs hw hv hc
  · exact .impI (condition_forward (ZFContext.add hZ _) f w V r xs (add hw _) (add hv _) (add hc _) (.hyp (Or.inl rfl)))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) : Derives Γ (allLaw f w V) := by
  apply OriginalUniversalBlock.intro_many (width f+1)
  apply Derives.impI
  let H := row (width f) (tag f) (old (width f+1) w : Fin (m+(width f+1)))
    (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))
  have hwk := of_eq (omega_rename w (old (width f+1))) (HornBinderRules.under_body (width f+1) hw H)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old (width f+1))) (HornBinderRules.under_body (width f+1) hv H)
  exact root_law (HornBinderRules.zf_body (width f+1) hZ H) f (old (width f+1) w) (old (width f+1) V)
    (slot (width f+1) (Fin.last (width f))) (fun i => slot (width f+1) i.castSucc) hwk hvk (.hyp (Or.inl rfl))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (existsSystem w) := by
  let P := PacketTraceCore.value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketTraceCore.exists_value hZ w)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hs : Derives Δ (system w.castSucc (Fin.last m)) := .conjI hP
    (.conjI (all_law hZ1 .tree w.castSucc (Fin.last m) hw1 hP)
      (.conjI (all_law hZ1 .forest w.castSucc (Fin.last m) hw1 hP) (all_law hZ1 .packet w.castSucc (Fin.last m) hw1 hP)))
  exact of_eq (existsSystem_rename w Fin.castSucc).symm (intro_system w.castSucc (Fin.last m) hs)

end PPAC.Migration.Internal.PacketStructureSystem
