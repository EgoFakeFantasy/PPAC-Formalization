import PPAC.Migration.Internal.PacketStructureSearchLawSyntax

/-! Full original application equivalence and exact all-internal typed recursive laws are exported from the unchanged original kernel. -/
namespace PPAC.Migration.Internal.PacketStructureSearchLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData PacketStructureSearchLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) : Derives Γ (allRoot f w V) := by
  apply OriginalUniversalBlock.intro_many (width f+1)
  apply Derives.impI
  let H := row (width f) (tag f) (old (width f+1) w : Fin (m+(width f+1)))
    (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))
  have hwk := of_eq (omega_rename w (old (width f+1))) (HornBinderRules.under_body (width f+1) hw H)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old (width f+1))) (HornBinderRules.under_body (width f+1) hv H)
  exact PacketStructureSearchEquation.condition_iff_criterion (HornBinderRules.zf_body (width f+1) hZ H) f (old (width f+1) w)
    (old (width f+1) V) (slot (width f+1) (Fin.last (width f))) (fun i => slot (width f+1) i.castSucc) hwk hvk (.hyp (Or.inl rfl))

theorem all_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allActual f w) := by
  apply OriginalUniversalBlock.intro_many (width f)
  have hwk := of_eq (omega_rename w (old (width f))) (HornBinderRules.under_many (width f) hw)
  exact PacketStructureSearchAccepted.accepted_iff (HornBinderRules.zf_many (width f) hZ) f (old (width f) w) (slot (width f)) hwk

theorem all_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allSystem w) :=
  .conjI (all_actual hZ .tree w hw) (.conjI (all_actual hZ .forest w hw) (all_actual hZ .packet w hw))

theorem exists_canonical {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (existsCanonical w) := by
  let P := PacketTraceCore.value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketTraceCore.exists_value hZ w)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hs : Derives Δ (canonicalSystem w.castSucc (Fin.last m)) := .conjI hP
    (.conjI (all_root hZ1 .tree w.castSucc (Fin.last m) hw1 hP)
      (.conjI (all_root hZ1 .forest w.castSucc (Fin.last m) hw1 hP) (all_root hZ1 .packet w.castSucc (Fin.last m) hw1 hP)))
  exact of_eq (existsCanonical_rename w Fin.castSucc).symm (intro_canonical w.castSucc (Fin.last m) hs)

theorem tree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((tree w n t a).iff ((environmentNat 3 w (SyntaxAtomSyntax.three n t a)).conj (treeCase w n t a))) :=
  PacketStructureSearchAccepted.accepted_iff hZ .tree w (SyntaxAtomSyntax.three n t a) hw

theorem forest_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((forest w n l t a).iff ((environmentNat 4 w (four n l t a)).conj
      ((PacketStructureRootSyntax.nilCase n l t a).disj (consCase w n l t a)))) :=
  PacketStructureSearchAccepted.accepted_iff hZ .forest w (four n l t a) hw

theorem packet_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((packet w a n).iff ((environmentNat 2 w (SyntaxAtomSyntax.two a n)).conj (packetCase w a n))) :=
  PacketStructureSearchAccepted.accepted_iff hZ .packet w (SyntaxAtomSyntax.two a n) hw

end PPAC.Migration.Internal.PacketStructureSearchLaws
