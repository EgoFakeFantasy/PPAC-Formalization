import PPAC.Migration.Internal.PacketTokenBoundsSystemSyntax

/-! All runtime induction hypotheses and radix witnesses are object-eliminated; only omega remains. -/
namespace PPAC.Migration.Internal.PacketTokenBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenBoundsSyntax PacketTokenBoundsSystemSyntax
open NaturalAdditionBounds (below)
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := accepted (old 3 w : Fin (m+3)) (slot 3 0) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw H)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_body 3 hB H)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_body 3 hC H)
  exact PacketTokenBoundsInduction.bounds_at (HornBinderRules.zf_body 3 hZ H) (old 3 w) (old 3 B) (old 3 C)
    (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 hC3 (.hyp (Or.inl rfl))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  let P := PacketAffineLiteralSyntax.frame false w.castSucc (Fin.last m)
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 128 w hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  let Q := PacketAffineLiteralSyntax.frame true w.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (SyntaxNumerals.exists_numeral hZ1 256 w.castSucc hw1)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (PacketAffineLiteralSyntax.frame false w.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [P,Formula.raise,PacketAffineLiteralSyntax.frame_rename]) (under hP Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := all_law_at hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjR hP2) (.conjR hQ)
  simpa only [Formula.raise,allLaw_rename] using ho


theorem bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) : Derives Γ (PacketTokenBoundsSyntax.bounds n t a) := by
  have hi := OriginalUniversalBlock.at_many 3 (lawBody w) (SyntaxAtomSyntax.three n t a) (all_law hZ w hw)
  have he : Derives Γ ((accepted w n t a).imp (PacketTokenBoundsSyntax.bounds n t a)) :=
    of_eq (by simp only [lawBody,Formula.rename,accepted_rename,bounds_rename,assign_old,assign_slot]; rfl) hi
  exact .impE he ha

theorem input_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) : Derives Γ (below n a) := .conjL (bounds hZ w n t a hw ha)

theorem tail_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) : Derives Γ (below t a) := .conjR (bounds hZ w n t a hw ha)

theorem contained_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) (hr : Derives Γ (.mem r w))
    (har : Derives Γ (below a r)) : Derives Γ (PacketTokenBoundsSyntax.bounds n t r) := by
  have hb := bounds hZ w n t a hw ha
  exact .conjI (NaturalOrderBasic.transitive hZ w n a r hw hr (.conjL hb) har)
    (NaturalOrderBasic.transitive hZ w t a r hw hr (.conjR hb) har)

end PPAC.Migration.Internal.PacketTokenBounds
