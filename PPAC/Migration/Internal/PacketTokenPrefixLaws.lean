import PPAC.Migration.Internal.PacketTokenPrefixInduction
import PPAC.Migration.Internal.PacketTokenPrefixLawSyntax
import PPAC.Migration.Internal.PacketTokenExecution

/-! Only omega remains in actual numeric prefix inversion, including invalid and nonstandard candidates. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenPrefixLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let H := accepted (old 5 w : Fin (m+5)) (slot 5 0) (slot 5 1) (slot 5 2)
  let K := accepted (old 5 w : Fin (m+5)) (slot 5 3) (slot 5 4) (slot 5 2)
  let Δ := Context.add K (Context.add H (raisedContext 5 Γ))
  have hZ5 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 5 hZ) H) K
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_many 5 hw)
  have hB5 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 5)) (HornBinderRules.under_many 5 hB)
  have hC5 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 5)) (HornBinderRules.under_many 5 hC)
  have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  exact PacketTokenPrefixInduction.unique hZ5 (old 5 w) (old 5 B) (old 5 C) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
    (add (add hw5 H) K) (add (add hB5 H) K) (add (add hC5 H) K) hH hK

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


theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) :
    Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  have hi := OriginalUniversalBlock.at_many 5 (lawBody w) (five n t a k s) (all_law hZ w hw)
  have he : Derives Γ ((accepted w n t a).imp ((accepted w k s a).imp ((Formula.equal n k).conj (.equal t s)))) :=
    of_eq (by simp only [lawBody,Formula.rename,accepted_rename,assign_old,assign_slot]; rfl) hi
  exact .impE (.impE he ha) hb

theorem input_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) :
    Derives Γ (.equal n k) := .conjL (unique hZ w n t a k s hw ha hb)

theorem tail_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) :
    Derives Γ (.equal t s) := .conjR (unique hZ w n t a k s hw ha hb)

theorem accepted_tail {m} {Γ : Context m} (w n t a s : Fin m) (he : Derives Γ (.equal t s))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (accepted w n s a) := by
  let P := accepted w.castSucc n.castSucc (Fin.last m) a.castSucc
  have h0 : P.instantiate t = accepted w n t a := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate s = accepted w n s a := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ha))

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) :
    Derives Γ ((accepted w k s a).iff ((Formula.equal n k).conj (.equal t s))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact unique (ZFContext.add hZ _) w n t a k s (add hw _) (add ha _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hE : Derives (Context.add ((Formula.equal n k).conj (.equal t s)) Γ) ((Formula.equal n k).conj (.equal t s)) := .hyp (Or.inl rfl)
    exact accepted_tail w k t a s (.conjR hE) (PacketTokenValueTransport.accepted_input w n t a k (.conjL hE) (add ha _))

theorem output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a k s b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s b)) :
    Derives Γ ((Formula.equal a b).iff ((Formula.equal n k).conj (.equal t s))) := by
  apply Derives.conjI
  · apply Derives.impI
    have he : Derives (Context.add (.equal a b) Γ) (.equal a b) := .hyp (Or.inl rfl)
    exact unique (ZFContext.add hZ _) w n t a k s (add hw _) (add ha _)
      (PacketTokenPrefixTransport.accepted_output w k s b a (eq_symm he) (add hb _))
  · apply Derives.impI
    have he : Derives (Context.add ((Formula.equal n k).conj (.equal t s)) Γ) ((Formula.equal n k).conj (.equal t s)) := .hyp (Or.inl rfl)
    have hks := accepted_tail w k t a s (.conjR he) (PacketTokenValueTransport.accepted_input w n t a k (.conjL he) (add ha _))
    exact PacketTokenExecution.unique (ZFContext.add hZ _) w k s a b (add hw _) hks (add hb _)

end PPAC.Migration.Internal.PacketTokenPrefixLaws
