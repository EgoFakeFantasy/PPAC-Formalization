import PPAC.Migration.Internal.PacketTokenExecutionFiber

/-! Only omega remains: actual token execution is total and unique exactly on internal natural input/tail pairs. -/
namespace PPAC.Migration.Internal.PacketTokenExecution
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_many 2 hB)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_many 2 hC)
  exact PacketTokenExecutionFiber.fiber_iff (HornBinderRules.zf_many 2 hZ) (old 2 w) (old 2 B) (old 2 C) (slot 2 0) (slot 2 1) hw2 hB2 hC2

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

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((fiber w n t).iff ((Formula.mem n w).conj (.mem t w))) := by
  have hi := OriginalUniversalBlock.at_many 2 (lawBody w) (SyntaxAtomSyntax.two n t) (all_law hZ w hw)
  exact of_eq (by simp only [lawBody,Formula.iff,Formula.rename,fiber_rename,assign_old,assign_slot]; rfl) hi

theorem output_of_fiber {m} {Γ : Context m} (w n t : Fin m) (hf : Derives Γ (fiber w n t)) :
    Derives Γ (PacketTokenExistenceSyntax.existsOutput w n t) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj ((accepted w.castSucc n.castSucc t.castSucc (Fin.last m)).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m)))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (PacketTokenExistenceSyntax.existsOutput_rename w n t Fin.castSucc).symm
    (PacketTokenExistenceSyntax.intro_output w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjL hR) (.conjL (.conjR hR)))

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (PacketTokenExistenceSyntax.existsOutput w n t) :=
  output_of_fiber w n t (.impE (.conjR (fiber_iff hZ w n t hw)) (.conjI hn ht))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w n t b)) : Derives Γ (.equal a b) := by
  have he := PacketTokenAcceptedNatural.accepted_environment hZ w n t a hw ha
  have hn := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a) he 0
  have ht := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a) he 1
  have hf := Derives.impE (.conjR (fiber_iff hZ w n t hw)) (.conjI hn ht)
  let R := (Formula.mem (Fin.last m) w.castSucc).conj ((accepted w.castSucc n.castSucc t.castSucc (Fin.last m)).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m)))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have ha1 := of_eq (accepted_rename w n t a Fin.castSucc) (under ha R)
  have hb1 := of_eq (accepted_rename w n t b Fin.castSucc) (under hb R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have haC := uniqueAt_at w.castSucc n.castSucc t.castSucc (Fin.last m) a.castSucc (.conjR (.conjR hR)) ha1
  have hbC := uniqueAt_at w.castSucc n.castSucc t.castSucc (Fin.last m) b.castSucc (.conjR (.conjR hR)) hb1
  exact eq_trans haC (eq_symm hbC)

end PPAC.Migration.Internal.PacketTokenExecution
