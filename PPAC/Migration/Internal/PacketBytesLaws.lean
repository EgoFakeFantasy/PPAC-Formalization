import PPAC.Migration.Internal.PacketBytesTraceAppend
import PPAC.Migration.Internal.PacketBytesTraceBase

/-! Actual radix 256 is internally constructed and eliminated in ordered byte-fold closure laws. -/
namespace PPAC.Migration.Internal.PacketBytesLaws
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketBytesTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem fold_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hb : Derives Γ (bytes w n t a)) : Derives Γ (foldAt w C n t a) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (foldAt w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ R) 256 (Fin.last m) C.castSucc (.conjL hR) hC1
  simpa only [Formula.raise,foldAt_rename] using PacketBytesTraceTransport.radix_subst _ _ _ _ _ _ he (.conjR hR)

theorem fold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((bytes w n t a).iff (foldAt w C n t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact fold_at (ZFContext.add hZ _) w C n t a (add hC _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_bytes w C n t a (add hC _) (.hyp (Or.inl rfl))

theorem domain {m} {Γ : Context m} (w n t a : Fin m) (hb : Derives Γ (bytes w n t a)) :
    Derives Γ ((StructuralListTraceSyntax.valid w n).conj ((Formula.mem t w).conj (.mem a w))) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (foldAt w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,Formula.rename,StructuralListTraceSyntax.valid_rename] using PacketBytesTraceBase.domain _ _ _ _ _ (.conjR hR)

theorem nil_fold {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (bytes w n t t) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hn1 := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under hn R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hf := PacketBytesTraceBase.nil_fold hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc hw1 hn1 (under ht R)
  simpa only [Formula.raise,bytes_rename] using intro_bytes w.castSucc (Fin.last m) n.castSucc t.castSucc t.castSucc (.conjR hR) hf

theorem nil_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (hb : Derives Γ (bytes w n t a)) :
    Derives Γ (.equal t a) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (foldAt w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hn1 := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under hn R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact PacketBytesTraceBase.nil_value hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc hw1 hn1 (.conjR hR)

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ ((bytes w n t a).iff ((Formula.mem t w).conj (.equal t a))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hb : Derives (Context.add (bytes w n t a) Γ) (bytes w n t a) := .hyp (Or.inl rfl)
    exact .conjI (.conjL (.conjR (domain w n t a hb))) (nil_value (ZFContext.add hZ _) w n t a (add hw _) (add hn _) hb)
  · apply Derives.impI
    have hE : Derives (Context.add ((Formula.mem t w).conj (.equal t a)) Γ) ((Formula.mem t w).conj (.equal t a)) := .hyp (Or.inl rfl)
    let Δ := Context.add ((Formula.mem t w).conj (.equal t a)) Γ
    let P := bytes w.castSucc n.castSucc t.castSucc (Fin.last m)
    have hi : P.instantiate t = bytes w n t t := by simp only [P,Formula.instantiate,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    have ho : P.instantiate a = bytes w n t a := by simp only [P,Formula.instantiate,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    exact of_eq ho (Derives.eqSubst P (.conjR hE) (of_eq hi.symm (nil_fold (ZFContext.add hZ _) w n t (add hw _) (add hn _) (.conjL hE))))

theorem cons_bytes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a h p b : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (bytes w n t a))
    (hc : Derives Γ (StructuralListSyntax.consCode w h n p)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h a b)) :
    Derives Γ (bytes w p t b) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hf1 := of_eq (bytes_rename w n t a Fin.castSucc) (under hf R)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h n p Fin.castSucc) (under hc R)
  have ha1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w h a b Fin.castSucc) (under ha R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hfold := fold_at hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc (.conjR hR) hf1
  have harith := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc (Fin.last m) h.castSucc a.castSucc b.castSucc hw1 (.conjR hR))) ha1
  have hnew := PacketBytesTraceAppend.cons_fold hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc h.castSucc p.castSucc b.castSucc hw1 hfold hc1 harith
  simpa only [Formula.raise,bytes_rename] using intro_bytes w.castSucc (Fin.last m) p.castSucc t.castSucc b.castSucc (.conjR hR) hnew

theorem singleton_bytes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e n t h a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (StructuralListSyntax.nilCode w e)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h e n)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h t a)) :
    Derives Γ (bytes w n t a) := cons_bytes hZ w e t t h n a hw (nil_fold hZ w e t hw he ht) hc ha

end PPAC.Migration.Internal.PacketBytesLaws
