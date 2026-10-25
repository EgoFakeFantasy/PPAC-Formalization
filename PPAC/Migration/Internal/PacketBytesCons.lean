import PPAC.Migration.Internal.PacketBytesConsSyntax

/-! Real field naturality and original Cons injectivity align every actual Bytes branch to the given Cons. -/
namespace PPAC.Migration.Internal.PacketBytesCons
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesConsSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a d y u : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hd : Derives Γ (StructuralListSyntax.consCode w d y s))
    (hb : Derives Γ (bytes w y t u)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w d u a)) : Derives Γ (remaining w h x t a) := by
  have hdW := PacketByteInputLaws.byte_natural hZ w d hw (.conjL (PacketBytesExecutionAffine.data hZ w d u a hw ha))
  have hyW := PacketBytesExecutionAffine.bytes_input_natural w y t u hb
  have he := StructuralConsUnique.injective hZ w h x d y s hw hh hx hdW hyW hc hd
  have hbX := PacketBytesExecutionTransport.input_subst w y t u x (eq_symm (.conjR he)) hb
  have haH := PacketBytesExecutionTransport.affine_digit w d u a h (eq_symm (.conjL he)) ha
  exact intro_remaining w h x t a u hbX haH

theorem actual_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hb : Derives Γ (PacketBytesRecursionSyntax.actualCons w s t a)) : Derives Γ (remaining w h x t a) := by
  let R := PacketBytesRecursionSyntax.actualBody w s t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hb
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hc3 := of_eq (StructuralListSyntax.consCode_rename w h x s (old 3)) (HornBinderRules.under_body 3 hc R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (remaining_rename w h x t a (old 3)).symm (values hZ3 (old 3 w) (old 3 h) (old 3 x) (old 3 s) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2)
    hw3 (HornBinderRules.under_body 3 hh R) (HornBinderRules.under_body 3 hx R) hc3 (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR)))

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hb : Derives Γ (bytes w s t a)) : Derives Γ (remaining w h x t a) := by
  have he := Derives.impE (.conjL (PacketBytesRecursionLaws.actual_iff hZ w s t a hw)) hb
  apply Derives.disjE he
  · exact .botE (StructuralConsUnique.disjoint (ZFContext.add hZ _) w h x s (add hw _) (.conjL (.hyp (Or.inl rfl))) (add hc _))
  · exact actual_case (ZFContext.add hZ _) w h x s t a (add hw _) (add hh _) (add hx _) (add hc _) (.hyp (Or.inl rfl))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (StructuralListSyntax.consCode w h x s))
    (hr : Derives Γ (remaining w h x t a)) : Derives Γ (bytes w s t a) := by
  let U := (bytes w.castSucc x.castSucc t.castSucc (Fin.last m)).conj (PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hr
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x s Fin.castSucc) (under hc U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  simpa only [Formula.raise,bytes_rename] using PacketBytesLaws.cons_bytes hZ1 w.castSucc x.castSucc t.castSucc (Fin.last m) h.castSucc s.castSucc a.castSucc hw1 (.conjL hU) hc1 (.conjR hU)

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w)) (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) :
    Derives Γ ((bytes w s t a).iff (remaining w h x t a)) :=
  .conjI (.impI (forward (ZFContext.add hZ _) w h x s t a (add hw _) (add hh _) (add hx _) (add hc _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w h x s t a (add hw _) (add hc _) (.hyp (Or.inl rfl))))

theorem singleton {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h e s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hc : Derives Γ (StructuralListSyntax.consCode w h e s)) (hb : Derives Γ (bytes w s t a)) : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h t a) := by
  have hr := forward hZ w h e s t a hw hh (StructuralNil.range hZ w e hw he) hc hb
  let U := (bytes w.castSucc e.castSucc t.castSucc (Fin.last m)).conj (PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hr
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have htu := PacketBytesLaws.nil_value hZ1 w.castSucc e.castSucc t.castSucc (Fin.last m) hw1 he1 (.conjL hU)
  simpa only [Formula.raise,PacketAffineAcceptedSyntax.accepted_rename] using PacketBytesExecutionTransport.affine_tail w.castSucc h.castSucc (Fin.last m) a.castSucc t.castSucc (eq_symm htu) (.conjR hU)

end PPAC.Migration.Internal.PacketBytesCons
