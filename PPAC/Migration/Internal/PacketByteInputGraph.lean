import PPAC.Migration.Internal.PacketByteInputSyntax

/-! Full original Fields graphs and pointwise byte bounds are exactly equivalent; no byte execution predicate is used. -/
namespace PPAC.Migration.Internal.PacketByteInputGraph
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax StructuralListLengthSyntax StructuralListFieldSyntax StructuralListFieldGraphSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem graph_to_bounds {m} {Γ : Context m} (w C n l f : Fin m) (hf : Derives Γ (fields w n l f))
    (hb : Derives Γ (SequenceSyntax.bounded f C)) : Derives Γ (bounds w C n l) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (Fin.last m).castSucc l.castSucc.castSucc
  let Y := field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.add I (raisedContext 2 Γ))
  have hf2 := of_eq (fields_rename w n l f (old 2)) (HornBinderRules.under_many 2 hf)
  have hb2 := of_eq (SequenceSyntax.bounded_rename f C (old 2)) (HornBinderRules.under_many 2 hb)
  have hi : Derives Δ I := .hyp (Or.inr (Or.inl rfl))
  have hy : Derives Δ Y := .hyp (Or.inl rfl)
  have hlaw := law_at (old 2 w) (old 2 n) (old 2 l) (old 2 f) (Fin.last m).castSucc (Fin.last (m+1)) (add (add (.conjR (.conjR hf2)) I) Y)
  have hedge := Derives.impE (.conjR hlaw) (.conjI hi hy)
  exact .impE (SequenceSyntax.bounded_at _ _ _ _ (add (add hb2 I) Y)) hedge

theorem bounds_to_graph {m} {Γ : Context m} (w C n l f : Fin m) (hf : Derives Γ (fields w n l f))
    (hb : Derives Γ (bounds w C n l)) : Derives Γ (SequenceSyntax.bounded f C) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  have hf2 := of_eq (fields_rename w n l f (old 2)) (HornBinderRules.under_body 2 hf E)
  have hb2 := of_eq (bounds_rename w C n l (old 2)) (HornBinderRules.under_body 2 hb E)
  have he : Derives (Context.add E (raisedContext 2 Γ)) E := .hyp (Or.inl rfl)
  have hd := Derives.impE (.conjL (law_at _ _ _ _ _ _ (.conjR (.conjR hf2)))) he
  exact bounds_at _ _ _ _ _ _ hb2 (.conjL hd) (.conjR hd)

theorem to_length {m} {Γ : Context m} (w C n : Fin m) (hi : Derives Γ (inputAt w C n)) : Derives Γ (lengthExists w C n) := by
  let R := inputBody w C n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb := graph_to_bounds (old 2 w) (old 2 C) (old 2 n) (slot 2 0) (slot 2 1) (.conjR (.conjL hR)) (.conjR hR)
  exact of_eq (lengthExists_rename w C n (old 2)).symm
    (intro_length (old 2 w) (old 2 C) (old 2 n) (slot 2 0) (.conjR (.conjL (.conjL hR))) hb)

theorem from_length_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hb : Derives Γ (bounds w C n l)) : Derives Γ (inputAt w C n) := by
  have hF := StructuralListFieldGraphFiber.exists_unique hZ w n l hw (StructuralListLengthBasic.length_member _ _ _ hl)
  let R := (fields w.castSucc n.castSucc l.castSucc (Fin.last m)).conj (.all
    ((StructuralListFieldPairSyntax.graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hF
  have hl1 := of_eq (hasLength_rename w n l Fin.castSucc) (under hl R)
  have hb1 := of_eq (bounds_rename w C n l Fin.castSucc) (under hb R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hbound := bounds_to_graph w.castSucc C.castSucc n.castSucc l.castSucc (Fin.last m) (.conjL hR) hb1
  have henc : Derives Δ (StructuralListEncodeSyntax.encoding w.castSucc (Fin.last m) l.castSucc n.castSucc) :=
    .conjI (.conjI (StructuralListLengthBasic.code_member _ _ _ hl1) hl1) (.conjL hR)
  simpa only [Formula.raise,inputAt_rename] using intro_input w.castSucc C.castSucc n.castSucc l.castSucc (Fin.last m) henc hbound

theorem from_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lengthExists w C n)) : Derives Γ (inputAt w C n) := by
  let R := lengthCase w.castSucc C.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hl
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,inputAt_rename] using from_length_at (ZFContext.under hZ R) w.castSucc C.castSucc n.castSucc (Fin.last m) hw1 (.conjL hR) (.conjR hR)

theorem length_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((inputAt w C n).iff (lengthExists w C n)) :=
  .conjI (.impI (to_length w C n (.hyp (Or.inl rfl))))
    (.impI (from_length (ZFContext.add hZ _) w C n (add hw _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketByteInputGraph
