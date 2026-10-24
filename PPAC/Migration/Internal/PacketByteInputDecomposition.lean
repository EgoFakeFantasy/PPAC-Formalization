import PPAC.Migration.Internal.PacketByteInputRecursionSyntax

/-! Original valid-list decomposition and full field bounds give exact byte input recursion on all internal candidates. -/
namespace PPAC.Migration.Internal.PacketByteInputDecomposition
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketByteInputSyntax PacketByteInputRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (inputAt w C n)) : Derives Γ (criterionAt w C n) := by
  have hv := PacketByteInputProperties.valid w C n hi
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw hv
  apply Derives.disjE hd
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := StructuralListDecodeSyntax.tailCase w n
    let T := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let ΓT := Context.add T (Context.image Formula.raise (Context.add P Γ))
    have hTEx : Derives (Context.add P Γ) (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) hTEx
    have hT : Derives ΓT T := .hyp (Or.inl rfl)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Δ := Context.add H (Context.image Formula.raise ΓT)
    have hHEx : Derives ΓT (.ex H) := .conjR hT
    apply Derives.exE (p := H) hHEx
    have hZ2 := ZFContext.under (ZFContext.under (ZFContext.add hZ P) T) H
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using under (under (add hw P) T) H
    have hi2 : Derives Δ (inputAt w.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise,inputAt_rename] using under (under (add hi P) T) H
    have ht2 := of_eq (StructuralListTraceSyntax.valid_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hT) H)
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have htW := StructuralListValidity.range _ _ ht2
    have hparts := PacketByteInputProperties.typed_cons_inverse hZ2 w.castSucc.castSucc C.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc
      hw2 (.conjL hH) htW (.conjR hH) hi2
    have hout : Derives Δ (criterionAt w.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc) :=
      .disjR (intro_cons _ _ _ _ _ (.conjR hH) (.conjL hparts) (.conjR hparts))
    simpa only [Formula.raise,criterionAt_rename] using hout

theorem cons_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w))
    (hC : Derives Γ (.mem C w)) (hc : Derives Γ (consCase w C n)) : Derives Γ (inputAt w C n) := by
  let R := consBody w C n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hc
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hC2 : Derives Δ (.mem (old 2 C) (old 2 w)) := HornBinderRules.under_body 2 hC R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (inputAt_rename w C n (old 2)).symm
    (PacketByteInputProperties.cons_input hZ2 (old 2 w) (old 2 C) (slot 2 0) (slot 2 1) (old 2 n) hw2 hC2 (.conjL (.conjR hR)) (.conjR (.conjR hR)) (.conjL hR))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w))
    (hC : Derives Γ (.mem C w)) (hc : Derives Γ (criterionAt w C n)) : Derives Γ (inputAt w C n) := by
  apply Derives.disjE hc
  · exact PacketByteInputProperties.nil_input (ZFContext.add hZ _) w C n (add hw _) (.hyp (Or.inl rfl))
  · exact cons_backward (ZFContext.add hZ _) w C n (add hw _) (add hC _) (.hyp (Or.inl rfl))

theorem input_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w)) (hC : Derives Γ (.mem C w)) :
    Derives Γ ((inputAt w C n).iff (criterionAt w C n)) :=
  .conjI (.impI (forward (ZFContext.add hZ _) w C n (add hw _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w C n (add hw _) (add hC _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketByteInputDecomposition
