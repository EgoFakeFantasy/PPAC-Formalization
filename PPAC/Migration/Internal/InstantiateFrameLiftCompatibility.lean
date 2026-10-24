import PPAC.Migration.Internal.InstantiateFrameLiftValues

/-! mode2全部内部变量由原零／后继分解合成兼容性；独立源／目标后继及闭参数保持构成真实下一层frame。 -/
namespace PPAC.Migration.Internal.InstantiateFrameLiftCompatibility
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax InstantiateOperationFrameSyntax InstantiateVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i A)) (hX : Derives Γ (SyntaxVariableSyntax.code true w i X)) :
    Derives Γ ((boundValue w D P i X q).iff (StructuralListFieldSyntax.field w K i q)) := by
  have hin := SyntaxVariableDecode.index_natural true w i X hX
  have hsplit := OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw
  apply Derives.disjE (OmegaStructureAlgebra.decomposition_at w i hsplit hin)
  · exact InstantiateFrameLiftPoint.fresh (ZFContext.add hZ _) w depth P D R S a b c e A C K H U V z n i X q
      (add hw _) (add (.conjL (metadata w mode depth P a b c e R S hF)) _) (add hD _) (add hl _) (add hU _) (add hV _) (add hHead _) (add hi _) (.hyp (Or.inl rfl)) (add hX _)
  · let E := OmegaStructureSyntax.predecessor w i
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hF1 : Derives Δ (frame w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc) := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under (add hF E) B)
    have hD1 : Derives Δ (successor D.castSucc depth.castSucc) := of_eq (successor_rename D depth Fin.castSucc) (under (add hD E) B)
    have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c e A C K H Fin.castSucc) (under (add hl E) B)
    have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under (add hU E) B)
    have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc e.castSucc V.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under (add hV E) B)
    have hHead1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc e.castSucc z.castSucc n.castSucc) := of_eq (SyntaxMixedImageHead.head_rename w C e z n Fin.castSucc) (under (add hHead E) B)
    have hi1 : Derives Δ (Formula.mem i.castSucc A.castSucc) := under (add hi E) B
    have hX1 : Derives Δ (SyntaxVariableSyntax.code true w.castSucc i.castSucc X.castSucc) := of_eq (SyntaxVariableSyntax.code_rename true w i X Fin.castSucc) (under (add hX E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc hl1
    have ha := Derives.conjL (Derives.conjL (term_lists w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc hF1))
    have hj := SyntaxIndexLiftOrder.predecessor_member hZ1 w.castSucc a.castSucc A.castSucc i.castSucc (Fin.last m) hw1 ha (.conjL (.conjR hInput)) hi1 (.conjR hB)
    have ho := InstantiateFrameLiftValues.bound_successor hZ1 w.castSucc mode.castSucc depth.castSucc P.castSucc D.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc z.castSucc n.castSucc i.castSucc (Fin.last m) X.castSucc q.castSucc hw1 hF1 hD1 hl1 hU1 hV1 hHead1 hi1 hj (.conjR hB) hX1
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, boundValue_rename, StructuralListFieldSyntax.field_rename]) ho

theorem compatible {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n)) : Derives Γ (InstantiateOperationFrameSyntax.compatible boundTag w D P A b K H) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 3 0) (SyntaxTermSyntax.limit boundTag (old 3 A) (old 3 b))).conj
    (SyntaxVariableSyntax.code boundTag (old 3 w) (slot 3 0) (slot 3 1))
  let Δ := Context.add G (raisedContext 3 Γ)
  have hZ3 := HornBinderRules.zf_body 3 hZ G
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw G)
  have hF3 : Derives Δ (frame (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 R) (old 3 S)) := of_eq (frame_rename w mode depth P a b c e R S (old 3)) (HornBinderRules.under_body 3 hF G)
  have hD3 : Derives Δ (successor (old 3 D) (old 3 depth)) := of_eq (successor_rename D depth (old 3)) (HornBinderRules.under_body 3 hD G)
  have hl3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 A) (old 3 C) (old 3 K) (old 3 H)) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c e A C K H (old 3)) (HornBinderRules.under_body 3 hl G)
  have hU3 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap (old 3 w) (old 3 c) (old 3 C) (old 3 U)) := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U (old 3)) (HornBinderRules.under_body 3 hU G)
  have hV3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap (old 3 w) (old 3 e) (old 3 V)) := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V (old 3)) (HornBinderRules.under_body 3 hV G)
  have hHead3 : Derives Δ (SyntaxMixedImageHead.head (old 3 w) (old 3 C) (old 3 e) (old 3 z) (old 3 n)) := of_eq (SyntaxMixedImageHead.head_rename w C e z n (old 3)) (HornBinderRules.under_body 3 hHead G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  cases boundTag
  · exact InstantiateFrameLiftValues.free hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 D) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 U) (old 3 V) (old 3 z) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hF3 hD3 hl3 hU3 hV3 hHead3 (.conjL hG) (.conjR hG)
  · exact bound hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 P) (old 3 D) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 e) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 U) (old 3 V) (old 3 z) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hF3 hD3 hl3 hU3 hV3 hHead3 (.conjL hG) (.conjR hG)

theorem at_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n)) : Derives Γ (frame w mode D P A b C e K H) := by
  have hMeta := metadata w mode depth P a b c e R S hF
  have hDn := OmegaStructureAlgebra.successor_member w D depth (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hMeta) hD
  have hInput := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c e A C K H hl
  have hContexts := InstantiateBinderGeometry.lifted_contexts hZ depth a b c e D A C
    (contexts w mode depth P a b c e R S hF) hD (.conjL (.conjR hInput)) (.conjR (.conjR hInput))
  exact .conjI (mode_number w mode depth P a b c e R S hF)
    (.conjI (.conjI hDn (.conjR hMeta))
      (.conjI (parameter_closed w mode depth P a b c e R S hF)
        (.conjI (SyntaxCodedMixedBinderTyping.output_lists w R S a b c e A C K H hl)
          (.conjI (compatible hZ true w mode depth P D R S a b c e A C K H U V z n hw hF hD hl hU hV hHead)
            (.conjI (compatible hZ false w mode depth P D R S a b c e A C K H U V z n hw hF hD hl hU hV hHead) hContexts)))))

end PPAC.Migration.Internal.InstantiateFrameLiftCompatibility
