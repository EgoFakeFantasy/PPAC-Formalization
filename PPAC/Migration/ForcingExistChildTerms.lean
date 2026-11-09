import PPAC.Migration.ForcingExistChildCode
import PPAC.Migration.Internal.SyntaxCodedMixedTermFields
import PPAC.Migration.Internal.SyntaxRenameTermAtIndex

/-! Exact variable actions of the SAME original Force.ex child compiler.
The condition slot becomes bound1, the new name stays bound0, other free
slots stay fixed and old bound indices move by two. All indices, codes and
the original twelve compiler witnesses remain object variables. The original
shift/lift/table machinery is consumed, never reconstructed. -/
namespace PPAC.Migration.ForcingExistChildTerms
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w a A B C f j N Q x y i : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x y).iff
      (edge (SyntaxIndexMapSyntax.selectMap bound (v 8) (v 9)) i y)) := by
  have h8 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))))))
  have h9 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))))))
  have hl : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w A f C f (v 10) (v 11)) := .conjI
    (SyntaxMixedImageCodeFields.term_list w (v 8) A C f (v 10) h8)
    (SyntaxMixedImageCodeFields.term_list w (v 9) f C f (v 11) h9)
  have ht := SyntaxCodedMixedTermFields.at_field hZ bound w (v 10) (v 11) A f C f x y i hw hl hx
  have he := SyntaxMixedImageCodeFields.edges w (SyntaxIndexMapSyntax.selectMap bound (v 8) (v 9))
    (SyntaxTermSyntax.limit bound A f) C f (SyntaxIndexMapSyntax.selectMap bound (v 10) (v 11)) i y
    (SyntaxCodedMixedTermFields.selected_encoded bound w (v 8) (v 9) A f C f (v 10) (v 11) (.conjI h8 h9))
  exact SyntaxTypeLocalTransfer.iff_trans ht (.conjI (.conjR he) (.conjL he))

private theorem mapped_at {m} {Γ : Context m} (w j t f B D i q : Fin m)
    (hd : Derives Γ (ForcingConditionRebind.mapped w j t f B D)) :
    Derives Γ ((edge D i q).iff ((Formula.mem i f).conj (ForcingConditionRebind.value w j t i q))) :=
  of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, edge_rename,
    ForcingConditionRebind.value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE q (Derives.allE i (.conjR hd)))

private theorem identity_edge {m} {Γ : Context m}
    (w f R i : Fin m) (hR : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f R))
    (hi : Derives Γ (.mem i f)) : Derives Γ (edge R i i) := by
  let E := (Formula.mem (Fin.last m) f.castSucc).conj (valueAt R.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxIndexMapSyntax.value_exists w R f f i (.conjL hR) hi)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hd := of_eq (SyntaxRenameTermIdentity.diagonal_rename R Fin.castSucc) (under (.conjR hR) E)
  have he := SyntaxRenameTermIdentity.diagonal_at R.castSucc i.castSucc (Fin.last m) hd (.conjL (.conjR hE))
  exact of_eq (edge_rename R i i Fin.castSucc).symm
    (GraphPointwiseSyntax.edge_subst_output _ _ _ _ (eq_symm he) (.conjL (.conjR hE)))

private theorem shift_edge {m} {Γ : Context m} (w b B R i I : Fin m)
    (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w b B R))
    (hi : Derives Γ (.mem i b)) (hI : Derives Γ (successor I i)) : Derives Γ (edge R i I) :=
  .impE (.conjR (SyntaxFreeShiftGraph.edge_iff b R i I (SyntaxFreeShiftGraph.to_graph w b B R hR))) (.conjI hi hI)

private theorem head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q x y i : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hi : Derives Γ (empty i)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x y).iff (.equal y (v 1))) := by
  have hl := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))))
  exact SyntaxTypeLocalTransfer.iff_trans (at_graph hZ true w a A B C f j N Q x y i v hw hd hx)
    (SyntaxMixedImageLiftFields.zero_iff hZ w (v 4) (v 5) (v 6) (v 7) a f B f A C (v 1) (v 8) (v 9) i y hl hw hi)

private theorem free_other {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q x y i : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w i x)) (hi : Derives Γ (.mem i f))
    (hne : Derives Γ (Formula.equal i j).neg) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x y).iff
      (SyntaxVariableSyntax.code false w i y)) := by
  have h3 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hd))))
  have h4 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))
  have h6 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))))
  have h7 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))))
  have he := Derives.impE (.conjR (mapped_at w j (v 1) f B (v 7) i x h6))
    (.conjI hi (.disjR (.conjI hne hx)))
  have hLift := SyntaxMixedImageLiftFields.free_iff hZ w (v 4) (v 5) (v 6) (v 7) a f B f A C
    (v 1) (v 8) (v 9) i x y h7 he
  have hRename := SyntaxRenameTermAtIndex.renamed_at hZ false w (v 4) (v 5) B f C f x y i i hw
    (.conjI (.conjL (.conjR h3)) (.conjL h4)) hi (identity_edge w f (v 5) i h4 hi) hx
  exact SyntaxTypeLocalTransfer.iff_trans (at_graph hZ false w a A B C f j N Q x y i v hw hd hx)
    (SyntaxTypeLocalTransfer.iff_trans hLift hRename)

private theorem free_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q x y z one : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w j x)) (hj : Derives Γ (.mem j f))
    (hz : Derives Γ (empty z)) (hone : Derives Γ (successor one z)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x y).iff
      (SyntaxVariableSyntax.code true w one y)) := by
  have h0 := Derives.conjL (hd)
  have h3 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hd))))
  have h4 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))
  have h6 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))))
  have h7 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))))
  have he := Derives.impE (.conjR (mapped_at w j (v 1) f B (v 7) j (v 1) h6))
    (.conjI hj (.disjL (.conjI (.eqRefl j) (.eqRefl (v 1)))))
  have hm := SyntaxMixedImageLiftFields.source_inputs w (v 4) (v 5) (v 6) (v 7) a f B f A C (v 1) (v 8) (v 9) h7
  have ht := SyntaxTermImageSyntax.image_type w (v 7) f B f j (v 1) (.conjR (.conjL hm)) he
  have hi := SyntaxTerms.member hZ true w B f (v 1) (v 0) hw (.conjL (.conjR h0)) ht
  have hez := OmegaUniversal.empty_unique z (v 0) (ZFContext.arithmetic hZ).base.extensionality hz (.conjL h0)
  have hSucc : Derives Γ (successor one (v 0)) := by
    let P := successor one.castSucc (Fin.last m)
    exact of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P hez (of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hone))
  have hLift := SyntaxMixedImageLiftFields.free_iff hZ w (v 4) (v 5) (v 6) (v 7) a f B f A C
    (v 1) (v 8) (v 9) j (v 1) y h7 he
  have hRename := SyntaxRenameTermAtIndex.renamed_at hZ true w (v 4) (v 5) B f C f (v 1) y (v 0) one hw
    (.conjI (.conjL (.conjR h3)) (.conjL h4)) hi (shift_edge w B C (v 4) (v 0) one h3 hi hSucc) (.conjL (.conjR h0))
  exact SyntaxTypeLocalTransfer.iff_trans (at_graph hZ false w a A B C f j N Q x y j v hw hd hx)
    (SyntaxTypeLocalTransfer.iff_trans hLift hRename)

private theorem old_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q x y i pred I II : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hp : Derives Γ (.mem pred a))
    (hi : Derives Γ (.mem i A)) (hs : Derives Γ (successor i pred))
    (hI : Derives Γ (successor I i)) (hII : Derives Γ (successor II I)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x y).iff
      (SyntaxVariableSyntax.code true w II y)) := by
  have h1 := Derives.conjL (Derives.conjR (hd))
  have h2 := Derives.conjL (Derives.conjR (Derives.conjR (hd)))
  have h3 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hd))))
  have h4 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd)))))
  have h5 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))
  have h7 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hd))))))))
  have heF := Derives.impE (.conjR (SyntaxVariableTableFields.shifted_at hZ true w a A f (v 2) pred i x h1 hp hs)) hx
  have hMap : Derives Γ (SyntaxIndexMapSyntax.maps w (v 3) (v 5) A f B f) :=
    .conjI (.conjL (.conjR h2)) (.conjL h4)
  have heI := shift_edge w A B (v 3) i I h2 hi hI
  have hiB := SyntaxIndexMapSyntax.edge_target w (v 3) A B i I (.conjL hMap) heI
  have hctx := SyntaxIndexMapSyntax.source_contexts w (v 3) (v 5) A f B f hMap
  have hterm := SyntaxTermSyntax.intro_term true w A f x i (.conjI hctx hi) hx
  let T := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxRenameTermSyntax.renamed w.castSucc (v 3).castSucc (v 5).castSucc A.castSucc f.castSucc B.castSucc f.castSucc x.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxRenameTermExistence.for_term hZ w (v 3) (v 5) A f B f x hw hMap hterm)
  have hZ1 := ZFContext.under hZ T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hd1 := of_eq (ForcingExistChildCode.data_rename w a A B C f j N Q v Fin.castSucc) (under hd T)
  have hx1 := of_eq (SyntaxVariableSyntax.code_rename true w i x Fin.castSucc) (under hx T)
  have h2a := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B (v 3) Fin.castSucc) (under h2 T)
  have h3a := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C (v 4) Fin.castSucc) (under h3 T)
  have h4a := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f (v 5) Fin.castSucc) (under h4 T)
  have h5a := of_eq (SyntaxTermImagePushSyntax.pushed_rename w (v 3) (v 5) A f B f (v 2) a (v 6) Fin.castSucc) (under h5 T)
  have h7a := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w (v 4) (v 5) (v 6) (v 7) a f B f A C (v 1) (v 8) (v 9) Fin.castSucc) (under h7 T)
  have heFa := of_eq (edge_rename (v 2) pred x Fin.castSucc) (under heF T)
  have hiA := under hi T
  have hIA := of_eq (successor_rename I i Fin.castSucc) (under hI T)
  have heIA := shift_edge w.castSucc A.castSucc B.castSucc (v 3).castSucc i.castSucc I.castSucc h2a hiA hIA
  have hcode := Derives.impE (.conjL (SyntaxRenameTermAtIndex.renamed_at hZ1 true w.castSucc (v 3).castSucc (v 5).castSucc
    A.castSucc f.castSucc B.castSucc f.castSucc x.castSucc (Fin.last m) i.castSucc I.castSucc hw1
    (.conjI (.conjL (.conjR h2a)) (.conjL h4a)) hiA heIA hx1)) (.conjR hT)
  have heG := Derives.impE (.conjR (SyntaxTermImagePushGraph.at_value hZ1 w.castSucc (v 3).castSucc (v 5).castSucc
    A.castSucc f.castSucc B.castSucc f.castSucc (v 2).castSucc a.castSucc (v 6).castSucc pred.castSucc x.castSucc (Fin.last m) h5a heFa)) (.conjR hT)
  have hb := SyntaxMixedImageLiftFields.bound_iff hZ1 w.castSucc (v 4).castSucc (v 5).castSucc
    (v 6).castSucc (v 7).castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc
    (v 1).castSucc (v 8).castSucc (v 9).castSucc i.castSucc pred.castSucc (Fin.last m) y.castSucc h7a hw1
    (under hp T) (of_eq (successor_rename i pred Fin.castSucc) (under hs T)) heG
  have hIB := under hiB T
  have hIIA := of_eq (successor_rename II I Fin.castSucc) (under hII T)
  have hr := SyntaxRenameTermAtIndex.renamed_at hZ1 true w.castSucc (v 4).castSucc (v 5).castSucc
    B.castSucc f.castSucc C.castSucc f.castSucc (Fin.last m) y.castSucc I.castSucc II.castSucc hw1
    (.conjI (.conjL (.conjR h3a)) (.conjL h4a)) hIB
    (shift_edge w.castSucc B.castSucc C.castSucc (v 4).castSucc I.castSucc II.castSucc h3a hIB hIIA) hcode
  have ho := SyntaxTypeLocalTransfer.iff_trans
    (at_graph hZ1 true w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc Q.castSucc
      x.castSucc y.castSucc i.castSucc (fun k => (v k).castSucc) hw1 hd1 hx1)
    (SyntaxTypeLocalTransfer.iff_trans hb hr)
  exact of_eq (by simp only [Formula.rename, Formula.iff, SyntaxCodedMixedTermSyntax.substituted_rename,
    SyntaxVariableSyntax.code_rename]) ho

/-- Four exact actions on the original two coded tables; p contains eight
arbitrary runtime indices/codes, not a decoded standard syntax tree. -/
def point {m} (w a A C f j : Fin m) (p : Fin 8 → Fin m) (v : Fin 12 → Fin m) : Formula m :=
  (((empty (p 2)).conj (SyntaxVariableSyntax.code true w (p 2) (p 0))).imp
    ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f (p 0) (p 1)).iff (.equal (p 1) (v 1)))).conj
  ((((Formula.mem j f).conj ((SyntaxVariableSyntax.code false w j (p 0)).conj
    ((empty (p 6)).conj (successor (p 7) (p 6))))).imp
    ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f (p 0) (p 1)).iff
      (SyntaxVariableSyntax.code true w (p 7) (p 1)))).conj
  ((((Formula.mem (p 2) f).conj ((SyntaxVariableSyntax.code false w (p 2) (p 0)).conj (Formula.equal (p 2) j).neg)).imp
    ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f (p 0) (p 1)).iff
      (SyntaxVariableSyntax.code false w (p 2) (p 1)))).conj
  (((Formula.mem (p 3) a).conj ((Formula.mem (p 2) A).conj ((successor (p 2) (p 3)).conj
    ((successor (p 4) (p 2)).conj ((successor (p 5) (p 4)).conj
      (SyntaxVariableSyntax.code true w (p 2) (p 0))))))).imp
    ((SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f (p 0) (p 1)).iff
      (SyntaxVariableSyntax.code true w (p 5) (p 1))))))

theorem point_rename {m l} (w a A C f j : Fin m) (p : Fin 8 → Fin m) (v : Fin 12 → Fin m) (r : Fin m → Fin l) :
    (point w a A C f j p v).rename r =
      point (r w) (r a) (r A) (r C) (r f) (r j) (fun i => r (p i)) (fun i => r (v i)) := by
  simp only [point, Formula.rename, Formula.iff, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxCodedMixedTermSyntax.substituted_rename, Formula.neg]

private theorem point_from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q : Fin m) (p : Fin 8 → Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v)) :
    Derives Γ (point w a A C f j p v) := by
  apply Derives.conjI
  · apply Derives.impI
    have h : Derives (Context.add ((empty (p 2)).conj (SyntaxVariableSyntax.code true w (p 2) (p 0))) Γ)
        ((empty (p 2)).conj (SyntaxVariableSyntax.code true w (p 2) (p 0))) := .hyp (Or.inl rfl)
    exact head (ZFContext.add hZ _) w a A B C f j N Q (p 0) (p 1) (p 2) v
      (add hw _) (add hd _) (.conjR h) (.conjL h)
  · apply Derives.conjI
    · apply Derives.impI
      let E := (Formula.mem j f).conj ((SyntaxVariableSyntax.code false w j (p 0)).conj
        ((empty (p 6)).conj (successor (p 7) (p 6))))
      have h : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
      exact free_selected (ZFContext.add hZ _) w a A B C f j N Q (p 0) (p 1) (p 6) (p 7) v
        (add hw _) (add hd _) (.conjL (.conjR h)) (.conjL h) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))
    · apply Derives.conjI
      · apply Derives.impI
        let E := (Formula.mem (p 2) f).conj ((SyntaxVariableSyntax.code false w (p 2) (p 0)).conj (Formula.equal (p 2) j).neg)
        have h : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
        exact free_other (ZFContext.add hZ _) w a A B C f j N Q (p 0) (p 1) (p 2) v
          (add hw _) (add hd _) (.conjL (.conjR h)) (.conjL h) (.conjR (.conjR h))
      · apply Derives.impI
        let E := (Formula.mem (p 3) a).conj ((Formula.mem (p 2) A).conj ((successor (p 2) (p 3)).conj
          ((successor (p 4) (p 2)).conj ((successor (p 5) (p 4)).conj (SyntaxVariableSyntax.code true w (p 2) (p 0))))))
        have h : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
        exact old_bound (ZFContext.add hZ _) w a A B C f j N Q (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) v
          (add hw _) (add hd _) (.conjR (.conjR (.conjR (.conjR (.conjR h))))) (.conjL h)
          (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h))))
          (.conjL (.conjR (.conjR (.conjR (.conjR h)))))

private def lawsBody {m} (w a A C f j : Fin m) (v : Fin 12 → Fin m) : Formula (m+8) :=
  point (old 8 w) (old 8 a) (old 8 A) (old 8 C) (old 8 f) (old 8 j) (slot 8) (fun i => old 8 (v i))

/-- The same twelve witnesses satisfy ALL four laws at ALL internal candidates. -/
def laws {m} (w a A C f j : Fin m) (v : Fin 12 → Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 8 (lawsBody w a A C f j v)

theorem laws_rename {m l} (w a A C f j : Fin m) (v : Fin 12 → Fin m) (r : Fin m → Fin l) :
    (laws w a A C f j v).rename r =
      laws (r w) (r a) (r A) (r C) (r f) (r j) (fun i => r (v i)) := by
  simp only [laws, OriginalUniversalBlock.allMany_rename, lawsBody, point_rename, lift_old, lift_slot]

theorem from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q : Fin m) (v : Fin 12 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingExistChildCode.data w a A B C f j N Q v)) :
    Derives Γ (laws w a A C f j v) := by
  apply OriginalUniversalBlock.intro_many 8
  exact point_from_data (HornBinderRules.zf_many 8 hZ) (old 8 w) (old 8 a) (old 8 A) (old 8 B) (old 8 C)
    (old 8 f) (old 8 j) (old 8 N) (old 8 Q) (slot 8) (fun i => old 8 (v i))
    (of_eq (omega_rename w (old 8)) (HornBinderRules.under_many 8 hw))
    (of_eq (ForcingExistChildCode.data_rename w a A B C f j N Q v (old 8)) (HornBinderRules.under_many 8 hd))

theorem at_laws {m} {Γ : Context m} (w a A C f j : Fin m) (v : Fin 12 → Fin m) (p : Fin 8 → Fin m)
    (hl : Derives Γ (laws w a A C f j v)) : Derives Γ (point w a A C f j p v) :=
  of_eq (by simp only [lawsBody, point_rename, assign_old, assign_slot])
    (OriginalUniversalBlock.at_many 8 _ p hl)

private def resultBody {m} (w a A B C f j N Q : Fin m) : Formula (m+12) :=
  (ForcingExistChildCode.body w a A B C f j N Q).conj
    (laws (old 12 w) (old 12 a) (old 12 A) (old 12 C) (old 12 f) (old 12 j) (slot 12))

def result {m} (w a A B C f j N Q : Fin m) : Formula m :=
  existsMany 12 (resultBody w a A B C f j N Q)

theorem result_rename {m l} (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (result w a A B C f j N Q).rename r =
      result (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [result, existsMany_rename, resultBody, Formula.rename, ForcingExistChildCode.body,
    ForcingExistChildCode.data_rename, laws_rename, lift_old, lift_slot]

theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Q)) :
    Derives Γ (result w a A B C f j N Q) := by
  let D := ForcingExistChildCode.body w a A B C f j N Q
  let Δ := Context.add D (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 D _ hc
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hl := from_data (HornBinderRules.zf_body 12 hZ D) (old 12 w) (old 12 a) (old 12 A) (old 12 B)
    (old 12 C) (old 12 f) (old 12 j) (old 12 N) (old 12 Q) (slot 12)
    (of_eq (omega_rename w (old 12)) (HornBinderRules.under_body 12 hw D)) hD
  have ho : Derives Δ (result (old 12 w) (old 12 a) (old 12 A) (old 12 B) (old 12 C)
      (old 12 f) (old 12 j) (old 12 N) (old 12 Q)) := by
    apply HornBinderRules.intro_many 12 _ (slot 12)
    exact of_eq (by simp only [resultBody, D, ForcingExistChildCode.body, Formula.rename,
      ForcingExistChildCode.data_rename, laws_rename, assign_old, assign_slot]) (.conjI hD hl)
  exact of_eq (result_rename w a A B C f j N Q (old 12)).symm ho

def input {m} (w a A B C f j N Q : Fin m) : Formula m :=
  (omega w).conj (ForcingExistChildCode.compiled w a A B C f j N Q)

def sentence {m} (w a A B C f j N Q : Fin m) : Source.Sentence :=
  ((input w a A B C f j N Q).imp (result w a A B C f j N Q)).close

theorem kernel_certificate {m} (w a A B C f j N Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a A B C f j N Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w a A B C f j N Q
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) w a A B C f j N Q (.conjL h) (.conjR h)

end PPAC.Migration.ForcingExistChildTerms
