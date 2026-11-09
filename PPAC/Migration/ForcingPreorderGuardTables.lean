import PPAC.Migration.ForcingPreorderMember

/-! The actual negative branch changes the free condition slot before opening
its guard. Preserve the ORIGINAL carrier slot through that SAME replacement,
then compare the raw member leaf to the actual native guard instance. -/
namespace PPAC.Migration.ForcingPreorderGuardTables
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- The carrier index k differs from the original condition index k+1.
This is an object proof about the actual update, not a table equality premise. -/
theorem carrier_field {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f z T S j Q Sg I V : Fin m)
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j Q Sg))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S I V)) :
    Derives Γ (StructuralListFieldSyntax.field w Sg I V) := by
  have hIf := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f I hf hI
  have hNe := SyntaxNumerals.different hZ k (k+1) (Nat.ne_of_lt (Nat.lt_succ_self k)) I j hI hj
  exact Derives.impE (.conjR (ForcingReflexiveImages.field_iff w f z T S j Q Sg I V hr hIf))
    (.disjR (.conjI hNe hv))

/-- Reindex an actual replacement using an internally proved numeral
identity. The original replacement graph and list code stay unchanged. -/
theorem replacement_index {m} {Γ : Context m} (w f z T S j Q Sg J : Fin m)
    (he : Derives Γ (.equal j J))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j Q Sg)) :
    Derives Γ (ForcingReflexiveImages.replacement w f z T S J Q Sg) := by
  let E := ForcingReflexiveImages.replacement w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc
    (Fin.last m) Q.castSucc Sg.castSucc
  have hi : Derives Γ (E.instantiate j) :=
    of_eq (by simp only [E, Formula.instantiate, ForcingReflexiveImages.replacement_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  exact of_eq (by simp only [E, Formula.instantiate, ForcingReflexiveImages.replacement_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst E he hi)

/-- Consume the actual native InstantiateTop after the original condition
update. The carrier field is generated internally in S and transported to
Sg; no actual leaf query, carrier value or desired output equality supplied. -/
theorem member_from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)) (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j Q Sg))
    (hFrame : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P i) r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f u x))
    (hc : Derives Γ (ForcingGuardCode.compiled false R w A f x G))
    (ho : Derives Γ (substituted w K Hm A f C T G O))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P i) O Z)) :
    Derives Γ (.equal (H (ForcingPreorderMember.memberPosition i)) Z) := by
  have hw := Derives.conjL hFrame
  have hz := Derives.conjL (Derives.conjR (Derives.conjR hFrame))
  have hIW := SyntaxNumerals.range hZ k w I hw hI
  have he := StructuralListFieldValues.exists_value hZ w S I hw hIW
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc S.castSucc I.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hA11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under hA1 E)
  have hA21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under hA2 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hf E)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hj E)
  have hI1 := of_eq (SyntaxNumeralSyntax.numeral_rename k I Fin.castSucc) (under hI E)
  have hd1 := of_eq (ForcingPreorderLeaves.data_rename test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D Fin.castSucc) (under hd E)
  have hr1 := of_eq (ForcingReflexiveImages.replacement_rename w f z T S j Q Sg Fin.castSucc) (under hr E)
  have hFrame1 := of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C Rb Sg K Hm (P i) r s Fin.castSucc) (under hFrame E)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f u x Fin.castSucc) (under hh E)
  have hc1 := of_eq (ForcingGuardCode.compiled_rename false R w A f x G Fin.castSucc) (under hc E)
  have ho1 := of_eq (substituted_rename w K Hm A f C T G O Fin.castSucc) (under ho E)
  have hi1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C (P i) O Z Fin.castSucc) (under hi E)
  have hCarrier := carrier_field hZ1 w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc Q.castSucc Sg.castSucc I.castSucc (Fin.last m)
    hf1 hj1 hI1 hr1 (.conjR hE)
  have hRaw := ForcingPreorderMember.raw_from_data hZ1 test R i w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc T.castSucc C.castSucc B.castSucc S.castSucc Refl.castSucc Pre.castSucc I.castSucc (Fin.last m)
    (fun l => (v l).castSucc) (fun l => (Gb l).castSucc) (fun l => (H l).castSucc)
    (fun l => (U l).castSucc) (fun l => (F l).castSucc) (fun l => (P l).castSucc) (fun l => (N l).castSucc) (fun l => (D l).castSucc)
    hw1 hz1 hA11 hA21 hI1 hd1 (.conjR hE)
  have hTop := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hFrame1)))))
  have hMixed := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ1 w.castSucc z.castSucc T.castSucc C.castSucc (P i).castSucc O.castSucc Z.castSucc r.castSucc s.castSucc hw1 hTop)) hi1
  have hGuard := ForcingMemberGuardOpening.from_head hZ1 R w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc Rb.castSucc Sg.castSucc K.castSucc Hm.castSucc (P i).castSucc r.castSucc s.castSucc
    I.castSucc (Fin.last m) u.castSucc x.castSucc G.castSucc O.castSucc Z.castSucc hFrame1 hI1 hh1 hCarrier hc1 ho1 hMixed
  exact ForcingPreorderMember.same_result hZ1 w.castSucc (P i).castSucc (Fin.last m)
    (H (ForcingPreorderMember.memberPosition i)).castSucc Z.castSucc hw1 hRaw hGuard


private structure RawInputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hw : Derives Γ (omega w)
  hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)
  h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)
  h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)
  h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
  hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D)
  hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 2) Sg)
  hs : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z T S)
  hp0 : Derives Γ (SyntaxTermSyntax.term w z T (P 0))
  hp2 : Derives Γ (SyntaxTermSyntax.term w z T (P 2))

private theorem RawInputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre j Sg : Fin m}
    {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m}
    {U F P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : RawInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D) (E : Formula (m+l)) :
    RawInputs (Context.add E (raisedContext l Γ)) test R
      (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C)
      (old l B) (old l S) (old l Refl) (old l Pre) (old l j) (old l Sg)
      (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i))
      (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i))
      (fun i => old l (N i)) (fun i => old l (D i)) := by
  exact ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (omega_rename w (old l)) (HornBinderRules.under_body l h.hw E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old l)) (HornBinderRules.under_body l h.hz E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 (old l)) (HornBinderRules.under_body l h.h1 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 (old l)) (HornBinderRules.under_body l h.h2 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 (old l)) (HornBinderRules.under_body l h.h3 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f (old l)) (HornBinderRules.under_body l h.hf E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j (old l)) (HornBinderRules.under_body l h.hj E),
    of_eq (ForcingPreorderLeaves.data_rename test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D (old l)) (HornBinderRules.under_body l h.hd E),
    of_eq (ForcingReflexiveImages.replacement_rename w f z T S j (P 2) Sg (old l)) (HornBinderRules.under_body l h.hr E),
    of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z T S (old l)) (HornBinderRules.under_body l h.hs E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P 0) (old l)) (HornBinderRules.under_body l h.hp0 E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P 2) (old l)) (HornBinderRules.under_body l h.hp2 E)⟩

private theorem at_direct {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg g G X I J M W Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (E : Fin 4 → Fin m)
    (h : RawInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hSource : Derives Γ (ForcingRelationSource.data R 2 w z g A3 f (v 15) G X E))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (P 0) (P 2) I J M W))
    (hDirect : Derives Γ (ForcingGuardOpening.direct w z f T (P 0) Sg g G Y)) :
    Derives Γ (.equal (H 5) Y) := by
  let V := (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => (P 0).castSucc) (Fin.last m)).conj
    (substituted w.castSucc (Fin.last m) Sg.castSucc g.castSucc f.castSucc z.castSucc T.castSucc G.castSucc Y.castSucc)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hDirect
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have h1 := h.in_body V
  have hSource1 := of_eq (ForcingRelationSource.data_rename R 2 w z g A3 f (v 15) G X E Fin.castSucc) (under hSource V)
  have hImages1 := of_eq (ForcingRelationImages.data_rename k w f z T S (P 0) (P 2) I J M W Fin.castSucc) (under hImages V)
  have hJ := Derives.conjL (Derives.conjR hImages1)
  have heq := SyntaxNumerals.unique h1.zf (k+1) j.castSucc J.castSucc h1.hj hJ
  have hr := replacement_index w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc (P 2).castSucc Sg.castSucc J.castSucc heq h1.hr
  exact ForcingPreorderLeaves.relation_from_data h1.zf test R 2 w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc T.castSucc C.castSucc B.castSucc S.castSucc Refl.castSucc Pre.castSucc
    g.castSucc G.castSucc X.castSucc I.castSucc J.castSucc M.castSucc W.castSucc (Fin.last m) Sg.castSucc Y.castSucc
    (fun i => (v i).castSucc) (fun i => (Gb i).castSucc) (fun i => (H i).castSucc)
    (fun i => (U i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc)
    (fun i => (N i).castSucc) (fun i => (D i).castSucc) (fun i => (E i).castSucc)
    h1.hw h1.hz h1.h1 h1.h2 h1.hf h1.hd hSource1 hImages1 (.conjL hV) hr (.conjR hV)

private theorem from_guard_data {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (g : Fin 4 → Fin m)
    (h : RawInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hg : Derives Γ (ForcingGuardOpening.data true R w z f T (P 0) Sg a head q Y g)) :
    Derives Γ (.equal (H 5) Y) := by
  have hSrc := ForcingRelationSource.from_matrix h.zf R 2 w z A1 A2 A3 f a head q v g
    h.hw h.hz h.h3 h.hf (.conjL h.hd) (.conjL hg)
  let E := ForcingRelationSource.body R 2 w z (g 0) A3 f (v 15) (g 1)
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ hSrc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := h.in_body E
  have hd5 := of_eq (ForcingGuardOpening.direct_rename w z f T (P 0) Sg (g 0) (g 1) Y (old 5)) (HornBinderRules.under_body 5 (.conjR hg) E)
  have hTables := ForcingRelationImages.produce h5.zf k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P 2)) h5.hw h5.hs h5.hp0 h5.hp2
  let L := ForcingRelationImages.body k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P 2))
  let Ξ := Context.add L (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 L _ hTables
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have h9 := h5.in_body L
  have hd9 := of_eq (ForcingGuardOpening.direct_rename (old 5 w) (old 5 z) (old 5 f) (old 5 T) (old 5 (P 0)) (old 5 Sg) (old 5 (g 0)) (old 5 (g 1)) (old 5 Y) (old 4)) (HornBinderRules.under_body 4 hd5 L)
  have hs9 : Derives Ξ (ForcingRelationSource.data R 2 (old 9 w) (old 9 z) (old 9 (g 0)) (old 9 A3) (old 9 f) (old 9 (v 15)) (old 9 (g 1))
      (old 4 (slot 5 0)) (fun i => old 4 (slot 5 i.succ))) :=
    of_eq (by simp only [E, ForcingRelationSource.body, ForcingRelationSource.data_rename]; rfl) (HornBinderRules.under_body 4 hE L)
  exact at_direct test R (old 9 w) (old 9 z) (old 9 A1) (old 9 A2) (old 9 A3) (old 9 f) (old 9 T) (old 9 C) (old 9 B) (old 9 S) (old 9 Refl) (old 9 Pre) (old 9 j) (old 9 Sg)
    (old 9 (g 0)) (old 9 (g 1)) (old 4 (slot 5 0)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 9 Y)
    (fun i => old 9 (v i)) (fun i => old 9 (Gb i)) (fun i => old 9 (H i))
    (fun i => old 9 (U i)) (fun i => old 9 (F i)) (fun i => old 9 (P i))
    (fun i => old 9 (N i)) (fun i => old 9 (D i)) (fun i => old 4 (slot 5 i.succ))
    h9 hs9 hL hd9


/-- The actual relation guard after updating the free condition slot to P2
is the SAME raw R(P0,P2) leaf. The four compiler, five common-source, four
argument-table and single forest witnesses are all eliminated internally. -/
theorem relation_from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 2) Sg))
    (hFrame : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f u x))
    (hc : Derives Γ (ForcingGuardCode.compiled true R w A f x G))
    (ho : Derives Γ (substituted w K Hm A f C T G O))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P 0) O Z)) :
    Derives Γ (.equal (H 5) Z) := by
  have hw := Derives.conjL hFrame
  have hz := Derives.conjL (Derives.conjR (Derives.conjR hFrame))
  have hRow := Derives.conjL (Derives.conjL (Derives.conjR hd))
  have hParent := Derives.conjL (Derives.conjR (Derives.conjR hd))
  have hS := Derives.conjR (Derives.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hParent))
  have hP0 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 0) (F 0) (U 1) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hRow)))))))))))
  have hP2 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 2) (F 2) (N 0) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hRow)))))))))))))))
  have hRaw : RawInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D :=
    ⟨hZ,hw,hz,hA1,hA2,hA3,hf,hj,hd,hr,hS,hP0,hP2⟩
  have he := ForcingGuardOpening.from_instance hZ true R w mode z a f T A C Rb Sg K Hm (P 0) r s u x G O Z hFrame hh hc ho hi
  let E := ForcingGuardOpening.body true R w z f T (P 0) Sg A x G Z
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h4 := hRaw.in_body E
  exact from_guard_data test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 T) (old 4 C)
    (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 j) (old 4 Sg) (old 4 A) (old 4 x) (old 4 G) (old 4 Z)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i))
    (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i))
    (fun i => old 4 (N i)) (fun i => old 4 (D i)) (slot 4) h4 hE

def memberInput {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j Q Sg).conj ((ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P i) r s).conj ((SyntaxMixedImageHead.head w A f u x).conj ((ForcingGuardCode.compiled false R w A f x G).conj ((substituted w K Hm A f C T G O).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P i) O Z))))))))))))

def memberSentence {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((memberInput test R i w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D).imp (.equal (H (ForcingPreorderMember.memberPosition i)) Z)).close

theorem member_kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (memberSentence test R i w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := memberInput test R i w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact member_from_instance (ZFContext.add (ZFContext.source_ZF m) E) test R i w z A1 A2 A3 f T C B S Refl Pre I j Q Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D
    (Derives.conjL (h))
    (Derives.conjL (Derives.conjR (h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (h))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))

def relationInput {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingReflexiveImages.replacement w f z T S j (P 2) Sg).conj ((ForcingMemberGuardOpening.frame w mode z a f T A C Rb Sg K Hm (P 0) r s).conj ((SyntaxMixedImageHead.head w A f u x).conj ((ForcingGuardCode.compiled true R w A f x G).conj ((substituted w K Hm A f C T G O).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 0) O Z))))))))))))

def relationSentence {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((relationInput test R w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D).imp (.equal (H 5) Z)).close

theorem relation_kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (relationSentence test R w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := relationInput test R w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact relation_from_instance (ZFContext.add (ZFContext.source_ZF m) E) test R w z A1 A2 A3 f T C B S Refl Pre j Sg mode a A Rb K Hm r s u x G O Z v Gb H U F P N D
    (Derives.conjL (h))
    (Derives.conjL (Derives.conjR (h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (h))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))))))

end PPAC.Migration.ForcingPreorderGuardTables
