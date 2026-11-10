import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.Internal.StructuralListFieldGraphFiber
import PPAC.Migration.Internal.SyntaxNumeralMembers

/-! Canonical arguments for the SAME source H in pinned Force.ex. Reuse the
original single-slot replacement, the original complete field graph at the
H arity, and the original image-code encoder. Only the name slot k changes;
the condition slot k+1 is outside the H table. Runtime target scopes/terms
remain arbitrary internal objects. No new graph/list recursion or compiler. -/
namespace PPAC.Migration.ForcingExistDomainImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMixedImageCodeSyntax (termList termList_rename encoded encoded_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def input {m} (k : Nat) (w f h c T Base I Name : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral k I).conj
    ((SyntaxNumeralSyntax.numeral (k+1) h).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj
      ((termList w f c T Base).conj (SyntaxTermSyntax.term w c T Name)))))
theorem input_rename {m l} (k : Nat) (w f h c T Base I Name : Fin m) (r : Fin m → Fin l) :
    (input k w f h c T Base I Name).rename r = input k (r w) (r f) (r h) (r c) (r T) (r Base) (r I) (r Name) := by
  simp only [input, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename, termList_rename, SyntaxTermSyntax.term_rename]

def data {m} (k : Nat) (w f h c T Base I Name Whole G D : Fin m) : Formula m :=
  (input k w f h c T Base I Name).conj
    ((ForcingReflexiveImages.replacement w f c T Base I Name Whole).conj
      ((StructuralListFieldGraphSyntax.fields w Whole h G).conj (encoded w G h c T D)))
theorem data_rename {m l} (k : Nat) (w f h c T Base I Name Whole G D : Fin m) (r : Fin m → Fin l) :
    (data k w f h c T Base I Name Whole G D).rename r =
      data k (r w) (r f) (r h) (r c) (r T) (r Base) (r I) (r Name) (r Whole) (r G) (r D) := by
  simp only [data, Formula.rename, input_rename, ForcingReflexiveImages.replacement_rename, StructuralListFieldGraphSyntax.fields_rename, encoded_rename]
def body {m} (k : Nat) (w f h c T Base I Name : Fin m) : Formula (m+3) :=
  data k (old 3 w) (old 3 f) (old 3 h) (old 3 c) (old 3 T) (old 3 Base) (old 3 I) (old 3 Name) (slot 3 0) (slot 3 1) (slot 3 2)
def produced {m} (k : Nat) (w f h c T Base I Name : Fin m) : Formula m := existsMany 3 (body k w f h c T Base I Name)
theorem produced_rename {m l} (k : Nat) (w f h c T Base I Name : Fin m) (r : Fin m → Fin l) :
    (produced k w f h c T Base I Name).rename r = produced k (r w) (r f) (r h) (r c) (r T) (r Base) (r I) (r Name) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem within {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (h f i : Fin m)
    (hh : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) h))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hi : Derives Γ (.mem i h)) : Derives Γ (.mem i f) := by
  have hb := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ (k+1) h i hh)) hi
  have hc := SyntaxPositionSyntax.below_imp (k+1) i (.mem i f) (fun p => by
    apply Derives.impI
    exact SyntaxNumeralMembers.index_member (ZFContext.add hZ _) (k+2) p.castSucc f i (add hf _) (.hyp (Or.inl rfl)))
  exact .impE hc hb

/-- The EXISTING field graph already supplies its whole sequence. Attach
original term typing at its real edges and call the EXISTING encoder. -/
private theorem canonical_image {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f h c T Whole G : Fin m) (hw : Derives Γ (omega w))
    (hh : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) h))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hWhole : Derives Γ (termList w f c T Whole))
    (hG : Derives Γ (StructuralListFieldGraphSyntax.fields w Whole h G)) :
    Derives Γ (SyntaxTermImageSyntax.imageMap w G h c T) := by
  have hv : Derives Γ (SyntaxTermImageSyntax.values w G c T) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let E := edge G.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add E (raisedContext 2 Γ)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 hZ E
    have hh2 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) h (old 2)) (HornBinderRules.under_body 2 hh E)
    have hf2 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f (old 2)) (HornBinderRules.under_body 2 hf E)
    have ht2 := of_eq (termList_rename w f c T Whole (old 2)) (HornBinderRules.under_body 2 hWhole E)
    have hg2 := of_eq (StructuralListFieldGraphSyntax.fields_rename w Whole h G (old 2)) (HornBinderRules.under_body 2 hG E)
    have hfields := Derives.impE (.conjL (StructuralListFieldGraphSyntax.law_at (old 2 w) (old 2 Whole) (old 2 h) (old 2 G) (Fin.last m).castSucc (Fin.last (m+1)) (.conjR (.conjR hg2)))) hE
    exact SyntaxMixedImageCodeFields.field_type (old 2 w) (old 2 f) (old 2 c) (old 2 T) (old 2 Whole) (Fin.last m).castSucc (Fin.last (m+1)) ht2
      (within hZ2 (old 2 h) (old 2 f) (Fin.last m).castSucc hh2 hf2 (.conjL hfields)) (.conjR hfields)
  exact .conjI (SyntaxNumerals.range hZ (k+1) w h hw hh) (.conjI (.conjL (.conjR hWhole)) (.conjI (.conjL hG) hv))

private theorem from_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f h c T Base I Name Whole G : Fin m)
    (hi : Derives Γ (input k w f h c T Base I Name))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f c T Base I Name Whole))
    (hg : Derives Γ (StructuralListFieldGraphSyntax.fields w Whole h G)) :
    Derives Γ (produced k w f h c T Base I Name) := by
  have hw := Derives.conjL hi
  have hh := Derives.conjL (.conjR (.conjR hi))
  have hf := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have hWhole := ForcingReflexiveImages.target_type w f c T Base I Name Whole hr
  have himage := canonical_image hZ w f h c T Whole G hw hh hf hWhole hg
  let B := encoded w.castSucc G.castSucc h.castSucc c.castSucc T.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMixedImageCodeExistence.exists_code hZ w G h c T hw himage)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi1 := of_eq (input_rename k w f h c T Base I Name Fin.castSucc) (under hi B)
  have hr1 := of_eq (ForcingReflexiveImages.replacement_rename w f c T Base I Name Whole Fin.castSucc) (under hr B)
  have hg1 := of_eq (StructuralListFieldGraphSyntax.fields_rename w Whole h G Fin.castSucc) (under hg B)
  have hout : Derives Δ (produced k w.castSucc f.castSucc h.castSucc c.castSucc T.castSucc Base.castSucc I.castSucc Name.castSucc) := by
    apply HornBinderRules.intro_many 3 _ (SetLanguage.args3 Whole.castSucc G.castSucc (Fin.last m))
    have hd : Derives Δ (data k w.castSucc f.castSucc h.castSucc c.castSucc T.castSucc Base.castSucc I.castSucc Name.castSucc Whole.castSucc G.castSucc (Fin.last m)) := .conjI hi1 (.conjI hr1 (.conjI hg1 hB))
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) hd
  exact of_eq (produced_rename k w f h c T Base I Name Fin.castSucc).symm hout

private theorem from_replacement {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f h c T Base I Name Whole : Fin m)
    (hi : Derives Γ (input k w f h c T Base I Name))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f c T Base I Name Whole)) :
    Derives Γ (produced k w f h c T Base I Name) := by
  have hw := Derives.conjL hi
  have hh := Derives.conjL (.conjR (.conjR hi))
  let B := (StructuralListFieldGraphSyntax.fields w.castSucc Whole.castSucc h.castSucc (Fin.last m)).conj (.all
    ((StructuralListFieldPairSyntax.graph w.castSucc.castSucc Whole.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (StructuralListFieldGraphFiber.exists_unique hZ w Whole h hw (SyntaxNumerals.range hZ (k+1) w h hw hh))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi1 := of_eq (input_rename k w f h c T Base I Name Fin.castSucc) (under hi B)
  have hr1 := of_eq (ForcingReflexiveImages.replacement_rename w f c T Base I Name Whole Fin.castSucc) (under hr B)
  have hout := from_fields (ZFContext.under hZ B) w.castSucc f.castSucc h.castSucc c.castSucc T.castSucc Base.castSucc I.castSucc Name.castSucc Whole.castSucc (Fin.last m) hi1 hr1 (.conjL hB)
  exact of_eq (produced_rename k w f h c T Base I Name Fin.castSucc).symm hout

/-- Generate the actual original overwrite, complete H-prefix field graph
and actual encoded H argument table inside THREE OBJECT existential binders. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f h c T Base I Name : Fin m) (hi : Derives Γ (input k w f h c T Base I Name)) :
    Derives Γ (produced k w f h c T Base I Name) := by
  let B := ForcingReflexiveImages.replacement w.castSucc f.castSucc c.castSucc T.castSucc Base.castSucc I.castSucc Name.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ForcingReflexiveImages.exists_replacement hZ w f c T Base I Name
    (.conjL hi) (.conjL (.conjR (.conjR (.conjR (.conjR hi))))) (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi1 := of_eq (input_rename k w f h c T Base I Name Fin.castSucc) (under hi B)
  have hout := from_replacement (ZFContext.under hZ B) w.castSucc f.castSucc h.castSucc c.castSucc T.castSucc Base.castSucc I.castSucc Name.castSucc (Fin.last m) hi1 hB
  exact of_eq (produced_rename k w f h c T Base I Name Fin.castSucc).symm hout

theorem target_type {k m} {Γ : Context m} (w f h c T Base I Name Whole G D : Fin m)
    (hd : Derives Γ (data k w f h c T Base I Name Whole G D)) : Derives Γ (termList w h c T D) :=
  SyntaxMixedImageCodeFields.term_list w G h c T D (.conjR (.conjR (.conjR hd)))

/-- At ALL internal indices in the actual H arity, only the name slot k
changes. This is a derived field equation, not an input to produce. -/
theorem field_iff {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f h c T Base I Name Whole G D i q : Fin m)
    (hd : Derives Γ (data k w f h c T Base I Name Whole G D)) (hi : Derives Γ (.mem i h)) :
    Derives Γ ((field w D i q).iff (((Formula.equal i I).conj (.equal q Name)).disj
      ((Formula.equal i I).neg.conj (field w Base i q)))) := by
  have hInput := Derives.conjL hd
  have he := SyntaxMixedImageCodeFields.edges w G h c T D i q (.conjR (.conjR (.conjR hd)))
  have hf := StructuralListFieldGraphSyntax.law_at w Whole h G i q (.conjR (.conjR (.conjL (.conjR (.conjR hd)))))
  have hp : Derives Γ ((field w D i q).iff (field w Whole i q)) := by
    apply Derives.conjI
    · apply Derives.impI
      have hEdge := Derives.impE (add (.conjR he) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))
      exact .conjR (.impE (add (.conjL hf) _) hEdge)
    · apply Derives.impI
      have hEdge := Derives.impE (add (.conjR hf) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))
      exact .conjR (.impE (add (.conjL he) _) hEdge)
  have hin := within hZ h f i (.conjL (.conjR (.conjR hInput))) (.conjL (.conjR (.conjR (.conjR hInput)))) hi
  exact SyntaxTypeLocalTransfer.iff_trans hp (ForcingReflexiveImages.field_iff w f c T Base I Name Whole i q (.conjL (.conjR hd)) hin)

def sentence {m} (k : Nat) (w f h c T Base I Name : Fin m) : Source.Sentence :=
  ((input k w f h c T Base I Name).imp (produced k w f h c T Base I Name)).close
theorem kernel_certificate {m} (k : Nat) (w f h c T Base I Name : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence k w f h c T Base I Name)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) w f h c T Base I Name (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingExistDomainImages
