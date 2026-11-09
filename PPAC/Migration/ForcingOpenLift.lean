import PPAC.Migration.ForcingOpenLayout
import PPAC.Migration.Internal.InstantiateClosedParameterRename
import PPAC.Migration.Internal.SyntaxCodedMixedBinderFields
import PPAC.Migration.Internal.SyntaxFreeShiftGraph

/-! Closed images of the ACTUAL pointwise opening retain their exact codes
under the ORIGINAL mixed binder lift. Reuse closed-parameter rename invariance
and existing coded binder fields; auxiliary maps/head are object witnesses.
These are root-variable equations needed for rebind/open/instantiate transport,
not the outstanding full formula cancellation or normalized forcing MP. -/
namespace PPAC.Migration.ForcingOpenLift
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def mapsData {m} (w z T C U V n : Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w z C U).conj ((SyntaxIdentityMapSyntax.identityMap w T V).conj (SyntaxMixedImageHead.head w C T z n))
private theorem mapsData_rename {m l} (w z T C U V n : Fin m) (r : Fin m → Fin l) :
    (mapsData w z T C U V n).rename r = mapsData (r w) (r z) (r T) (r C) (r U) (r V) (r n) := by
  simp only [mapsData, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxMixedImageHead.head_rename]
private def mapsBody {m} (w z T C : Fin m) : Formula (m+3) :=
  mapsData (old 3 w) (old 3 z) (old 3 T) (old 3 C) (slot 3 0) (slot 3 1) (slot 3 2)
private def maps {m} (w z T C : Fin m) : Formula m := existsMany 3 (mapsBody w z T C)
private theorem maps_rename {m l} (w z T C : Fin m) (r : Fin m → Fin l) :
    (maps w z T C).rename r = maps (r w) (r z) (r T) (r C) := by
  simp only [maps, existsMany_rename, mapsBody, mapsData_rename, lift_old, lift_slot]
private theorem intro_maps {m} {Γ : Context m} (w z T C U V n : Fin m)
    (hu : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w z C U)) (hv : Derives Γ (SyntaxIdentityMapSyntax.identityMap w T V))
    (hn : Derives Γ (SyntaxMixedImageHead.head w C T z n)) : Derives Γ (maps w z T C) := by
  apply HornBinderRules.intro_many 3 _ (Source.SetLanguage.args3 U V n)
  exact of_eq (by simp only [mapsBody, mapsData_rename, assign_old, assign_slot]; rfl) (.conjI hu (.conjI hv hn))

private theorem maps_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z T C : Fin m)
    (hw : Derives Γ (omega w)) (hzN : Derives Γ (.mem z w)) (hT : Derives Γ (.mem T w))
    (hC : Derives Γ (successor C z)) (hz : Derives Γ (empty z)) : Derives Γ (maps w z T C) := by
  let U := SyntaxFreeShiftSyntax.shiftMap w.castSucc z.castSucc C.castSucc (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) (SyntaxFreeShiftGraph.exists_map hZ w z C hw hzN hC)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  let V := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (SyntaxIdentityGraph.exists_map (ZFContext.under hZ U) w.castSucc T.castSucc (under hT U))
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  let N := SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Θ := Context.add N (Context.image Formula.raise Ξ)
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw U) V)
  have hz2 := under (under hzN U) V
  have hT2 := under (under hT U) V
  have hC2 : Derives Ξ (successor C.castSucc.castSucc z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under hC U) V)
  have he2 : Derives Ξ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (under (under hz U) V)
  apply Derives.exE (p := N) (SyntaxMixedImageHead.code_exists (ZFContext.under (ZFContext.under hZ U) V)
    w.castSucc.castSucc z.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc z.castSucc.castSucc hw2 hz2 hT2 hC2 he2)
  have hN : Derives Θ N := .hyp (Or.inl rfl)
  have ho := intro_maps w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    (of_eq (by simp only [Formula.raise, U, SyntaxFreeShiftSyntax.shiftMap_rename]) (under (under hU V) N))
    (of_eq (SyntaxIdentityMapSyntax.identityMap_rename w.castSucc.castSucc T.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc) (under hV N)) hN
  exact of_eq (by simp only [Formula.raise, maps_rename]) ho

/-- Old bound indices shift once; old free indices stay in place. -/
def step {m} (bound : Bool) (i I : Fin m) : Formula m := if bound then successor I i else HornRuleSyntax.truth

theorem step_rename {m l} (bound : Bool) (i I : Fin m) (r : Fin m → Fin l) :
    (step bound i I).rename r = step bound (r i) (r I) := by
  cases bound <;> simp only [step, Bool.false_eq_true, ↓reduceIte, successor_rename, HornRuleSyntax.truth, Formula.rename]

def equation {m} (bound : Bool) (w A f K H i I q v : Fin m) : Formula m :=
  ((Formula.mem (if bound then I else i) (SyntaxTermSyntax.limit bound A f)).conj
    (field w (SyntaxIndexMapSyntax.selectMap bound K H) (if bound then I else i) v)).iff (.equal v q)

theorem equation_rename {m l} (bound : Bool) (w A f K H i I q v : Fin m) (r : Fin m → Fin l) :
    (equation bound w A f K H i I q v).rename r = equation bound (r w) (r A) (r f) (r K) (r H) (r i) (r I) (r q) (r v) := by
  cases bound <;> simp only [equation, Formula.iff, Formula.rename, SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap,
    Bool.false_eq_true, ↓reduceIte, field_rename]

private theorem at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z a f T A C R S K H i I q v U V n : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) (hs : Derives Γ (step bound i I))
    (hc : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w T q))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w z C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w T V))
    (hn : Derives Γ (SyntaxMixedImageHead.head w C T z n)) : Derives Γ (equation bound w A f K H i I q v) := by
  have hclosed := InstantiateClosedParameterRename.closed_iff hZ w U V z T C q v hw hU hV hc
  cases bound with
  | false =>
    exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.free_iff hZ w R S a f z T A C K H U V z n i q v hw hl hU hV hn hi hf) hclosed
  | true =>
    exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.bound_iff hZ w R S a f z T A C K H U V z n I i q v hw hl hU hV hn hi hs hf) hclosed

/-- Actual old name/parameter images retain their EXACT old codes under the
actual mixed lift. All auxiliary maps/head are internally constructed. -/
theorem old_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z a f T A C R S K H i I q v : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) (hs : Derives Γ (step bound i I)) :
    Derives Γ (equation bound w A f K H i I q v) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  have hList : Derives Γ (SyntaxMixedImageCodeSyntax.termList w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S)) := by
    cases bound
    · exact .conjR hLists
    · exact .conjL hLists
  have hterm := SyntaxMixedImageCodeFields.field_type w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S) i q hList hi hf
  have hclosed := InstantiateOperationFrameSyntax.intro_closedParameter w T q z hz hterm
  have hctx := Derives.conjL (.conjR (.conjL hLists))
  have hsucc := Derives.conjR (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl))
  let E := mapsBody w z T C
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ (maps_total hZ w z T C hw (.conjL hctx) (.conjR hctx) hsucc hz)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (equation_rename bound w A f K H i I q v (old 3)).symm
    (at_maps (HornBinderRules.zf_body 3 hZ E) bound (old 3 w) (old 3 z) (old 3 a) (old 3 f) (old 3 T) (old 3 A) (old 3 C)
      (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 i) (old 3 I) (old 3 q) (old 3 v) (slot 3 0) (slot 3 1) (slot 3 2)
      (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw E))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 3)) (HornBinderRules.under_body 3 hl E))
      (of_eq (by simp only [Formula.rename, SyntaxTermSyntax.limit_map]) (HornBinderRules.under_body 3 hi E))
      (of_eq (by cases bound <;> simp only [field_rename, SyntaxIndexMapSyntax.selectMap_map]) (HornBinderRules.under_body 3 hf E))
      (of_eq (step_rename bound i I (old 3)) (HornBinderRules.under_body 3 hs E))
      (of_eq (InstantiateOperationFrameSyntax.closedParameter_rename w T q (old 3)) (HornBinderRules.under_body 3 hclosed E))
      (.conjL hE) (.conjL (.conjR hE)) (.conjR (.conjR hE)))

/-- The lifted bound-zero entry is the internally generated ORIGINAL bvar0
code, in the SAME actual lifted table. -/
def zeroOutput {m} (w z T C K : Fin m) : Formula m := .ex
  ((SyntaxMixedImageHead.head w.castSucc C.castSucc T.castSucc z.castSucc (Fin.last m)).conj
    (field w.castSucc K.castSucc z.castSucc (Fin.last m)))

theorem zeroOutput_rename {m l} (w z T C K : Fin m) (r : Fin m → Fin l) :
    (zeroOutput w z T C K).rename r = zeroOutput (r w) (r z) (r T) (r C) (r K) := by
  simp only [zeroOutput, Formula.rename, SyntaxMixedImageHead.head_rename, field_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_zero {m} {Γ : Context m} (w z T C K n : Fin m)
    (hn : Derives Γ (SyntaxMixedImageHead.head w C T z n)) (hf : Derives Γ (field w K z n)) :
    Derives Γ (zeroOutput w z T C K) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxMixedImageHead.head_rename,
    field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hf)

/-- Generate the real bound-zero code and its actual lifted field internally;
no auxiliary map, head or field witness is supplied. -/
theorem zero_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)) :
    Derives Γ (zeroOutput w z T C K) := by
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  have hctx := Derives.conjL (.conjR (.conjL hLists))
  have hsucc := Derives.conjR (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl))
  let E := mapsBody w z T C
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ (maps_total hZ w z T C hw (.conjL hctx) (.conjR hctx) hsucc hz)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf := SyntaxCodedMixedBinderFields.zero_iff (HornBinderRules.zf_body 3 hZ E)
    (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 f) (old 3 z) (old 3 T) (old 3 A) (old 3 C)
    (old 3 K) (old 3 H) (slot 3 0) (slot 3 1) (old 3 z) (slot 3 2) (slot 3 2)
    (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw E))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 3)) (HornBinderRules.under_body 3 hl E))
    (.conjL hE) (.conjL (.conjR hE)) (.conjR (.conjR hE))
  have hfield := Derives.conjR (Derives.impE (.conjR hf) (Derives.eqRefl (slot 3 2)))
  exact of_eq (zeroOutput_rename w z T C K (old 3)).symm
    (intro_zero (old 3 w) (old 3 z) (old 3 T) (old 3 C) (old 3 K) (slot 3 2) (.conjR (.conjR hE)) hfield)

private def baseInput {m} (w z a f T A C R S K H : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj
    (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H)))

def input {m} (bound : Bool) (w z a f T A C R S K H i I q : Fin m) : Formula m :=
  (baseInput w z a f T A C R S K H).conj
    ((Formula.mem i (SyntaxTermSyntax.limit bound a f)).conj
      ((field w (SyntaxIndexMapSyntax.selectMap bound R S) i q).conj (step bound i I)))

def sentence {m} (bound : Bool) (w z a f T A C R S K H i I q v : Fin m) : Source.Sentence :=
  ((input bound w z a f T A C R S K H i I q).imp (equation bound w A f K H i I q v)).close

/-- Original native-ZF proof, for both source-variable roles and all internal
indices and codes, including nonstandard ones. -/
theorem kernel_certificate {m} (bound : Bool) (w z a f T A C R S K H i I q v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence bound w z a f T A C R S K H i I q v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input bound w z a f T A C R S K H i I q
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hb := Derives.conjL h
  have hi := Derives.conjR h
  exact old_fields (ZFContext.add (ZFContext.source_ZF m) E) bound w z a f T A C R S K H i I q v
    (.conjL hb) (.conjL (.conjR hb)) (.conjL (.conjR (.conjR hb))) (.conjR (.conjR (.conjR hb)))
    (.conjL hi) (.conjL (.conjR hi)) (.conjR (.conjR hi))

def zeroSentence {m} (w z a f T A C R S K H : Fin m) : Source.Sentence :=
  ((baseInput w z a f T A C R S K H).imp (zeroOutput w z T C K)).close

theorem zero_kernel_certificate {m} (w z a f T A C R S K H : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (zeroSentence w z a f T A C R S K H)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := baseInput w z a f T A C R S K H
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact zero_field (ZFContext.add (ZFContext.source_ZF m) E) w z a f T A C R S K H
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))

end PPAC.Migration.ForcingOpenLift

namespace PPAC.Migration.ForcingOpenLift
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- The same existing at_maps proof for ANY actual closed term tables. Earlier
native instances insert legal closed terms, so the original canonical-name
layout is no longer a legitimate premise at the next binder. -/
theorem old_fields_from_lists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w z a f T A C R S K H i I q v : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hLists : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)) (hs : Derives Γ (step bound i I)) :
    Derives Γ (equation bound w A f K H i I q v) := by
  have hList : Derives Γ (SyntaxMixedImageCodeSyntax.termList w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S)) := by
    cases bound
    · exact .conjR hLists
    · exact .conjL hLists
  have hterm := SyntaxMixedImageCodeFields.field_type w (SyntaxTermSyntax.limit bound a f) z T (SyntaxIndexMapSyntax.selectMap bound R S) i q hList hi hf
  have hclosed := InstantiateOperationFrameSyntax.intro_closedParameter w T q z hz hterm
  have hctx := Derives.conjL (.conjR (.conjL hLists))
  have hsucc := Derives.conjR (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl))
  let E := mapsBody w z T C
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ (maps_total hZ w z T C hw (.conjL hctx) (.conjR hctx) hsucc hz)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (equation_rename bound w A f K H i I q v (old 3)).symm
    (at_maps (HornBinderRules.zf_body 3 hZ E) bound (old 3 w) (old 3 z) (old 3 a) (old 3 f) (old 3 T) (old 3 A) (old 3 C)
      (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 i) (old 3 I) (old 3 q) (old 3 v) (slot 3 0) (slot 3 1) (slot 3 2)
      (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw E))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 3)) (HornBinderRules.under_body 3 hl E))
      (of_eq (by simp only [Formula.rename, SyntaxTermSyntax.limit_map]) (HornBinderRules.under_body 3 hi E))
      (of_eq (by cases bound <;> simp only [field_rename, SyntaxIndexMapSyntax.selectMap_map]) (HornBinderRules.under_body 3 hf E))
      (of_eq (step_rename bound i I (old 3)) (HornBinderRules.under_body 3 hs E))
      (of_eq (InstantiateOperationFrameSyntax.closedParameter_rename w T q (old 3)) (HornBinderRules.under_body 3 hclosed E))
      (.conjL hE) (.conjL (.conjR hE)) (.conjR (.conjR hE)))

/-- The actual lifted head is still the original bvar0 code for arbitrary
closed term tables. All auxiliary maps/head remain object witnesses. -/
theorem zero_code_from_lists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hLists : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hq : Derives Γ ((Formula.mem z A).conj (field w K z q))) :
    Derives Γ (SyntaxVariableSyntax.code true w z q) := by
  have hctx := Derives.conjL (Derives.conjR (Derives.conjL hLists))
  have hsucc := Derives.conjR (Derives.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl))
  let E := mapsBody w z T C
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ (maps_total hZ w z T C hw (Derives.conjL hctx) (Derives.conjR hctx) hsucc hz)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ E
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw E)
  have hl3 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 3)) (HornBinderRules.under_body 3 hl E)
  have hq3 : Derives Δ ((Formula.mem (old 3 z) (old 3 A)).conj (field (old 3 w) (old 3 K) (old 3 z) (old 3 q))) :=
    of_eq (by simp only [Formula.rename, field_rename]) (HornBinderRules.under_body 3 hq E)
  have hh := Derives.conjR (Derives.conjR hE)
  have hzero := SyntaxCodedMixedBinderFields.zero_iff hZ3 (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 f) (old 3 z) (old 3 T)
    (old 3 A) (old 3 C) (old 3 K) (old 3 H) (slot 3 0) (slot 3 1) (old 3 z) (slot 3 2) (old 3 q)
    hw3 hl3 (Derives.conjL hE) (Derives.conjL (Derives.conjR hE)) hh
  have heq := Derives.impE (Derives.conjL hzero) hq3
  let V := SyntaxVariableSyntax.code true (old 3 w).castSucc (old 3 z).castSucc (Fin.last (m+3))
  have hn : Derives Δ (V.instantiate (slot 3 2)) := of_eq
    (by simp only [V, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.conjL (Derives.conjR hh))
  have hout : Derives Δ (SyntaxVariableSyntax.code true (old 3 w) (old 3 z) (old 3 q)) := of_eq
    (by simp only [V, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst V (eq_symm heq) hn)
  exact of_eq (SyntaxVariableSyntax.code_rename true w z q (old 3)).symm hout

end PPAC.Migration.ForcingOpenLift
