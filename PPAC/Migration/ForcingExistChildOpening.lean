import PPAC.Migration.ForcingExistChildTerms
import PPAC.Migration.ForcingExistChildCanonical
import PPAC.Migration.ForcingBinderFormula

/-! Original existential child rescoping followed by TWO actual binder
openings versus the existing canonical child environment. Reuse the SAME
original coded lift witnesses and the existing full formula cancellation. -/
namespace PPAC.Migration.ForcingExistChildOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMixedImageCodeSyntax (termList termLists)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def mapsData {m} (w c C d : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w c C (v 0)).conj
    ((SyntaxIdentityMapSyntax.identityMap w d (v 1)).conj (SyntaxMixedImageHead.head w C d (v 2) (v 3)))
private theorem mapsData_rename {m l} (w c C d : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (mapsData w c C d v).rename r = mapsData (r w) (r c) (r C) (r d) (fun i => r (v i)) := by
  simp only [mapsData, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename,
    SyntaxIdentityMapSyntax.identityMap_rename, SyntaxMixedImageHead.head_rename]
private def mapsBody {m} (w c C d : Fin m) : Formula (m+4) :=
  mapsData (old 4 w) (old 4 c) (old 4 C) (old 4 d) (slot 4)
private def maps {m} (w c C d : Fin m) : Formula m := existsMany 4 (mapsBody w c C d)
private theorem maps_rename {m l} (w c C d : Fin m) (r : Fin m → Fin l) :
    (maps w c C d).rename r = maps (r w) (r c) (r C) (r d) := by
  simp only [maps, existsMany_rename, mapsBody, mapsData_rename, lift_old, lift_slot]

/-- READ the original witnesses, not another map/head producer. -/
private theorem maps_from_lifted {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (maps w c C d) := by
  let B := SyntaxCodedMixedBinderSyntax.body w R S a b c d A C K H
  let Δ1 := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hl
  have hB : Derives Δ1 B := .hyp (Or.inl rfl)
  let E := SyntaxMixedImageBinderSyntax.body (old 4 w) (slot 4 0) (slot 4 1)
    (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 A) (old 4 C) (slot 4 2) (slot 4 3)
  let Δ2 := Context.add E (raisedContext 4 Δ1)
  apply HornBinderRules.eliminate_many 4 E _ (.conjL (.conjR hB))
  have hE : Derives Δ2 E := .hyp (Or.inl rfl)
  have hd : Derives Δ2 (mapsData (old 8 w) (old 8 c) (old 8 C) (old 8 d) (slot 4)) :=
    .conjI (.conjL hE) (.conjI (.conjL (.conjR hE)) (.conjL (.conjR (.conjR hE))))
  have ho : Derives Δ2 (maps (old 8 w) (old 8 c) (old 8 C) (old 8 d)) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [mapsBody, mapsData_rename, assign_old, assign_slot]) hd
  exact of_eq (by simp only [maps_rename]; rfl) ho

private theorem closed_at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w R S a b c d A C K H i I t q : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hm : Derives Γ (mapsData w c C d v))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i t))
    (hs : Derives Γ (ForcingOpenLift.step bound i I))
    (ht : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w d t)) :
    Derives Γ (ForcingOpenLift.equation bound w A b K H i I t q) := by
  have he := InstantiateClosedParameterRename.closed_iff hZ w (v 0) (v 1) c d C t q hw (.conjL hm) (.conjL (.conjR hm)) ht
  cases bound
  · exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.free_iff hZ w R S a b c d A C K H (v 0) (v 1) (v 2) (v 3) i t q
        hw hl (.conjL hm) (.conjL (.conjR hm)) (.conjR (.conjR hm)) hi hf) he
  · exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.bound_iff hZ w R S a b c d A C K H (v 0) (v 1) (v 2) (v 3) I i t q
        hw hl (.conjL hm) (.conjL (.conjR hm)) (.conjR (.conjR hm)) hi hs hf) he

theorem closed_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w R S a b c d A C K H i I t q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i t))
    (hs : Derives Γ (ForcingOpenLift.step bound i I))
    (ht : Derives Γ (InstantiateOperationFrameSyntax.closedParameter w d t)) :
    Derives Γ (ForcingOpenLift.equation bound w A b K H i I t q) := by
  let E := mapsBody w c C d
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (maps_from_lifted w R S a b c d A C K H hl)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (ForcingOpenLift.equation_rename bound w A b K H i I t q (old 4)).symm
    (closed_at_maps (HornBinderRules.zf_body 4 hZ E) bound (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b)
      (old 4 c) (old 4 d) (old 4 A) (old 4 C) (old 4 K) (old 4 H) (old 4 i) (old 4 I) (old 4 t) (old 4 q) (slot 4)
      (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H (old 4)) (HornBinderRules.under_body 4 hl E)) hE
      (of_eq (by simp only [Formula.rename, SyntaxTermSyntax.limit_map]) (HornBinderRules.under_body 4 hi E))
      (of_eq (by simp only [field_rename, SyntaxIndexMapSyntax.selectMap_map]) (HornBinderRules.under_body 4 hf E))
      (of_eq (ForcingOpenLift.step_rename bound i I (old 4)) (HornBinderRules.under_body 4 hs E))
      (of_eq (InstantiateOperationFrameSyntax.closedParameter_rename w d t (old 4)) (HornBinderRules.under_body 4 ht E)))

def variableEquation {m} (bound : Bool) (w A b K H i I J q : Fin m) : Formula m :=
  (((Formula.mem (if bound then I else i) (SyntaxTermSyntax.limit bound A b)).conj
    (field w (SyntaxIndexMapSyntax.selectMap bound K H) (if bound then I else i) q)).iff
      (SyntaxVariableSyntax.code true w J q))
private theorem variableEquation_rename {m l} (bound : Bool) (w A b K H i I J q : Fin m) (r : Fin m → Fin l) :
    (variableEquation bound w A b K H i I J q).rename r =
      variableEquation bound (r w) (r A) (r b) (r K) (r H) (r i) (r I) (r J) (r q) := by
  cases bound <;> simp only [variableEquation, Formula.rename, Formula.iff, SyntaxTermSyntax.limit,
    SyntaxIndexMapSyntax.selectMap, field_rename, SyntaxVariableSyntax.code_rename, Bool.false_eq_true, ↓reduceIte]

private theorem variable_at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w R S a b c d A C K H i I t q k J : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hm : Derives Γ (mapsData w c C d v))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i t))
    (hs : Derives Γ (ForcingOpenLift.step bound i I))
    (ht : Derives Γ (SyntaxVariableSyntax.code true w k t)) (hJ : Derives Γ (successor J k)) :
    Derives Γ (variableEquation bound w A b K H i I J q) := by
  have hLists := SyntaxCodedMixedBinderTyping.input_lists w R S a b c d A C K H hl
  have hList : Derives Γ (termList w (SyntaxTermSyntax.limit bound a b) c d (SyntaxIndexMapSyntax.selectMap bound R S)) := by
    cases bound
    · exact .conjR hLists
    · exact .conjL hLists
  have hTerm := SyntaxMixedImageCodeFields.field_type w (SyntaxTermSyntax.limit bound a b) c d
    (SyntaxIndexMapSyntax.selectMap bound R S) i t hList hi hf
  have he := AbstractBinderRename.bound_at hZ w (v 0) (v 1) c d C t q k J hw (.conjL hm) (.conjL (.conjR hm)) hTerm ht hJ
  cases bound
  · exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.free_iff hZ w R S a b c d A C K H (v 0) (v 1) (v 2) (v 3) i t q
        hw hl (.conjL hm) (.conjL (.conjR hm)) (.conjR (.conjR hm)) hi hf) he
  · exact SyntaxTypeLocalTransfer.iff_trans
      (SyntaxCodedMixedBinderFields.bound_iff hZ w R S a b c d A C K H (v 0) (v 1) (v 2) (v 3) I i t q
        hw hl (.conjL hm) (.conjL (.conjR hm)) (.conjR (.conjR hm)) hi hs hf) he

theorem variable_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w R S a b c d A C K H i I t q k J : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hf : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i t))
    (hs : Derives Γ (ForcingOpenLift.step bound i I))
    (ht : Derives Γ (SyntaxVariableSyntax.code true w k t)) (hJ : Derives Γ (successor J k)) :
    Derives Γ (variableEquation bound w A b K H i I J q) := by
  let E := mapsBody w c C d
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (maps_from_lifted w R S a b c d A C K H hl)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (variableEquation_rename bound w A b K H i I J q (old 4)).symm
    (variable_at_maps (HornBinderRules.zf_body 4 hZ E) bound (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b)
      (old 4 c) (old 4 d) (old 4 A) (old 4 C) (old 4 K) (old 4 H) (old 4 i) (old 4 I) (old 4 t) (old 4 q)
      (old 4 k) (old 4 J) (slot 4)
      (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H (old 4)) (HornBinderRules.under_body 4 hl E)) hE
      (of_eq (by simp only [Formula.rename, SyntaxTermSyntax.limit_map]) (HornBinderRules.under_body 4 hi E))
      (of_eq (by simp only [field_rename, SyntaxIndexMapSyntax.selectMap_map]) (HornBinderRules.under_body 4 hf E))
      (of_eq (ForcingOpenLift.step_rename bound i I (old 4)) (HornBinderRules.under_body 4 hs E))
      (of_eq (SyntaxVariableSyntax.code_rename true w k t (old 4)) (HornBinderRules.under_body 4 ht E))
      (of_eq (successor_rename J k (old 4)) (HornBinderRules.under_body 4 hJ E)))

private def zeroEquation {m} (w z A K q : Fin m) : Formula m :=
  ((Formula.mem z A).conj (field w K z q)).iff (SyntaxVariableSyntax.code true w z q)
private theorem zeroEquation_rename {m l} (w z A K q : Fin m) (r : Fin m → Fin l) :
    (zeroEquation w z A K q).rename r = zeroEquation (r w) (r z) (r A) (r K) (r q) := by
  simp only [zeroEquation, Formula.rename, Formula.iff, field_rename, SyntaxVariableSyntax.code_rename]

private theorem zero_at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z R S a b c d A C K H q : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hm : Derives Γ (mapsData w c C d v)) : Derives Γ (zeroEquation w z A K q) := by
  have hh := Derives.conjR (.conjR hm)
  have he := OmegaUniversal.empty_unique (v 2) z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hz
  have hc := SyntaxMixedImageBinderAlign.head_code_subst_index w (v 2) z (v 3) he (.conjL (.conjR hh))
  have hHead : Derives Γ (SyntaxMixedImageHead.head w C d z (v 3)) :=
    .conjI hz (.conjI hc (.conjR (.conjR hh)))
  have hZero := SyntaxCodedMixedBinderFields.zero_iff hZ w R S a b c d A C K H (v 0) (v 1) z (v 3) q
    hw hl (.conjL hm) (.conjL (.conjR hm)) hHead
  have hCode := AbstractBinderRename.code_iff_equal hZ true w z (v 3) q hw hc
  exact SyntaxTypeLocalTransfer.iff_trans hZero (.conjI (.conjR hCode) (.conjL hCode))

theorem zero_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z R S a b c d A C K H q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (zeroEquation w z A K q) := by
  let E := mapsBody w c C d
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (maps_from_lifted w R S a b c d A C K H hl)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (zeroEquation_rename w z A K q (old 4)).symm
    (zero_at_maps (HornBinderRules.zf_body 4 hZ E) (old 4 w) (old 4 z) (old 4 R) (old 4 S)
      (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 A) (old 4 C) (old 4 K) (old 4 H) (old 4 q) (slot 4)
      (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E))
      (of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz E))
      (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H (old 4)) (HornBinderRules.under_body 4 hl E)) hE)

def frame {m} (w z a A B C f T c d R S D Q K H L M E V W head j : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((termLists w a f z T R S).conj
    ((SyntaxTermSyntax.term w z T Q).conj ((StructuralListSyntax.consCode w Q R D).conj
      ((SyntaxCodedMixedBinderSyntax.lifted w D S A f z T B c K H).conj
        ((SyntaxCodedMixedBinderSyntax.lifted w K H B f c T C d L M).conj
          ((SyntaxMixedImageHead.head w c T z head).conj
            ((ForcingReflexiveImages.replacement w f c T S j head E).conj
              (SyntaxCodedMixedBinderSyntax.lifted w R E a f c T A d V W)))))))))

theorem frame_rename {m l} (w z a A B C f T c d R S D Q K H L M E V W head j : Fin m) (r : Fin m → Fin l) :
    (frame w z a A B C f T c d R S D Q K H L M E V W head j).rename r = frame (r w) (r z) (r a) (r A) (r B) (r C) (r f) (r T) (r c) (r d) (r R) (r S) (r D) (r Q) (r K) (r H) (r L) (r M) (r E) (r V) (r W) (r head) (r j) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename,
    SyntaxTermSyntax.term_rename, StructuralListSyntax.consCode_rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    SyntaxMixedImageHead.head_rename, ForcingReflexiveImages.replacement_rename]

def path {m} (w A C f d T L M V W x u y o : Fin m) (v : Fin 12 → Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x u).conj
    ((SyntaxCodedMixedTermSyntax.substituted w L M C f d T u y).conj
      (SyntaxCodedMixedTermSyntax.substituted w V W A f d T x o))
theorem path_rename {m l} (w A C f d T L M V W x u y o : Fin m) (v : Fin 12 → Fin m) (r : Fin m → Fin l) :
    (path w A C f d T L M V W x u y o v).rename r =
      path (r w) (r A) (r C) (r f) (r d) (r T) (r L) (r M) (r V) (r W) (r x) (r u) (r y) (r o) (fun i => r (v i)) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private structure Inputs {m} (Γ : Context m) (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m) (v : Fin 12 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j)
  hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v)
  hp : Derives Γ (path w A C f d T L M V W x u y o v)

private theorem Inputs.in_body {m n} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (J : Formula (m+n)) :
    Inputs (Context.add J (raisedContext n Γ)) (old n w) (old n z) (old n a) (old n A) (old n B) (old n C) (old n f) (old n T) (old n c) (old n d) (old n R) (old n S) (old n D) (old n Q) (old n K) (old n H) (old n L) (old n M) (old n E) (old n V) (old n W) (old n head) (old n j) (old n N) (old n Nraw) (old n x) (old n u) (old n y) (old n o) (fun i => old n (v i)) :=
  ⟨HornBinderRules.zf_body n h.zf J,
    of_eq (frame_rename w z a A B C f T c d R S D Q K H L M E V W head j (old n)) (HornBinderRules.under_body n h.hf J),
    of_eq (ForcingExistChildCode.data_rename w a A B C f j N Nraw v (old n)) (HornBinderRules.under_body n h.hc J),
    of_eq (path_rename w A C f d T L M V W x u y o v (old n)) (HornBinderRules.under_body n h.hp J)⟩

private theorem Inputs.add {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (J : Formula m) : Inputs (Context.add J Γ) w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v :=
  ⟨ZFContext.add h.zf J, SourceLogic.add h.hf J, SourceLogic.add h.hc J, SourceLogic.add h.hp J⟩

private theorem Inputs.hw {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (omega w) := Derives.conjL (h.hf)

private theorem Inputs.zero {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (empty z) := Derives.conjL (Derives.conjR (h.hf))

private theorem Inputs.closed {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (termLists w a f z T R S) := Derives.conjL (Derives.conjR (Derives.conjR (h.hf)))

private theorem Inputs.query {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxTermSyntax.term w z T Q) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))

private theorem Inputs.cons {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (StructuralListSyntax.consCode w Q R D) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))

private theorem Inputs.lift1 {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w D S A f z T B c K H) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))

private theorem Inputs.lift2 {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w K H B f c T C d L M) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))

private theorem Inputs.head {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxMixedImageHead.head w c T z head) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))))

private theorem Inputs.replacement {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (ForcingReflexiveImages.replacement w f c T S j head E) := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))))

private theorem Inputs.canonical {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R E a f c T A d V W) := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))))

private theorem Inputs.first {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (v 10) (v 11) A f C f x u) := .conjL h.hp
private theorem Inputs.second {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w L M C f d T u y) := .conjL (.conjR h.hp)
private theorem Inputs.direct {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V W A f d T x o) := .conjR (.conjR h.hp)

private def eight {m} (x u i pred I II z c : Fin m) : Fin 8 → Fin m :=
  Fin.cases x (Fin.cases u (Fin.cases i (Fin.cases pred (Fin.cases I (Fin.cases II (Fin.cases z (fun _ => c)))))))

private theorem Inputs.point {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (i pred I II : Fin m) :
    Derives Γ (ForcingExistChildTerms.point w a A C f j (eight x u i pred I II z c) v) :=
  ForcingExistChildTerms.at_laws w a A C f j v (eight x u i pred I II z c)
    (ForcingExistChildTerms.from_data h.zf w a A B C f j N Nraw v h.hw h.hc)

private theorem head_point {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (hx : Derives Γ (SyntaxVariableSyntax.code true w z x)) : Derives Γ (.equal y o) := by
  have hr := Derives.impE (.conjL (h.point z z z z)) (.conjI h.zero hx)
  have he := Derives.impE (.conjL hr) h.first
  have hh := Derives.conjL h.hc
  have hz := OmegaUniversal.empty_unique (v 0) z (ZFContext.arithmetic h.zf).base.extensionality (.conjL hh) h.zero
  have hc := SyntaxMixedImageBinderAlign.head_code_subst_index w (v 0) z (v 1) hz (.conjL (.conjR hh))
  have hu := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal h.zf true w z (v 1) u h.hw hc)) he
  have hm := SyntaxCodedMixedBinderTyping.output_lists w K H B f c T C d L M h.lift2
  have hv := SyntaxCodedMixedBinderTyping.output_lists w R E a f c T A d V W h.canonical
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w L M C f d T u y z h.hw hm hu)) h.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w V W A f d T x o z h.hw hv hx)) h.direct
  have hY := Derives.impE (.conjL (zero_fields h.zf w z K H B f c T C d L M y h.hw h.zero h.lift2)) hy
  have hO := Derives.impE (.conjL (zero_fields h.zf w z R E a f c T A d V W o h.hw h.zero h.canonical)) ho
  exact SyntaxVariables.unique h.zf true w z y o h.hw hY hO

private theorem selected_point {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (hx : Derives Γ (SyntaxVariableSyntax.code false w j x)) : Derives Γ (.equal y o) := by
  have hSource := SyntaxCodedMixedTermTyping.source_type w V W A f d T x o h.direct
  have hj := SyntaxTerms.member h.zf false w A f x j h.hw hx hSource
  have hc := Derives.conjR (Derives.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w D S A f z T B c K H h.lift1))
  have hr := Derives.impE (.conjL (.conjR (h.point j z z z)))
    (.conjI hj (.conjI hx (.conjI h.zero hc)))
  have hu := Derives.impE (.conjL hr) h.first
  have hm := SyntaxCodedMixedBinderTyping.output_lists w K H B f c T C d L M h.lift2
  have hv := SyntaxCodedMixedBinderTyping.output_lists w R E a f c T A d V W h.canonical
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w L M C f d T u y c h.hw hm hu)) h.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w V W A f d T x o j h.hw hv hx)) h.direct
  have hCode := Derives.conjL (.conjR h.head)
  have hFirst := Derives.impE (.conjR (zero_fields h.zf w z D S A f z T B c K H head h.hw h.zero h.lift1)) hCode
  have hY := Derives.impE (.conjL (variable_fields h.zf true w K H B f c T C d L M z c head y z c
    h.hw h.lift2 (.conjL hFirst) (.conjR hFirst) hc hCode hc)) hy
  have hE := Derives.impE (.conjR (ForcingReflexiveImages.field_iff w f c T S j head E j head h.replacement hj))
    (.disjL (.conjI (.eqRefl j) (.eqRefl head)))
  have hs : Derives Γ (ForcingOpenLift.step false j j) := .impI (.hyp (Or.inl rfl))
  have hO := Derives.impE (.conjL (variable_fields h.zf false w R E a f c T A d V W j j head o z c
    h.hw h.canonical hj hE hs hCode hc)) ho
  exact SyntaxVariables.unique h.zf true w c y o h.hw hY hO

private theorem away_point {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (hne : Derives Γ (Formula.equal i j).neg) : Derives Γ (.equal y o) := by
  have hSource := SyntaxCodedMixedTermTyping.source_type w V W A f d T x o h.direct
  have hi := SyntaxTerms.member h.zf false w A f x i h.hw hx hSource
  have hiNat := StructuralListTraceOrder.member_member h.zf w i f h.hw (.conjL (.conjR h.closed)) hi
  let J := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc S.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add J (Context.image Formula.raise Γ)
  apply Derives.exE (p := J) (StructuralListFieldValues.exists_value h.zf w S i h.hw hiNat)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have h1 := h.in_body J
  have hx1 := of_eq (SyntaxVariableSyntax.code_rename false w i x Fin.castSucc) (under hx J)
  have hn1 : Derives Δ (Formula.equal i.castSucc j.castSucc).neg := under hne J
  have hi1 : Derives Δ (.mem i.castSucc f.castSucc) := under hi J
  have hTerm := SyntaxMixedImageCodeFields.field_type w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc i.castSucc (Fin.last m)
    (.conjR h1.closed) hi1 (.conjR hJ)
  have hClosed := InstantiateOperationFrameSyntax.intro_closedParameter w.castSucc T.castSucc (Fin.last m) z.castSucc h1.zero hTerm
  have hRule := Derives.impE (.conjL (.conjR (.conjR (h1.point i.castSucc z.castSucc z.castSucc z.castSucc))))
    (.conjI hi1 (.conjI hx1 hn1))
  have hu1 := Derives.impE (.conjL hRule) h1.first
  have hActual := SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h1.lift2
  have hCanon := SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h1.canonical
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h1.zf false
    w.castSucc L.castSucc M.castSucc C.castSucc f.castSucc d.castSucc T.castSucc u.castSucc y.castSucc i.castSucc h1.hw hActual hu1)) h1.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h1.zf false
    w.castSucc V.castSucc W.castSucc A.castSucc f.castSucc d.castSucc T.castSucc x.castSucc o.castSucc i.castSucc h1.hw hCanon hx1)) h1.direct
  have hs : Derives Δ (ForcingOpenLift.step false i.castSucc i.castSucc) := .impI (.hyp (Or.inl rfl))
  have hFirst := Derives.impE (.conjR (closed_fields h1.zf false w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc
    B.castSucc c.castSucc K.castSucc H.castSucc i.castSucc i.castSucc (Fin.last m) (Fin.last m)
    h1.hw h1.lift1 hi1 (.conjR hJ) hs hClosed)) (.eqRefl (Fin.last m))
  have hY := Derives.impE (.conjL (closed_fields h1.zf false w.castSucc K.castSucc H.castSucc B.castSucc f.castSucc c.castSucc T.castSucc
    C.castSucc d.castSucc L.castSucc M.castSucc i.castSucc i.castSucc (Fin.last m) y.castSucc
    h1.hw h1.lift2 (.conjL hFirst) (.conjR hFirst) hs hClosed)) hy
  have hE := Derives.impE (.conjR (ForcingReflexiveImages.field_iff w.castSucc f.castSucc c.castSucc T.castSucc S.castSucc
    j.castSucc head.castSucc E.castSucc i.castSucc (Fin.last m) h1.replacement hi1)) (.disjR (.conjI hn1 (.conjR hJ)))
  have hO := Derives.impE (.conjL (closed_fields h1.zf false w.castSucc R.castSucc E.castSucc a.castSucc f.castSucc c.castSucc T.castSucc
    A.castSucc d.castSucc V.castSucc W.castSucc i.castSucc i.castSucc (Fin.last m) o.castSucc
    h1.hw h1.canonical hi1 hE hs hClosed)) ho
  exact eq_trans hY (eq_symm hO)

private theorem old_point {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) (i pred : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hpNat : Derives Γ (.mem pred w))
    (hs : Derives Γ (successor i pred)) : Derives Γ (.equal y o) := by
  have hSource := SyntaxCodedMixedTermTyping.source_type w V W A f d T x o h.direct
  have hi := SyntaxTerms.member h.zf true w A f x i h.hw hx hSource
  have hA := Derives.conjL (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R E a f c T A d V W h.canonical))
  have hp := SyntaxIndexLiftOrder.predecessor_member h.zf w a A i pred h.hw (.conjL (.conjL h.closed)) hA hi hs
  let IBody := successor (Fin.last m) i.castSucc
  let Δ1 := Context.add IBody (Context.image Formula.raise Γ)
  have hIExists : Derives Γ (.ex IBody) := InsertExistence.exists_insert i i (ZFContext.arithmetic h.zf).base.pairing (ZFContext.arithmetic h.zf).base.union
  apply Derives.exE (p := IBody) hIExists
  have hI : Derives Δ1 IBody := .hyp (Or.inl rfl)
  have h1 := h.in_body IBody
  let IIBody := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ2 := Context.add IIBody (Context.image Formula.raise Δ1)
  have hIIExists : Derives Δ1 (.ex IIBody) := InsertExistence.exists_insert (Fin.last m) (Fin.last m)
    (ZFContext.arithmetic h1.zf).base.pairing (ZFContext.arithmetic h1.zf).base.union
  apply Derives.exE (p := IIBody) hIIExists
  have hII : Derives Δ2 IIBody := .hyp (Or.inl rfl)
  have h2 := h1.in_body IIBody
  have hx2 : Derives Δ2 (SyntaxVariableSyntax.code true (old 2 w) (old 2 i) (old 2 x)) :=
    of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename]; rfl) (under (under hx IBody) IIBody)
  have hs2 : Derives Δ2 (successor (old 2 i) (old 2 pred)) :=
    of_eq (by simp only [Formula.raise, successor_rename]; rfl) (under (under hs IBody) IIBody)
  have hp2 : Derives Δ2 (.mem (old 2 pred) (old 2 a)) := under (under hp IBody) IIBody
  have hi2 : Derives Δ2 (.mem (old 2 i) (old 2 A)) := under (under hi IBody) IIBody
  have hpNat2 : Derives Δ2 (.mem (old 2 pred) (old 2 w)) := under (under hpNat IBody) IIBody
  have hI2 : Derives Δ2 (successor (Fin.last m).castSucc (old 2 i)) :=
    of_eq (by simp only [IBody, Formula.raise, successor_rename]; rfl) (under hI IIBody)
  have hRule := Derives.impE (.conjR (.conjR (.conjR (h2.point (old 2 i) (old 2 pred) (Fin.last m).castSucc (Fin.last (m+1))))))
    (.conjI hp2 (.conjI hi2 (.conjI hs2 (.conjI hI2 (.conjI hII hx2)))))
  have hu2 := Derives.impE (.conjL hRule) h2.first
  let J := (Formula.mem (Fin.last (m+2)) (old 3 w)).conj (field (old 3 w) (old 3 R) (old 3 pred) (Fin.last (m+2)))
  let Δ3 := Context.add J (Context.image Formula.raise Δ2)
  apply Derives.exE (p := J) (StructuralListFieldValues.exists_value h2.zf (old 2 w) (old 2 R) (old 2 pred) h2.hw hpNat2)
  have hJ : Derives Δ3 J := .hyp (Or.inl rfl)
  have h3 := h2.in_body J
  have hx3 := of_eq (SyntaxVariableSyntax.code_rename true (old 2 w) (old 2 i) (old 2 x) Fin.castSucc) (under hx2 J)
  have hu3 := of_eq (SyntaxVariableSyntax.code_rename true (old 2 w) (Fin.last (m+1)) (old 2 u) Fin.castSucc) (under hu2 J)
  have hs3 := of_eq (successor_rename (old 2 i) (old 2 pred) Fin.castSucc) (under hs2 J)
  have hI3 := of_eq (successor_rename (Fin.last m).castSucc (old 2 i) Fin.castSucc) (under hI2 J)
  have hII3 := of_eq (by simp only [IIBody, Formula.raise, successor_rename]; rfl) (under hII J)
  have hp3 : Derives Δ3 (.mem (old 3 pred) (old 3 a)) := under hp2 J
  have hpNat3 : Derives Δ3 (.mem (old 3 pred) (old 3 w)) := under hpNat2 J
  have hClosed := InstantiateOperationFrameSyntax.intro_closedParameter (old 3 w) (old 3 T) (Fin.last (m+2)) (old 3 z) h3.zero
    (SyntaxMixedImageCodeFields.field_type (old 3 w) (old 3 a) (old 3 z) (old 3 T) (old 3 R)
      (old 3 pred) (Fin.last (m+2)) (.conjL h3.closed) hp3 (.conjR hJ))
  have hRlist := Derives.conjL h3.closed
  have hRnat := Derives.conjL (.conjL (.conjR (.conjR hRlist)))
  have hQnat := SyntaxTerms.range h3.zf (old 3 w) (old 3 z) (old 3 T) (old 3 Q) h3.hw h3.query
  have hDfield := StructuralListFieldCons.successor_backward h3.zf (old 3 w) (old 3 Q) (old 3 R) (old 3 D)
    (old 3 pred) (old 3 i) (Fin.last (m+2)) h3.hw hQnat hRnat hpNat3 hs3 h3.cons (.conjR hJ)
  have hActual := SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h3.lift2
  have hCanon := SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h3.canonical
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h3.zf true
    (old 3 w) (old 3 L) (old 3 M) (old 3 C) (old 3 f) (old 3 d) (old 3 T) (old 3 u) (old 3 y)
    (Fin.last (m+1)).castSucc h3.hw hActual hu3)) h3.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h3.zf true
    (old 3 w) (old 3 V) (old 3 W) (old 3 A) (old 3 f) (old 3 d) (old 3 T) (old 3 x) (old 3 o)
    (old 3 i) h3.hw hCanon hx3)) h3.direct
  have hFirst := Derives.impE (.conjR (closed_fields h3.zf true
    (old 3 w) (old 3 D) (old 3 S) (old 3 A) (old 3 f) (old 3 z) (old 3 T) (old 3 B) (old 3 c) (old 3 K) (old 3 H)
    (old 3 i) (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+2))
    h3.hw h3.lift1 (.conjL ho) hDfield hI3 hClosed)) (.eqRefl (Fin.last (m+2)))
  have hY := Derives.impE (.conjL (closed_fields h3.zf true
    (old 3 w) (old 3 K) (old 3 H) (old 3 B) (old 3 f) (old 3 c) (old 3 T) (old 3 C) (old 3 d) (old 3 L) (old 3 M)
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (old 3 y)
    h3.hw h3.lift2 (.conjL hFirst) (.conjR hFirst) hII3 hClosed)) hy
  have hO := Derives.impE (.conjL (closed_fields h3.zf true
    (old 3 w) (old 3 R) (old 3 E) (old 3 a) (old 3 f) (old 3 c) (old 3 T) (old 3 A) (old 3 d) (old 3 V) (old 3 W)
    (old 3 pred) (old 3 i) (Fin.last (m+2)) (old 3 o)
    h3.hw h3.canonical hp3 (.conjR hJ) hs3 hClosed)) ho
  exact eq_trans hY (eq_symm hO)

private theorem excluded {m} {Γ : Context m} (p : Formula m) : Derives Γ (p.disj p.neg) := by
  apply Derives.classical
  let J := (p.disj p.neg).neg
  have hJ : Derives (Context.add J Γ) J := .hyp (Or.inl rfl)
  have hn : Derives (Context.add J Γ) p.neg := .impI (.impE (add hJ p) (.disjL (.hyp (Or.inl rfl))))
  exact .impE hJ (.disjR hn)

private theorem term_from_inputs {m} {Γ : Context m} {w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m} {v : Fin 12 → Fin m}
    (h : Inputs Γ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o v) : Derives Γ (.equal y o) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w V W A f d T x o h.direct
  apply Derives.disjE (.conjR ht)
  · let J := SyntaxTermSyntax.branch true w A x
    let B0 := SyntaxTermSyntax.branchWitness true w A x
    let Δ := Context.add B0 (Context.image Formula.raise (Context.add J Γ))
    apply SyntaxTermSyntax.eliminate_branch true w A x _ (.hyp (Or.inl rfl))
    have hB0 : Derives Δ B0 := .hyp (Or.inl rfl)
    have h1 := (h.add J).in_body B0
    have ht1 := SyntaxCodedMixedTermTyping.source_type w.castSucc V.castSucc W.castSucc A.castSucc f.castSucc d.castSucc T.castSucc x.castSucc o.castSucc h1.direct
    have hi := StructuralListTraceOrder.member_member h1.zf w.castSucc (Fin.last m) A.castSucc h1.hw (.conjL (.conjL ht1)) (.conjL hB0)
    have hs := OmegaStructureAlgebra.decomposition_at w.castSucc (Fin.last m)
      (OmegaStructureInduction.decomposition w.castSucc (ZFContext.separation h1.zf OmegaStructureSyntax.splitMatrix) h1.hw) hi
    apply Derives.disjE hs
    · let Z := empty (Fin.last m)
      have hZ : Derives (Context.add Z Δ) Z := .hyp (Or.inl rfl)
      have h2 := h1.add Z
      have he := OmegaUniversal.empty_unique (Fin.last m) z.castSucc (ZFContext.arithmetic h2.zf).base.extensionality hZ h2.zero
      have hxZ := SyntaxVariableImagePoint.code_subst_index true w.castSucc (Fin.last m) x.castSucc z.castSucc he (add (.conjR hB0) Z)
      exact head_point h2 hxZ
    · let P := OmegaStructureSyntax.predecessor w.castSucc (Fin.last m)
      let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
        (successor (Fin.last m).castSucc (Fin.last (m+1)))
      let Ξ := Context.add B1 (Context.image Formula.raise (Context.add P Δ))
      apply Derives.exE (p := B1) (.hyp (Or.inl rfl))
      have hB1 : Derives Ξ B1 := .hyp (Or.inl rfl)
      have h2 := (h1.add P).in_body B1
      have hx2 := of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) x.castSucc Fin.castSucc)
        (under (add (.conjR hB0) P) B1)
      exact old_point h2 (Fin.last m).castSucc (Fin.last (m+1)) hx2 (.conjL hB1) (.conjR hB1)
  · let J := SyntaxTermSyntax.branch false w f x
    let B0 := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add B0 (Context.image Formula.raise (Context.add J Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hB0 : Derives Δ B0 := .hyp (Or.inl rfl)
    have h1 := (h.add J).in_body B0
    apply Derives.disjE (excluded (Formula.equal (Fin.last m) j.castSucc))
    · let E0 := Formula.equal (Fin.last m) j.castSucc
      have hE0 : Derives (Context.add E0 Δ) E0 := .hyp (Or.inl rfl)
      have hxj := SyntaxVariableImagePoint.code_subst_index false w.castSucc (Fin.last m) x.castSucc j.castSucc hE0 (add (.conjR hB0) E0)
      exact selected_point (h1.add E0) hxj
    · exact away_point (h1.add _) (Fin.last m) (add (.conjR hB0) _) (.hyp (Or.inl rfl))

/-- ALL internal term codes: actual child compilation, TWO actual binder
advances and the actual canonical update/lift agree. No term output answer. -/
theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw x u y o : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hp : Derives Γ (path w A C f d T L M V W x u y o v)) : Derives Γ (.equal y o) :=
  term_from_inputs ⟨hZ, hf, hc, hp⟩


private def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem child_substitution {m} {Γ : Context m} (w a A B C f j N Nraw : Fin m) (v : Fin 12 → Fin m)
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 10) (v 11) A f C f N Nraw) :=
  Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hc)))))))))))

private theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw I J IB IF : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF A f A f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four A A C d) (four f f f T)
      (four IB (v 10) L V) (four IF (v 11) M W)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let G := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 IB) (old 5 IF) (old 5 A) (old 5 f) (old 5 A) (old 5 f) (slot 5 0) (slot 5 1)).conj
    ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 (v 10)) (old 5 (v 11)) (old 5 A) (old 5 f) (old 5 C) (old 5 f) (slot 5 1) (slot 5 2)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 L) (old 5 M) (old 5 C) (old 5 f) (old 5 d) (old 5 T) (slot 5 2) (slot 5 3)).conj
        (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 V) (old 5 W) (old 5 A) (old 5 f) (old 5 d) (old 5 T) (slot 5 0) (slot 5 4))))
  let Δ := Context.add G (raisedContext 5 Γ)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hf5 := of_eq (frame_rename w z a A B C f T c d R S D Q K H L M E V W head j (old 5)) (HornBinderRules.under_body 5 hf G)
  have hc5 := of_eq (ForcingExistChildCode.data_rename w a A B C f j N Nraw v (old 5)) (HornBinderRules.under_body 5 hc G)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I (old 5)) (HornBinderRules.under_body 5 hI G)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ G)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF A f A f (old 5)) (HornBinderRules.under_body 5 he G)
  have hZ5 := HornBinderRules.zf_body 5 hZ G
  have hId := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 A) (old 5 f)
    (old 5 I) (old 5 J) (old 5 IB) (old 5 IF) (slot 5 0) (slot 5 1) (.conjL hf5) hI5 hJ5 he5 (.conjL hG)
  have hFirst := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 (v 10)) (old 5 (v 11))
    (old 5 A) (old 5 f) (old 5 C) (old 5 f) (slot 5 1) (slot 5 2) (slot 5 0) (eq_symm hId) (.conjL (.conjR hG))
  exact term hZ5 (old 5 w) (old 5 z) (old 5 a) (old 5 A) (old 5 B) (old 5 C) (old 5 f) (old 5 T) (old 5 c) (old 5 d) (old 5 R) (old 5 S) (old 5 D) (old 5 Q) (old 5 K) (old 5 H) (old 5 L) (old 5 M) (old 5 E) (old 5 V) (old 5 W) (old 5 head) (old 5 j) (old 5 N) (old 5 Nraw) (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (v i))
    hf5 hc5 (.conjI hFirst (.conjI (.conjL (.conjR (.conjR hG))) (.conjR (.conjR (.conjR hG)))))

private theorem at_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y O I J IB IF : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N O))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF A f A f)) : Derives Γ (.equal Y O) := by
  have hw := Derives.conjL hf
  have hChild := child_substitution w a A B C f j N Nraw v hc
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 10) (v 11) A f C f N Nraw hw hChild
  have hId := SyntaxIdentityInduction.reflexive hZ w I J A f N hw hI hJ hType
  have hIdMixed := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J IB IF A f A f N N hw he)) hId
  have hd := term_diagram hZ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw I J IB IF v hf hc hI hJ he
  exact ForcingFormulaInduction.cancel hZ w (four A A C d) (four f f f T)
    (four IB (v 10) L V) (four IF (v 11) M W) N N Nraw Y O hw hd hIdMixed hChild hOpen hDirect

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y O I J : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N O))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J)) : Derives Γ (.equal Y O) := by
  let G := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 A) (old 2 f) (old 2 A) (old 2 f)
  let Δ := Context.add G (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 G _ (IndexTermImageEnvironment.exists_environment hZ w I J A f A f (.conjL hf)
    (SyntaxIdentityCode.map_code w A I hI) (SyntaxIdentityCode.map_code w f J hJ))
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact at_identity (HornBinderRules.zf_body 2 hZ G) (old 2 w) (old 2 z) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 T) (old 2 c) (old 2 d) (old 2 R) (old 2 S) (old 2 D) (old 2 Q) (old 2 K) (old 2 H) (old 2 L) (old 2 M) (old 2 E) (old 2 V) (old 2 W) (old 2 head) (old 2 j) (old 2 N) (old 2 Nraw) (old 2 Y) (old 2 O) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (fun i => old 2 (v i))
    (of_eq (frame_rename w z a A B C f T c d R S D Q K H L M E V W head j (old 2)) (HornBinderRules.under_body 2 hf G))
    (of_eq (ForcingExistChildCode.data_rename w a A B C f j N Nraw v (old 2)) (HornBinderRules.under_body 2 hc G))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M C f d T Nraw Y (old 2)) (HornBinderRules.under_body 2 hOpen G))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V W A f d T N O (old 2)) (HornBinderRules.under_body 2 hDirect G))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I (old 2)) (HornBinderRules.under_body 2 hI G))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ G)) hG

/-- Actual raw child + TWO actual openings = actual canonical child output,
for ALL internal formulas. Existing full formula induction is reused unchanged. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y O : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N O)) : Derives Γ (.equal Y O) := by
  have hw := Derives.conjL hf
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 10) (v 11) A f C f N Nraw hw (child_substitution w a A B C f j N Nraw v hc)
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w N A f hType)
  let IBody := SyntaxIdentityMapSyntax.identityCode w.castSucc A.castSucc (Fin.last m)
  let Δ1 := Context.add IBody (Context.image Formula.raise Γ)
  apply Derives.exE (p := IBody) (SyntaxIdentityCode.exists_code hZ w A hw (.conjL hCtx))
  have hI : Derives Δ1 IBody := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ IBody
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw IBody)
  have hfNat1 : Derives Δ1 (.mem f.castSucc w.castSucc) := under (.conjR hCtx) IBody
  let JBody := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Δ2 := Context.add JBody (Context.image Formula.raise Δ1)
  apply Derives.exE (p := JBody) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 hfNat1)
  have hJ : Derives Δ2 JBody := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 JBody
  have hf2 : Derives Δ2 (frame (old 2 w) (old 2 z) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 T) (old 2 c) (old 2 d) (old 2 R) (old 2 S) (old 2 D) (old 2 Q) (old 2 K) (old 2 H) (old 2 L) (old 2 M) (old 2 E) (old 2 V) (old 2 W) (old 2 head) (old 2 j)) := of_eq
    (by simp only [Formula.raise, frame_rename]; rfl) (under (under hf IBody) JBody)
  have hc2 : Derives Δ2 (ForcingExistChildCode.data (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f)
      (old 2 j) (old 2 N) (old 2 Nraw) (fun i => old 2 (v i))) :=
    of_eq (by simp only [Formula.raise, ForcingExistChildCode.data_rename]; rfl) (under (under hc IBody) JBody)
  have ho2 : Derives Δ2 (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 L) (old 2 M) (old 2 C) (old 2 f) (old 2 d) (old 2 T) (old 2 Nraw) (old 2 Y)) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (under (under hOpen IBody) JBody)
  have hd2 : Derives Δ2 (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 V) (old 2 W) (old 2 A) (old 2 f) (old 2 d) (old 2 T) (old 2 N) (old 2 O)) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (under (under hDirect IBody) JBody)
  have hI2 := of_eq (by simp only [IBody, Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]; rfl) (under hI JBody)
  exact at_codes hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 T) (old 2 c) (old 2 d) (old 2 R) (old 2 S) (old 2 D) (old 2 Q) (old 2 K) (old 2 H) (old 2 L) (old 2 M) (old 2 E) (old 2 V) (old 2 W) (old 2 head) (old 2 j) (old 2 N) (old 2 Nraw) (old 2 Y) (old 2 O) (Fin.last m).castSucc (Fin.last (m+1))
    (fun i => old 2 (v i)) hf2 hc2 ho2 hd2 hI2 hJ

private theorem output_subst {m} {Γ : Context m} (w R S a b c d n q r : Fin m)
    (he : Derives Γ (.equal q r)) (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n r) := by
  let P := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq))

/-- Produce the canonical query at the SAME actual raw output. The direct
candidate and four auxiliary identity witnesses are object-generated. -/
theorem query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y : Fin m) (v : Fin 12 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.data w a A B C f j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N Y) := by
  have hw := Derives.conjL hf
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 10) (v 11) A f C f N Nraw hw (child_substitution w a A B C f j N Nraw v hc)
  have hCanon := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))
  have hLists := SyntaxCodedMixedBinderTyping.output_lists w R E a f c T A d V W hCanon
  let G := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc V.castSucc W.castSucc A.castSucc f.castSucc d.castSucc T.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w V W A f d T N hw (.conjI hType hLists))
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ G
  have hf1 := of_eq (frame_rename w z a A B C f T c d R S D Q K H L M E V W head j Fin.castSucc) (under hf G)
  have hc1 := of_eq (ForcingExistChildCode.data_rename w a A B C f j N Nraw v Fin.castSucc) (under hc G)
  have ho1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M C f d T Nraw Y Fin.castSucc) (under hOpen G)
  have heq := formula hZ1 w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc T.castSucc c.castSucc d.castSucc R.castSucc S.castSucc D.castSucc Q.castSucc K.castSucc H.castSucc L.castSucc M.castSucc E.castSucc V.castSucc W.castSucc head.castSucc j.castSucc N.castSucc Nraw.castSucc Y.castSucc (Fin.last m)
    (fun i => (v i).castSucc) hf1 hc1 ho1 hG
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V W A f d T N Y Fin.castSucc).symm
    (output_subst _ _ _ _ _ _ _ _ _ _ (eq_symm heq) hG)

/-- Eliminate the ORIGINAL twelve compiler witnesses, preserving the exact
actual raw child query and generating the canonical query at its output. -/
theorem from_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y : Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nraw))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N Y) := by
  let G := ForcingExistChildCode.body w a A B C f j N Nraw
  let Δ := Context.add G (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 G _ hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hq := query (HornBinderRules.zf_body 12 hZ G) (old 12 w) (old 12 z) (old 12 a) (old 12 A) (old 12 B) (old 12 C) (old 12 f) (old 12 T) (old 12 c) (old 12 d) (old 12 R) (old 12 S) (old 12 D) (old 12 Q) (old 12 K) (old 12 H) (old 12 L) (old 12 M) (old 12 E) (old 12 V) (old 12 W) (old 12 head) (old 12 j) (old 12 N) (old 12 Nraw) (old 12 Y) (slot 12)
    (of_eq (frame_rename w z a A B C f T c d R S D Q K H L M E V W head j (old 12)) (HornBinderRules.under_body 12 hf G)) hG
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M C f d T Nraw Y (old 12)) (HornBinderRules.under_body 12 hOpen G))
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V W A f d T N Y (old 12)).symm hq

def input {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y : Fin m) : Formula m :=
  (frame w z a A B C f T c d R S D Q K H L M E V W head j).conj ((ForcingExistChildCode.compiled w a A B C f j N Nraw).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
def sentence {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y : Fin m) : Source.Sentence :=
  ((input w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y).imp (SyntaxMixedFormulaJudgmentSyntax.substituted w V W A f d T N Y)).close

theorem kernel_certificate {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) G) w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y
    (.conjL hG) (.conjL (.conjR hG)) (.conjR (.conjR hG))


/-- The SAME actual raw child at two outer-condition updates has the SAME
actual output after TWO openings. Consume the existing canonical whole-formula
independence, not a field/equality/guard-truth answer. -/
theorem compare_prefixes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1 : Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hg : Derives Γ (frame w z a A B C f T c d R S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 head j))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nraw))
    (hd : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 C f d T Nraw1 Y1))
    (hp : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j p S))
    (hq : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j q S1)) : Derives Γ (.equal Y Y1) := by
  have hu := from_compiled hZ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y hf hc hy
  have hv := from_compiled hZ w z a A B C f T c d R S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 head j N Nraw1 Y1 hg hd hy1
  have hE := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))
  have hC := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))
  have hE1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hg)))))))))
  have hC1 := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hg)))))))))
  exact ForcingExistChildCanonical.formula hZ w a A c d f T R Base j p q S S1 head N
    (four E V W Y) (four E1 V1 W1 Y1) (.conjL hf) hp hq
    (.conjI hE (.conjI hC hu)) (.conjI hE1 (.conjI hC1 hv))

theorem compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1 : Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j))
    (hg : Derives Γ (frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nraw))
    (hd : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 C f d T Nraw1 Y1))
    (hp : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j p S))
    (hq : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j q S1)) : Derives Γ (.equal Y Y1) :=
  compare_prefixes hZ w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 D Q K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1
    hf hg hc hd hy hy1 hp hq

def compareInput {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1 : Fin m) : Formula m :=
  (frame w z a A B C f T c d R S D Q K H L M E V W head j).conj ((frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j).conj
    ((ForcingExistChildCode.compiled w a A B C f j N Nraw).conj
      ((ForcingExistChildCode.compiled w a A B C f j N Nraw1).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w L M C f d T Nraw Y).conj
          ((SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 C f d T Nraw1 Y1).conj
            ((ForcingReflexiveImages.replacement w f c T Base j p S).conj
              (ForcingReflexiveImages.replacement w f c T Base j q S1)))))))
def compareSentence {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1 : Fin m) : Source.Sentence :=
  ((compareInput w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1).imp (.equal Y Y1)).close

theorem compare_kernel_certificate {m} (w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1 : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (compareSentence w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := compareInput w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact compare (ZFContext.add (ZFContext.source_ZF m) G) w z a A B C f T c d R S D Q K H L M E V W head j N Nraw Y Base p q S1 K1 H1 L1 M1 E1 V1 W1 Nraw1 Y1
    (Derives.conjL (hG))
    (Derives.conjL (Derives.conjR (hG)))
    (Derives.conjL (Derives.conjR (Derives.conjR (hG))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))))

end PPAC.Migration.ForcingExistChildOpening
