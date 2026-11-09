import PPAC.Migration.ForcingRelationSource
import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.Internal.TermImageQuotationFields
import PPAC.Migration.Internal.OriginalQuotationVariableFields

/-! Actual argument images for the SAME bare source relation R. These are
TWO existing single-slot replacements, not a new table/graph constructor.
The original forcing table is retained: only this NEW bare-R table reads
slots k,k+1 as the left/right relation arguments. Target scopes/codes remain
arbitrary internal values, with no standardness or source truth premise. -/
namespace PPAC.Migration.ForcingRelationImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMixedImageCodeSyntax (termList termList_rename)
open ForcingReflexiveImages (replacement replacement_rename)
set_option maxRecDepth 32768
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature
attribute [local irreducible] NaturalRecursionSyntax.matrix

def data {m} (k : Nat) (w f c d S L R i j M D : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral k i).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj
    ((replacement w f c d S i L M).conj (replacement w f c d M j R D)))

theorem data_rename {m l} (k : Nat) (w f c d S L R i j M D : Fin m) (ρ : Fin m → Fin l) :
    (data k w f c d S L R i j M D).rename ρ = data k (ρ w) (ρ f) (ρ c) (ρ d) (ρ S) (ρ L) (ρ R) (ρ i) (ρ j) (ρ M) (ρ D) := by
  simp only [data, Formula.rename, SyntaxNumeralSyntax.numeral_rename, replacement_rename]

def body {m} (k : Nat) (w f c d S L R : Fin m) : Formula (m+4) :=
  data k (old 4 w) (old 4 f) (old 4 c) (old 4 d) (old 4 S) (old 4 L) (old 4 R) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def produced {m} (k : Nat) (w f c d S L R : Fin m) : Formula m := existsMany 4 (body k w f c d S L R)

theorem produced_rename {m l} (k : Nat) (w f c d S L R : Fin m) (ρ : Fin m → Fin l) :
    (produced k w f c d S L R).rename ρ = produced k (ρ w) (ρ f) (ρ c) (ρ d) (ρ S) (ρ L) (ρ R) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_slot {m} {Γ : Context m} (w f c d S i L M q : Fin m)
    (hr : Derives Γ (replacement w f c d S i L M)) (hi : Derives Γ (.mem i f)) :
    Derives Γ ((field w M i q).iff (.equal q L)) := by
  have he := ForcingReflexiveImages.field_iff w f c d S i L M i q hr hi
  apply Derives.conjI
  · apply Derives.impI
    let E := field w M i q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have cases := Derives.impE (add (Derives.conjL he) E) hE
    apply Derives.disjE cases
    · exact Derives.conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (Derives.conjL (.hyp (Or.inl rfl))) (.eqRefl i))
  · apply Derives.impI
    let E := Formula.equal q L
    exact Derives.impE (add (Derives.conjR he) E)
      (Derives.disjL (Derives.conjI (.eqRefl i) (.hyp (Or.inl rfl))))

private theorem unchanged {m} {Γ : Context m} (w f c d S i L M x q : Fin m)
    (hr : Derives Γ (replacement w f c d S i L M)) (hx : Derives Γ (.mem x f))
    (hxi : Derives Γ (Formula.equal x i).neg) : Derives Γ ((field w M x q).iff (field w S x q)) := by
  have he := ForcingReflexiveImages.field_iff w f c d S i L M x q hr hx
  apply Derives.conjI
  · apply Derives.impI
    let E := field w M x q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have cases := Derives.impE (add (Derives.conjL he) E) hE
    apply Derives.disjE cases
    · exact .botE (.impE (add (add hxi E) _) (Derives.conjL (.hyp (Or.inl rfl))))
    · exact Derives.conjR (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := field w S x q
    exact Derives.impE (add (Derives.conjR he) E)
      (Derives.disjR (Derives.conjI (add hxi E) (.hyp (Or.inl rfl))))

theorem target_type {m} {Γ : Context m} (k : Nat) (w f c d S L R i j M D : Fin m)
    (hd : Derives Γ (data k w f c d S L R i j M D)) : Derives Γ (termList w f c d D) :=
  ForcingReflexiveImages.target_type w f c d M j R D (Derives.conjR (Derives.conjR (Derives.conjR hd)))

/-- Exact right argument, with no requested output equality assumed. -/
theorem right_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w f c d S L R i j M D q : Fin m)
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hd : Derives Γ (data k w f c d S L R i j M D)) :
    Derives Γ ((field w D j q).iff (.equal q R)) :=
  at_slot w f c d M j R D q (Derives.conjR (Derives.conjR (Derives.conjR hd)))
    (SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last (k+1)) f j hf (Derives.conjL (Derives.conjR hd)))

/-- Exact left argument, retained through the second update. -/
theorem left_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w f c d S L R i j M D q : Fin m)
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hd : Derives Γ (data k w f c d S L R i j M D)) :
    Derives Γ ((field w D i q).iff (.equal q L)) := by
  have hi := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last k).castSucc f i hf (Derives.conjL hd)
  have hneq := SyntaxNumerals.different hZ k (k+1) (Nat.ne_of_lt (Nat.lt_succ_self k)) i j (Derives.conjL hd) (Derives.conjL (Derives.conjR hd))
  exact SyntaxTypeLocalTransfer.iff_trans
    (unchanged w f c d M j R D i q (Derives.conjR (Derives.conjR (Derives.conjR hd))) hi hneq)
    (at_slot w f c d S i L M q (Derives.conjL (Derives.conjR (Derives.conjR hd))) hi)

/-- All INTERNAL indices outside the two argument slots keep the old value. -/
theorem outside {m} {Γ : Context m} (k : Nat) (w f c d S L R i j M D x q : Fin m)
    (hd : Derives Γ (data k w f c d S L R i j M D)) (hx : Derives Γ (.mem x f))
    (hxi : Derives Γ (Formula.equal x i).neg) (hxj : Derives Γ (Formula.equal x j).neg) :
    Derives Γ ((field w D x q).iff (field w S x q)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (unchanged w f c d M j R D x q (Derives.conjR (Derives.conjR (Derives.conjR hd))) hx hxj)
    (unchanged w f c d S i L M x q (Derives.conjL (Derives.conjR (Derives.conjR hd))) hx hxi)

/-- Every original parameter slot is retained, even when the target scopes
and term codes are internally nonstandard. -/
theorem parameter_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (p : Fin k)
    (w f c d S L R i j M D x q : Fin m)
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hd : Derives Γ (data k w f c d S L R i j M D))
    (hx : Derives Γ (SyntaxNumeralSyntax.numeral p.val x)) : Derives Γ ((field w D x q).iff (field w S x q)) := by
  exact outside k w f c d S L R i j M D x q hd
    (SyntaxNumeralMembers.index_member hZ (k+2) p.castSucc.castSucc f x hf hx)
    (SyntaxNumerals.different hZ p.val k (Nat.ne_of_lt p.isLt) x i hx (Derives.conjL hd))
    (SyntaxNumerals.different hZ p.val (k+1) (Nat.ne_of_lt (Nat.lt_trans p.isLt (Nat.lt_succ_self k))) x j hx (Derives.conjL (Derives.conjR hd)))

private structure Inputs {m} (Γ : Context m) (w f c d S L R : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  table : Derives Γ (termList w f c d S)
  left : Derives Γ (SyntaxTermSyntax.term w c d L)
  right : Derives Γ (SyntaxTermSyntax.term w c d R)

private theorem Inputs.in_body {m} {Γ : Context m} {w f c d S L R : Fin m}
    (h : Inputs Γ w f c d S L R) (n : Nat) (E : Formula (m+n)) :
    Inputs (Context.add E (raisedContext n Γ)) (old n w) (old n f) (old n c) (old n d)
      (old n S) (old n L) (old n R) := {
  zf := HornBinderRules.zf_body n h.zf E
  omega := of_eq (omega_rename w (old n)) (HornBinderRules.under_body n h.omega E)
  table := of_eq (termList_rename w f c d S (old n)) (HornBinderRules.under_body n h.table E)
  left := of_eq (SyntaxTermSyntax.term_rename w c d L (old n)) (HornBinderRules.under_body n h.left E)
  right := of_eq (SyntaxTermSyntax.term_rename w c d R (old n)) (HornBinderRules.under_body n h.right E)
}

private theorem at_numbers {m} {Γ : Context m} (k : Nat) (w f c d S L R i j : Fin m)
    (h : Inputs Γ w f c d S L R)
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)) :
    Derives Γ (produced k w f c d S L R) := by
  let E := replacement (old 1 w) (old 1 f) (old 1 c) (old 1 d) (old 1 S) (old 1 i) (old 1 L) (slot 1 0)
  let Δ := Context.add E (raisedContext 1 Γ)
  have hex := ForcingReflexiveImages.exists_replacement h.zf w f c d S i L h.omega h.table h.left
  apply HornBinderRules.eliminate_many 1 E _ hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body 1 E
  have hi1 := of_eq (SyntaxNumeralSyntax.numeral_rename k i (old 1)) (HornBinderRules.under_body 1 hi E)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j (old 1)) (HornBinderRules.under_body 1 hj E)
  have hM := ForcingReflexiveImages.target_type (old 1 w) (old 1 f) (old 1 c) (old 1 d)
    (old 1 S) (old 1 i) (old 1 L) (slot 1 0) hE
  have hey := ForcingReflexiveImages.exists_replacement h1.zf (old 1 w) (old 1 f) (old 1 c) (old 1 d)
    (slot 1 0) (old 1 j) (old 1 R) h1.omega hM h1.right
  let F := replacement (old 2 w) (old 2 f) (old 2 c) (old 2 d) (slot 2 0) (old 2 j) (old 2 R) (slot 2 1)
  let Ξ := Context.add F (raisedContext 1 Δ)
  apply HornBinderRules.eliminate_many 1 F _ hey
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hE2 : Derives Ξ (replacement (old 2 w) (old 2 f) (old 2 c) (old 2 d)
      (old 2 S) (old 2 i) (old 2 L) (slot 2 0)) :=
    of_eq (replacement_rename (old 1 w) (old 1 f) (old 1 c) (old 1 d)
      (old 1 S) (old 1 i) (old 1 L) (slot 1 0) (old 1)) (HornBinderRules.under_body 1 hE F)
  have hi2 : Derives Ξ (SyntaxNumeralSyntax.numeral k (old 2 i)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename k (old 1 i) (old 1)) (HornBinderRules.under_body 1 hi1 F)
  have hj2 : Derives Ξ (SyntaxNumeralSyntax.numeral (k+1) (old 2 j)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) (old 1 j) (old 1)) (HornBinderRules.under_body 1 hj1 F)
  have hData : Derives Ξ (data k (old 2 w) (old 2 f) (old 2 c) (old 2 d) (old 2 S)
      (old 2 L) (old 2 R) (old 2 i) (old 2 j) (slot 2 0) (slot 2 1)) :=
    .conjI hi2 (.conjI hj2 (.conjI hE2 hF))
  have hout : Derives Ξ (produced k (old 2 w) (old 2 f) (old 2 c) (old 2 d) (old 2 S) (old 2 L) (old 2 R)) := by
    let values : Fin 4 → Fin (m+2) := Fin.cases (old 2 i) (Fin.cases (old 2 j) (Fin.cases (slot 2 0) (fun _ => slot 2 1)))
    apply HornBinderRules.intro_many 4 _ values
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (by simp only [produced_rename] <;> rfl) hout

/-- Generate both index numerals and both replacement tables INTERNALLY.
No index, table, requested equality, or relation truth is an input. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w f c d S L R : Fin m)
    (hw : Derives Γ (omega w)) (hS : Derives Γ (termList w f c d S))
    (hL : Derives Γ (SyntaxTermSyntax.term w c d L)) (hR : Derives Γ (SyntaxTermSyntax.term w c d R)) :
    Derives Γ (produced k w f c d S L R) := by
  let h : Inputs Γ w f c d S L R := ⟨hZ,hw,hS,hL,hR⟩
  let E := (Formula.mem (slot 1 0) (old 1 w)).conj (SyntaxNumeralSyntax.numeral k (slot 1 0))
  let Δ := Context.add E (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 E _ (SyntaxNumerals.exists_numeral hZ k w hw)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body 1 E
  let F := (Formula.mem (slot 2 1) (old 2 w)).conj (SyntaxNumeralSyntax.numeral (k+1) (slot 2 1))
  let Ξ := Context.add F (raisedContext 1 Δ)
  apply HornBinderRules.eliminate_many 1 F _ (SyntaxNumerals.exists_numeral h1.zf (k+1) (old 1 w) h1.omega)
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have h2 := h1.in_body 1 F
  have hi2 : Derives Ξ (SyntaxNumeralSyntax.numeral k (slot 2 0)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename k (slot 1 0) (old 1)) (HornBinderRules.under_body 1 (Derives.conjR hE) F)
  have hout := at_numbers k (old 2 w) (old 2 f) (old 2 c) (old 2 d) (old 2 S)
    (old 2 L) (old 2 R) (slot 2 0) (slot 2 1) h2 hi2 (Derives.conjR hF)
  exact of_eq (by simp only [produced_rename] <;> rfl) hout

def input {m} (w f c d S L R : Fin m) : Formula m :=
  (omega w).conj ((termList w f c d S).conj
    ((SyntaxTermSyntax.term w c d L).conj (SyntaxTermSyntax.term w c d R)))

def sentence {m} (k : Nat) (w f c d S L R : Fin m) : Source.Sentence :=
  ((input w f c d S L R).imp (produced k w f c d S L R)).close

theorem kernel_certificate {m} (k : Nat) (w f c d S L R : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence k w f c d S L R)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w f c d S L R
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) k w f c d S L R
    (Derives.conjL h) (Derives.conjL (Derives.conjR h))
    (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjR (Derives.conjR (Derives.conjR h)))

/-- Read an ACTUAL native map field by its original source-variable index.
The native term-image quotation and original list-field theorem are reused. -/
theorem mapped_field {n m} {Γ : Context m} {tb tf : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (ρ : Fin (n+2) → PureSyntaxQuotation.Tm tb tf) (j : Fin (n+2))
    (w z f A T B F I q : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap
      (ForcingRelationSource.mapping ρ) w z f A T B F))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val I)) :
    Derives Γ ((field w F I q).iff (PureQuotationSyntax.term (ρ j) w q)) := by
  let σ : NativeSubstitutionSyntax.Mapping (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)) tb tf := ForcingRelationSource.mapping ρ
  let v := YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable j
  have hIndex : v.index = j.val := ProjectNativeRenaming.variable_index (fun _ : Fin 1 => j)
    (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hi' : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.entryIndex σ v).val I) :=
    of_eq (congrArg (fun k => SyntaxNumeralSyntax.numeral k I) hIndex).symm hi
  have hImages := Derives.conjR (Derives.conjL he)
  have hp := TermImageQuotationFields.field_at hZ (NativeSubstitutionImages.images _ σ) w F
    (NativeSubstitutionImages.entryIndex σ v) I q hw hImages hi'
  exact of_eq (by simp only [NativeSubstitutionImages.get_image, σ, v, ForcingRelationSource.mapping_at]) hp

/-- The real first mixed term-query gives the literal mapped-variable
quotation. No image-field or output-code answer is supplied. -/
theorem mapped_variable {n m} {Γ : Context m} {tb tf : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (ρ : Fin (n+2) → PureSyntaxQuotation.Tm tb tf) (j : Fin (n+2))
    (w z f A T B F I x u : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap
      (ForcingRelationSource.mapping ρ) w z f A T B F))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val I))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w I x))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B F z f A T x u)) :
    Derives Γ (PureQuotationSyntax.term (ρ j) w u) := by
  have hAt := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B F z f A T x u I
    hw (Derives.conjR he) hx)) hq
  exact Derives.impE (Derives.conjL (mapped_field hZ ρ j w z f A T B F I u hw he hi)) (Derives.conjR hAt)

/-- Left-argument part of the ACTUAL guard two-path term diagram.
All three queries are real coded operations; the target table and guard
singleton are the same generated values, not requested equality answers. -/
theorem guard_left_path {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 x u v y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap (ForcingRelationSource.guardMap k) w z f t f B F))
    (hd : Derives Γ (data k w f c d S L R i j M D))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => L) V))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w i x))
    (h0 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B F z f t f x u))
    (h1 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V K t f c d u v))
    (h2 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B0 D z f c d x y)) :
    Derives Γ (.equal v y) := by
  have hu := mapped_variable hZ
    (ForcingRelationSource.arguments (.bvar .here) (.fvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (Fin.last (k+1)))))
    (Fin.last k).castSucc w z f t f B F i x u hw he (Derives.conjL hd) hx h0
  have hu' : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 0 [PureSyntaxQuotation.Original.leaf 0]) w u) :=
    of_eq (by simp only [ForcingRelationSource.arguments, Fin.lastCases_castSucc, Fin.lastCases_last,
      PureQuotationSyntax.term, PureSyntaxQuotation.termTree]; rfl) hu
  have hU := OriginalQuotationVariableFields.variable_of_tree hZ true 0 w z u hw hz hu'
  have hLists1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V K t f c d u v h1)
  have hMid := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V K t f c d u v z hw hLists1 hU)) h1
  have hv := Derives.impE (Derives.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => L) V 0 z v hw hV hz)) (Derives.conjR hMid)
  have hLists2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B0 D z f c d x y h2)
  have hDir := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B0 D z f c d x y i hw hLists2 hx)) h2
  have hy := Derives.impE (Derives.conjL (left_field hZ k w f c d S L R i j M D y hf hd)) (Derives.conjR hDir)
  exact eq_trans hv (eq_symm hy)

/-- Right argument of that same guard diagram. The original guard free
p-slot uses the existing single-slot update, not the bare-R table. -/
theorem guard_right_path {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 x u v y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap (ForcingRelationSource.guardMap k) w z f t f B F))
    (hd : Derives Γ (data k w f c d S L R i j M D))
    (hK : Derives Γ (replacement w f c d S j R K))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w j x))
    (h0 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B F z f t f x u))
    (h1 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V K t f c d u v))
    (h2 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B0 D z f c d x y)) :
    Derives Γ (.equal v y) := by
  have hj := Derives.conjL (Derives.conjR hd)
  have hu := mapped_variable hZ
    (ForcingRelationSource.arguments (.bvar .here) (.fvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (Fin.last (k+1)))))
    (Fin.last (k+1)) w z f t f B F j x u hw he hj hx h0
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (Fin.last (k+1))).index = k+1 :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => Fin.last (k+1))
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hu' : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [PureSyntaxQuotation.Original.leaf (k+1)]) w u) :=
    of_eq (by simp only [ForcingRelationSource.arguments, Fin.lastCases_last, PureQuotationSyntax.term,
      PureSyntaxQuotation.termTree, hIndex]) hu
  have hU := OriginalQuotationVariableFields.variable_of_tree hZ false (k+1) w j u hw hj hu'
  have hLists1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V K t f c d u v h1)
  have hMid := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V K t f c d u v j hw hLists1 hU)) h1
  have hjf := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last (k+1)) f j hf hj
  have hv := Derives.impE (Derives.conjL (at_slot w f c d S j R K v hK hjf)) (Derives.conjR hMid)
  have hLists2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B0 D z f c d x y h2)
  have hDir := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B0 D z f c d x y j hw hLists2 hx)) h2
  have hy := Derives.impE (Derives.conjL (right_field hZ k w f c d S L R i j M D y hf hd)) (Derives.conjR hDir)
  exact eq_trans hv (eq_symm hy)

/-- Every original parameter slot of the ACTUAL guard diagram. The slot
index is quotation metadata; all term/output/table candidates are internal. -/
theorem guard_parameter_path {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : Fin k)
    (w z f t c d S L R i j M D B F V K B0 I x u v y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap (ForcingRelationSource.guardMap k) w z f t f B F))
    (hd : Derives Γ (data k w f c d S L R i j M D))
    (hK : Derives Γ (replacement w f c d S j R K))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral p.val I))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w I x))
    (h0 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B F z f t f x u))
    (h1 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w V K t f c d u v))
    (h2 : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w B0 D z f c d x y)) :
    Derives Γ (.equal v y) := by
  have hu := mapped_variable hZ
    (ForcingRelationSource.arguments (.bvar .here) (.fvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (Fin.last (k+1)))))
    p.castSucc.castSucc w z f t f B F I x u hw he hI hx h0
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable p.castSucc.castSucc).index = p.val :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => p.castSucc.castSucc)
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hu' : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [PureSyntaxQuotation.Original.leaf p.val]) w u) :=
    of_eq (by simp only [ForcingRelationSource.arguments, Fin.lastCases_castSucc, PureQuotationSyntax.term,
      PureSyntaxQuotation.termTree, hIndex]) hu
  have hU := OriginalQuotationVariableFields.variable_of_tree hZ false p.val w I u hw hI hu'
  have hLists1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V K t f c d u v h1)
  have hMid := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V K t f c d u v I hw hLists1 hU)) h1
  have hIf := SyntaxNumeralMembers.index_member hZ (k+2) p.castSucc.castSucc f I hf hI
  have hneq := SyntaxNumerals.different hZ p.val (k+1) (Nat.ne_of_lt (Nat.lt_trans p.isLt (Nat.lt_succ_self k))) I j hI (Derives.conjL (Derives.conjR hd))
  have hv := Derives.impE (Derives.conjL (unchanged w f c d S j R K I v hK hIf hneq)) (Derives.conjR hMid)
  have hLists2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B0 D z f c d x y h2)
  have hDir := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B0 D z f c d x y I hw hLists2 hx)) h2
  have hy := Derives.impE (Derives.conjL (parameter_field hZ k p w f c d S L R i j M D I y hf hd hI)) (Derives.conjR hDir)
  exact StructuralListFieldValues.unique hZ w S I v y hw (SyntaxNumerals.range hZ p.val w I hw hI) hv hy

def guardFrame {k m : Nat} (w z f t c d S L R i j M D B F V K : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj
    ((SyntaxNumeralSyntax.numeral (k+2) f).conj
      ((NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap (ForcingRelationSource.guardMap k) w z f t f B F).conj
        ((data k w f c d S L R i j M D).conj
          ((SyntaxForestSyntax.forest 1 w (fun _ => L) V).conj (replacement w f c d S j R K))))))

theorem guardFrame_rename {k m l : Nat} (w z f t c d S L R i j M D B F V K : Fin m) (ρ : Fin m → Fin l) :
    (guardFrame (k := k) w z f t c d S L R i j M D B F V K).rename ρ =
    guardFrame (k := k) (ρ w) (ρ z) (ρ f) (ρ t) (ρ c) (ρ d) (ρ S) (ρ L) (ρ R) (ρ i) (ρ j) (ρ M) (ρ D) (ρ B) (ρ F) (ρ V) (ρ K) := by
  simp only [guardFrame, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename,
    NativeSubstitutionSyntax.environment_rename, data_rename, SyntaxForestSyntax.forest_rename, replacement_rename]

def guardPath {m} (w z f t c d B F V K B0 D x u v y : Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w B F z f t f x u).conj
    ((SyntaxCodedMixedTermSyntax.substituted w V K t f c d u v).conj
      (SyntaxCodedMixedTermSyntax.substituted w B0 D z f c d x y))

theorem guardPath_rename {m l} (w z f t c d B F V K B0 D x u v y : Fin m) (ρ : Fin m → Fin l) :
    (guardPath w z f t c d B F V K B0 D x u v y).rename ρ =
    guardPath (ρ w) (ρ z) (ρ f) (ρ t) (ρ c) (ρ d) (ρ B) (ρ F) (ρ V) (ρ K) (ρ B0) (ρ D) (ρ x) (ρ u) (ρ v) (ρ y) := by
  simp only [guardPath, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private theorem guard_index_point {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : Fin (k+2))
    (w z f t c d S L R i j M D B F V K B0 I x u v y : Fin m)
    (hF : Derives Γ (guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hP : Derives Γ (guardPath w z f t c d B F V K B0 D x u v y))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral p.val I))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w I x)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (Derives.conjR hF)
  have hf := Derives.conjL (Derives.conjR (Derives.conjR hF))
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hF)))
  have hd := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))
  have hV := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF)))))
  have hK := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF)))))
  have h0 := Derives.conjL hP
  have h1 := Derives.conjL (Derives.conjR hP)
  have h2 := Derives.conjR (Derives.conjR hP)
  revert hI
  refine Fin.lastCases ?_ (fun q => Fin.lastCases ?_ (fun p => ?_) q) p
  · intro hI
    have hEq := SyntaxNumerals.unique hZ (k+1) I j hI (Derives.conjL (Derives.conjR hd))
    have hx' := SyntaxVariableImagePoint.code_subst_index false w I x j hEq hx
    exact guard_right_path hZ w z f t c d S L R i j M D B F V K B0 x u v y hw hf he hd hK hx' h0 h1 h2
  · intro hI
    have hEq := SyntaxNumerals.unique hZ k I i hI (Derives.conjL hd)
    have hx' := SyntaxVariableImagePoint.code_subst_index false w I x i hEq hx
    exact guard_left_path hZ w z f t c d S L R i j M D B F V K B0 x u v y hw hz hf he hd hV hx' h0 h1 h2
  · intro hI
    exact guard_parameter_path hZ p w z f t c d S L R i j M D B F V K B0 I x u v y hw hf he hd hK hI hx h0 h1 h2

/-- Full INTERNAL term comparison for the original guard route versus the
same bare-R argument table. All source terms and candidates are object
variables. Source f is the fixed R arity; target c,d/codes remain arbitrary.
Empty-bound elimination and finite-arity classification use existing
object formulas; there is no host decoder, new recursion or standardness
assumption on runtime target syntax. -/
theorem guard_term {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 x u v y : Fin m)
    (hF : Derives Γ (guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hP : Derives Γ (guardPath w z f t c d B F V K B0 D x u v y)) : Derives Γ (.equal v y) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w B F z f t f x u (Derives.conjL hP)
  apply Derives.disjE (Derives.conjR ht)
  · let E := SyntaxTermSyntax.branch true w z x
    let Q := SyntaxTermSyntax.branchWitness true w z x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w z x _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hz := Derives.conjL (Derives.conjR hF)
    have hz1 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under (add hz E) Q)
    exact .botE (.impE (OmegaSyntax.empty_at z.castSucc (Fin.last m) hz1) (Derives.conjL hQ))
  · let E := SyntaxTermSyntax.branch false w f x
    let Q := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) Q
    have hF1 := of_eq (guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K Fin.castSucc) (under (add hF E) Q)
    have hP1 := of_eq (guardPath_rename w z f t c d B F V K B0 D x u v y Fin.castSucc) (under (add hP E) Q)
    have hf1 := Derives.conjL (Derives.conjR (Derives.conjR hF1))
    have hBelow := Derives.impE (Derives.conjL (SyntaxNumeralMembers.member_iff hZ1 (k+2) f.castSucc (Fin.last m) hf1)) (Derives.conjL hQ)
    have hCases := SyntaxPositionSyntax.below_imp (k+2) (Fin.last m) (.equal v.castSucc y.castSucc) (fun p => by
      apply Derives.impI
      exact guard_index_point (ZFContext.add hZ1 _) p w.castSucc z.castSucc f.castSucc t.castSucc c.castSucc d.castSucc
        S.castSucc L.castSucc R.castSucc i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc K.castSucc
        B0.castSucc (Fin.last m) x.castSucc u.castSucc v.castSucc y.castSucc (add hF1 _) (add hP1 _) (.hyp (Or.inl rfl)) (add (Derives.conjR hQ) _))
    exact Derives.impE hCases hBelow

def guardSentence {k m : Nat} (w z f t c d S L R i j M D B F V K B0 x u v y : Fin m) : Source.Sentence :=
  (((guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj
    (guardPath w z f t c d B F V K B0 D x u v y)).imp (.equal v y)).close

theorem guard_kernel_certificate {k m : Nat} (w z f t c d S L R i j M D B F V K B0 x u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (guardSentence (k := k) w z f t c d S L R i j M D B F V K B0 x u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj (guardPath w z f t c d B F V K B0 D x u v y)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact guard_term (ZFContext.add (ZFContext.source_ZF m) E) w z f t c d S L R i j M D B F V K B0 x u v y (.conjL h) (.conjR h)

end PPAC.Migration.ForcingRelationImages
