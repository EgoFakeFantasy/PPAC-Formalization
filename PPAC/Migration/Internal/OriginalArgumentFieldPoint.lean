import PPAC.Migration.Internal.OriginalArgumentConsFields

/-! 原Run₂逐字段正确性的实际Nil／Cons归纳步，源有类型范围保持全部内部索引。 -/
namespace PPAC.Migration.Internal.OriginalArgumentFieldPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalArgumentFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_fields {m} {Γ : Context m} (w mode depth parameter k n q : Fin m) (hz : Derives Γ (empty k)) : Derives Γ (fields w mode depth parameter k n q) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (slot 3 0) (old 3 k)).conj ((StructuralListFieldSyntax.field (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).conj (StructuralListFieldSyntax.field (old 3 w) (old 3 q) (slot 3 0) (slot 3 2)))
  let Δ := Context.add A (raisedContext 3 Γ)
  have hz3 : Derives Δ (empty (old 3 k)) := of_eq (empty_rename k (old 3)) (HornBinderRules.under_body 3 hz A)
  exact .botE (.impE (empty_at _ _ hz3) (.conjL (.hyp (Or.inl rfl))))

theorem cons_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b n k q h t H T : Fin m)
    (hw : Derives Γ (omega w))
    (he : Derives Γ (OriginalArgumentFieldSyntax.earlier w mode depth parameter a b n))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hC : Derives Γ (OriginalArgumentCaseSyntax.consData w mode depth parameter n q h t H T))
    : Derives Γ (fields w mode depth parameter k n q) := by
  have hhN := OriginalArgumentRunNaturality.input_natural hZ 1 _ _ _ _ _ _ hw (.conjL (.conjR hC))
  have htN := OriginalArgumentRunNaturality.input_natural hZ 2 _ _ _ _ _ _ hw (.conjR (.conjR hC))
  have hHN := OriginalArgumentRunNaturality.output_natural hZ 1 _ _ _ _ _ _ hw (.conjL (.conjR hC))
  have hTN := OriginalArgumentRunNaturality.output_natural hZ 2 _ _ _ _ _ _ hw (.conjR (.conjR hC))
  have htn := Derives.conjR (StructuralConsCore.components hZ w h t n hw hhN htN (.conjL (.conjL hC)))
  have hparts := TypedArgumentListElimination.cons_parts hZ w k a b h t n hw hL hhN htN (.conjL (.conjL hC))
  let B := ((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj ((SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc h.castSucc).conj (SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc t.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hparts
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under hw B)
  have he1 : Derives Δ (OriginalArgumentFieldSyntax.earlier w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (by simp only [OriginalArgumentFieldSyntax.earlier_rename]) (under he B)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (under hL B)
  have hC1 : Derives Δ (OriginalArgumentCaseSyntax.consData w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc h.castSucc t.castSucc H.castSucc T.castSucc) := of_eq (by simp only [OriginalArgumentCaseSyntax.consData_rename]) (under hC B)
  have hhN1 : Derives Δ (Formula.mem h.castSucc w.castSucc) := under hhN B
  have htN1 : Derives Δ (Formula.mem t.castSucc w.castSucc) := under htN B
  have hHN1 : Derives Δ (Formula.mem H.castSucc w.castSucc) := under hHN B
  have hTN1 : Derives Δ (Formula.mem T.castSucc w.castSucc) := under hTN B
  have htn1 : Derives Δ (Formula.mem t.castSucc n.castSucc) := under htn B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have htProp := earlier_at _ _ _ _ _ _ _ _ he1 htN1 htn1
  have htFields := property_at _ _ _ _ _ _ _ (Fin.last m) T.castSucc htProp (.conjR (.conjR hB)) (.conjR (.conjR hC1))
  have ho := OriginalArgumentConsFields.cons_fields hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) k.castSucc h.castSucc t.castSucc H.castSucc T.castSucc n.castSucc q.castSucc hw1 hhN1 htN1 hHN1 hTN1 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjL (.conjL hC1)) (.conjR (.conjL hC1)) (.conjL (.conjR hC1)) htFields
  exact of_eq (fields_rename w mode depth parameter k n q Fin.castSucc).symm ho

theorem at_source_run {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter a b n k q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (he : Derives Γ (OriginalArgumentFieldSyntax.earlier w mode depth parameter a b n))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q))
    : Derives Γ (fields w mode depth parameter k n q) := by
  have ho := Derives.impE (.conjL (OriginalArgumentsRunEquation.run_iff hZ three w mode depth parameter n q hw hm hd hp)) hr
  apply Derives.disjE ho
  · let E := OriginalArgumentCaseSyntax.nilData w n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hz := StructuralListLengthRules.nil_empty (ZFContext.add hZ E) w n k (add hw E) (.conjL hE) (add (.conjR (.conjL (.conjR (.conjR hL)))) E)
    exact nil_fields w mode depth parameter k n q hz
  · let E := OriginalArgumentCaseSyntax.consCase w mode depth parameter n q
    let C := OriginalArgumentCaseSyntax.consBody w mode depth parameter n q
    let Δ := Context.add C (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 C _ (.hyp (Or.inl rfl))
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) C
    have hw4 : Derives Δ (omega (old 4 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 4 (add hw E) C)
    have he4 : Derives Δ (OriginalArgumentFieldSyntax.earlier (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 a) (old 4 b) (old 4 n)) := of_eq (by simp only [OriginalArgumentFieldSyntax.earlier_rename]) (HornBinderRules.under_body 4 (add he E) C)
    have hL4 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 4 w) (old 4 k) (old 4 a) (old 4 b) (old 4 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 4 (add hL E) C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hh := cons_from_earlier hZ4 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 a) (old 4 b) (old 4 n) (old 4 k) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 he4 hL4 hC
    exact of_eq (fields_rename w mode depth parameter k n q (old 4)).symm hh

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter a b n : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (he : Derives Γ (OriginalArgumentFieldSyntax.earlier w mode depth parameter a b n))
    : Derives Γ (property w mode depth parameter a b n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let A := SyntaxMixedImageCodeSyntax.termList (old 2 w) (slot 2 0) (old 2 a) (old 2 b) (old 2 n)
  let B := OriginalTransformRowSyntax.run 2 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 n) (slot 2 1)
  let Δ := Context.add B (Context.add A (raisedContext 2 Γ))
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) A) B
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (by simp only [omega_rename]) (add (add (HornBinderRules.under_many 2 hw) A) B)
  have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (old 2 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (add (add (HornBinderRules.under_many 2 hm) A) B)
  have hd2 : Derives Δ (Formula.mem (old 2 depth) (old 2 w)) := of_eq (by simp only [Formula.rename]) (add (add (HornBinderRules.under_many 2 hd) A) B)
  have hp2 : Derives Δ (Formula.mem (old 2 parameter) (old 2 w)) := of_eq (by simp only [Formula.rename]) (add (add (HornBinderRules.under_many 2 hp) A) B)
  have he2 : Derives Δ (OriginalArgumentFieldSyntax.earlier (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 n)) := of_eq (by simp only [OriginalArgumentFieldSyntax.earlier_rename]) (add (add (HornBinderRules.under_many 2 he) A) B)
  exact at_source_run hZ2 three (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 n) (slot 2 0) (slot 2 1) hw2 hm2 hd2 hp2 he2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalArgumentFieldPoint
