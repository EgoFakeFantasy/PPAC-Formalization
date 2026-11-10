import PPAC.Migration.ForcingMemberRows
import PPAC.Migration.ForcingWeakenedOverwrite
import PPAC.Migration.ForcingPreorderGuardTables

/-! Actual old/new bare R(q,p) leaves. Generate and eliminate the shared
source quotation and both original double-overwrite records; consume the
unchanged raw-prefix and actual weakening consumers. -/
namespace PPAC.Migration.ForcingRelationWeakening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def left {m} (x : Fin 48 → Fin m) : Fin 24 → Fin m := fun i => x (i.castAdd 24)
private def right {m} (x : Fin 48 → Fin m) : Fin 24 → Fin m := fun i => x (i.addNat 24)
private def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def input {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) : Formula m :=
  (ForcingMemberRows.data test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).conj (SyntaxNumeralSyntax.numeral 3 A3)

theorem input_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (ρ : Fin m → Fin l) :
    (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).rename ρ =
      input test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K) (fun j => ρ (raw j)) (fun j => ρ (v j))
        (fun s => ρ (C s)) (fun s => ρ (Refl s)) (fun s => ρ (Pre s)) (fun s => ρ (U0 s))
        (fun s j => ρ (P s j)) (fun j => ρ (x j)) := by
  simp only [input, Formula.rename, ForcingMemberRows.data_rename, SyntaxNumeralSyntax.numeral_rename]

private theorem row_term {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f T C Bound S Refl Pre U0 : Fin m) (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m) (y : Fin 24 → Fin m)
    (hr : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f T C Bound S Refl Pre U0 raw P y))
    (i : Fin 3) : Derives Γ (SyntaxTermSyntax.term w z T (P i)) := by
  let U := ForcingMemberRows.nativeFields U0 y
  let F := ForcingMemberRows.proofFields y
  let N := ForcingMemberRows.tailFields y
  have hRow := Derives.conjL (.conjL (.conjR hr))
  have t0 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 0) (F 0) (U 1) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hRow))))))))))
  have t1 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 1) (F 1) (U 2) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hRow))))))))))))
  have t2 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 2) (F 2) (N 0) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hRow))))))))))))))
  rcases i with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact t0
  · exact t1
  · exact t2

private theorem direct {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f T C Bound S Refl Pre U0 G X i j M D : Fin m)
    (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m) (y : Fin 24 → Fin m) (E : Fin 4 → Fin m)
    (hr : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f T C Bound S Refl Pre U0 raw P y))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hBound : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z T Bound))
    (hSource : Derives Γ (ForcingRelationSource.data Reln 1 w z A1 A3 f (raw 14) G X E))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (P 1) (P 2) i j M D)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w Bound D z f z T X (ForcingMemberRows.leafFields y 4)) := by
  let U := ForcingMemberRows.nativeFields U0 y
  let N := ForcingMemberRows.tailFields y
  let V := ForcingMemberRows.prefixFields y
  have hPrefix : Derives Γ (ForcingPreorderPrefix.data w z f T Bound S (four z A1 A2 A3)
      (four (raw 2) (raw 3) (raw 4) (raw 5)) (four (U 0) (U 1) (U 2) (N 0)) P V) := .conjL (.conjR (.conjR (.conjR hr)))
  have hLeaf := ForcingPreorderLeaves.leaf_at w (V 2) S A3 f z T raw (ForcingMemberRows.leafFields y) N 4 (.conjR (.conjR (.conjR (.conjR hr))))
  exact ForcingRelationRawFormula.from_prefix hZ Reln 1 w z A1 A2 A3 A1 f T Bound S (raw 14) G X i j M D
    (ForcingMemberRows.leafFields y 4) E (four z A1 A2 A3) (four (raw 2) (raw 3) (raw 4) (raw 5)) (four (U 0) (U 1) (U 2) (N 0)) P V
    hw hz h1 h2 hf hSource hPrefix hBound
    (fun i => SyntaxTerms.range hZ w z T (P i) hw (row_term test Reln w z A1 A2 A3 f T C Bound S Refl Pre U0 raw P y hr i)) hImages hLeaf

private structure Inputs {k m} (Γ : Context m) (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  source : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x)

section
variable {k m : Nat} {Γ : Context m} {test : Formula 1} {Reln : Source.Formula (k+2)}
variable {w z A1 A2 A3 f b B R S K : Fin m} {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m}
variable {C Refl Pre U0 : Fin 2 → Fin m} {P : Fin 2 → Fin 3 → Fin m} {x : Fin 48 → Fin m}
private theorem Inputs.in_body {l} (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) (F : Formula (m+l)) :
    Inputs (Context.add F (raisedContext l Γ)) test Reln (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l b) (old l B) (old l R) (old l S) (old l K) (fun j => old l (raw j)) (fun j => old l (v j))
      (fun s => old l (C s)) (fun s => old l (Refl s)) (fun s => old l (Pre s)) (fun s => old l (U0 s))
      (fun s j => old l (P s j)) (fun j => old l (x j)) :=
  ⟨HornBinderRules.zf_body l h.zf F, of_eq (input_rename test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x (old l)) (HornBinderRules.under_body l h.source F)⟩
private theorem Inputs.basis (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (ForcingMemberRows.input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P) := .conjL (.conjL h.source)
private theorem Inputs.old_row (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0) (left x)) := .conjL (.conjR (.conjL h.source))
private theorem Inputs.new_row (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) raw (P 1) (right x)) := .conjL (.conjR (.conjR (.conjL h.source)))
private theorem Inputs.zero (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxNumeralSyntax.numeral 0 z) := .conjL h.basis
private theorem Inputs.one (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1) := .conjL (.conjR h.basis)
private theorem Inputs.two (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2) := .conjL (.conjR (.conjR h.basis))
private theorem Inputs.free (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f) := .conjL (.conjR (.conjR (.conjR (.conjR h.basis))))
private theorem Inputs.base (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (ForcingWeakenedImages.data w z f z b B R S v) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.basis)))))
private theorem Inputs.three (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3) := .conjR h.source
private theorem Inputs.omega (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (omega w) := .conjL (.conjL h.base)
private theorem Inputs.old_lists (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z f z b R S) := .conjR (.conjR (.conjL h.base))
private theorem Inputs.new_lists (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z f z B (v 8) (v 9)) :=
  SyntaxMixedImageCodePairs.term_lists w (v 6) (v 7) z f z B (v 8) (v 9) (.conjR (.conjR (.conjR (.conjR h.base))))
private theorem Inputs.q_rename (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B (P 0 1) (P 1 1)) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.basis))))))))
private theorem Inputs.p_rename (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B (P 0 2) (P 1 2)) := .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.basis))))))))

private theorem at_images (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) (G X : Fin m) (E a c : Fin 4 → Fin m)
    (hs : Derives Γ (ForcingRelationSource.data Reln 1 w z A1 A3 f (raw 14) G X E))
    (ha : Derives Γ (ForcingRelationImages.data k w f z b S (P 0 1) (P 0 2) (a 0) (a 1) (a 2) (a 3)))
    (hc : Derives Γ (ForcingRelationImages.data k w f z B (v 9) (P 1 1) (P 1 2) (c 0) (c 1) (c 2) (c 3))) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B
      (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4)) := by
  have ei := SyntaxNumerals.unique h.zf k (c 0) (a 0) (.conjL hc) (.conjL ha)
  have ej := SyntaxNumerals.unique h.zf (k+1) (c 1) (a 1) (.conjL (.conjR hc)) (.conjL (.conjR ha))
  have hm := ForcingPreorderGuardTables.replacement_index w f z B (v 9) (c 0) (P 1 1) (c 2) (a 0) ei (.conjL (.conjR (.conjR hc)))
  have hd := ForcingPreorderGuardTables.replacement_index w f z B (c 2) (c 1) (P 1 2) (c 3) (a 1) ej (.conjR (.conjR (.conjR hc)))
  have hc' : Derives Γ (ForcingRelationImages.data k w f z B (v 9) (P 1 1) (P 1 2) (a 0) (a 1) (c 2) (c 3)) :=
    .conjI (.conjL ha) (.conjI (.conjL (.conjR ha)) (.conjI hm hd))
  have oldQuery := direct h.zf test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) G X (a 0) (a 1) (a 2) (a 3)
    raw (P 0) (left x) E h.old_row h.omega h.zero h.one h.two h.free (.conjL h.old_lists) hs ha
  have newQuery := direct h.zf test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) G X (a 0) (a 1) (c 2) (c 3)
    raw (P 1) (right x) E h.new_row h.omega h.zero h.one h.two h.free (.conjL h.new_lists) hs hc'
  exact ForcingWeakenedOverwrite.from_double_queries h.zf k w z f z b B R S (P 0 1) (P 0 2) (P 1 1) (P 1 2)
    (a 0) (a 1) (a 2) (a 3) (c 2) (c 3) X (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4) v
    (.conjI h.base (.conjI ha (.conjI hc' (.conjI h.q_rename h.p_rename)))) oldQuery newQuery

private theorem at_source (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) (G X : Fin m) (E : Fin 4 → Fin m)
    (hs : Derives Γ (ForcingRelationSource.data Reln 1 w z A1 A3 f (raw 14) G X E)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B
      (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4)) := by
  let A := ForcingRelationImages.body k w f z b S (P 0 1) (P 0 2)
  let Δ := Context.add A (raisedContext 4 Γ)
  have hOldImages := ForcingRelationImages.produce h.zf k w f z b S (P 0 1) (P 0 2) h.omega (.conjR h.old_lists)
    (row_term test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0) (left x) h.old_row 1)
    (row_term test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0) (left x) h.old_row 2)
  apply HornBinderRules.eliminate_many 4 A _ hOldImages
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have h4 := h.in_body A
  have hs4 := of_eq (ForcingRelationSource.data_rename Reln 1 w z A1 A3 f (raw 14) G X E (old 4)) (HornBinderRules.under_body 4 hs A)
  let Cn := ForcingRelationImages.body k (old 4 w) (old 4 f) (old 4 z) (old 4 B) (old 4 (v 9)) (old 4 (P 1 1)) (old 4 (P 1 2))
  let Ξ := Context.add Cn (raisedContext 4 Δ)
  have hNewImages := ForcingRelationImages.produce h4.zf k (old 4 w) (old 4 f) (old 4 z) (old 4 B) (old 4 (v 9))
    (old 4 (P 1 1)) (old 4 (P 1 2)) h4.omega (.conjR h4.new_lists)
    (row_term test Reln (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 B)
      (old 4 (C 1)) (old 4 (v 8)) (old 4 (v 9)) (old 4 (Refl 1)) (old 4 (Pre 1)) (old 4 (U0 1))
      (fun j => old 4 (raw j)) (fun j => old 4 (P 1 j)) (right (fun j => old 4 (x j))) h4.new_row 1)
    (row_term test Reln (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 f) (old 4 B)
      (old 4 (C 1)) (old 4 (v 8)) (old 4 (v 9)) (old 4 (Refl 1)) (old 4 (Pre 1)) (old 4 (U0 1))
      (fun j => old 4 (raw j)) (fun j => old 4 (P 1 j)) (right (fun j => old 4 (x j))) h4.new_row 2)
  apply HornBinderRules.eliminate_many 4 Cn _ hNewImages
  have hCn : Derives Ξ Cn := .hyp (Or.inl rfl)
  have h8 := h4.in_body Cn
  have hs8 : Derives Ξ (ForcingRelationSource.data Reln 1 (old 8 w) (old 8 z) (old 8 A1) (old 8 A3) (old 8 f)
      (old 8 (raw 14)) (old 8 G) (old 8 X) (fun j => old 8 (E j))) :=
    of_eq (by simp only [ForcingRelationSource.data_rename]; rfl) (HornBinderRules.under_body 4 hs4 Cn)
  have ha8 : Derives Ξ (ForcingRelationImages.data k (old 8 w) (old 8 f) (old 8 z) (old 8 b) (old 8 S)
      (old 8 (P 0 1)) (old 8 (P 0 2)) (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (slot 4 2)) (old 4 (slot 4 3))) :=
    of_eq (by simp only [A, ForcingRelationImages.body, ForcingRelationImages.data_rename]; rfl) (HornBinderRules.under_body 4 hA Cn)
  have ho := at_images h8 (old 8 G) (old 8 X) (fun j => old 8 (E j)) (fun j => old 4 (slot 4 j)) (slot 4) hs8 ha8 hCn
  exact of_eq (by simp only [SyntaxWeakenFreeSyntax.weakened_rename]; rfl) ho

private theorem at_guard (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) (G : Fin m)
    (hG : Derives Γ (PureQuotationSyntax.formula (ForcingGuardCode.template true Reln) w G)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B
      (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4)) := by
  have hAtom := ForcingRelationSource.raw_quotation Reln 1 w z A1 A2 A3 f raw (.conjL h.old_row)
  let F := ForcingRelationSource.body Reln 1 w z A1 A3 f (raw 14) G
  let Δ := Context.add F (raisedContext 5 Γ)
  have he := ForcingRelationSource.produce h.zf Reln 1 w z A1 A3 f (raw 14) G h.omega h.zero h.one h.three h.free hAtom hG
  apply HornBinderRules.eliminate_many 5 F _ he
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have h5 := h.in_body F
  have ho := at_source h5 (old 5 G) (slot 5 0) (fun j => slot 5 j.succ) hF
  exact of_eq (by simp only [SyntaxWeakenFreeSyntax.weakened_rename]; rfl) ho

end

/-- Source quotation, source maps and BOTH actual double-overwrite records
are generated internally. Only actual original paired records are inputs. -/
theorem from_rows {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m)
    (hi : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B
      (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4)) := by
  have h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x := ⟨hZ,hi⟩
  have he := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (ForcingGuardCode.template true Reln)) w h.omega
  let F := (Formula.mem (slot 1 0) (old 1 w)).conj
    (PureQuotationSyntax.formula (ForcingGuardCode.template true Reln) (old 1 w) (slot 1 0))
  let Δ := Context.add F (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 F _ he
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have h1 := h.in_body F
  have ho := at_guard h1 (slot 1 0) (.conjR hF)
  exact of_eq (by simp only [SyntaxWeakenFreeSyntax.weakened_rename]; rfl) ho

/-- Preserve the complete paired record, including q/p member weakenings,
while adding the actually derived bare R(q,p) weakening. -/
theorem enrich {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m)
    (hi : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x)) :
    Derives Γ ((input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).conj
      (SyntaxWeakenFreeSyntax.weakened w z b B
        (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4))) :=
  .conjI hi (from_rows hZ test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x hi)

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) : Source.Sentence :=
  ((input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).imp
    (SyntaxWeakenFreeSyntax.weakened w z b B
      (ForcingMemberRows.leafFields (left x) 4) (ForcingMemberRows.leafFields (right x) 4))).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_rows (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingRelationWeakening
