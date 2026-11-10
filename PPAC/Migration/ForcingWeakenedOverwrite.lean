import PPAC.Migration.ForcingWeakenedImages
import PPAC.Migration.ForcingRelationImages

/-! Actual original slot replacement commutes with original free-head
weakening. Use real old/new replacement records, the existing pushed-image
field law and original list-code uniqueness. No new recursion or induction. -/
namespace PPAC.Migration.ForcingWeakenedOverwrite
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open ForcingReflexiveImages (replacement replacement_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def images {m} (v : Fin 10 → Fin m) : Fin 6 → Fin m :=
  Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases (v 6) (Fin.cases (v 7) (SyntaxAtomSyntax.two (v 8) (v 9)))))

def frame {m} (w a b c d D R S j P Pn Old New : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (ForcingWeakenedImages.data w a b c d D R S v).conj
    ((replacement w b c d S j P Old).conj
      ((replacement w b c D (v 9) j Pn New).conj
        (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) c d c D P Pn)))
theorem frame_rename {m l} (w a b c d D R S j P Pn Old New : Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (frame w a b c d D R S j P Pn Old New v).rename ρ =
      frame (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) (ρ j) (ρ P) (ρ Pn) (ρ Old) (ρ New) (fun i => ρ (v i)) := by
  simp only [frame, Formula.rename, ForcingWeakenedImages.data_rename, replacement_rename, SyntaxRenameTermSyntax.renamed_rename]

private theorem index_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b i : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hi : Derives Γ (.mem i b)) : Derives Γ (.mem i w) := by
  have ht := OmegaStructureInduction.omega_transitive w (ZFContext.separation hZ OmegaStructureSyntax.subsetMatrix) hw
  exact .impE (RestrictionSyntax.subset_at b w i (.impE (OmegaStructureSyntax.transitive_at w b ht) hb)) hi

/-- Arbitrary internal source slot; source equality selects the actual
replacement branch, and every other slot uses the completed push field law. -/
theorem field_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S j P Pn Old New i u t : Fin m) (v : Fin 10 → Fin m)
    (hf : Derives Γ (frame w a b c d D R S j P Pn Old New v)) (hi : Derives Γ (.mem i b))
    (hu : Derives Γ (field w Old i u))
    (ht : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) c d c D u t)) : Derives Γ (field w New i t) := by
  have hBase := Derives.conjL hf
  have hw := Derives.conjL (.conjL hBase)
  have hOld := Derives.conjL (.conjR hf)
  have hNew := Derives.conjL (.conjR (.conjR hf))
  have hP := Derives.conjR (.conjR (.conjR hf))
  have hLeft := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w b c d S j P Old i u hOld hi)) hu
  have hRight := ForcingReflexiveImages.field_iff w b c D (v 9) j Pn New i t hNew hi
  apply Derives.disjE hLeft
  · let E := (Formula.equal i j).conj (.equal u P)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hRename := SyntaxTermImagePushPoint.renamed_subst_input w (v 2) (v 3) c d c D u P t (.conjR hE) (add ht E)
    have hEq := SyntaxRenameTermUnique.unique (ZFContext.add hZ E) w (v 2) (v 3) c d c D P t Pn (add hw E) hRename (add hP E)
    exact .impE (add (.conjR hRight) E) (.disjL (.conjI (.conjL hE) hEq))
  · let E := (Formula.equal i j).neg.conj (field w S i u)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hField := Derives.impE (.conjR (ForcingReindexedImages.field_iff (ZFContext.add hZ E) false
      w a b c d c D R S (v 2) (v 3) i u t (images v)
      (add (.conjR (.conjR hBase)) E) (.conjI (add hi E) (.conjR hE)))) (add ht E)
    exact .impE (add (.conjR hRight) E) (.disjR (.conjI (.conjL hE) (.conjR hField)))

private structure Candidate {m} (Γ : Context m) (w a b c d D R S j P Pn Old New : Fin m)
    (v : Fin 10 → Fin m) (p : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  original : Derives Γ (frame w a b c d D R S j P Pn Old New v)
  pushed : Derives Γ (ForcingReindexedImages.data w a b c d c D R Old (v 2) (v 3) p)

private theorem Candidate.in_body {m l} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) (E : Formula (m+l)) :
    Candidate (Context.add E (raisedContext l Γ)) (old l w) (old l a) (old l b) (old l c) (old l d) (old l D)
      (old l R) (old l S) (old l j) (old l P) (old l Pn) (old l Old) (old l New)
      (fun i => old l (v i)) (fun i => old l (p i)) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (frame_rename w a b c d D R S j P Pn Old New v (old l)) (HornBinderRules.under_body l h.original E),
    of_eq (ForcingReindexedImages.data_rename w a b c d c D R Old (v 2) (v 3) p (old l)) (HornBinderRules.under_body l h.pushed E)⟩

private theorem Candidate.omega {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) : Derives Γ (omega w) :=
  .conjL (.conjL (.conjL h.original))
private theorem Candidate.arity {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) : Derives Γ (.mem b w) :=
  .conjL (.conjR (.conjR (.conjR (.conjL (.conjL h.original)))))

private theorem Candidate.target {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w b c D (p 5)) :=
  SyntaxMixedImageCodeFields.term_list w (p 3) b c D (p 5) (.conjR (.conjR (.conjR h.pushed)))
private theorem Candidate.actual_target {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w b c D New) :=
  ForcingReflexiveImages.target_type w b c D (v 9) j Pn New (.conjL (.conjR (.conjR h.original)))

/-- Read an internally generated old field, then consume the actual
pushed field and the actual replacement branch; no inverse image assumed. -/
private theorem Candidate.forward_field {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p)
    (i t : Fin m) (hi : Derives Γ (.mem i b)) (ht : Derives Γ (field w (p 5) i t)) : Derives Γ (field w New i t) := by
  have hin := index_natural h.zf w b i h.omega h.arity hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc Old.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (StructuralListFieldValues.exists_value h.zf w Old i h.omega hin)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body E
  have hi1 : Derives Δ (.mem i.castSucc b.castSucc) := under hi E
  have ht1 := of_eq (field_rename w (p 5) i t Fin.castSucc) (under ht E)
  have hRename := Derives.impE (.conjL (ForcingReindexedImages.field_iff h1.zf false
    w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc c.castSucc D.castSucc R.castSucc Old.castSucc
    (v 2).castSucc (v 3).castSucc i.castSucc (Fin.last m) t.castSucc (fun x => (p x).castSucc)
    h1.pushed (.conjI hi1 (.conjR hE)))) (.conjI hi1 ht1)
  have ho := field_forward h1.zf w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc D.castSucc
    R.castSucc S.castSucc j.castSucc P.castSucc Pn.castSucc Old.castSucc New.castSucc i.castSucc (Fin.last m) t.castSucc
    (fun x => (v x).castSucc) h1.original hi1 (.conjR hE) hRename
  exact of_eq (field_rename w New i t Fin.castSucc).symm ho

private theorem Candidate.reverse_field {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p)
    (i t : Fin m) (hi : Derives Γ (.mem i b)) (ht : Derives Γ (field w New i t)) : Derives Γ (field w (p 5) i t) := by
  have hin := index_natural h.zf w b i h.omega h.arity hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc (p 5).castSucc i.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (StructuralListFieldValues.exists_value h.zf w (p 5) i h.omega hin)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body E
  have hi1 : Derives Δ (.mem i.castSucc b.castSucc) := under hi E
  have hForward := h1.forward_field i.castSucc (Fin.last m) hi1 (.conjR hE)
  have ht1 := of_eq (field_rename w New i t Fin.castSucc) (under ht E)
  have hEq := StructuralListFieldValues.unique h1.zf w.castSucc New.castSucc i.castSucc (Fin.last m) t.castSucc h1.omega (under hin E) hForward ht1
  have ho := StructuralListFieldSyntax.output_subst w.castSucc (p 5).castSucc i.castSucc (Fin.last m) t.castSucc hEq (.conjR hE)
  exact of_eq (field_rename w (p 5) i t Fin.castSucc).symm ho

/-- Reuse ORIGINAL list-code extensionality. Both field directions are
derived from real records, so the list-code equality is not a premise. -/
private theorem Candidate.equal {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) :
    Derives Γ (.equal (p 5) New) := by
  have hAgree : Derives Γ (StructuralListCodeSyntax.agree w b (p 5) New) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let E := Formula.mem (Fin.last m).castSucc b.castSucc.castSucc
    let Δ := Context.add E (raisedContext 2 Γ)
    have h2 := h.in_body (l := 2) E
    have hi : Derives Δ E := .hyp (Or.inl rfl)
    apply Derives.conjI
    · apply Derives.impI
      let H := field (old 2 w) (old 2 (p 5)) (slot 2 0) (slot 2 1)
      have hH : Derives (Context.add H Δ) H := .hyp (Or.inl rfl)
      exact (Candidate.mk (ZFContext.add h2.zf H) (add h2.original H) (add h2.pushed H)).forward_field (slot 2 0) (slot 2 1) (add hi H) hH
    · apply Derives.impI
      let H := field (old 2 w) (old 2 New) (slot 2 0) (slot 2 1)
      have hH : Derives (Context.add H Δ) H := .hyp (Or.inl rfl)
      exact (Candidate.mk (ZFContext.add h2.zf H) (add h2.original H) (add h2.pushed H)).reverse_field (slot 2 0) (slot 2 1) (add hi H) hH
  exact StructuralListCodeInduction.unique h.zf w b (p 5) New h.omega
    (.conjR (.conjL (.conjR (.conjR h.target)))) (.conjR (.conjL (.conjR (.conjR h.actual_target)))) hAgree

private def updated {m} (v : Fin 10 → Fin m) (g h New : Fin m) : Fin 10 → Fin m :=
  Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4)
    (Fin.cases g (Fin.cases (v 6) (Fin.cases h (SyntaxAtomSyntax.two (v 8) New))))))))
private theorem updated_map {m l} (v : Fin 10 → Fin m) (g h New : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (updated v g h New i)) = updated (fun i => ρ (v i)) (ρ g) (ρ h) (ρ New) := by
  funext i
  rcases i with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem Candidate.record {m} {Γ : Context m} {w a b c d D R S j P Pn Old New : Fin m}
    {v : Fin 10 → Fin m} {p : Fin 6 → Fin m} (h : Candidate Γ w a b c d D R S j P Pn Old New v p) :
    Derives Γ (ForcingWeakenedImages.data w a b c d D R Old (updated v (p 1) (p 3) New)) := by
  have hBase := Derives.conjL h.original
  have hInput := Derives.conjL hBase
  have hBaseImages := Derives.conjR (.conjR hBase)
  have hOld := Derives.conjL (.conjR h.original)
  have hOldType := ForcingReflexiveImages.target_type w b c d S j P Old hOld
  have hInputNew : Derives Γ (ForcingWeakenedImages.input w a b c d D R Old) :=
    .conjI (.conjL hInput) (.conjI (.conjL (.conjR hInput)) (.conjI (.conjL (.conjR (.conjR hInput))) hOldType))
  have hFreeCode := SyntaxMixedImageCodeUnique.subst_code w (p 3) b c D (p 5) New h.equal
    (.conjR (.conjR (.conjR h.pushed)))
  have hImage : Derives Γ (ForcingReindexedImages.data w a b c d c D R Old (v 2) (v 3)
      (images (updated v (p 1) (p 3) New))) :=
    .conjI (.conjI (.conjL (.conjL hBaseImages)) (.conjR (.conjL h.pushed)))
      (.conjI (.conjI (.conjL (.conjL (.conjR hBaseImages))) (.conjR (.conjL (.conjR h.pushed))))
        (.conjI (.conjL (.conjR (.conjR hBaseImages))) hFreeCode))
  exact .conjI hInputNew (.conjI (.conjL (.conjR hBase)) hImage)

def resultBody {m} (w a b c d D R Old New : Fin m) (v : Fin 10 → Fin m) : Formula (m+2) :=
  ForcingWeakenedImages.data (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 D) (old 2 R) (old 2 Old)
    (updated (fun i => old 2 (v i)) (slot 2 0) (slot 2 1) (old 2 New))
def result {m} (w a b c d D R Old New : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 2 (resultBody w a b c d D R Old New v)
theorem result_rename {m l} (w a b c d D R Old New : Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (result w a b c d D R Old New v).rename ρ = result (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ Old) (ρ New) (fun i => ρ (v i)) := by
  simp only [result, existsMany_rename, resultBody, ForcingWeakenedImages.data_rename, updated_map, lift_old, lift_slot]

/-- SAME original weak operation codes, SAME bound input/output tables and
SAME actual NEW replacement list. Only the two changed free graphs remain
as object witnesses; the full six-image candidate and list equality are
generated and eliminated internally. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S j P Pn Old New : Fin m) (v : Fin 10 → Fin m)
    (hf : Derives Γ (frame w a b c d D R S j P Pn Old New v)) : Derives Γ (result w a b c d D R Old New v) := by
  have hBase := Derives.conjL hf
  have hi := Derives.conjL hBase
  have hOps := Derives.conjL (.conjR hBase)
  have hOld := Derives.conjL (.conjR hf)
  have hOldType := ForcingReflexiveImages.target_type w b c d S j P Old hOld
  have hm : Derives Γ (SyntaxIndexMapSyntax.maps w (v 2) (v 3) c d c D) :=
    .conjI (.conjR (.conjL (.conjR (.conjR hOps)))) (.conjR (.conjR (.conjR (.conjR hOps))))
  let E := ForcingReindexedImages.data (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 c) (old 6 D)
    (old 6 R) (old 6 Old) (old 6 (v 2)) (old 6 (v 3)) (slot 6)
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _
    (ForcingReindexedImages.produce hZ w a b c d c D R Old (v 2) (v 3) (.conjL hi) hm
      (.conjI (.conjL (.conjR (.conjR hi))) hOldType))
  have h6 : Candidate Δ (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 D) (old 6 R) (old 6 S)
      (old 6 j) (old 6 P) (old 6 Pn) (old 6 Old) (old 6 New) (fun i => old 6 (v i)) (slot 6) :=
    ⟨HornBinderRules.zf_body 6 hZ E,
      of_eq (frame_rename w a b c d D R S j P Pn Old New v (old 6)) (HornBinderRules.under_body 6 hf E),
      .hyp (Or.inl rfl)⟩
  have ho : Derives Δ (result (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 D)
      (old 6 R) (old 6 Old) (old 6 New) (fun i => old 6 (v i))) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (slot 6 1) (slot 6 3))
    exact of_eq (by simp only [resultBody, ForcingWeakenedImages.data_rename, updated_map, assign_old, assign_slot]; rfl) h6.record
  exact of_eq (result_rename w a b c d D R Old New v (old 6)).symm ho

/-- Consume the ACTUAL old/new covered queries, not a generated table or
the desired query equality. Existing original weak covariance is reused. -/
theorem from_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S j P Pn Old New n u o : Fin m) (v : Fin 10 → Fin m)
    (hf : Derives Γ (frame w a b c d D R S j P Pn Old New v))
    (hOld : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R Old a b c d n u))
    (hNew : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) New a b c D n o)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w c d D u o) := by
  let E := resultBody w a b c d D R Old New v
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (produce hZ w a b c d D R S j P Pn Old New v hf)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h0 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R Old a b c d n u (old 2)) (HornBinderRules.under_body 2 hOld E)
  have h1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w (v 8) New a b c D n o (old 2)) (HornBinderRules.under_body 2 hNew E)
  have ho := ForcingWeakenedImages.from_queries (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 D) (old 2 R) (old 2 Old) (old 2 n) (old 2 u) (old 2 o)
    (updated (fun i => old 2 (v i)) (slot 2 0) (slot 2 1) (old 2 New)) (.conjI hE (.conjI h0 h1))
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w c d D u o (old 2)).symm ho

def doubleFrame {m} (k : Nat) (w a b c d D R S L Q Ln Qn i j M Old Mn New : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (ForcingWeakenedImages.data w a b c d D R S v).conj
    ((ForcingRelationImages.data k w b c d S L Q i j M Old).conj
      ((ForcingRelationImages.data k w b c D (v 9) Ln Qn i j Mn New).conj
        ((SyntaxRenameTermSyntax.renamed w (v 2) (v 3) c d c D L Ln).conj
          (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) c d c D Q Qn))))
theorem doubleFrame_rename {m l} (k : Nat) (w a b c d D R S L Q Ln Qn i j M Old Mn New : Fin m)
    (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (doubleFrame k w a b c d D R S L Q Ln Qn i j M Old Mn New v).rename ρ =
      doubleFrame k (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) (ρ L) (ρ Q) (ρ Ln) (ρ Qn)
        (ρ i) (ρ j) (ρ M) (ρ Old) (ρ Mn) (ρ New) (fun x => ρ (v x)) := by
  simp only [doubleFrame, Formula.rename, ForcingWeakenedImages.data_rename, ForcingRelationImages.data_rename,
    SyntaxRenameTermSyntax.renamed_rename]

/-- ACTUAL original q/p double-overwrite records, not two assumed weak
leaf answers. The first real record is transported, then consumed as the
second record's input. The SAME original operation/bound tables survive;
all changed free graph witnesses and formula-output witnesses are internal. -/
theorem from_double_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w a b c d D R S L Q Ln Qn i j M Old Mn New n u o : Fin m) (v : Fin 10 → Fin m)
    (hf : Derives Γ (doubleFrame k w a b c d D R S L Q Ln Qn i j M Old Mn New v))
    (hOld : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R Old a b c d n u))
    (hNew : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) New a b c D n o)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w c d D u o) := by
  have hBase := Derives.conjL hf
  have hA := Derives.conjL (.conjR hf)
  have hB := Derives.conjL (.conjR (.conjR hf))
  have hL := Derives.conjL (.conjR (.conjR (.conjR hf)))
  have hFirst : Derives Γ (frame w a b c d D R S i L Ln M Mn v) :=
    .conjI hBase (.conjI (.conjL (.conjR (.conjR hA))) (.conjI (.conjL (.conjR (.conjR hB))) hL))
  let E := resultBody w a b c d D R M Mn v
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (produce hZ w a b c d D R S i L Ln M Mn v hFirst)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h2 := of_eq (doubleFrame_rename k w a b c d D R S L Q Ln Qn i j M Old Mn New v (old 2))
    (HornBinderRules.under_body 2 hf E)
  have hA2 := Derives.conjL (.conjR h2)
  have hB2 := Derives.conjL (.conjR (.conjR h2))
  have hQ2 := Derives.conjR (.conjR (.conjR (.conjR h2)))
  have hSecond : Derives Δ (frame (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 D)
      (old 2 R) (old 2 M) (old 2 j) (old 2 Q) (old 2 Qn) (old 2 Old) (old 2 New)
      (updated (fun x => old 2 (v x)) (slot 2 0) (slot 2 1) (old 2 Mn))) :=
    .conjI hE (.conjI (.conjR (.conjR (.conjR hA2))) (.conjI (.conjR (.conjR (.conjR hB2))) hQ2))
  have h0 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R Old a b c d n u (old 2))
    (HornBinderRules.under_body 2 hOld E)
  have h1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w (v 8) New a b c D n o (old 2))
    (HornBinderRules.under_body 2 hNew E)
  have ho := from_queries (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 D) (old 2 R) (old 2 M) (old 2 j) (old 2 Q) (old 2 Qn) (old 2 Old) (old 2 New)
    (old 2 n) (old 2 u) (old 2 o) (updated (fun x => old 2 (v x)) (slot 2 0) (slot 2 1) (old 2 Mn)) hSecond h0 h1
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w c d D u o (old 2)).symm ho

def sentence {m} (w a b c d D R S j P Pn Old New : Fin m) (v : Fin 10 → Fin m) : Source.Sentence :=
  ((frame w a b c d D R S j P Pn Old New v).imp (result w a b c d D R Old New v)).close
theorem kernel_certificate {m} (w a b c d D R S j P Pn Old New : Fin m) (v : Fin 10 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a b c d D R S j P Pn Old New v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) w a b c d D R S j P Pn Old New v (.hyp (Or.inl rfl))

def doubleSentence {m} (k : Nat) (w a b c d D R S L Q Ln Qn i j M Old Mn New n u o : Fin m) (v : Fin 10 → Fin m) : Source.Sentence :=
  (((doubleFrame k w a b c d D R S L Q Ln Qn i j M Old Mn New v).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R Old a b c d n u).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) New a b c D n o))).imp
        (SyntaxWeakenFreeSyntax.weakened w c d D u o)).close
theorem double_kernel_certificate {m} (k : Nat) (w a b c d D R S L Q Ln Qn i j M Old Mn New n u o : Fin m) (v : Fin 10 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (doubleSentence k w a b c d D R S L Q Ln Qn i j M Old Mn New n u o v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (doubleFrame k w a b c d D R S L Q Ln Qn i j M Old Mn New v).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R Old a b c d n u).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) New a b c D n o))
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_double_queries (ZFContext.add (ZFContext.source_ZF m) E) k w a b c d D R S L Q Ln Qn i j M Old Mn New n u o v
    (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

end PPAC.Migration.ForcingWeakenedOverwrite
