import PPAC.Migration.ForcingWeakenedImages
import PPAC.Migration.ForcingPreorderInstances
import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! Instantiate the SAME original raw preorder after the actual free-head
extension. Reuse the original open_target proof, not a second compiler or
native-instance producer. New r/q/p and Pre/Refl/transitivity codes remain
under six object existential binders. -/
namespace PPAC.Migration.ForcingFreshPreorder
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def three {m} (a b c : Fin m) : Fin 3 → Fin m := Fin.cases a (SyntaxAtomSyntax.two b c)
private theorem three_map {m l} (a b c : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (three a b c i)) = three (ρ a) (ρ b) (ρ c) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.cases rfl (fun e => Fin.elim0 e) i)) i

def input {k m} (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (empty z).conj ((successor A z).conj
    ((ForcingWeakenedImages.data w z f z b B R S v).conj
      ((ForcingPreorderCode.rawData Reln w z A1 A2 A3 f raw).conj
        ((SyntaxTermSyntax.term w z b q).conj ((SyntaxTermSyntax.term w z b p).conj
          (SyntaxMixedFormulaJudgmentSyntax.substituted w R S z f z b (raw 0) Pre))))))
theorem input_rename {k m l} (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v).rename ρ =
      input Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun i => ρ (raw i)) (fun i => ρ (v i)) := by
  simp only [input, Formula.rename, empty_rename, successor_rename, ForcingWeakenedImages.data_rename,
    ForcingPreorderCode.rawData_rename, SyntaxTermSyntax.term_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def data {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (x : Fin 6 → Fin m) : Formula m :=
  (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v).conj
    ((SyntaxVariableSyntax.code false w z (x 0)).conj
      ((SyntaxTermSyntax.term w z B (x 0)).conj
        ((SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B q (x 1)).conj
          ((SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B p (x 2)).conj
            ((ForcingPreorderInstances.targetData test w z f B A (v 8) (v 9) (raw 0) (raw 1) (raw 2)
              (three (x 0) (x 1) (x 2)) (x 3) (x 4) (x 5)).conj
                (SyntaxWeakenFreeSyntax.weakened w z b B Pre (x 3)))))))
theorem data_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (x : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (data test Reln w z A1 A2 A3 f b A B R S q p Pre raw v x).rename ρ =
      data test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun i => ρ (raw i)) (fun i => ρ (v i)) (fun i => ρ (x i)) := by
  simp only [data, Formula.rename, input_rename, SyntaxVariableSyntax.code_rename, SyntaxTermSyntax.term_rename,
    SyntaxRenameTermSyntax.renamed_rename, ForcingPreorderInstances.targetData_rename, SyntaxWeakenFreeSyntax.weakened_rename, three_map]

def body {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula (m+6) :=
  data test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 b) (old 6 A) (old 6 B)
    (old 6 R) (old 6 S) (old 6 q) (old 6 p) (old 6 Pre) (fun i => old 6 (raw i)) (fun i => old 6 (v i)) (slot 6)
def produced {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 6 (body test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)
theorem produced_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v).rename ρ =
      produced test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun i => ρ (raw i)) (fun i => ρ (v i)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private structure Inputs {k m} (Γ : Context m) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  source : Derives Γ (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v)
private theorem Inputs.in_body {k m l} {Γ : Context m} {Reln : Source.Formula (k+2)} {w z A1 A2 A3 f b A B R S q p Pre : Fin m}
    {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m} (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Γ)) Reln (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l b)
      (old l A) (old l B) (old l R) (old l S) (old l q) (old l p) (old l Pre) (fun i => old l (raw i)) (fun i => old l (v i)) :=
  ⟨HornBinderRules.zf_body l h.zf E, of_eq (input_rename Reln w z A1 A2 A3 f b A B R S q p Pre raw v (old l)) (HornBinderRules.under_body l h.source E)⟩

private theorem Inputs.base {k m} {Γ : Context m} {Reln : Source.Formula (k+2)} {w z A1 A2 A3 f b A B R S q p Pre : Fin m}
    {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m} (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) :
    Derives Γ (ForcingWeakenedImages.data w z f z b B R S v) := .conjL (.conjR (.conjR h.source))
private theorem Inputs.omega {k m} {Γ : Context m} {Reln : Source.Formula (k+2)} {w z A1 A2 A3 f b A B R S q p Pre : Fin m}
    {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m} (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) : Derives Γ (omega w) :=
  .conjL (.conjL h.base)
private theorem Inputs.maps {k m} {Γ : Context m} {Reln : Source.Formula (k+2)} {w z A1 A2 A3 f b A B R S q p Pre : Fin m}
    {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m} (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) :
    Derives Γ (SyntaxIndexMapSyntax.maps w (v 2) (v 3) z b z B) := by
  have ho := Derives.conjL (.conjR h.base)
  exact .conjI (.conjR (.conjL (.conjR (.conjR ho)))) (.conjR (.conjR (.conjR (.conjR ho))))

private theorem at_terms {k m} {Γ : Context m} (test : Formula 1) {Reln : Source.Formula (k+2)}
    {w z A1 A2 A3 f b A B R S q p Pre : Fin m} {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m}
    (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) (r qn pn : Fin m)
    (hr : Derives Γ (SyntaxVariableSyntax.code false w z r)) (hrt : Derives Γ (SyntaxTermSyntax.term w z B r))
    (hq : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B q qn))
    (hp : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B p pn)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v) := by
  have hRaw := Derives.conjL (.conjR (.conjR (.conjR h.source)))
  have hNewLists := SyntaxMixedImageCodePairs.term_lists w (v 6) (v 7) z f z B (v 8) (v 9)
    (.conjR (.conjR (.conjR (.conjR h.base))))
  have hqTy := SyntaxRenameTermTyping.target_term _ _ _ _ _ _ _ _ _ hq
  have hpTy := SyntaxRenameTermTyping.target_term _ _ _ _ _ _ _ _ _ hp
  have hP : ∀ i, Derives Γ (SyntaxTermSyntax.term w z B (three r qn pn i)) := by
    rintro ⟨i,hi⟩
    have hCases : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact hrt
    · exact hqTy
    · exact hpTy
  have hTarget := ForcingPreorderInstances.open_target h.zf test Reln w z A1 A2 A3 f B A (v 8) (v 9)
    (three r qn pn) raw h.omega (.conjL h.source) (.conjL (.conjR h.source)) hP (.conjL hNewLists) (.conjR hNewLists) hRaw
  let E := ForcingPreorderInstances.targetData test (old 3 w) (old 3 z) (old 3 f) (old 3 B) (old 3 A)
    (old 3 (v 8)) (old 3 (v 9)) (old 3 (raw 0)) (old 3 (raw 1)) (old 3 (raw 2))
    (three (old 3 r) (old 3 qn) (old 3 pn)) (slot 3 0) (slot 3 1) (slot 3 2)
  let Δ := Context.add E (raisedContext 3 Γ)
  have hTargetExact : Derives Γ (existsMany 3 E) := of_eq
    (by simp only [ForcingPreorderInstances.targetExists, ForcingPreorderInstances.targetBody, three_map]; rfl) hTarget
  apply HornBinderRules.eliminate_many 3 E _ hTargetExact
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h3 := h.in_body (l := 3) E
  have hOldQuery := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h3.source)))))
  have hNewQuery := Derives.conjL (.conjR hE)
  have hWeak := ForcingWeakenedImages.from_queries h3.zf
    (old 3 w) (old 3 z) (old 3 f) (old 3 z) (old 3 b) (old 3 B) (old 3 R) (old 3 S)
    (old 3 (raw 0)) (old 3 Pre) (slot 3 0) (fun i => old 3 (v i)) (.conjI h3.base (.conjI hOldQuery hNewQuery))
  have hr3 := of_eq (SyntaxVariableSyntax.code_rename false w z r (old 3)) (HornBinderRules.under_body 3 hr E)
  have hrt3 := of_eq (SyntaxTermSyntax.term_rename w z B r (old 3)) (HornBinderRules.under_body 3 hrt E)
  have hq3 := of_eq (SyntaxRenameTermSyntax.renamed_rename w (v 2) (v 3) z b z B q qn (old 3)) (HornBinderRules.under_body 3 hq E)
  have hp3 := of_eq (SyntaxRenameTermSyntax.renamed_rename w (v 2) (v 3) z b z B p pn (old 3)) (HornBinderRules.under_body 3 hp E)
  let x : Fin 6 → Fin (m+3) := Fin.cases (old 3 r) (Fin.cases (old 3 qn) (Fin.cases (old 3 pn) (slot 3)))
  have hd : Derives Δ (data test Reln (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f)
      (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S) (old 3 q) (old 3 p) (old 3 Pre)
      (fun i => old 3 (raw i)) (fun i => old 3 (v i)) x) :=
    .conjI h3.source (.conjI hr3 (.conjI hrt3 (.conjI hq3 (.conjI hp3 (.conjI hE hWeak)))))
  have ho : Derives Δ (produced test Reln (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f)
      (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 S) (old 3 q) (old 3 p) (old 3 Pre)
      (fun i => old 3 (raw i)) (fun i => old 3 (v i))) := by
    apply HornBinderRules.intro_many 6 _ x
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b A B R S q p Pre raw v (old 3)).symm ho

private theorem at_q {k m} {Γ : Context m} (test : Formula 1) {Reln : Source.Formula (k+2)}
    {w z A1 A2 A3 f b A B R S q p Pre : Fin m} {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m}
    (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) (r qn : Fin m)
    (hr : Derives Γ (SyntaxVariableSyntax.code false w z r)) (hrt : Derives Γ (SyntaxTermSyntax.term w z B r))
    (hq : Derives Γ (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B q qn)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v) := by
  have hpTy := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.source)))))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxRenameTermSyntax.renamed w.castSucc (v 2).castSucc (v 3).castSucc z.castSucc b.castSucc z.castSucc B.castSucc p.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxRenameTermExistence.for_term h.zf w (v 2) (v 3) z b z B p h.omega h.maps hpTy)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body (l := 1) E
  have ho := at_terms test h1 r.castSucc qn.castSucc (Fin.last m)
    (of_eq (SyntaxVariableSyntax.code_rename false w z r Fin.castSucc) (under hr E))
    (of_eq (SyntaxTermSyntax.term_rename w z B r Fin.castSucc) (under hrt E))
    (of_eq (SyntaxRenameTermSyntax.renamed_rename w (v 2) (v 3) z b z B q qn Fin.castSucc) (under hq E)) (.conjR hE)
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b A B R S q p Pre raw v Fin.castSucc).symm ho

private theorem at_r {k m} {Γ : Context m} (test : Formula 1) {Reln : Source.Formula (k+2)}
    {w z A1 A2 A3 f b A B R S q p Pre : Fin m} {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m}
    (h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v) (r : Fin m)
    (hr : Derives Γ (SyntaxVariableSyntax.code false w z r)) (hrt : Derives Γ (SyntaxTermSyntax.term w z B r)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v) := by
  have hqTy := Derives.conjL (.conjR (.conjR (.conjR (.conjR h.source))))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxRenameTermSyntax.renamed w.castSucc (v 2).castSucc (v 3).castSucc z.castSucc b.castSucc z.castSucc B.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxRenameTermExistence.for_term h.zf w (v 2) (v 3) z b z B q h.omega h.maps hqTy)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body (l := 1) E
  have ho := at_q test h1 r.castSucc (Fin.last m)
    (of_eq (SyntaxVariableSyntax.code_rename false w z r Fin.castSucc) (under hr E))
    (of_eq (SyntaxTermSyntax.term_rename w z B r Fin.castSucc) (under hrt E)) (.conjR hE)
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b A B R S q p Pre raw v Fin.castSucc).symm ho

/-- No chosen fresh terms, new Pre output or desired weak relation is an
input. Generate original free0 r and actual q/p rename outputs, and consume
the unchanged original same-raw target producer including all3 instances. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b A B R S q p Pre : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v) := by
  have h : Inputs Γ Reln w z A1 A2 A3 f b A B R S q p Pre raw v := ⟨hZ,hi⟩
  have hContexts := SyntaxIndexMapSyntax.target_contexts w (v 2) (v 3) z b z B h.maps
  have hb := Derives.conjR (SyntaxIndexMapSyntax.source_contexts w (v 2) (v 3) z b z B h.maps)
  have hB := Derives.conjL (.conjR (.conjL h.base))
  have hzB := SyntaxIndexLiftOrder.zero_member hZ w b B z h.omega hb hB (.conjL hi)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    ((SyntaxVariableSyntax.code false w.castSucc z.castSucc (Fin.last m)).conj
      (SyntaxTermSyntax.term w.castSucc z.castSucc B.castSucc (Fin.last m)))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxTerms.exists_at hZ false w z B z h.omega (.conjI hContexts hzB))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body (l := 1) E
  have ho := at_r test h1 (Fin.last m) (.conjL (.conjR hE)) (.conjR (.conjR hE))
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b A B R S q p Pre raw v Fin.castSucc).symm ho

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Source.Sentence :=
  ((input Reln w z A1 A2 A3 f b A B R S q p Pre raw v).imp
    (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)).close
theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z A1 A2 A3 f b A B R S q p Pre raw v (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingFreshPreorder
