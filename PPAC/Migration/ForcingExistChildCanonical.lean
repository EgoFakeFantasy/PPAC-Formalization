import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.Internal.SyntaxCodedMixedBinderUnique
import PPAC.Migration.Internal.StructuralListCodeInduction

/-! Pinned Force.ex: the canonical child environment keeps name0 and puts
the inner condition at bound1. Updating the external p-slot first does not
change this canonical environment or its full formula output. All replacement
tables, binder outputs and formula outputs are produced in OBJECT EX.
The existing raw-child/opening triangle and full raw-tail comparison remain
separate obligations; this file does not claim them or final Con. -/
namespace PPAC.Migration.ForcingExistChildCanonical
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingReflexiveImages (replacement replacement_rename)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMixedImageCodeSyntax (termList termList_rename termLists termLists_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem forward_field {m} {Γ : Context m}
    (w f c T S j p q M U head D E i y : Fin m)
    (hp : Derives Γ (replacement w f c T S j p M))
    (hq : Derives Γ (replacement w f c T S j q U))
    (hd : Derives Γ (replacement w f c T M j head D))
    (he : Derives Γ (replacement w f c T U j head E))
    (hi : Derives Γ (.mem i f)) : Derives Γ ((field w D i y).imp (field w E i y)) := by
  have hM := ForcingReflexiveImages.field_iff w f c T S j p M i y hp hi
  have hU := ForcingReflexiveImages.field_iff w f c T S j q U i y hq hi
  have hD := ForcingReflexiveImages.field_iff w f c T M j head D i y hd hi
  have hE := ForcingReflexiveImages.field_iff w f c T U j head E i y he hi
  apply Derives.impI
  let F := field w D i y
  have hF : Derives (Context.add F Γ) F := .hyp (Or.inl rfl)
  apply Derives.disjE (.impE (add (.conjL hD) F) hF)
  · exact .impE (add (add (.conjR hE) F) _) (.disjL (.hyp (Or.inl rfl)))
  · let A := (Formula.equal i j).neg.conj (field w M i y)
    have hA : Derives (Context.add A (Context.add F Γ)) A := .hyp (Or.inl rfl)
    apply Derives.disjE (.impE (add (add (.conjL hM) F) A) (.conjR hA))
    · exact .botE (.impE (add (.conjL hA) _) (.conjL (.hyp (Or.inl rfl))))
    · let B := (Formula.equal i j).neg.conj (field w S i y)
      have hB : Derives (Context.add B (Context.add A (Context.add F Γ))) B := .hyp (Or.inl rfl)
      have hOther := Derives.impE (add (add (add (.conjR hU) F) A) B) (.disjR hB)
      exact .impE (add (add (add (.conjR hE) F) A) B) (.disjR (.conjI (.conjL hB) hOther))

/-- Two ACTUAL outer-condition updates followed by the SAME inner-condition
overwrite have equal final lists, on ALL internal indices and list codes. -/
theorem overwrite {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w f c T S j p q M U head D E : Fin m)
    (hw : Derives Γ (omega w))
    (hp : Derives Γ (replacement w f c T S j p M))
    (hq : Derives Γ (replacement w f c T S j q U))
    (hd : Derives Γ (replacement w f c T M j head D))
    (he : Derives Γ (replacement w f c T U j head E)) : Derives Γ (.equal D E) := by
  have htD := ForcingReflexiveImages.target_type w f c T M j head D hd
  have htE := ForcingReflexiveImages.target_type w f c T U j head E he
  have ha : Derives Γ (StructuralListCodeSyntax.agree w f D E) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let B := Formula.mem (Fin.last m).castSucc f.castSucc.castSucc
    let Δ := Context.add B (raisedContext 2 Γ)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hp2 := of_eq (replacement_rename w f c T S j p M (old 2)) (HornBinderRules.under_body 2 hp B)
    have hq2 := of_eq (replacement_rename w f c T S j q U (old 2)) (HornBinderRules.under_body 2 hq B)
    have hd2 := of_eq (replacement_rename w f c T M j head D (old 2)) (HornBinderRules.under_body 2 hd B)
    have he2 := of_eq (replacement_rename w f c T U j head E (old 2)) (HornBinderRules.under_body 2 he B)
    exact .conjI
      (forward_field (old 2 w) (old 2 f) (old 2 c) (old 2 T) (old 2 S) (old 2 j) (old 2 p) (old 2 q)
        (old 2 M) (old 2 U) (old 2 head) (old 2 D) (old 2 E) (Fin.last m).castSucc (Fin.last (m+1)) hp2 hq2 hd2 he2 hB)
      (forward_field (old 2 w) (old 2 f) (old 2 c) (old 2 T) (old 2 S) (old 2 j) (old 2 q) (old 2 p)
        (old 2 U) (old 2 M) (old 2 head) (old 2 E) (old 2 D) (Fin.last m).castSucc (Fin.last (m+1)) hq2 hp2 he2 hd2 hB)
  exact StructuralListCodeInduction.unique hZ w f D E hw
    (.conjR (.conjL (.conjR (.conjR htD)))) (.conjR (.conjL (.conjR (.conjR htE)))) ha

def oneData {m} (w a A c C f T R M j head N : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (replacement w f c T M j head (v 0)).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w R (v 0) a f c T A C (v 1) (v 2)).conj
      (substituted w (v 1) (v 2) A f C T N (v 3)))

theorem oneData_rename {m l} (w a A c C f T R M j head N : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (oneData w a A c C f T R M j head N v).rename r =
      oneData (r w) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r j) (r head) (r N) (fun i => r (v i)) := by
  simp only [oneData, Formula.rename, replacement_rename, SyntaxCodedMixedBinderSyntax.lifted_rename, substituted_rename]

/-- Compare two complete canonical child executions. No output equality,
canonical table, or formula-operation answer is assumed. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A c C f T R S j p q M U head N : Fin m) (v u : Fin 4 → Fin m)
    (hw : Derives Γ (omega w))
    (hp : Derives Γ (replacement w f c T S j p M)) (hq : Derives Γ (replacement w f c T S j q U))
    (hv : Derives Γ (oneData w a A c C f T R M j head N v))
    (hu : Derives Γ (oneData w a A c C f T R U j head N u)) : Derives Γ (.equal (v 3) (u 3)) := by
  have he := overwrite hZ w f c T S j p q M U head (v 0) (u 0) hw hp hq (.conjL hv) (.conjL hu)
  let P := SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc (Fin.last m) a.castSucc f.castSucc
    c.castSucc T.castSucc A.castSucc C.castSucc (v 1).castSucc (v 2).castSucc
  have hLift : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R (u 0) a f c T A C (v 1) (v 2)) := by
    exact of_eq (by simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR hv))))
  have hEq := SyntaxCodedMixedBinderUnique.unique_pair hZ w R (u 0) a f c T A C (v 1) (v 2) (u 1) (u 2)
    hw hLift (.conjL (.conjR hu))
  let B := substituted w.castSucc (Fin.last m) (v 2).castSucc A.castSucc f.castSucc C.castSucc T.castSucc N.castSucc (v 3).castSucc
  have hSub : Derives Γ (substituted w (u 1) (v 2) A f C T N (v 3)) := by
    exact of_eq (by simp only [B, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst B (.conjL hEq) (of_eq (by simp only [B, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR (.conjR hv))))
  let F := substituted w.castSucc (u 1).castSucc (Fin.last m) A.castSucc f.castSucc C.castSucc T.castSucc N.castSucc (v 3).castSucc
  have hSub2 : Derives Γ (substituted w (u 1) (u 2) A f C T N (v 3)) := by
    exact of_eq (by simp only [F, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst F (.conjR hEq) (of_eq (by simp only [F, Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hSub))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (u 1) (u 2) A f C T N (v 3) (u 3) hw hSub2 (.conjR (.conjR hu))

private def oneInput {m} (w a A c C f T R M _j head N : Fin m) : Formula m :=
  (omega w).conj ((termLists w a f c T R M).conj ((successor A a).conj
    ((successor C c).conj ((SyntaxTermSyntax.term w c T head).conj (FormulaCodeSyntax.formulaCode w N A f)))))

private theorem oneInput_rename {m l} (w a A c C f T R M j head N : Fin m) (r : Fin m → Fin l) :
    (oneInput w a A c C f T R M j head N).rename r =
      oneInput (r w) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r j) (r head) (r N) := by
  simp only [oneInput, Formula.rename, omega_rename, termLists_rename, successor_rename,
    SyntaxTermSyntax.term_rename, FormulaCodeSyntax.formulaCode_rename]

private def oneBody {m} (w a A c C f T R M j head N : Fin m) : Formula (m+4) :=
  oneData (old 4 w) (old 4 a) (old 4 A) (old 4 c) (old 4 C) (old 4 f) (old 4 T)
    (old 4 R) (old 4 M) (old 4 j) (old 4 head) (old 4 N) (slot 4)
private def oneResult {m} (w a A c C f T R M j head N : Fin m) : Formula m :=
  existsMany 4 (oneBody w a A c C f T R M j head N)
private theorem oneResult_rename {m l} (w a A c C f T R M j head N : Fin m) (r : Fin m → Fin l) :
    (oneResult w a A c C f T R M j head N).rename r =
      oneResult (r w) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r j) (r head) (r N) := by
  simp only [oneResult, existsMany_rename, oneBody, oneData_rename, lift_old, lift_slot]

/-- Existing replacement, existing binder producer, existing whole formula
producer; all four returned values are OBJECT witnesses. -/
private theorem one_derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A c C f T R M j head N : Fin m) (hi : Derives Γ (oneInput w a A c C f T R M j head N)) :
    Derives Γ (oneResult w a A c C f T R M j head N) := by
  have hw := Derives.conjL hi
  have hLists := Derives.conjL (.conjR hi)
  have hHead := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  let X := replacement w.castSucc f.castSucc c.castSucc T.castSucc M.castSucc j.castSucc head.castSucc (Fin.last m)
  let Δ1 := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (ForcingReflexiveImages.exists_replacement hZ w f c T M j head hw (.conjR hLists) hHead)
  have hX : Derives Δ1 X := .hyp (Or.inl rfl)
  have hi1 := of_eq (oneInput_rename w a A c C f T R M j head N Fin.castSucc) (under hi X)
  have hZ1 := ZFContext.under hZ X
  have hw1 := Derives.conjL hi1
  have hType := ForcingReflexiveImages.target_type w.castSucc f.castSucc c.castSucc T.castSucc M.castSucc j.castSucc head.castSucc (Fin.last m) hX
  have hb : Derives Δ1 (SyntaxCodedMixedBinderSyntax.existsPair w.castSucc R.castSucc (Fin.last m)
      a.castSucc f.castSucc c.castSucc T.castSucc A.castSucc C.castSucc) :=
    SyntaxCodedMixedBinderExistence.exists_pair hZ1 _ _ _ _ _ _ _ _ _ hw1
      (.conjI (.conjI (.conjL (.conjL (.conjR hi1))) hType)
        (.conjI (.conjL (.conjR (.conjR hi1))) (.conjL (.conjR (.conjR (.conjR hi1))))))
  let B := SyntaxCodedMixedBinderSyntax.lifted (old 3 w) (old 3 R) (old 2 (Fin.last m))
    (old 3 a) (old 3 f) (old 3 c) (old 3 T) (old 3 A) (old 3 C) (slot 2 0) (slot 2 1)
  let Δ2 := Context.add B (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 B _ hb
  have hB : Derives Δ2 B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 B
  have hi2 : Derives Δ2 (oneInput (old 3 w) (old 3 a) (old 3 A) (old 3 c) (old 3 C) (old 3 f) (old 3 T)
      (old 3 R) (old 3 M) (old 3 j) (old 3 head) (old 3 N)) :=
    of_eq (by simp only [oneInput_rename]; rfl) (HornBinderRules.under_body 2 hi1 B)
  have hw2 := Derives.conjL hi2
  have hN := Derives.conjR (.conjR (.conjR (.conjR (.conjR hi2))))
  have hOut := SyntaxCodedMixedBinderTyping.output_lists (old 3 w) (old 3 R) (old 2 (Fin.last m))
    (old 3 a) (old 3 f) (old 3 c) (old 3 T) (old 3 A) (old 3 C) (slot 2 0) (slot 2 1) hB
  let Y := substituted (old 4 w) (old 1 (slot 2 0)) (old 1 (slot 2 1)) (old 4 A) (old 4 f)
    (old 4 C) (old 4 T) (old 4 N) (Fin.last (m+3))
  let Δ3 := Context.add Y (Context.image Formula.raise Δ2)
  apply Derives.exE (p := Y) (SyntaxMixedFormulaOutputInduction.actual_exists hZ2 (old 3 w)
    (slot 2 0) (slot 2 1) (old 3 A) (old 3 f) (old 3 C) (old 3 T) (old 3 N) hw2 (.conjI hN hOut))
  have hY : Derives Δ3 Y := .hyp (Or.inl rfl)
  have hX2 : Derives Δ2 (replacement (old 3 w) (old 3 f) (old 3 c) (old 3 T) (old 3 M) (old 3 j) (old 3 head) (old 2 (Fin.last m))) :=
    of_eq (by simp only [X, replacement_rename]; rfl) (HornBinderRules.under_body 2 hX B)
  have hX3 := of_eq (replacement_rename (old 3 w) (old 3 f) (old 3 c) (old 3 T) (old 3 M) (old 3 j) (old 3 head)
    (old 2 (Fin.last m)) Fin.castSucc) (under hX2 Y)
  have hB3 := of_eq (by simp only [B, Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]; rfl) (under hB Y)
  let vals : Fin 4 → Fin (m+4) := Fin.cases (old 3 (Fin.last m))
    (Fin.cases (old 1 (slot 2 0)) (Fin.cases (old 1 (slot 2 1)) (fun _ => Fin.last (m+3))))
  have ho : Derives Δ3 (oneResult (old 4 w) (old 4 a) (old 4 A) (old 4 c) (old 4 C) (old 4 f) (old 4 T)
      (old 4 R) (old 4 M) (old 4 j) (old 4 head) (old 4 N)) := by
    apply HornBinderRules.intro_many 4 _ vals
    exact of_eq (by simp only [oneBody, oneData_rename, assign_old, assign_slot]; rfl)
      (.conjI hX3 (.conjI hB3 hY))
  exact of_eq (by simp only [oneResult_rename]; rfl) ho

private def left {m} (v : Fin 8 → Fin m) : Fin 4 → Fin m := fun i => v i.castSucc.castSucc.castSucc.castSucc
private def right {m} (v : Fin 8 → Fin m) : Fin 4 → Fin m := fun i => v i.succ.succ.succ.succ

private def agreementBody {m} (w a A c C f T R M U j head N : Fin m) : Formula (m+8) :=
  ((oneData (old 8 w) (old 8 a) (old 8 A) (old 8 c) (old 8 C) (old 8 f) (old 8 T) (old 8 R) (old 8 M)
    (old 8 j) (old 8 head) (old 8 N) (left (slot 8))).conj
   (oneData (old 8 w) (old 8 a) (old 8 A) (old 8 c) (old 8 C) (old 8 f) (old 8 T) (old 8 R) (old 8 U)
    (old 8 j) (old 8 head) (old 8 N) (right (slot 8)))).imp (.equal (slot 8 3) (slot 8 7))

def agreement {m} (w a A c C f T R M U j head N : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 8 (agreementBody w a A c C f T R M U j head N)

theorem agreement_rename {m l} (w a A c C f T R M U j head N : Fin m) (r : Fin m → Fin l) :
    (agreement w a A c C f T R M U j head N).rename r =
      agreement (r w) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r U) (r j) (r head) (r N) := by
  simp only [agreement, OriginalUniversalBlock.allMany_rename, agreementBody, Formula.rename,
    oneData_rename, left, right, lift_old, lift_slot]
  rfl

theorem at_agreement {m} {Γ : Context m} (w a A c C f T R M U j head N : Fin m) (v : Fin 8 → Fin m)
    (ha : Derives Γ (agreement w a A c C f T R M U j head N))
    (hv : Derives Γ (oneData w a A c C f T R M j head N (left v)))
    (hu : Derives Γ (oneData w a A c C f T R U j head N (right v))) : Derives Γ (.equal (v 3) (v 7)) := by
  have hp := OriginalUniversalBlock.at_many 8 (agreementBody w a A c C f T R M U j head N) v ha
  have he : Derives Γ (((oneData w a A c C f T R M j head N (left v)).conj
      (oneData w a A c C f T R U j head N (right v))).imp (.equal (v 3) (v 7))) :=
    of_eq (by simp only [agreementBody, Formula.rename, oneData_rename, left, right, assign_old, assign_slot]; rfl) hp
  exact .impE he (.conjI hv hu)

private theorem agreement_derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A c C f T R S j p q M U head N : Fin m) (hw : Derives Γ (omega w))
    (hp : Derives Γ (replacement w f c T S j p M)) (hq : Derives Γ (replacement w f c T S j q U)) :
    Derives Γ (agreement w a A c C f T R M U j head N) := by
  apply OriginalUniversalBlock.intro_many 8
  apply Derives.impI
  let E := (oneData (old 8 w) (old 8 a) (old 8 A) (old 8 c) (old 8 C) (old 8 f) (old 8 T) (old 8 R) (old 8 M)
    (old 8 j) (old 8 head) (old 8 N) (left (slot 8))).conj
    (oneData (old 8 w) (old 8 a) (old 8 A) (old 8 c) (old 8 C) (old 8 f) (old 8 T) (old 8 R) (old 8 U)
    (old 8 j) (old 8 head) (old 8 N) (right (slot 8)))
  have h : Derives (Context.add E (raisedContext 8 Γ)) E := .hyp (Or.inl rfl)
  exact formula (HornBinderRules.zf_body 8 hZ E) (old 8 w) (old 8 a) (old 8 A) (old 8 c) (old 8 C)
    (old 8 f) (old 8 T) (old 8 R) (old 8 S) (old 8 j) (old 8 p) (old 8 q) (old 8 M) (old 8 U)
    (old 8 head) (old 8 N) (left (slot 8)) (right (slot 8))
    (of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw E))
    (of_eq (replacement_rename w f c T S j p M (old 8)) (HornBinderRules.under_body 8 hp E))
    (of_eq (replacement_rename w f c T S j q U (old 8)) (HornBinderRules.under_body 8 hq E))
    (.conjL h) (.conjR h)

/-- One common inner-condition code, two actual four-witness executions,
and an OBJECT-universal equality guarantee for all candidate executions. -/
def data {m} (w z a A c C f T R M U j N head : Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w c T z head).conj
    ((oneResult w a A c C f T R M j head N).conj
      ((oneResult w a A c C f T R U j head N).conj
        (agreement w a A c C f T R M U j head N)))

theorem data_rename {m l} (w z a A c C f T R M U j N head : Fin m) (r : Fin m → Fin l) :
    (data w z a A c C f T R M U j N head).rename r =
      data (r w) (r z) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r U) (r j) (r N) (r head) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, oneResult_rename, agreement_rename]

def result {m} (w z a A c C f T R M U j N : Fin m) : Formula m := .ex
  (data w.castSucc z.castSucc a.castSucc A.castSucc c.castSucc C.castSucc f.castSucc T.castSucc
    R.castSucc M.castSucc U.castSucc j.castSucc N.castSucc (Fin.last m))

theorem result_rename {m l} (w z a A c C f T R M U j N : Fin m) (r : Fin m → Fin l) :
    (result w z a A c C f T R M U j N).rename r =
      result (r w) (r z) (r a) (r A) (r c) (r C) (r f) (r T) (r R) (r M) (r U) (r j) (r N) := by
  simp only [result, Formula.rename, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def input {m} (w z b c C a A f T R S p q M U j N : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((Formula.mem b w).conj ((successor c b).conj
    ((successor C c).conj ((successor A a).conj ((termLists w a f c T R S).conj
      ((replacement w f c T S j p M).conj ((replacement w f c T S j q U).conj
        (FormulaCodeSyntax.formulaCode w N A f)))))))))

private theorem input_rename {m l} (w z b c C a A f T R S p q M U j N : Fin m) (r : Fin m → Fin l) :
    (input w z b c C a A f T R S p q M U j N).rename r =
      input (r w) (r z) (r b) (r c) (r C) (r a) (r A) (r f) (r T) (r R) (r S) (r p) (r q) (r M) (r U) (r j) (r N) := by
  simp only [input, Formula.rename, omega_rename, empty_rename, successor_rename, termLists_rename,
    replacement_rename, FormulaCodeSyntax.formulaCode_rename]

theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b c C a A f T R S p q M U j N : Fin m)
    (hi : Derives Γ (input w z b c C a A f T R S p q M U j N)) :
    Derives Γ (result w z a A c C f T R M U j N) := by
  have h0 := Derives.conjL (hi)
  have h1 := Derives.conjL (Derives.conjR (hi))
  have h2 := Derives.conjL (Derives.conjR (Derives.conjR (hi)))
  have h3 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hi))))
  have h6 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi)))))))
  have hT := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjL h6)))
  let H := SyntaxMixedImageHead.head w.castSucc c.castSucc T.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) (SyntaxMixedImageHead.code_exists hZ w b c T z h0 h2 hT h3 h1)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ H
  have hi1 := of_eq (input_rename w z b c C a A f T R S p q M U j N Fin.castSucc) (under hi H)
  have f0 := Derives.conjL (hi1)
  have f4 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1)))))
  have f5 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1))))))
  have f6 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1)))))))
  have f7 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1))))))))
  have f8 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1)))))))))
  have f9 := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hi1)))))))))
  have hM := ForcingReflexiveImages.target_type w.castSucc f.castSucc c.castSucc T.castSucc S.castSucc j.castSucc p.castSucc M.castSucc f7
  have hU := ForcingReflexiveImages.target_type w.castSucc f.castSucc c.castSucc T.castSucc S.castSucc j.castSucc q.castSucc U.castSucc f8
  have hv := one_derive hZ1 w.castSucc a.castSucc A.castSucc c.castSucc C.castSucc f.castSucc T.castSucc R.castSucc M.castSucc j.castSucc (Fin.last m) N.castSucc
    (.conjI f0 (.conjI (.conjI (.conjL f6) hM) (.conjI f5 (.conjI f4 (.conjI (.conjR (.conjR hH)) f9)))))
  have hu := one_derive hZ1 w.castSucc a.castSucc A.castSucc c.castSucc C.castSucc f.castSucc T.castSucc R.castSucc U.castSucc j.castSucc (Fin.last m) N.castSucc
    (.conjI f0 (.conjI (.conjI (.conjL f6) hU) (.conjI f5 (.conjI f4 (.conjI (.conjR (.conjR hH)) f9)))))
  have ha := agreement_derive hZ1 w.castSucc a.castSucc A.castSucc c.castSucc C.castSucc f.castSucc T.castSucc R.castSucc S.castSucc
    j.castSucc p.castSucc q.castSucc M.castSucc U.castSucc (Fin.last m) N.castSucc f0 f7 f8
  have ho : Derives Δ (result w.castSucc z.castSucc a.castSucc A.castSucc c.castSucc C.castSucc f.castSucc T.castSucc
      R.castSucc M.castSucc U.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, data_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI hH (.conjI hv (.conjI hu ha)))
  exact of_eq (result_rename w z a A c C f T R M U j N Fin.castSucc).symm ho

def sentence {m} (w z b c C a A f T R S p q M U j N : Fin m) : Source.Sentence :=
  ((input w z b c C a A f T R S p q M U j N).imp (result w z a A c C f T R M U j N)).close

theorem kernel_certificate {m} (w z b c C a A f T R S p q M U j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z b c C a A f T R S p q M U j N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w z b c C a A f T R S p q M U j N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) w z b c C a A f T R S p q M U j N (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingExistChildCanonical
