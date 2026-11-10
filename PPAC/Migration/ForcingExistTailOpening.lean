import PPAC.Migration.ForcingExistCode
import PPAC.Migration.ForcingMixedUnary
import PPAC.Migration.ForcingFormulaDiagram

/-! Read the WHOLE literal original existential tail at an ACTUAL mixed output.
Both EX binder lifts and all three AND outputs are object witnesses. The source
is the pinned ForcingExistCode.shellData, not a replacement compiler. This reader
does not assert cross-condition equality or final internal consistency. -/
namespace PPAC.Migration.ForcingExistTailOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open SyntaxCodedMixedBinderSyntax (lifted lifted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def openedData {m} (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (singleCode 10 w (v 0) Q).conj
    ((lifted w R S a f c T (v 1) (v 2) (v 3) (v 4)).conj
      (substituted w (v 3) (v 4) (v 1) f (v 2) T x (v 0)))

theorem openedData_rename {m l} (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (openedData w R S a f c T x Q v).rename ρ =
      openedData (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) (fun i => ρ (v i)) := by
  simp only [openedData, Formula.rename, singleCode_rename, lifted_rename, substituted_rename]

def openedBody {m} (w R S a f c T x Q : Fin m) : Formula (m+5) :=
  openedData (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q) (slot 5)
def opened {m} (w R S a f c T x Q : Fin m) : Formula m :=
  existsMany 5 (openedBody w R S a f c T x Q)

theorem opened_rename {m l} (w R S a f c T x Q : Fin m) (ρ : Fin m → Fin l) :
    (opened w R S a f c T x Q).rename ρ =
      opened (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) := by
  simp only [opened, openedBody, existsMany_rename, openedData_rename, lift_old, lift_slot]

/-- The original unary reader and its original four lifted-environment
witnesses, packed together without prescribing any of their values. -/
theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a f c T n x Q : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (singleCode 10 w x n))
    (hq : Derives Γ (substituted w R S a f c T n Q)) :
    Derives Γ (opened w R S a f c T x Q) := by
  have ho := ForcingMixedUnary.single_output hZ 10 true (.inr (.inr ⟨rfl, rfl⟩)) w R S a f c T n x Q hw hc hq
  let E := (singleCode 10 w.castSucc (Fin.last m) Q.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc f.castSucc c.castSucc T.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) ho
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let B := SyntaxMixedFormulaRecursiveSyntax.advancedBody w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc f.castSucc c.castSucc T.castSucc (Fin.last m)
  let Ξ := Context.add B (raisedContext 4 Δ)
  have hb : Derives Δ (existsMany 4 B) := .conjR hE
  apply HornBinderRules.eliminate_many 4 B _ hb
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have he := of_eq (by simp only [E, Formula.rename, singleCode_rename, SyntaxMixedFormulaRecursiveSyntax.check_rename]; rfl)
    (HornBinderRules.under_body 4 hE B)
  let v : Fin 5 → Fin (m+1+4) := Fin.cases (old 4 (Fin.last m))
    (Fin.cases (slot 4 0) (Fin.cases (slot 4 1) (Fin.cases (slot 4 2) (Fin.cases (slot 4 3) Fin.elim0))))
  have hd : Derives Ξ (openedData (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q) v) :=
    .conjI (.conjL he) hB
  have hout : Derives Ξ (opened (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q)) := by
    apply HornBinderRules.intro_many 5 _ v
    exact of_eq (by simp only [openedBody, openedData_rename, assign_old, assign_slot]) hd
  exact of_eq (by simp only [Formula.raise, opened_rename]; rfl) hout

/-- Source codes: tail, r-body, r-rest, EX-name, name-body, domain,
child, inner-member, inner-order. This is exactly the original shell. -/
def source {m} (w : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  (singleCode 10 w (s 1) (s 0)).conj
    ((binaryCode 0 w (s 7) (s 2) (s 1)).conj
      ((binaryCode 0 w (s 8) (s 3) (s 2)).conj
        ((singleCode 10 w (s 4) (s 3)).conj (binaryCode 0 w (s 5) (s 6) (s 4)))))

theorem source_rename {m l} (w : Fin m) (s : Fin 9 → Fin m) (ρ : Fin m → Fin l) :
    (source w s).rename ρ = source (ρ w) (fun i => ρ (s i)) := by
  simp only [source, Formula.rename, singleCode_rename, binaryCode_rename]

/-- Sixteen actual object values, in execution order. The five records
retain BOTH real binder lifts, all leaf queries and all target constructors. -/
def data {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (openedData w R S a f c T (s 1) Q (fun i => v (⟨i.val, by omega⟩))).conj
    ((ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 7) (s 2) (v 0) (v 5) (v 6)).conj
      ((ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 8) (s 3) (v 6) (v 7) (v 8)).conj
        ((openedData w (v 3) (v 4) (v 1) f (v 2) T (s 4) (v 8)
          (fun i => v (⟨9 + i.val, by omega⟩))).conj
          (ForcingFormulaDiagram.binaryData 0 w (v 12) (v 13) (v 10) f (v 11) T (s 5) (s 6) (v 9) (v 14) (v 15)))))

theorem data_rename {m l} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) (v : Fin 16 → Fin m) (ρ : Fin m → Fin l) :
    (data w R S a f c T Q s v).rename ρ =
      data (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ Q) (fun i => ρ (s i)) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, openedData_rename, ForcingFormulaDiagram.binaryData_rename]

def body {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) : Formula (m+16) :=
  data (old 16 w) (old 16 R) (old 16 S) (old 16 a) (old 16 f) (old 16 c) (old 16 T) (old 16 Q) (fun i => old 16 (s i)) (slot 16)
def result {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  existsMany 16 (body w R S a f c T Q s)

theorem result_rename {m l} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) (ρ : Fin m → Fin l) :
    (result w R S a f c T Q s).rename ρ =
      result (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ Q) (fun i => ρ (s i)) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

private structure Inputs {m} (Γ : Context m) (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hw : Derives Γ (omega w)
  hs : Derives Γ (source w s)
  hq : Derives Γ (substituted w R S a f c T (s 0) Q)

private theorem Inputs.in_body {m t} {Γ : Context m} {w R S a f c T Q : Fin m} {s : Fin 9 → Fin m}
    (h : Inputs Γ w R S a f c T Q s) (E : Formula (m+t)) :
    Inputs (Context.add E (raisedContext t Γ)) (old t w) (old t R) (old t S) (old t a)
      (old t f) (old t c) (old t T) (old t Q) (fun i => old t (s i)) :=
  ⟨HornBinderRules.zf_body t h.zf E,
    of_eq (omega_rename w (old t)) (HornBinderRules.under_body t h.hw E),
    of_eq (source_rename w s (old t)) (HornBinderRules.under_body t h.hs E),
    of_eq (substituted_rename w R S a f c T (s 0) Q (old t)) (HornBinderRules.under_body t h.hq E)⟩

private theorem stage4 {m} {Γ : Context m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (h : Inputs Γ w R S a f c T Q s) (v : Fin 14 → Fin m)
    (p0 : Derives Γ (openedData w R S a f c T (s 1) Q (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4) Fin.elim0)))))))
    (p1 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 7) (s 2) (v 0) (v 5) (v 6)))
    (p2 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 8) (s 3) (v 6) (v 7) (v 8)))
    (p3 : Derives Γ (openedData w (v 3) (v 4) (v 1) f (v 2) T (s 4) (v 8) (Fin.cases (v 9) (Fin.cases (v 10) (Fin.cases (v 11) (Fin.cases (v 12) (Fin.cases (v 13) Fin.elim0))))))) :
    Derives Γ (result w R S a f c T Q s) := by
  have he := ForcingFormulaDiagram.binary_output h.zf 0 w (v 12) (v 13) (v 10) f (v 11) T (s 4) (s 5) (s 6) (v 9) h.hw (.conjR (.conjR (.conjR (.conjR h.hs)))) (.conjR (.conjR p3))
  let E := ForcingFormulaDiagram.binaryBody 0 w (v 12) (v 13) (v 10) f (v 11) T (s 5) (s 6) (v 9)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h' := h.in_body E
  let u : Fin 16 → Fin (m+2) := fun i => Fin.addCases (m := 14) (n := 2) (motive := fun _ => Fin (m+2)) (fun j => old 2 (v j)) (slot 2) i
  have q0 : Derives Δ (openedData (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 (s 1)) (old 2 Q) (Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 2) (Fin.cases (u 3) (Fin.cases (u 4) Fin.elim0)))))) :=
    of_eq (by simp only [openedData_rename]; rfl)
      (HornBinderRules.under_body 2 p0 E)
  have q1 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 7)) (old 2 (s 2)) (u 0) (u 5) (u 6)) :=
    of_eq (by simp only [ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 2 p1 E)
  have q2 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 8)) (old 2 (s 3)) (u 6) (u 7) (u 8)) :=
    of_eq (by simp only [ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 2 p2 E)
  have q3 : Derives Δ (openedData (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 4)) (u 8) (Fin.cases (u 9) (Fin.cases (u 10) (Fin.cases (u 11) (Fin.cases (u 12) (Fin.cases (u 13) Fin.elim0)))))) :=
    of_eq (by simp only [openedData_rename]; rfl)
      (HornBinderRules.under_body 2 p3 E)
  have q4 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 12) (u 13) (u 10) (old 2 f) (u 11) (old 2 T) (old 2 (s 5)) (old 2 (s 6)) (u 9) (u 14) (u 15)) := hE
  have hd : Derives Δ (data (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 Q) (fun i => old 2 (s i)) u) :=
    .conjI q0 (.conjI q1 (.conjI q2 (.conjI q3 q4)))
  have hout : Derives Δ (result (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 Q) (fun i => old 2 (s i))) := by
    apply HornBinderRules.intro_many 16 _ u
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (result_rename w R S a f c T Q s (old 2)).symm hout

private theorem stage3 {m} {Γ : Context m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (h : Inputs Γ w R S a f c T Q s) (v : Fin 9 → Fin m)
    (p0 : Derives Γ (openedData w R S a f c T (s 1) Q (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4) Fin.elim0)))))))
    (p1 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 7) (s 2) (v 0) (v 5) (v 6)))
    (p2 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 8) (s 3) (v 6) (v 7) (v 8))) :
    Derives Γ (result w R S a f c T Q s) := by
  have he := quantified h.zf w (v 3) (v 4) (v 1) f (v 2) T (s 3) (s 4) (v 8) h.hw (.conjL (.conjR (.conjR (.conjR h.hs)))) (.conjR (.conjR p2))
  let E := openedBody w (v 3) (v 4) (v 1) f (v 2) T (s 4) (v 8)
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h' := h.in_body E
  let u : Fin 14 → Fin (m+5) := fun i => Fin.addCases (m := 9) (n := 5) (motive := fun _ => Fin (m+5)) (fun j => old 5 (v j)) (slot 5) i
  have q0 : Derives Δ (openedData (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 (s 1)) (old 5 Q) (Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 2) (Fin.cases (u 3) (Fin.cases (u 4) Fin.elim0)))))) :=
    of_eq (by simp only [openedData_rename]; rfl)
      (HornBinderRules.under_body 5 p0 E)
  have q1 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 5 w) (u 3) (u 4) (u 1) (old 5 f) (u 2) (old 5 T) (old 5 (s 7)) (old 5 (s 2)) (u 0) (u 5) (u 6)) :=
    of_eq (by simp only [ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 5 p1 E)
  have q2 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 5 w) (u 3) (u 4) (u 1) (old 5 f) (u 2) (old 5 T) (old 5 (s 8)) (old 5 (s 3)) (u 6) (u 7) (u 8)) :=
    of_eq (by simp only [ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 5 p2 E)
  have q3 : Derives Δ (openedData (old 5 w) (u 3) (u 4) (u 1) (old 5 f) (u 2) (old 5 T) (old 5 (s 4)) (u 8) (Fin.cases (u 9) (Fin.cases (u 10) (Fin.cases (u 11) (Fin.cases (u 12) (Fin.cases (u 13) Fin.elim0)))))) := hE
  have hout := stage4 (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 Q) (fun i => old 5 (s i)) h' u q0 q1 q2 q3
  exact of_eq (result_rename w R S a f c T Q s (old 5)).symm hout

private theorem stage2 {m} {Γ : Context m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (h : Inputs Γ w R S a f c T Q s) (v : Fin 7 → Fin m)
    (p0 : Derives Γ (openedData w R S a f c T (s 1) Q (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4) Fin.elim0)))))))
    (p1 : Derives Γ (ForcingFormulaDiagram.binaryData 0 w (v 3) (v 4) (v 1) f (v 2) T (s 7) (s 2) (v 0) (v 5) (v 6))) :
    Derives Γ (result w R S a f c T Q s) := by
  have he := ForcingFormulaDiagram.binary_output h.zf 0 w (v 3) (v 4) (v 1) f (v 2) T (s 2) (s 8) (s 3) (v 6) h.hw (.conjL (.conjR (.conjR h.hs))) (.conjR (.conjR p1))
  let E := ForcingFormulaDiagram.binaryBody 0 w (v 3) (v 4) (v 1) f (v 2) T (s 8) (s 3) (v 6)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h' := h.in_body E
  let u : Fin 9 → Fin (m+2) := fun i => Fin.addCases (m := 7) (n := 2) (motive := fun _ => Fin (m+2)) (fun j => old 2 (v j)) (slot 2) i
  have q0 : Derives Δ (openedData (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 (s 1)) (old 2 Q) (Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 2) (Fin.cases (u 3) (Fin.cases (u 4) Fin.elim0)))))) :=
    of_eq (by simp only [openedData_rename]; rfl)
      (HornBinderRules.under_body 2 p0 E)
  have q1 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 7)) (old 2 (s 2)) (u 0) (u 5) (u 6)) :=
    of_eq (by simp only [ForcingFormulaDiagram.binaryData_rename]; rfl)
      (HornBinderRules.under_body 2 p1 E)
  have q2 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 8)) (old 2 (s 3)) (u 6) (u 7) (u 8)) := hE
  have hout := stage3 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 Q) (fun i => old 2 (s i)) h' u q0 q1 q2
  exact of_eq (result_rename w R S a f c T Q s (old 2)).symm hout

private theorem stage1 {m} {Γ : Context m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (h : Inputs Γ w R S a f c T Q s) (v : Fin 5 → Fin m)
    (p0 : Derives Γ (openedData w R S a f c T (s 1) Q (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4) Fin.elim0))))))) :
    Derives Γ (result w R S a f c T Q s) := by
  have he := ForcingFormulaDiagram.binary_output h.zf 0 w (v 3) (v 4) (v 1) f (v 2) T (s 1) (s 7) (s 2) (v 0) h.hw (.conjL (.conjR h.hs)) (.conjR (.conjR p0))
  let E := ForcingFormulaDiagram.binaryBody 0 w (v 3) (v 4) (v 1) f (v 2) T (s 7) (s 2) (v 0)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h' := h.in_body E
  let u : Fin 7 → Fin (m+2) := fun i => Fin.addCases (m := 5) (n := 2) (motive := fun _ => Fin (m+2)) (fun j => old 2 (v j)) (slot 2) i
  have q0 : Derives Δ (openedData (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 (s 1)) (old 2 Q) (Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 2) (Fin.cases (u 3) (Fin.cases (u 4) Fin.elim0)))))) :=
    of_eq (by simp only [openedData_rename]; rfl)
      (HornBinderRules.under_body 2 p0 E)
  have q1 : Derives Δ (ForcingFormulaDiagram.binaryData 0 (old 2 w) (u 3) (u 4) (u 1) (old 2 f) (u 2) (old 2 T) (old 2 (s 7)) (old 2 (s 2)) (u 0) (u 5) (u 6)) := hE
  have hout := stage2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 Q) (fun i => old 2 (s i)) h' u q0 q1
  exact of_eq (result_rename w R S a f c T Q s (old 2)).symm hout

private theorem stage0 {m} {Γ : Context m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (h : Inputs Γ w R S a f c T Q s) :
    Derives Γ (result w R S a f c T Q s) := by
  have he := quantified h.zf w R S a f c T (s 0) (s 1) Q h.hw (.conjL h.hs) h.hq
  let E := openedBody w R S a f c T (s 1) Q
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h' := h.in_body E
  let u : Fin 5 → Fin (m+5) := slot 5
  have q0 : Derives Δ (openedData (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 (s 1)) (old 5 Q) (Fin.cases (u 0) (Fin.cases (u 1) (Fin.cases (u 2) (Fin.cases (u 3) (Fin.cases (u 4) Fin.elim0)))))) := hE
  have hout := stage1 (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 Q) (fun i => old 5 (s i)) h' u q0
  exact of_eq (result_rename w R S a f c T Q s (old 5)).symm hout

/-- Consume a whole ACTUAL raw tail query. No canonical output, table,
constructor operand or equality is an input. -/
theorem from_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (source w s))
    (hq : Derives Γ (substituted w R S a f c T (s 0) Q)) :
    Derives Γ (result w R S a f c T Q s) :=
  stage0 w R S a f c T Q s ⟨hZ, hw, hs, hq⟩

def shellCodes {m} (rM rO D Nc : Fin m) (v : Fin 7 → Fin m) : Fin 9 → Fin m :=
  Fin.cases (v 4) (Fin.cases (v 3) (Fin.cases (v 2) (Fin.cases (v 1)
    (Fin.cases (v 0) (Fin.cases D (Fin.cases Nc (Fin.cases rM (Fin.cases rO Fin.elim0))))))))

/-- The exact already produced original shell supplies every source
constructor; the queried tail is its original v[4], with no new compiler. -/
theorem from_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc Q R S c T Y : Fin m) (v : Fin 7 → Fin m)
    (hw : Derives Γ (omega w))
    (hs : Derives Γ (ForcingExistCode.shellData w a A B C f qM qO rM rO D Nc Q v))
    (hy : Derives Γ (substituted w R S A f c T (v 4) Y)) :
    Derives Γ (result w R S A f c T Y (shellCodes rM rO D Nc v)) := by
  have hsrc : Derives Γ (source w (shellCodes rM rO D Nc v)) :=
    .conjI (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR hs))))))
      (.conjI (.conjL (.conjL (.conjR (.conjR (.conjR hs)))))
        (.conjI (.conjL (.conjL (.conjR (.conjR hs))))
          (.conjI (.conjL (.conjL (.conjR hs))) (.conjL (.conjL hs)))))
  exact from_query hZ w R S A f c T Y (shellCodes rM rO D Nc v) hw hsrc hy

def input {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  (omega w).conj ((source w s).conj (substituted w R S a f c T (s 0) Q))
def sentence {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) : Source.Sentence :=
  ((input w R S a f c T Q s).imp (result w R S a f c T Q s)).close

theorem kernel_certificate {m} (w R S a f c T Q : Fin m) (s : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w R S a f c T Q s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input w R S a f c T Q s
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact from_query (ZFContext.add (ZFContext.source_ZF m) G) w R S a f c T Q s
    (.conjL hG) (.conjL (.conjR hG)) (.conjR (.conjR hG))

end PPAC.Migration.ForcingExistTailOpening
