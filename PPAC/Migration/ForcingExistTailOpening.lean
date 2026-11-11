import PPAC.Migration.ForcingExistCode
import PPAC.Migration.ForcingMixedUnary
import PPAC.Migration.ForcingFormulaDiagram
import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.Internal.EmptyBoundFreeInputs

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

def quantifiedData {m} (universal : Bool) (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (singleCode (SyntaxLogicalSyntax.quantifierTag universal) w (v 0) Q).conj
    ((lifted w R S a f c T (v 1) (v 2) (v 3) (v 4)).conj
      (substituted w (v 3) (v 4) (v 1) f (v 2) T x (v 0)))

theorem quantifiedData_rename {m l} (universal : Bool) (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (quantifiedData universal w R S a f c T x Q v).rename ρ =
      quantifiedData universal (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) (fun i => ρ (v i)) := by
  simp only [quantifiedData, Formula.rename, singleCode_rename, lifted_rename, substituted_rename]

private def quantifiedBody {m} (universal : Bool) (w R S a f c T x Q : Fin m) : Formula (m+5) :=
  quantifiedData universal (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q) (slot 5)
def quantifiedOutput {m} (universal : Bool) (w R S a f c T x Q : Fin m) : Formula m :=
  existsMany 5 (quantifiedBody universal w R S a f c T x Q)

theorem quantifiedOutput_rename {m l} (universal : Bool) (w R S a f c T x Q : Fin m) (ρ : Fin m → Fin l) :
    (quantifiedOutput universal w R S a f c T x Q).rename ρ =
      quantifiedOutput universal (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) := by
  simp only [quantifiedOutput, quantifiedBody, existsMany_rename, quantifiedData_rename, lift_old, lift_slot]

/-- The original unary reader and its original four lifted-environment
witnesses, packed together without prescribing any of their values. -/
theorem quantified_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w R S a f c T n x Q : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hq : Derives Γ (substituted w R S a f c T n Q)) :
    Derives Γ (quantifiedOutput universal w R S a f c T x Q) := by
  have valid : (SyntaxLogicalSyntax.quantifierTag universal = 4 ∧ true = false) ∨
      (SyntaxLogicalSyntax.quantifierTag universal = 9 ∧ true = true) ∨
      (SyntaxLogicalSyntax.quantifierTag universal = 10 ∧ true = true) := by
    cases universal
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inr (.inl ⟨rfl, rfl⟩)
  have ho := ForcingMixedUnary.single_output hZ (SyntaxLogicalSyntax.quantifierTag universal) true valid
    w R S a f c T n x Q hw hc hq
  let E := (singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc (Fin.last m) Q.castSucc).conj
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
  have hd : Derives Ξ (quantifiedData universal (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q) v) :=
    .conjI (.conjL he) hB
  have hout : Derives Ξ (quantifiedOutput universal (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (old 5 x) (old 5 Q)) := by
    apply HornBinderRules.intro_many 5 _ v
    exact of_eq (by simp only [quantifiedBody, quantifiedData_rename, assign_old, assign_slot]) hd
  exact of_eq (by simp only [Formula.raise, quantifiedOutput_rename]; rfl) hout

def openedData {m} (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  quantifiedData false w R S a f c T x Q v

theorem openedData_rename {m l} (w R S a f c T x Q : Fin m) (v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (openedData w R S a f c T x Q v).rename ρ =
      openedData (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) (fun i => ρ (v i)) :=
  quantifiedData_rename false w R S a f c T x Q v ρ

def openedBody {m} (w R S a f c T x Q : Fin m) : Formula (m+5) :=
  quantifiedBody false w R S a f c T x Q

def opened {m} (w R S a f c T x Q : Fin m) : Formula m :=
  quantifiedOutput false w R S a f c T x Q

theorem opened_rename {m l} (w R S a f c T x Q : Fin m) (ρ : Fin m → Fin l) :
    (opened w R S a f c T x Q).rename ρ =
      opened (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ c) (ρ T) (ρ x) (ρ Q) :=
  quantifiedOutput_rename false w R S a f c T x Q ρ

theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a f c T n x Q : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (singleCode 10 w x n))
    (hq : Derives Γ (substituted w R S a f c T n Q)) :
    Derives Γ (opened w R S a f c T x Q) :=
  quantified_output hZ false w R S a f c T n x Q hw hc hq

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

/-- Retag the SAME already encoded graph of closed terms. The original
free/mixed bridges do all term work; the structural encoding is untouched. -/
private theorem encoded_at_scope {m} {Γ : Context m}
    (w a z C T L G : Fin m) (hz : Derives Γ (empty z))
    (hC : Derives Γ (.mem C w))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w G a z T L)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.encoded w G a C T L) :=
  .conjI (EmptyBoundFreeInputs.graph_mixed w G a C T hC
    (EmptyBoundFreeInputs.graph_free w G a z T hz (.conjL he))) (.conjR he)

/-- Read the original source encodings from the FIRST actual lift and retain
both closed code tables at an arbitrary actual target scope. No new graphs. -/
private theorem lists_at_scope {m} {Γ : Context m}
    (w R S a f z T A C K H D : Fin m) (hz : Derives Γ (empty z))
    (hD : Derives Γ (.mem D w))
    (hl : Derives Γ (lifted w R S a f z T A C K H)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f D T R S) := by
  let E := SyntaxCodedMixedBinderSyntax.body w R S a f z T A C K H
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hl
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz E)
  have hD4 := HornBinderRules.under_body 4 hD E
  have hR := encoded_at_scope (old 4 w) (old 4 a) (old 4 z) (old 4 D) (old 4 T)
    (old 4 R) (slot 4 0) hz4 hD4 (.conjL (.conjL hE))
  have hS := encoded_at_scope (old 4 w) (old 4 f) (old 4 z) (old 4 D) (old 4 T)
    (old 4 S) (slot 4 1) hz4 hD4 (.conjR (.conjL hE))
  have hLists : Derives Δ (SyntaxMixedImageCodeSyntax.termLists (old 4 w) (old 4 a) (old 4 f)
      (old 4 D) (old 4 T) (old 4 R) (old 4 S)) :=
    .conjI (SyntaxMixedImageCodeFields.term_list (old 4 w) (slot 4 0) (old 4 a) (old 4 D) (old 4 T) (old 4 R) hR)
      (SyntaxMixedImageCodeFields.term_list (old 4 w) (slot 4 1) (old 4 f) (old 4 D) (old 4 T) (old 4 S) hS)
  exact of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f D T R S (old 4)).symm hLists

/-- Preserve BOTH actual replacement graphs and the SAME result list.
Neither a replacement candidate nor a list uniqueness comparison is needed. -/
private theorem replacement_at_scope {m} {Γ : Context m}
    (w a z C T Base j p S : Fin m) (hz : Derives Γ (empty z))
    (hC : Derives Γ (.mem C w))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w a z T Base j p S)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w a C T Base).conj
      (ForcingReflexiveImages.replacement w a C T Base j p S)) := by
  let E := ForcingReflexiveImages.body w a z T Base j p S
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hr
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E)
  have hC2 := HornBinderRules.under_body 2 hC E
  have hInput := encoded_at_scope (old 2 w) (old 2 a) (old 2 z) (old 2 C) (old 2 T)
    (old 2 Base) (slot 2 0) hz2 hC2 (.conjL hE)
  have hOutput := encoded_at_scope (old 2 w) (old 2 a) (old 2 z) (old 2 C) (old 2 T)
    (old 2 S) (slot 2 1) hz2 hC2 (.conjR (.conjR hE))
  have hData : Derives Δ (ForcingReflexiveImages.data (old 2 w) (old 2 a) (old 2 C) (old 2 T)
      (old 2 Base) (old 2 j) (old 2 p) (old 2 S) (slot 2 0) (slot 2 1)) :=
    .conjI hInput (.conjI (.conjL (.conjR hE)) hOutput)
  have hRep : Derives Δ (ForcingReflexiveImages.replacement (old 2 w) (old 2 a) (old 2 C) (old 2 T)
      (old 2 Base) (old 2 j) (old 2 p) (old 2 S)) := by
    apply HornBinderRules.intro_many 2 _ (slot 2)
    exact of_eq (by simp only [ForcingReflexiveImages.body, ForcingReflexiveImages.data_rename, assign_old, assign_slot]) hData
  have hType := SyntaxMixedImageCodeFields.term_list (old 2 w) (slot 2 0) (old 2 a) (old 2 C) (old 2 T) (old 2 Base) hInput
  exact of_eq (by simp only [Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename,
    ForcingReflexiveImages.replacement_rename]) (.conjI hType hRep)

/-- SAME sixteen actual tail witnesses, now with the actual source/target
successors and the SAME closed base/overwrite at BOTH target scopes. -/
def scopeData {m} (w R S a f z T Q Base j p : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (data w R S a f z T Q s v).conj
    ((SyntaxCodedMixedBinderSyntax.input w R S a f z T (v 1) (v 2)).conj
      ((SyntaxCodedMixedBinderSyntax.input w (v 3) (v 4) (v 1) f (v 2) T (v 10) (v 11)).conj
        ((SyntaxMixedImageCodeSyntax.termLists w a f (v 2) T R S).conj
          ((SyntaxMixedImageCodeSyntax.termLists w a f (v 11) T R S).conj
        (((SyntaxMixedImageCodeSyntax.termList w f (v 2) T Base).conj
          (ForcingReflexiveImages.replacement w f (v 2) T Base j p S)).conj
          ((SyntaxMixedImageCodeSyntax.termList w f (v 11) T Base).conj
            (ForcingReflexiveImages.replacement w f (v 11) T Base j p S)))))))

theorem scopeData_rename {m l} (w R S a f z T Q Base j p : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 16 → Fin m) (ρ : Fin m → Fin l) :
    (scopeData w R S a f z T Q Base j p s v).rename ρ =
      scopeData (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ z) (ρ T) (ρ Q) (ρ Base) (ρ j) (ρ p)
        (fun i => ρ (s i)) (fun i => ρ (v i)) := by
  simp only [scopeData, Formula.rename, data_rename, SyntaxCodedMixedBinderSyntax.input_rename,
    SyntaxMixedImageCodeSyntax.termList_rename, ForcingReflexiveImages.replacement_rename,
    SyntaxMixedImageCodeSyntax.termLists_rename]

def scopeBody {m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m) : Formula (m+16) :=
  scopeData (old 16 w) (old 16 R) (old 16 S) (old 16 a) (old 16 f) (old 16 z) (old 16 T) (old 16 Q)
    (old 16 Base) (old 16 j) (old 16 p) (fun i => old 16 (s i)) (slot 16)
def scopeResult {m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  existsMany 16 (scopeBody w R S a f z T Q Base j p s)

theorem scopeResult_rename {m l} (w R S a f z T Q Base j p : Fin m)
    (s : Fin 9 → Fin m) (ρ : Fin m → Fin l) :
    (scopeResult w R S a f z T Q Base j p s).rename ρ =
      scopeResult (ρ w) (ρ R) (ρ S) (ρ a) (ρ f) (ρ z) (ρ T) (ρ Q) (ρ Base) (ρ j) (ρ p)
        (fun i => ρ (s i)) := by
  simp only [scopeResult, existsMany_rename, scopeBody, scopeData_rename, lift_old, lift_slot]

/-- All scope/base operations required here are read from the SAME actual
tail lifts and closed replacement. No target-scope typing is assumed. -/
theorem prepare_records {m} {Γ : Context m} (w R S a f z T Q Base j p : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 16 → Fin m)
    (hz : Derives Γ (empty z))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T Base j p S))
    (hd : Derives Γ (data w R S a f z T Q s v)) :
    Derives Γ (scopeData w R S a f z T Q Base j p s v) := by
  have hLift0 := Derives.conjL (.conjR (.conjL hd))
  have hLift1 := Derives.conjL (.conjR (.conjL (.conjR (.conjR (.conjR hd)))))
  have hFirst := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T (v 1) (v 2) (v 3) (v 4) hLift0
  have hSecond := SyntaxCodedMixedBinderTyping.input_of_lifted w (v 3) (v 4) (v 1) f (v 2) T (v 10) (v 11) (v 12) (v 13) hLift1
  have hOut0 := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T (v 1) (v 2) (v 3) (v 4) hLift0
  have hOut1 := SyntaxCodedMixedBinderTyping.output_lists w (v 3) (v 4) (v 1) f (v 2) T (v 10) (v 11) (v 12) (v 13) hLift1
  have hBase0 := replacement_at_scope w f z (v 2) T Base j p S hz
    (.conjL (.conjL (.conjR (.conjL hOut0)))) hr
  have hBase1 := replacement_at_scope w f z (v 11) T Base j p S hz
    (.conjL (.conjL (.conjR (.conjL hOut1)))) hr
  have hRoots0 := lists_at_scope w R S a f z T (v 1) (v 2) (v 3) (v 4) (v 2) hz
    (.conjL (.conjL (.conjR (.conjL hOut0)))) hLift0
  have hRoots1 := lists_at_scope w R S a f z T (v 1) (v 2) (v 3) (v 4) (v 11) hz
    (.conjL (.conjL (.conjR (.conjL hOut1)))) hLift0
  exact .conjI hd (.conjI hFirst (.conjI hSecond (.conjI hRoots0 (.conjI hRoots1 (.conjI hBase0 hBase1)))))

/-- Enrich the already proved whole-tail reader, without changing or
reproducing its sixteen witnesses. -/
theorem prepare_result {m} {Γ : Context m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m)
    (hz : Derives Γ (empty z))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T Base j p S))
    (he : Derives Γ (result w R S a f z T Q s)) :
    Derives Γ (scopeResult w R S a f z T Q Base j p s) := by
  let E := body w R S a f z T Q s
  let Δ := Context.add E (raisedContext 16 Γ)
  apply HornBinderRules.eliminate_many 16 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hd := prepare_records (old 16 w) (old 16 R) (old 16 S) (old 16 a) (old 16 f) (old 16 z) (old 16 T) (old 16 Q)
    (old 16 Base) (old 16 j) (old 16 p) (fun i => old 16 (s i)) (slot 16)
    (of_eq (empty_rename z (old 16)) (HornBinderRules.under_body 16 hz E))
    (of_eq (ForcingReflexiveImages.replacement_rename w f z T Base j p S (old 16)) (HornBinderRules.under_body 16 hr E)) hE
  have hout : Derives Δ (scopeResult (old 16 w) (old 16 R) (old 16 S) (old 16 a) (old 16 f) (old 16 z) (old 16 T) (old 16 Q)
      (old 16 Base) (old 16 j) (old 16 p) (fun i => old 16 (s i))) := by
    apply HornBinderRules.intro_many 16 _ (slot 16)
    exact of_eq (by simp only [scopeBody, scopeData_rename, assign_old, assign_slot]) hd
  exact of_eq (scopeResult_rename w R S a f z T Q Base j p s (old 16)).symm hout

theorem prepare_query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T Base j p S))
    (hs : Derives Γ (source w s))
    (hq : Derives Γ (substituted w R S a f z T (s 0) Q)) :
    Derives Γ (scopeResult w R S a f z T Q Base j p s) :=
  prepare_result w R S a f z T Q Base j p s hz hr (from_query hZ w R S a f z T Q s hw hs hq)

theorem prepare_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f qM qO rM rO D Nc Q R S z T Y Base j p : Fin m) (v : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T Base j p S))
    (hs : Derives Γ (ForcingExistCode.shellData w a A B C f qM qO rM rO D Nc Q v))
    (hy : Derives Γ (substituted w R S A f z T (v 4) Y)) :
    Derives Γ (scopeResult w R S A f z T Y Base j p (shellCodes rM rO D Nc v)) :=
  prepare_result w R S A f z T Y Base j p (shellCodes rM rO D Nc v) hz hr
    (from_shell hZ w a A B C f qM qO rM rO D Nc Q R S z T Y v hw hs hy)

def preparedInput {m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  (input w R S a f z T Q s).conj ((empty z).conj
    (ForcingReflexiveImages.replacement w f z T Base j p S))
def preparedSentence {m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m) : Source.Sentence :=
  ((preparedInput w R S a f z T Q Base j p s).imp (scopeResult w R S a f z T Q Base j p s)).close

theorem prepared_kernel_certificate {m} (w R S a f z T Q Base j p : Fin m) (s : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (preparedSentence w R S a f z T Q Base j p s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := preparedInput w R S a f z T Q Base j p s
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  have hI := Derives.conjL hG
  exact prepare_query (ZFContext.add (ZFContext.source_ZF m) G) w R S a f z T Q Base j p s
    (.conjL hI) (.conjL (.conjR hG)) (.conjR (.conjR hG))
    (.conjL (.conjR hI)) (.conjR (.conjR hI))

private theorem successor_predecessor {m} {Γ : Context m} (s i j : Fin m)
    (he : Derives Γ (.equal i j)) (hs : Derives Γ (successor s i)) :
    Derives Γ (successor s j) := by
  let P := successor s.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he
      (of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs))

/-- TWO independent actual tail executions have equal source/target
successors. No externally standard depth or supplied scope equality. -/
theorem scope_alignment_at_prefixes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S R1 S1 a f z T Q Q1 Base j p q : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 16 → Fin m)
    (hv : Derives Γ (scopeData w R S a f z T Q Base j p s v))
    (hu : Derives Γ (scopeData w R1 S1 a f z T Q1 Base j q s u)) :
    Derives Γ ((Formula.equal (v 1) (u 1)).conj
      ((Formula.equal (v 2) (u 2)).conj
        ((Formula.equal (v 10) (u 10)).conj (.equal (v 11) (u 11))))) := by
  have hv0 := Derives.conjL (.conjR hv)
  have hu0 := Derives.conjL (.conjR hu)
  have hv1 := Derives.conjL (.conjR (.conjR hv))
  have hu1 := Derives.conjL (.conjR (.conjR hu))
  have he := (ZFContext.arithmetic hZ).base.extensionality
  have eA := OmegaUniversal.successor_unique (v 1) (u 1) a he (.conjL (.conjR hv0)) (.conjL (.conjR hu0))
  have ec := OmegaUniversal.successor_unique (v 2) (u 2) z he (.conjR (.conjR hv0)) (.conjR (.conjR hu0))
  have hA := successor_predecessor (u 10) (u 1) (v 1) (eq_symm eA) (.conjL (.conjR hu1))
  have hc := successor_predecessor (u 11) (u 2) (v 2) (eq_symm ec) (.conjR (.conjR hu1))
  exact .conjI eA (.conjI ec (.conjI
    (OmegaUniversal.successor_unique (v 10) (u 10) (v 1) he (.conjL (.conjR hv1)) hA)
    (OmegaUniversal.successor_unique (v 11) (u 11) (v 2) he (.conjR (.conjR hv1)) hc)))

theorem scope_alignment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S S1 a f z T Q Q1 Base j p q : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 16 → Fin m)
    (hv : Derives Γ (scopeData w R S a f z T Q Base j p s v))
    (hu : Derives Γ (scopeData w R S1 a f z T Q1 Base j q s u)) :
    Derives Γ ((Formula.equal (v 1) (u 1)).conj
      ((Formula.equal (v 2) (u 2)).conj
        ((Formula.equal (v 10) (u 10)).conj (.equal (v 11) (u 11))))) :=
  scope_alignment_at_prefixes hZ w R S R S1 a f z T Q Q1 Base j p q s v u hv hu

end PPAC.Migration.ForcingExistTailOpening
