import PPAC.Migration.ForcingPreorderLeaves

/-! Consume ACTUAL targetData/instancesProved, retaining its SAME six native,
ten matrix and five background witnesses. Only the existing three prefix
witnesses and eleven derived queries are added, all as object existentials.
No separately supplied native instance, matrix row, leaf or query answer. -/
namespace PPAC.Migration.ForcingPreorderLeafTarget
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def v3 {m} (a b c : Fin m) : Fin 3 → Fin m := (Fin.cases a (Fin.cases b (fun _ => c)))
private theorem v3_map {m l} (a b c : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (v3 a b c i)) = v3 (ρ a) (ρ b) (ρ c) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private def v5 {m} (a b c d e : Fin m) : Fin 5 → Fin m := (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e)))))
private theorem v5_map {m l} (a b c d e : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (v5 a b c d e i)) = v5 (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) i

private def v6 {m} (a b c d e f : Fin m) : Fin 6 → Fin m := (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (fun _ => f))))))
private theorem v6_map {m l} (a b c d e f : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (v6 a b c d e f i)) = v6 (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))) i

private def backgroundBody {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula (m+5) :=
  ForcingPreorderLeaves.produced test R (old 5 w) (old 5 z) (old 5 A1) (old 5 A2) (old 5 A3) (old 5 f) (old 5 T) (old 5 C) (old 5 B) (old 5 S) (old 5 Refl) (old 5 Pre) (fun i => old 5 (v i)) (slot 5) (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))

def background {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  existsMany 5 (backgroundBody test R w z A1 A2 A3 f T C B S Refl Pre v H U F P N)

theorem background_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (background test R w z A1 A2 A3 f T C B S Refl Pre v H U F P N).rename ρ =
    background test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre)
      (fun i => ρ (v i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [background, existsMany_rename, backgroundBody, ForcingPreorderLeaves.produced_rename, lift_old, lift_slot]

private def matrixBody {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre N0 : Fin m)
    (v : Fin 16 → Fin m) (U F P : Fin 3 → Fin m) : Formula (m+10) :=
  background test R (old 10 w) (old 10 z) (old 10 A1) (old 10 A2) (old 10 A3) (old 10 f) (old 10 T) (old 10 C) (old 10 B) (old 10 S) (old 10 Refl) (old 10 Pre) (fun i => old 10 (v i)) (v6 (slot 10 0) (slot 10 2) (slot 10 4) (slot 10 6) (slot 10 8) (slot 10 9)) (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i)) (v5 (old 10 N0) (slot 10 1) (slot 10 3) (slot 10 5) (slot 10 7))

def matrix {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre N0 : Fin m)
    (v : Fin 16 → Fin m) (U F P : Fin 3 → Fin m) : Formula m := existsMany 10 (matrixBody test R w z A1 A2 A3 f T C B S Refl Pre N0 v U F P)

theorem matrix_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre N0 : Fin m)
    (v : Fin 16 → Fin m) (U F P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (matrix test R w z A1 A2 A3 f T C B S Refl Pre N0 v U F P).rename ρ =
    matrix test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre) (ρ N0)
      (fun i => ρ (v i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) := by
  simp only [matrix, existsMany_rename, matrixBody, background_rename, v6_map, v5_map, lift_old, lift_slot]

private def instancesBody {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m)
    (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) : Formula (m+6) :=
  matrix test R (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 T) (old 6 C) (old 6 B) (old 6 S) (old 6 Refl) (old 6 Pre) (slot 6 5) (fun i => old 6 (v i)) (v3 (old 6 U0) (slot 6 1) (slot 6 3)) (v3 (slot 6 0) (slot 6 2) (slot 6 4)) (fun i => old 6 (P i))

def instances {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m)
    (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) : Formula m := existsMany 6 (instancesBody test R w z A1 A2 A3 f T C B S Refl Pre U0 v P)

theorem instances_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m)
    (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (instances test R w z A1 A2 A3 f T C B S Refl Pre U0 v P).rename ρ =
    instances test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre) (ρ U0) (fun i => ρ (v i)) (fun i => ρ (P i)) := by
  simp only [instances, existsMany_rename, instancesBody, matrix_rename, v3_map, lift_old, lift_slot]

private structure Inputs {k m} (Γ : Context m) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T B S U0 : Fin m) (v : Fin 16 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  zero : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)
  one : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)
  two : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)
  three : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)
  raw : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v)
  parent : Derives Γ (substituted w B S z f z T (v 2) U0)

private theorem Inputs.in_body {k m} {Γ : Context m} {R : Source.Formula (k+2)} {w z A1 A2 A3 f T B S U0 : Fin m} {v : Fin 16 → Fin m}
    (h : Inputs Γ R w z A1 A2 A3 f T B S U0 v) (j : Nat) (E : Formula (m+j)) :
    Inputs (Context.add E (raisedContext j Γ)) R (old j w) (old j z) (old j A1) (old j A2) (old j A3) (old j f) (old j T) (old j B) (old j S) (old j U0) (fun i => old j (v i)) := {
  zf := HornBinderRules.zf_body j h.zf E
  omega := of_eq (omega_rename w (old j)) (HornBinderRules.under_body j h.omega E)
  zero := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old j)) (HornBinderRules.under_body j h.zero E)
  one := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 (old j)) (HornBinderRules.under_body j h.one E)
  two := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 (old j)) (HornBinderRules.under_body j h.two E)
  three := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 (old j)) (HornBinderRules.under_body j h.three E)
  raw := of_eq (ForcingPreorderCode.rawData_rename R w z A1 A2 A3 f v (old j)) (HornBinderRules.under_body j h.raw E)
  parent := of_eq (substituted_rename w B S z f z T (v 2) U0 (old j)) (HornBinderRules.under_body j h.parent E)
}

private theorem from_background {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (h : Inputs Γ R w z A1 A2 A3 f T B S (U 0) v)
    (hb : Derives Γ (ForcingPreorderInstances.backgroundExists test w z T C Refl Pre H U F P N)) :
    Derives Γ (background test R w z A1 A2 A3 f T C B S Refl Pre v H U F P N) := by
  let E := ForcingPreorderInstances.backgroundBody test w z T C Refl Pre H U F P N
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ hb
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := h.in_body 5 E
  have hProd := ForcingPreorderLeaves.from_numbers h5.zf test R (old 5 w) (old 5 z) (old 5 A1) (old 5 A2) (old 5 A3) (old 5 f) (old 5 T) (old 5 C) (old 5 B) (old 5 S) (old 5 Refl) (old 5 Pre)
    (fun i => old 5 (v i)) (slot 5) (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))
    h5.omega h5.zero h5.one h5.two h5.three h5.raw hE h5.parent
  have hout : Derives Δ (background test R (old 5 w) (old 5 z) (old 5 A1) (old 5 A2) (old 5 A3) (old 5 f) (old 5 T) (old 5 C) (old 5 B) (old 5 S) (old 5 Refl) (old 5 Pre) (fun i => old 5 (v i)) (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))) := by
    apply HornBinderRules.intro_many 5 _ (slot 5)
    exact of_eq (by simp only [backgroundBody, ForcingPreorderLeaves.produced_rename, assign_old, assign_slot] <;> rfl) hProd
  exact of_eq (background_rename test R w z A1 A2 A3 f T C B S Refl Pre v H U F P N (old 5)).symm hout

private theorem from_matrix {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre N0 : Fin m)
    (v : Fin 16 → Fin m) (U F P : Fin 3 → Fin m)
    (h : Inputs Γ R w z A1 A2 A3 f T B S (U 0) v)
    (hm : Derives Γ (ForcingPreorderInstances.matrixExists test w z T C Refl Pre N0 U F P)) :
    Derives Γ (matrix test R w z A1 A2 A3 f T C B S Refl Pre N0 v U F P) := by
  let E := ForcingPreorderInstances.matrixBody test w z T C Refl Pre N0 U F P
  let Δ := Context.add E (raisedContext 10 Γ)
  apply HornBinderRules.eliminate_many 10 E _ hm
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h10 := h.in_body 10 E
  have hBG := from_background test R (old 10 w) (old 10 z) (old 10 A1) (old 10 A2) (old 10 A3) (old 10 f) (old 10 T) (old 10 C) (old 10 B) (old 10 S) (old 10 Refl) (old 10 Pre) (fun i => old 10 (v i)) (v6 (slot 10 0) (slot 10 2) (slot 10 4) (slot 10 6) (slot 10 8) (slot 10 9)) (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i)) (v5 (old 10 N0) (slot 10 1) (slot 10 3) (slot 10 5) (slot 10 7)) h10 hE
  have hout : Derives Δ (matrix test R (old 10 w) (old 10 z) (old 10 A1) (old 10 A2) (old 10 A3) (old 10 f) (old 10 T) (old 10 C) (old 10 B) (old 10 S) (old 10 Refl) (old 10 Pre) (old 10 N0) (fun i => old 10 (v i)) (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i))) := by
    apply HornBinderRules.intro_many 10 _ (slot 10)
    exact of_eq (by simp only [matrixBody, background_rename, v6_map, v5_map, assign_old, assign_slot] <;> rfl) hBG
  exact of_eq (matrix_rename test R w z A1 A2 A3 f T C B S Refl Pre N0 v U F P (old 10)).symm hout

private theorem from_instances {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m)
    (v : Fin 16 → Fin m) (P : Fin 3 → Fin m)
    (h : Inputs Γ R w z A1 A2 A3 f T B S U0 v)
    (hi : Derives Γ (ForcingPreorderInstances.instancesProved test w z T C Refl Pre U0 P)) :
    Derives Γ (instances test R w z A1 A2 A3 f T C B S Refl Pre U0 v P) := by
  let E := ForcingPreorderInstances.instancesBody test w z T C Refl Pre U0 P
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h6 := h.in_body 6 E
  have hM := from_matrix test R (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 T) (old 6 C) (old 6 B) (old 6 S) (old 6 Refl) (old 6 Pre) (slot 6 5) (fun i => old 6 (v i)) (v3 (old 6 U0) (slot 6 1) (slot 6 3)) (v3 (slot 6 0) (slot 6 2) (slot 6 4)) (fun i => old 6 (P i)) h6 hE
  have hout : Derives Δ (instances test R (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 T) (old 6 C) (old 6 B) (old 6 S) (old 6 Refl) (old 6 Pre) (old 6 U0) (fun i => old 6 (v i)) (fun i => old 6 (P i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [instancesBody, matrix_rename, v3_map, assign_old, assign_slot] <;> rfl) hM
  exact of_eq (instances_rename test R w z A1 A2 A3 f T C B S Refl Pre U0 v P (old 6)).symm hout

/-- Consume ACTUAL original targetData. All original 6+10+5 witnesses,
internal background proofs, SAME native instances and SAME five-IMP row
remain object-existential; original prefix producer adds its own 3 tables
and all ELEVEN actual queries. No native/row/leaf/query answer supplied. -/
theorem at_target {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m) (v : Fin 16 → Fin m) (P : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)) (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (ht : Derives Γ (ForcingPreorderInstances.targetData test w z f T C B S (v 0) (v 1) (v 2) P Pre Refl U0)) :
    Derives Γ (instances test R w z A1 A2 A3 f T C B S Refl Pre U0 v P) := by
  have hp := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ht))))
  have hi := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ht)))))
  exact from_instances test R w z A1 A2 A3 f T C B S Refl Pre U0 v P ⟨hZ,hw,hz,hA1,hA2,hA3,hr,hp⟩ hi

def input {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m) (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((ForcingPreorderCode.rawData R w z A1 A2 A3 f v).conj ((ForcingPreorderInstances.targetData test w z f T C B S (v 0) (v 1) (v 2) P Pre Refl U0)))))))

def sentence {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m) (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) : Source.Sentence :=
  ((input test R w z A1 A2 A3 f T C B S Refl Pre U0 v P).imp (instances test R w z A1 A2 A3 f T C B S Refl Pre U0 v P)).close

theorem kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre U0 : Fin m) (v : Fin 16 → Fin m) (P : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test R w z A1 A2 A3 f T C B S Refl Pre U0 v P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input test R w z A1 A2 A3 f T C B S Refl Pre U0 v P
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact at_target (ZFContext.add (ZFContext.source_ZF m) E) test R w z A1 A2 A3 f T C B S Refl Pre U0 v P
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h)))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))

end PPAC.Migration.ForcingPreorderLeafTarget
