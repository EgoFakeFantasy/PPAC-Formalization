import PPAC.Migration.ForcingFormulaAtoms
import PPAC.Migration.Internal.SyntaxCodedMixedBinderExistence

/-! Shared original binder frames for four-table formula cancellation.
All twelve witnesses are constructed in the object theory. Full formula
induction and final Con are not asserted by this module. -/
namespace PPAC.Migration.ForcingFormulaLifts
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingFormulaDiagram (atSource atSource_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix SyntaxCodedMixedBinderSyntax.lifted

private def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private theorem four_map {α β : Type} (a b c d : α) (r : α → β) :
    (fun i => r (four a b c d i)) = four (r a) (r b) (r c) (r d) := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
private def src : Fin 4 → Fin 4 := four 0 1 2 0
private def dst : Fin 4 → Fin 4 := four 1 2 3 3
private def listsAt {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (e : Fin 4) : Formula m :=
  SyntaxMixedImageCodeSyntax.termLists w (a (src e)) (b (src e)) (a (dst e)) (b (dst e)) (R e) (S e)
private theorem listsAt_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (e : Fin 4) (r : Fin m → Fin l) :
    (listsAt w a b R S e).rename r = listsAt (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) e := by
  simp only [listsAt, SyntaxMixedImageCodeSyntax.termLists_rename]

def input {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula m :=
  (ForcingTermDiagram.diagram w a b R S).conj ((listsAt w a b R S 0).conj
    ((listsAt w a b R S 1).conj ((listsAt w a b R S 2).conj (listsAt w a b R S 3))))

theorem input_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (input w a b R S).rename r = input (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [input, Formula.rename, ForcingTermDiagram.diagram_rename, listsAt_rename]
private theorem input_lists {m} {Γ : Context m} (w : Fin m) (a b R S : Fin 4 → Fin m)
    (hi : Derives Γ (input w a b R S)) (e : Fin 4) : Derives Γ (listsAt w a b R S e) :=
  Fin.cases (.conjL (.conjR hi)) (Fin.cases (.conjL (.conjR (.conjR hi)))
    (Fin.cases (.conjL (.conjR (.conjR (.conjR hi)))) (Fin.cases (.conjR (.conjR (.conjR (.conjR hi)))) (fun i => Fin.elim0 i)))) e
private theorem input_natural {m} {Γ : Context m} (w : Fin m) (a b R S : Fin 4 → Fin m)
    (hi : Derives Γ (input w a b R S)) (i : Fin 4) : Derives Γ (.mem (a i) w) := by
  have h0 := Derives.conjL (.conjL (input_lists w a b R S hi 0))
  have h1 := Derives.conjL (.conjL (input_lists w a b R S hi 1))
  have h2 := Derives.conjL (.conjL (input_lists w a b R S hi 2))
  have h3 := Derives.conjL (.conjL (.conjR (.conjL (input_lists w a b R S hi 2))))
  exact Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun j => Fin.elim0 j)))) i

attribute [local irreducible] input ForcingTermDiagram.diagram

private def scopeData {m} (w : Fin m) (a A : Fin 4 → Fin m) : Formula m :=
  ((Formula.mem (A 0) w).conj (successor (A 0) (a 0))).conj
    (((Formula.mem (A 1) w).conj (successor (A 1) (a 1))).conj
      (((Formula.mem (A 2) w).conj (successor (A 2) (a 2))).conj
        ((Formula.mem (A 3) w).conj (successor (A 3) (a 3)))))
private theorem scopeData_rename {m l} (w : Fin m) (a A : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (scopeData w a A).rename r = scopeData (r w) (fun i => r (a i)) (fun i => r (A i)) := by
  simp only [scopeData, Formula.rename, successor_rename]
private def scopeBody {m} (w : Fin m) (a : Fin 4 → Fin m) : Formula (m+4) :=
  scopeData (old 4 w) (fun i => old 4 (a i)) (four (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))
private def existsScopes {m} (w : Fin m) (a : Fin 4 → Fin m) : Formula m := existsMany 4 (scopeBody w a)
private theorem existsScopes_rename {m l} (w : Fin m) (a : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsScopes w a).rename r = existsScopes (r w) (fun i => r (a i)) := by
  simp only [existsScopes, existsMany_rename, scopeBody, scopeData_rename, four_map, lift_old, lift_slot]
private theorem exists_scopes {m} {Γ : Context m} (w : Fin m) (a b R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b R S)) : Derives Γ (existsScopes w a) := by
  have he0 := OriginalBinderStepSyntax.successor_exists w (a 0) hw (input_natural w a b R S hi 0)
  let E0 := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) (a 0).castSucc)
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E0)
  have hi1 := of_eq (input_rename w a b R S Fin.castSucc) (under hi E0)
  have he1 := OriginalBinderStepSyntax.successor_exists w.castSucc (a 1).castSucc hw1 (input_natural w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (R i).castSucc) (fun i => (S i).castSucc) hi1 1)
  let E1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (a 1).castSucc.castSucc)
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E1)
  have hi2 := of_eq (input_rename w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (R i).castSucc) (fun i => (S i).castSucc) Fin.castSucc) (under hi1 E1)
  have he2 := OriginalBinderStepSyntax.successor_exists w.castSucc.castSucc (a 2).castSucc.castSucc hw2 (input_natural w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) hi2 2)
  let E2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+2)) (a 2).castSucc.castSucc.castSucc)
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 E2)
  have hi3 := of_eq (input_rename w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) Fin.castSucc) (under hi2 E2)
  have he3 := OriginalBinderStepSyntax.successor_exists w.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc hw3 (input_natural w.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc) hi3 3)
  let E3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+3)) (a 3).castSucc.castSucc.castSucc.castSucc)
  let Δ4 := Context.add E3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := E3) he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hs0 : Derives Δ4 ((Formula.mem (slot 4 0) (old 4 w)).conj (successor (slot 4 0) (old 4 (a 0)))) := of_eq (by simp only [E0, Formula.raise, Formula.rename, successor_rename]; rfl) (under (under (under hE0 E1) E2) E3)
  have hs1 : Derives Δ4 ((Formula.mem (slot 4 1) (old 4 w)).conj (successor (slot 4 1) (old 4 (a 1)))) := of_eq (by simp only [E1, Formula.raise, Formula.rename, successor_rename]; rfl) (under (under hE1 E2) E3)
  have hs2 : Derives Δ4 ((Formula.mem (slot 4 2) (old 4 w)).conj (successor (slot 4 2) (old 4 (a 2)))) := of_eq (by simp only [E2, Formula.raise, Formula.rename, successor_rename]; rfl) (under hE2 E3)
  have hs3 : Derives Δ4 ((Formula.mem (slot 4 3) (old 4 w)).conj (successor (slot 4 3) (old 4 (a 3)))) := hE3
  have hout : Derives Δ4 (existsScopes (old 4 w) (fun i => old 4 (a i))) := by
    apply HornBinderRules.intro_many 4 _ (fun i => slot 4 i)
    exact of_eq (by simp only [scopeBody, scopeData_rename, four_map, assign_old, assign_slot]; rfl) (.conjI hs0 (.conjI hs1 (.conjI hs2 hs3)))
  exact of_eq (by simp only [Formula.raise, existsScopes_rename]; rfl) hout

private def mapsBody {m} (w : Fin m) (a b A R S : Fin 4 → Fin m) : Formula (m+8) :=
  ForcingTermDiagram.lifts (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (A i))
    (fun i => old 8 (R i)) (fun i => old 8 (S i))
    (four (slot 8 0) (slot 8 2) (slot 8 4) (slot 8 6)) (four (slot 8 1) (slot 8 3) (slot 8 5) (slot 8 7))
private def existsMaps {m} (w : Fin m) (a b A R S : Fin 4 → Fin m) : Formula m := existsMany 8 (mapsBody w a b A R S)
private theorem existsMaps_rename {m l} (w : Fin m) (a b A R S : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsMaps w a b A R S).rename r = existsMaps (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (A i)) (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [existsMaps, existsMany_rename, mapsBody, ForcingTermDiagram.lifts_rename, four_map, lift_old, lift_slot]
private theorem under_lift_two {m} {Γ : Context m} {w R S a b c d A C K H : Fin m}
    (hp : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) (B : Formula (m+2)) :
    Derives (Context.add B (raisedContext 2 Γ))
      (SyntaxCodedMixedBinderSyntax.lifted (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 A) (old 2 C) (old 2 K) (old 2 H)) :=
  of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H (old 2)) (HornBinderRules.under_body 2 hp B)
private theorem exists_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b A R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b R S))
    (hs : ∀ i : Fin 4, Derives Γ (successor (A i) (a i))) : Derives Γ (existsMaps w a b A R S) := by
  have hs0_0 : Derives Γ (successor (A 0) (a 0)) := (hs 0)
  have hs0_1 : Derives Γ (successor (A 1) (a 1)) := (hs 1)
  have he0 := SyntaxCodedMixedBinderExistence.exists_pair hZ w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) (A 0) (A 1) hw (.conjI (input_lists w a b R S hi 0) (.conjI hs0_0 hs0_1))
  let E0 := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc (R 0).castSucc.castSucc (S 0).castSucc.castSucc (a 0).castSucc.castSucc (b 0).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (A 0).castSucc.castSucc (A 1).castSucc.castSucc (slot 2 0 (m := m+0)) (slot 2 1 (m := m+0))
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ E0
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E0)
  have hi1 := of_eq (input_rename w a b R S (old 2)) (HornBinderRules.under_body 2 hi E0)
  have hs1_1 : Derives Δ1 (successor (A 1).castSucc.castSucc (a 1).castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (hs 1) E0)
  have hs1_2 : Derives Δ1 (successor (A 2).castSucc.castSucc (a 2).castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (hs 2) E0)
  have he1 := SyntaxCodedMixedBinderExistence.exists_pair hZ1 w.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (A 1).castSucc.castSucc (A 2).castSucc.castSucc hw1 (.conjI (input_lists w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) hi1 1) (.conjI hs1_1 hs1_2))
  let E1 := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc (R 1).castSucc.castSucc.castSucc.castSucc (S 1).castSucc.castSucc.castSucc.castSucc (a 1).castSucc.castSucc.castSucc.castSucc (b 1).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (A 1).castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+2)) (slot 2 1 (m := m+2))
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hi2 := of_eq (input_rename w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) (old 2)) (HornBinderRules.under_body 2 hi1 E1)
  have hs2_2 : Derives Δ2 (successor (A 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (hs 2) E0) E1)
  have hs2_3 : Derives Δ2 (successor (A 3).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (hs 3) E0) E1)
  have he2 := SyntaxCodedMixedBinderExistence.exists_pair hZ2 w.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc hw2 (.conjI (input_lists w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) hi2 2) (.conjI hs2_2 hs2_3))
  let E2 := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+4)) (slot 2 1 (m := m+4))
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ2 E2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hi3 := of_eq (input_rename w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) (old 2)) (HornBinderRules.under_body 2 hi2 E2)
  have hs3_0 : Derives Δ3 (successor (A 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (hs 0) E0) E1) E2)
  have hs3_3 : Derives Δ3 (successor (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [successor_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (hs 3) E0) E1) E2)
  have he3 := SyntaxCodedMixedBinderExistence.exists_pair hZ3 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw3 (.conjI (input_lists w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) hi3 3) (.conjI hs3_0 hs3_3))
  let E3 := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+6)) (slot 2 1 (m := m+6))
  let Δ4 := Context.add E3 (raisedContext 2 Δ3)
  apply HornBinderRules.eliminate_many 2 E3 _ he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hl0 : Derives Δ4 (SyntaxCodedMixedBinderSyntax.lifted (old 8 w) (old 8 (R 0)) (old 8 (S 0)) (old 8 (a 0)) (old 8 (b 0)) (old 8 (a 1)) (old 8 (b 1)) (old 8 (A 0)) (old 8 (A 1)) (slot 8 0) (slot 8 1)) := (under_lift_two (under_lift_two (under_lift_two hE0 E1) E2) E3)
  have hl1 : Derives Δ4 (SyntaxCodedMixedBinderSyntax.lifted (old 8 w) (old 8 (R 1)) (old 8 (S 1)) (old 8 (a 1)) (old 8 (b 1)) (old 8 (a 2)) (old 8 (b 2)) (old 8 (A 1)) (old 8 (A 2)) (slot 8 2) (slot 8 3)) := (under_lift_two (under_lift_two hE1 E2) E3)
  have hl2 : Derives Δ4 (SyntaxCodedMixedBinderSyntax.lifted (old 8 w) (old 8 (R 2)) (old 8 (S 2)) (old 8 (a 2)) (old 8 (b 2)) (old 8 (a 3)) (old 8 (b 3)) (old 8 (A 2)) (old 8 (A 3)) (slot 8 4) (slot 8 5)) := (under_lift_two hE2 E3)
  have hl3 : Derives Δ4 (SyntaxCodedMixedBinderSyntax.lifted (old 8 w) (old 8 (R 3)) (old 8 (S 3)) (old 8 (a 0)) (old 8 (b 0)) (old 8 (a 3)) (old 8 (b 3)) (old 8 (A 0)) (old 8 (A 3)) (slot 8 6) (slot 8 7)) := hE3
  have hl : Derives Δ4 (mapsBody w a b A R S) := .conjI hl0 (.conjI hl1 (.conjI hl2 hl3))
  have hout : Derives Δ4 (existsMaps (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (A i)) (fun i => old 8 (R i)) (fun i => old 8 (S i))) := by
    apply HornBinderRules.intro_many 8 _ (fun i => slot 8 i)
    exact of_eq (by simp only [mapsBody, ForcingTermDiagram.lifts_rename, four_map, assign_old, assign_slot]) hl
  exact of_eq (by simp only [existsMaps_rename, old]) hout

attribute [local irreducible] ForcingTermDiagram.lifts

private def liftBody {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula (m+12) :=
  ForcingTermDiagram.lifts (old 12 w) (fun i => old 12 (a i)) (fun i => old 12 (b i))
    (four (slot 12 0) (slot 12 1) (slot 12 2) (slot 12 3)) (fun i => old 12 (R i)) (fun i => old 12 (S i))
    (four (slot 12 4) (slot 12 6) (slot 12 8) (slot 12 10)) (four (slot 12 5) (slot 12 7) (slot 12 9) (slot 12 11))
private def existsLifts {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula m := existsMany 12 (liftBody w a b R S)
private theorem existsLifts_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsLifts w a b R S).rename r = existsLifts (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [existsLifts, existsMany_rename, liftBody, ForcingTermDiagram.lifts_rename, four_map, lift_old, lift_slot]
private theorem old_val {m} (n : Nat) (i : Fin m) : (old n i).val = i.val := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem slot_val {m} (n : Nat) (i : Fin n) : (slot (m := m) n i).val = m+i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [slot, Fin.lastCases_last, Fin.val_last]
    · simpa only [slot, Fin.lastCases_castSucc, Fin.val_castSucc] using ih j

private theorem maps_after_scope {m} (w : Fin m) (a b R S : Fin 4 → Fin m) :
    mapsBody (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i))
      (four (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) = liftBody w a b R S := by
  unfold mapsBody liftBody
  rw [four_map]
  have ha0 : old 8 (slot 4 0 (m := m)) = slot 12 0 := Fin.ext (by simp only [old_val, slot_val]; rfl)
  have ha1 : old 8 (slot 4 1 (m := m)) = slot 12 1 := Fin.ext (by simp only [old_val, slot_val]; rfl)
  have ha2 : old 8 (slot 4 2 (m := m)) = slot 12 2 := Fin.ext (by simp only [old_val, slot_val]; rfl)
  have ha3 : old 8 (slot 4 3 (m := m)) = slot 12 3 := Fin.ext (by simp only [old_val, slot_val]; rfl)
  have ht0 : slot 8 0 (m := m+4) = slot 12 4 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht1 : slot 8 1 (m := m+4) = slot 12 5 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht2 : slot 8 2 (m := m+4) = slot 12 6 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht3 : slot 8 3 (m := m+4) = slot 12 7 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht4 : slot 8 4 (m := m+4) = slot 12 8 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht5 : slot 8 5 (m := m+4) = slot 12 9 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht6 : slot 8 6 (m := m+4) = slot 12 10 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  have ht7 : slot 8 7 (m := m+4) = slot 12 11 (m := m) := Fin.ext (by simp only [slot_val]; rfl)
  rw [ha0, ha1, ha2, ha3, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7]
  rfl

private theorem exists_lifts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b R S)) : Derives Γ (existsLifts w a b R S) := by
  let B := scopeBody w a
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ (exists_scopes w a b R S hw hi)
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hi4 := of_eq (input_rename w a b R S (old 4)) (HornBinderRules.under_body 4 hi B)
  let A : Fin 4 → Fin (m+4) := four (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs : ∀ i : Fin 4, Derives Δ (successor (A i) (old 4 (a i))) :=
    Fin.cases (.conjR (.conjL hB)) (Fin.cases (.conjR (.conjL (.conjR hB)))
      (Fin.cases (.conjR (.conjL (.conjR (.conjR hB)))) (Fin.cases (.conjR (.conjR (.conjR (.conjR hB)))) (fun i => Fin.elim0 i))))
  have he := exists_maps hZ4 (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) A (fun i => old 4 (R i)) (fun i => old 4 (S i)) hw4 hi4 hs
  let C := mapsBody (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) A (fun i => old 4 (R i)) (fun i => old 4 (S i))
  let Ξ := Context.add C (raisedContext 8 Δ)
  apply HornBinderRules.eliminate_many 8 C _ he
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hC1 : Derives Ξ (liftBody w a b R S) := of_eq (maps_after_scope w a b R S) hC
  have hout : Derives Ξ (existsLifts (old 12 w) (fun i => old 12 (a i)) (fun i => old 12 (b i)) (fun i => old 12 (R i)) (fun i => old 12 (S i))) := by
    apply HornBinderRules.intro_many 12 _ (fun i => slot 12 i)
    exact of_eq (by simp only [liftBody, ForcingTermDiagram.lifts_rename, four_map, assign_old, assign_slot]) hC1
  exact of_eq (by simp only [existsLifts_rename, old]) hout

/-- The original four lifts preserve both the term diagram and all actual
list typing needed by the formula induction. -/
theorem input_lifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b A R S K H : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b R S))
    (hl : Derives Γ (ForcingTermDiagram.lifts w a b A R S K H)) : Derives Γ (input w A b K H) := by
  unfold input at hi
  have hd := ForcingTermDiagram.lifted hZ w a b A R S K H hw (.conjL hi) hl
  unfold ForcingTermDiagram.lifts at hl
  have h0 := SyntaxCodedMixedBinderTyping.output_lists w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) (A 0) (A 1) (K 0) (H 0) (.conjL hl)
  have h1 := SyntaxCodedMixedBinderTyping.output_lists w (R 1) (S 1) (a 1) (b 1) (a 2) (b 2) (A 1) (A 2) (K 1) (H 1) (.conjL (.conjR hl))
  have h2 := SyntaxCodedMixedBinderTyping.output_lists w (R 2) (S 2) (a 2) (b 2) (a 3) (b 3) (A 2) (A 3) (K 2) (H 2) (.conjL (.conjR (.conjR hl)))
  have h3 := SyntaxCodedMixedBinderTyping.output_lists w (R 3) (S 3) (a 0) (b 0) (a 3) (b 3) (A 0) (A 3) (K 3) (H 3) (.conjR (.conjR (.conjR hl)))
  unfold input
  exact .conjI hd (.conjI h0 (.conjI h1 (.conjI h2 h3)))

/-- Twelve ORIGINAL object witnesses: four shared successor scopes and
four pairs of actual lifted tables, with the resulting induction input. -/
def frameBody {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula (m+12) :=
  (liftBody w a b R S).conj (input (old 12 w)
    (four (slot 12 0) (slot 12 1) (slot 12 2) (slot 12 3)) (fun i => old 12 (b i))
    (four (slot 12 4) (slot 12 6) (slot 12 8) (slot 12 10)) (four (slot 12 5) (slot 12 7) (slot 12 9) (slot 12 11)))

def existsFrame {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula m := existsMany 12 (frameBody w a b R S)

theorem existsFrame_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (existsFrame w a b R S).rename r = existsFrame (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [existsFrame, existsMany_rename, frameBody, liftBody, Formula.rename, input_rename,
    ForcingTermDiagram.lifts_rename, four_map, lift_old, lift_slot]

/-- All shared scopes, lifted tables and lifted input are constructed in
the object theory; no chosen-lift witness is a theorem premise. -/
theorem exists_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b R S)) : Derives Γ (existsFrame w a b R S) := by
  let B := liftBody w a b R S
  let Δ := Context.add B (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 B _ (exists_lifts hZ w a b R S hw hi)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hnew := input_lifted (HornBinderRules.zf_body 12 hZ B) (old 12 w)
    (fun i => old 12 (a i)) (fun i => old 12 (b i)) (four (slot 12 0) (slot 12 1) (slot 12 2) (slot 12 3))
    (fun i => old 12 (R i)) (fun i => old 12 (S i))
    (four (slot 12 4) (slot 12 6) (slot 12 8) (slot 12 10)) (four (slot 12 5) (slot 12 7) (slot 12 9) (slot 12 11))
    (of_eq (omega_rename w (old 12)) (HornBinderRules.under_body 12 hw B))
    (of_eq (input_rename w a b R S (old 12)) (HornBinderRules.under_body 12 hi B)) hB
  have hout : Derives Δ (existsFrame (old 12 w) (fun i => old 12 (a i)) (fun i => old 12 (b i)) (fun i => old 12 (R i)) (fun i => old 12 (S i))) := by
    apply HornBinderRules.intro_many 12 _ (fun i => slot 12 i)
    exact of_eq (by simp only [frameBody, B, liftBody, Formula.rename, input_rename,
      ForcingTermDiagram.lifts_rename, four_map, assign_old, assign_slot]) (.conjI hB hnew)
  exact of_eq (existsFrame_rename w a b R S (old 12)).symm hout

def sentence {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Source.Sentence :=
  (((omega w).conj (input w a b R S)).imp (existsFrame w a b R S)).close

theorem kernel_certificate {m} (w : Fin m) (a b R S : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a b R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (omega w).conj (input w a b R S)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact exists_frame (ZFContext.add (ZFContext.source_ZF m) E) w a b R S (.conjL h) (.conjR h)

end PPAC.Migration.ForcingFormulaLifts
