import PPAC.Migration.ForcingBinderFormula
import PPAC.Migration.ForcingPreorderInstances
import PPAC.Migration.Internal.SyntaxCodedMixedBinderExistence

/-! The original preorder has THREE ordered native instantiations. Consume
actual ALL fields and the existing native judgments, and produce the exact
Cons(p,Cons(q,Cons(r,R))) direct opening. The finite row is the original
three-binder outer pattern; formula codes and runtime scopes remain internal. -/
namespace PPAC.Migration.ForcingPreorderPrefix
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Consume a parent ALL opening and its SAME actual native instance. No
lift table or direct-output answer is supplied; both are object-generated.
The direct table type is derived from the real prefix cons. -/
theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S P D n x Q F q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z T R S))
    (hA : Derives Γ (successor A a))
    (hc : Derives Γ (StructuralListSyntax.consCode w P R D))
    (hs : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w x n))
    (ht : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F Q))
    (hn : Derives Γ (substituted w R S a f z T n Q))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F q)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w A z T D).conj
      (substituted w D S A f z T x q)) := by
  have hI := SyntaxTopFormulaTyping.instantiate_input hZ w z T C P F q hw hi
  have hP := Derives.conjL (Derives.conjL hI)
  have hC := Derives.conjR (Derives.conjL hI)
  have hD := TypedArgumentListConstruction.cons_list hZ w a A z T P R D hw hP (Derives.conjL he) hc hA
  apply Derives.conjI hD
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w R S a f z T n Q hw hn
  have hX := Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.quantified_iff hZ true w a f x n A hw hs hA)) hType)
  have hDirect := SyntaxMixedFormulaOutputInduction.actual_exists hZ w D S A f z T x hw
    (Derives.conjI hX (Derives.conjI hD (Derives.conjR he)))
  let E := substituted w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hDirect
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have he1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z T R S Fin.castSucc) (under he E)
  have hA1 := of_eq (successor_rename A a Fin.castSucc) (under hA E)
  have hC1 := of_eq (successor_rename C z Fin.castSucc) (under hC E)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w P R D Fin.castSucc) (under hc E)
  have hs1 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w x n Fin.castSucc) (under hs E)
  have ht1 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w F Q Fin.castSucc) (under ht E)
  have hn1 := of_eq (substituted_rename w R S a f z T n Q Fin.castSucc) (under hn E)
  have hi1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P F q Fin.castSucc) (under hi E)
  have hLift := SyntaxCodedMixedBinderExistence.exists_pair hZ1 w.castSucc R.castSucc S.castSucc a.castSucc f.castSucc z.castSucc T.castSucc A.castSucc C.castSucc
    hw1 (Derives.conjI he1 (Derives.conjI hA1 hC1))
  let B := SyntaxCodedMixedBinderSyntax.lifted (old 2 w.castSucc) (old 2 R.castSucc) (old 2 S.castSucc) (old 2 a.castSucc) (old 2 f.castSucc)
    (old 2 z.castSucc) (old 2 T.castSucc) (old 2 A.castSucc) (old 2 C.castSucc) (slot 2 0) (slot 2 1)
  let Ξ := Context.add B (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 B _ hLift
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ1 B
  have hw3 := of_eq (omega_rename w.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 B)
  have hz3 := of_eq (empty_rename z.castSucc (old 2)) (HornBinderRules.under_body 2 hz1 B)
  have he3 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w.castSucc a.castSucc f.castSucc z.castSucc T.castSucc R.castSucc S.castSucc (old 2)) (HornBinderRules.under_body 2 he1 B)
  have hc3 := of_eq (StructuralListSyntax.consCode_rename w.castSucc P.castSucc R.castSucc D.castSucc (old 2)) (HornBinderRules.under_body 2 hc1 B)
  have hs3 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w.castSucc x.castSucc n.castSucc (old 2)) (HornBinderRules.under_body 2 hs1 B)
  have ht3 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w.castSucc F.castSucc Q.castSucc (old 2)) (HornBinderRules.under_body 2 ht1 B)
  have hn3 := of_eq (substituted_rename w.castSucc R.castSucc S.castSucc a.castSucc f.castSucc z.castSucc T.castSucc n.castSucc Q.castSucc (old 2)) (HornBinderRules.under_body 2 hn1 B)
  have hi3 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc F.castSucc q.castSucc (old 2)) (HornBinderRules.under_body 2 hi1 B)
  have hDirect3 := of_eq (substituted_rename w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc x.castSucc (Fin.last m) (old 2)) (HornBinderRules.under_body 2 hE B)
  have hType3 := SyntaxMixedFormulaJudgmentTyping.source_type hZ3 (old 2 w.castSucc) (old 2 R.castSucc) (old 2 S.castSucc) (old 2 a.castSucc) (old 2 f.castSucc) (old 2 z.castSucc) (old 2 T.castSucc)
    (old 2 n.castSucc) (old 2 Q.castSucc) hw3 hn3
  have hAdvance := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.single_iff hZ3 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩))
    (old 2 w.castSucc) (old 2 R.castSucc) (old 2 S.castSucc) (old 2 a.castSucc) (old 2 f.castSucc) (old 2 z.castSucc) (old 2 T.castSucc)
    (old 2 n.castSucc) (old 2 Q.castSucc) (old 2 x.castSucc) (old 2 F.castSucc) hw3 (Derives.conjI hType3 he3) hs3 ht3)) hn3
  have hOpen := Derives.impE (Derives.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ3
    (old 2 w.castSucc) (old 2 x.castSucc) (old 2 R.castSucc) (old 2 S.castSucc) (old 2 a.castSucc) (old 2 f.castSucc) (old 2 z.castSucc) (old 2 T.castSucc)
    (old 2 F.castSucc) (old 2 A.castSucc) (old 2 C.castSucc) (slot 2 0) (slot 2 1) hw3 hB)) hAdvance
  have hEq := ForcingBinderFormula.native hZ3 (old 2 w.castSucc) (old 2 z.castSucc) (old 2 a.castSucc) (old 2 f.castSucc) (old 2 T.castSucc) (old 2 A.castSucc) (old 2 C.castSucc)
    (old 2 R.castSucc) (old 2 S.castSucc) (slot 2 0) (slot 2 1) (old 2 P.castSucc) (old 2 D.castSucc) (old 2 x.castSucc) (old 2 F.castSucc) (old 2 q.castSucc) (old 2 (Fin.last m))
    hw3 hz3 he3 hB hc3 hOpen hi3 hDirect3
  have hout := SyntaxMixedFormulaJudgmentSubst.subst_q (old 2 w.castSucc) (old 2 D.castSucc) (old 2 S.castSucc) (old 2 A.castSucc) (old 2 f.castSucc) (old 2 z.castSucc) (old 2 T.castSucc)
    (old 2 x.castSucc) (old 2 (Fin.last m)) (old 2 q.castSucc) (eq_symm hEq) hDirect3
  exact of_eq (by simp only [Formula.raise, substituted_rename]) hout


private structure Inputs {m} (Γ : Context m) (w z f T C : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  zero : Derives Γ (empty z)
  scopes : ∀ i : Fin 3, Derives Γ (successor (a i.succ) (a i.castSucc))
  sourceFields : ∀ i : Fin 3, Derives Γ (SyntaxLogicalSyntax.singleCode 9 w (n i.succ) (n i.castSucc))
  targetFields : ∀ i : Fin 3, Derives Γ (SyntaxLogicalSyntax.singleCode 9 w (F i) (q i.castSucc))
  instances : ∀ i : Fin 3, Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P i) (F i) (q i.succ))

private theorem Inputs.under {m} {Γ : Context m} {w z f T C : Fin m} {a n q : Fin 4 → Fin m} {F P : Fin 3 → Fin m}
    (h : Inputs Γ w z f T C a n q F P) (E : Formula (m+1)) :
    Inputs (Context.add E (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc T.castSucc C.castSucc
      (fun i => (a i).castSucc) (fun i => (n i).castSucc) (fun i => (q i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc) := {
  zf := ZFContext.under h.zf E
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega E)
  zero := of_eq (empty_rename z Fin.castSucc) (SourceLogic.under h.zero E)
  scopes := fun i => of_eq (successor_rename (a i.succ) (a i.castSucc) Fin.castSucc) (SourceLogic.under (h.scopes i) E)
  sourceFields := fun i => of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w (n i.succ) (n i.castSucc) Fin.castSucc) (SourceLogic.under (h.sourceFields i) E)
  targetFields := fun i => of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w (F i) (q i.castSucc) Fin.castSucc) (SourceLogic.under (h.targetFields i) E)
  instances := fun i => of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C (P i) (F i) (q i.succ) Fin.castSucc) (SourceLogic.under (h.instances i) E)
}

/-- Exact original cons, its derived type, and direct opening to the SAME
actual native output at this original preorder binder. -/
def oneData {m} (i : Fin 3) (w z f T R S D : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula m :=
  (StructuralListSyntax.consCode w (P i) R D).conj
    ((SyntaxMixedImageCodeSyntax.termList w (a i.succ) z T D).conj (substituted w D S (a i.succ) f z T (n i.succ) (q i.succ)))

theorem oneData_rename {m l} (i : Fin 3) (w z f T R S D : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (oneData i w z f T R S D a n q P).rename ρ = oneData i (ρ w) (ρ z) (ρ f) (ρ T) (ρ R) (ρ S) (ρ D)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (q i)) (fun i => ρ (P i)) := by
  simp only [oneData, Formula.rename, StructuralListSyntax.consCode_rename, SyntaxMixedImageCodeSyntax.termList_rename, substituted_rename]

private def extension {m} (i : Fin 3) (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula m := .ex
  (oneData i w.castSucc z.castSucc f.castSucc T.castSucc R.castSucc S.castSucc (Fin.last m)
    (fun i => (a i).castSucc) (fun i => (n i).castSucc) (fun i => (q i).castSucc) (fun i => (P i).castSucc))

private theorem extension_rename {m l} (i : Fin 3) (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (extension i w z f T R S a n q P).rename ρ = extension i (ρ w) (ρ z) (ρ f) (ρ T) (ρ R) (ρ S)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (q i)) (fun i => ρ (P i)) := by
  simp only [extension, Formula.rename, oneData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_extension {m} {Γ : Context m} (i : Fin 3) (w z f T R S D : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m)
    (hd : Derives Γ (oneData i w z f T R S D a n q P)) : Derives Γ (extension i w z f T R S a n q P) := by
  apply Derives.exI D
  exact of_eq (by simp only [Formula.instantiate, oneData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd

private theorem extend {m} {Γ : Context m} {w z f T C : Fin m} {a n q : Fin 4 → Fin m} {F P : Fin 3 → Fin m}
    (h : Inputs Γ w z f T C a n q F P) (i : Fin 3) (R S : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w (a i.castSucc) f z T R S))
    (hn : Derives Γ (substituted w R S (a i.castSucc) f z T (n i.castSucc) (q i.castSucc))) :
    Derives Γ (extension i w z f T R S a n q P) := by
  have hI := SyntaxTopFormulaTyping.instantiate_input h.zf w z T C (P i) (F i) (q i.succ) h.omega (h.instances i)
  have hP := SyntaxTerms.range h.zf w z T (P i) h.omega (Derives.conjL (Derives.conjL hI))
  have hR := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjL he))))
  have hc := StructuralConsCore.exists_cons h.zf w (P i) R h.omega hP hR
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc (P i).castSucc R.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.under E
  have he1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w (a i.castSucc) f z T R S Fin.castSucc) (SourceLogic.under he E)
  have hn1 := of_eq (substituted_rename w R S (a i.castSucc) f z T (n i.castSucc) (q i.castSucc) Fin.castSucc) (SourceLogic.under hn E)
  have hd := step h1.zf w.castSucc z.castSucc (a i.castSucc).castSucc f.castSucc T.castSucc (a i.succ).castSucc C.castSucc R.castSucc S.castSucc
    (P i).castSucc (Fin.last m) (n i.castSucc).castSucc (n i.succ).castSucc (q i.castSucc).castSucc (F i).castSucc (q i.succ).castSucc
    h1.omega h1.zero he1 (h1.scopes i) (Derives.conjR hE) (h1.sourceFields i) (h1.targetFields i) hn1 (h1.instances i)
  have hout := intro_extension i w.castSucc z.castSucc f.castSucc T.castSucc R.castSucc S.castSucc (Fin.last m)
    (fun i => (a i).castSucc) (fun i => (n i).castSucc) (fun i => (q i).castSucc) (fun i => (P i).castSucc) (Derives.conjI (Derives.conjR hE) hd)
  exact of_eq (extension_rename i w z f T R S a n q P Fin.castSucc).symm hout

/-- The THREE original prefixes in order, each retaining its exact direct
output, type and real cons operation. Final bound list is [P2,P1,P0]++R. -/
def data {m} (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P D : Fin 3 → Fin m) : Formula m :=
  (oneData 0 w z f T R S (D 0) a n q P).conj
    ((oneData 1 w z f T (D 0) S (D 1) a n q P).conj (oneData 2 w z f T (D 1) S (D 2) a n q P))

theorem data_rename {m l} (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P D : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (data w z f T R S a n q P D).rename ρ = data (ρ w) (ρ z) (ρ f) (ρ T) (ρ R) (ρ S)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (q i)) (fun i => ρ (P i)) (fun i => ρ (D i)) := by
  simp only [data, Formula.rename, oneData_rename]

def body {m} (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula (m+3) :=
  data (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 R) (old 3 S)
    (fun i => old 3 (a i)) (fun i => old 3 (n i)) (fun i => old 3 (q i)) (fun i => old 3 (P i)) (slot 3)

def produced {m} (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula m := existsMany 3 (body w z f T R S a n q P)

theorem produced_rename {m l} (w z f T R S : Fin m) (a n q : Fin 4 → Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (produced w z f T R S a n q P).rename ρ = produced (ρ w) (ρ z) (ρ f) (ρ T) (ρ R) (ρ S)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (q i)) (fun i => ρ (P i)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem from_rows {m} {Γ : Context m} {w z f T C : Fin m} {a n q : Fin 4 → Fin m} {F P : Fin 3 → Fin m}
    (h : Inputs Γ w z f T C a n q F P) (R S : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w (a 0) f z T R S))
    (hn : Derives Γ (substituted w R S (a 0) f z T (n 0) (q 0))) : Derives Γ (produced w z f T R S a n q P) := by
  have hFirst := extend h 0 R S he hn
  let E := oneData 0 w.castSucc z.castSucc f.castSucc T.castSucc R.castSucc S.castSucc (Fin.last m)
    (fun i => (a i).castSucc) (fun i => (n i).castSucc) (fun i => (q i).castSucc) (fun i => (P i).castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hFirst
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.under E
  have he1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w (a 0) f z T R S Fin.castSucc) (SourceLogic.under he E)
  have hSecond := extend h1 1 (Fin.last m) S.castSucc (Derives.conjI (Derives.conjL (Derives.conjR hE)) (Derives.conjR he1)) (Derives.conjR (Derives.conjR hE))
  let B := oneData 1 w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc (Fin.last m).castSucc S.castSucc.castSucc (Fin.last (m+1))
    (fun i => (a i).castSucc.castSucc) (fun i => (n i).castSucc.castSucc) (fun i => (q i).castSucc.castSucc) (fun i => (P i).castSucc.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Δ)
  apply Derives.exE (p := B) hSecond
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have h2 := h1.under B
  have he2 : Derives Ξ (SyntaxMixedImageCodeSyntax.termLists w.castSucc.castSucc (a 0).castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) (SourceLogic.under he1 B)
  have hThird := extend h2 2 (Fin.last (m+1)) S.castSucc.castSucc (Derives.conjI (Derives.conjL (Derives.conjR hB)) (Derives.conjR he2)) (Derives.conjR (Derives.conjR hB))
  let L := oneData 2 w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc S.castSucc.castSucc.castSucc (Fin.last (m+2))
    (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (n i).castSucc.castSucc.castSucc) (fun i => (q i).castSucc.castSucc.castSucc) (fun i => (P i).castSucc.castSucc.castSucc)
  let Ω := Context.add L (Context.image Formula.raise Ξ)
  apply Derives.exE (p := L) hThird
  have hL : Derives Ω L := .hyp (Or.inl rfl)
  have hE3 : Derives Ω (oneData 0 w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
    (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (n i).castSucc.castSucc.castSucc) (fun i => (q i).castSucc.castSucc.castSucc) (fun i => (P i).castSucc.castSucc.castSucc)) :=
    of_eq (by simp only [E, Formula.raise, oneData_rename]) (SourceLogic.under (SourceLogic.under hE B) L)
  have hB3 : Derives Ω (oneData 1 w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
    (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (n i).castSucc.castSucc.castSucc) (fun i => (q i).castSucc.castSucc.castSucc) (fun i => (P i).castSucc.castSucc.castSucc)) :=
    of_eq (by simp only [B, Formula.raise, oneData_rename]) (SourceLogic.under hB L)
  have hout : Derives Ω (produced w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc
    (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (n i).castSucc.castSucc.castSucc) (fun i => (q i).castSucc.castSucc.castSucc) (fun i => (P i).castSucc.castSucc.castSucc)) := by
    let d : Fin 3 → Fin (m+3) := Fin.cases (Fin.last m).castSucc.castSucc (Fin.cases (Fin.last (m+1)).castSucc (fun _ => Fin.last (m+2)))
    have hData : Derives Ω (data w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc
      (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (n i).castSucc.castSucc.castSucc) (fun i => (q i).castSucc.castSucc.castSucc) (fun i => (P i).castSucc.castSucc.castSucc) d) :=
      Derives.conjI hE3 (Derives.conjI hB3 hL)
    apply HornBinderRules.intro_many 3 _ d
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (by simp only [Formula.raise, produced_rename]) hout


private def threeAnd {m} (F : Fin 3 → Formula m) : Formula m := (F 0).conj ((F 1).conj (F 2))
private theorem threeAnd_at {m} {Γ : Context m} (F : Fin 3 → Formula m) (i : Fin 3) (h : Derives Γ (threeAnd F)) : Derives Γ (F i) :=
  Fin.cases (Derives.conjL h) (Fin.cases (Derives.conjL (Derives.conjR h)) (Fin.cases (Derives.conjR (Derives.conjR h)) (fun i => Fin.elim0 i))) i

private def sourceRow {m} (i : Fin 3) (w : Fin m) (a n : Fin 4 → Fin m) : Formula m :=
  (successor (a i.succ) (a i.castSucc)).conj (SyntaxLogicalSyntax.singleCode 9 w (n i.succ) (n i.castSucc))
private theorem sourceRow_rename {m l} (i : Fin 3) (w : Fin m) (a n : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (sourceRow i w a n).rename ρ = sourceRow i (ρ w) (fun i => ρ (a i)) (fun i => ρ (n i)) := by
  simp only [sourceRow, Formula.rename, successor_rename, SyntaxLogicalSyntax.singleCode_rename]

/-- Actual raw three-ALL fields and the initial mixed opening; only syntax
operations, not the truth or provability of the preorder. -/
def basis {m} (w z f T R S U : Fin m) (a n : Fin 4 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w (a 0) f z T R S).conj
    ((substituted w R S (a 0) f z T (n 0) U).conj (threeAnd (fun i => sourceRow i w a n)))))

theorem basis_rename {m l} (w z f T R S U : Fin m) (a n : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (basis w z f T R S U a n).rename ρ = basis (ρ w) (ρ z) (ρ f) (ρ T) (ρ R) (ρ S) (ρ U)
      (fun i => ρ (a i)) (fun i => ρ (n i)) := by
  simp only [basis, threeAnd, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename, substituted_rename, sourceRow_rename]

private def row {m} (i : Fin 3) (w z T C : Fin m) (q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) : Formula m :=
  (SyntaxLogicalSyntax.singleCode 9 w (F i) (q i.castSucc)).conj (SyntaxTopFormulaSyntax.instantiated w z T C (P i) (F i) (q i.succ))
private theorem row_rename {m l} (i : Fin 3) (w z T C : Fin m) (q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (row i w z T C q F P).rename ρ = row i (ρ w) (ρ z) (ρ T) (ρ C) (fun i => ρ (q i)) (fun i => ρ (F i)) (fun i => ρ (P i)) := by
  simp only [row, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

def input {m} (w z f T C R S : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) : Formula m :=
  (basis w z f T R S (q 0) a n).conj (threeAnd (fun i => row i w z T C q F P))

theorem input_rename {m l} (w z f T C R S : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (input w z f T C R S a n q F P).rename ρ = input (ρ w) (ρ z) (ρ f) (ρ T) (ρ C) (ρ R) (ρ S)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (q i)) (fun i => ρ (F i)) (fun i => ρ (P i)) := by
  simp only [input, threeAnd, Formula.rename, basis_rename, row_rename]

/-- Generate ALL three real prefix lists and direct outputs to the SAME
three native instance values. All runtime codes/scopes remain internal. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f T C R S : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m)
    (hi : Derives Γ (input w z f T C R S a n q F P)) : Derives Γ (produced w z f T R S a n q P) := by
  have hb := Derives.conjL hi
  have hs := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb)))
  have ht := Derives.conjR hi
  let h : Inputs Γ w z f T C a n q F P := {
    zf := hZ
    omega := Derives.conjL hb
    zero := Derives.conjL (Derives.conjR hb)
    scopes := fun i => Derives.conjL (threeAnd_at _ i hs)
    sourceFields := fun i => Derives.conjR (threeAnd_at _ i hs)
    targetFields := fun i => Derives.conjL (threeAnd_at _ i ht)
    instances := fun i => Derives.conjR (threeAnd_at _ i ht)
  }
  exact from_rows h R S (Derives.conjL (Derives.conjR (Derives.conjR hb))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hb))))

def sentence {m} (w z f T C R S : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) : Source.Sentence :=
  ((input w z f T C R S a n q F P).imp (produced w z f T R S a n q P)).close

theorem kernel_certificate {m} (w z f T C R S : Fin m) (a n q : Fin 4 → Fin m) (F P : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z f T C R S a n q F P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w z f T C R S a n q F P
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) w z f T C R S a n q F P (.hyp (Or.inl rfl))


private def quad {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private def three {α : Type} (a b c : α) : Fin 3 → α := Fin.cases a (Fin.cases b (fun _ => c))
private theorem quad_map {α β : Type} (a b c d : α) (ρ : α → β) :
    (fun i => ρ (quad a b c d i)) = quad (ρ a) (ρ b) (ρ c) (ρ d) := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
private theorem three_map {α β : Type} (a b c : α) (ρ : α → β) :
    (fun i => ρ (three a b c i)) = three (ρ a) (ρ b) (ρ c) := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) i

private def pair {m} (w z T C P F Q q : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.singleCode 9 w F Q).conj (SyntaxTopFormulaSyntax.instantiated w z T C P F q)
private theorem pair_rename {m l} (w z T C P F Q q : Fin m) (ρ : Fin m → Fin l) :
    (pair w z T C P F Q q).rename ρ = pair (ρ w) (ρ z) (ρ T) (ρ C) (ρ P) (ρ F) (ρ Q) (ρ q) := by
  simp only [pair, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

private def link {m} (w z T C P Q : Fin m) (rest : Formula (m+2)) : Formula m := existsMany 2
  ((SyntaxLogicalSyntax.singleCode 9 (old 2 w) (slot 2 0) (old 2 Q)).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 P) (slot 2 0) (slot 2 1)).conj rest))

private def chain {m} (w z T C U : Fin m) (P : Fin 3 → Fin m) (rest : Formula (m+6)) : Formula m :=
  link w z T C (P 0) U
    (link (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 1)) (slot 2 1)
      (link (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 2)) (slot 4 3) rest))

/-- The SIX native body/instance values and THREE prefix lists are all
object witnesses. Exact parent/child fields and every original native
operation are retained, not replaced with an equality answer. -/
def normalizedBody {m} (w z f T C R S U : Fin m) (a n : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula (m+6) :=
  (input (old 6 w) (old 6 z) (old 6 f) (old 6 T) (old 6 C) (old 6 R) (old 6 S)
    (fun i => old 6 (a i)) (fun i => old 6 (n i)) (quad (old 6 U) (slot 6 1) (slot 6 3) (slot 6 5))
    (three (slot 6 0) (slot 6 2) (slot 6 4)) (fun i => old 6 (P i))).conj
      (produced (old 6 w) (old 6 z) (old 6 f) (old 6 T) (old 6 R) (old 6 S)
        (fun i => old 6 (a i)) (fun i => old 6 (n i)) (quad (old 6 U) (slot 6 1) (slot 6 3) (slot 6 5)) (fun i => old 6 (P i)))

def normalized {m} (w z f T C R S U : Fin m) (a n : Fin 4 → Fin m) (P : Fin 3 → Fin m) : Formula m :=
  existsMany 6 (normalizedBody w z f T C R S U a n P)

theorem normalized_rename {m l} (w z f T C R S U : Fin m) (a n : Fin 4 → Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (normalized w z f T C R S U a n P).rename ρ = normalized (ρ w) (ρ z) (ρ f) (ρ T) (ρ C) (ρ R) (ρ S) (ρ U)
      (fun i => ρ (a i)) (fun i => ρ (n i)) (fun i => ρ (P i)) := by
  simp only [normalized, existsMany_rename, normalizedBody, Formula.rename, input_rename, produced_rename, quad_map, three_map, lift_old, lift_slot]

private theorem from_chain {m} {Γ : Context m} {rest : Formula (m+6)} (hZ : ZFContext.Evidence Γ)
    (w z f T C R S U : Fin m) (a n : Fin 4 → Fin m) (P : Fin 3 → Fin m)
    (hb : Derives Γ (basis w z f T R S U a n)) (hc : Derives Γ (chain w z T C U P rest)) :
    Derives Γ (normalized w z f T C R S U a n P) := by
  let E := (SyntaxLogicalSyntax.singleCode 9 (old 2 w) (slot 2 0) (old 2 U)).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 0)) (slot 2 0) (slot 2 1)).conj
      (link (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 1)) (slot 2 1)
        (link (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 2)) (slot 4 3) rest)))
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hb2 := of_eq (basis_rename w z f T R S U a n (old 2)) (HornBinderRules.under_body 2 hb E)
  have h0 : Derives Δ (pair (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 0)) (slot 2 0) (old 2 U) (slot 2 1)) :=
    Derives.conjI (Derives.conjL hE) (Derives.conjL (Derives.conjR hE))
  let B := (SyntaxLogicalSyntax.singleCode 9 (old 4 w) (slot 4 2) (slot 4 1)).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 1)) (slot 4 2) (slot 4 3)).conj
      (link (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 2)) (slot 4 3) rest))
  let Ξ := Context.add B (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 B _ (Derives.conjR (Derives.conjR hE))
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 2 hZ2 B
  have hb4 := of_eq (basis_rename (old 2 w) (old 2 z) (old 2 f) (old 2 T) (old 2 R) (old 2 S) (old 2 U)
    (fun i => old 2 (a i)) (fun i => old 2 (n i)) (old 2)) (HornBinderRules.under_body 2 hb2 B)
  have h04 := of_eq (pair_rename (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 0)) (slot 2 0) (old 2 U) (slot 2 1) (old 2)) (HornBinderRules.under_body 2 h0 B)
  have h1 : Derives Ξ (pair (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 1)) (slot 4 2) (slot 4 1) (slot 4 3)) :=
    Derives.conjI (Derives.conjL hB) (Derives.conjL (Derives.conjR hB))
  let L := (SyntaxLogicalSyntax.singleCode 9 (old 6 w) (slot 6 4) (slot 6 3)).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 2)) (slot 6 4) (slot 6 5)).conj rest)
  let Ω := Context.add L (raisedContext 2 Ξ)
  apply HornBinderRules.eliminate_many 2 L _ (Derives.conjR (Derives.conjR hB))
  have hL : Derives Ω L := .hyp (Or.inl rfl)
  have hZ6 := HornBinderRules.zf_body 2 hZ4 L
  have hb6 := of_eq (basis_rename (old 4 w) (old 4 z) (old 4 f) (old 4 T) (old 4 R) (old 4 S) (old 4 U)
    (fun i => old 4 (a i)) (fun i => old 4 (n i)) (old 2)) (HornBinderRules.under_body 2 hb4 L)
  have h06 := of_eq (pair_rename (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 0)) (slot 4 0) (old 4 U) (slot 4 1) (old 2)) (HornBinderRules.under_body 2 h04 L)
  have h16 := of_eq (pair_rename (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 1)) (slot 4 2) (slot 4 1) (slot 4 3) (old 2)) (HornBinderRules.under_body 2 h1 L)
  have h26 : Derives Ω (pair (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 2)) (slot 6 4) (slot 6 3) (slot 6 5)) :=
    Derives.conjI (Derives.conjL hL) (Derives.conjL (Derives.conjR hL))
  let qv := quad (old 6 U) (slot 6 1) (slot 6 3) (slot 6 5)
  let fv : Fin 3 → Fin (m+6) := three (slot 6 0) (slot 6 2) (slot 6 4)
  have hInput : Derives Ω (input (old 6 w) (old 6 z) (old 6 f) (old 6 T) (old 6 C) (old 6 R) (old 6 S)
    (fun i => old 6 (a i)) (fun i => old 6 (n i)) qv fv (fun i => old 6 (P i))) :=
    Derives.conjI hb6 (Derives.conjI h06 (Derives.conjI h16 h26))
  have hOut := produce hZ6 (old 6 w) (old 6 z) (old 6 f) (old 6 T) (old 6 C) (old 6 R) (old 6 S)
    (fun i => old 6 (a i)) (fun i => old 6 (n i)) qv fv (fun i => old 6 (P i)) hInput
  have hData := Derives.conjI hInput hOut
  have hout : Derives Ω (normalized (old 6 w) (old 6 z) (old 6 f) (old 6 T) (old 6 C) (old 6 R) (old 6 S) (old 6 U)
    (fun i => old 6 (a i)) (fun i => old 6 (n i)) (fun i => old 6 (P i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [normalizedBody, Formula.rename, input_rename, produced_rename, quad_map, three_map, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (by simp only [normalized_rename] <;> rfl) hout


/-- Consume the already GENERATED original raw quotation and targetData,
including its SAME actual three native instances. All six body/instance
codes and all three direct prefix tables stay existential object witnesses.
No separately supplied six-state instance witnesses, prefix table code,
direct output, or desired equality is supplied. -/
theorem at_target {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Formula (k+2))
    (w z A1 A2 A3 f T C B S Pre Refl U : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (successor A1 z)) (hA2 : Derives Γ (successor A2 A1)) (hA3 : Derives Γ (successor A3 A2))
    (hr : Derives Γ (ForcingPreorderCode.rawData Reln w z A1 A2 A3 f v))
    (ht : Derives Γ (ForcingPreorderInstances.targetData test w z f T C B S (v 0) (v 1) (v 2) P Pre Refl U)) :
    Derives Γ (normalized w z f T C B S U (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) P) := by
  have hParent := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ht)))))
  have hChain := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ht))))))
  have hs0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))
  have hs1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))
  have hs2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))
  have he := Derives.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) U hw hParent)
  have hb : Derives Γ (basis w z f T B S U (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5))) :=
    Derives.conjI hw (Derives.conjI hz (Derives.conjI he (Derives.conjI hParent
      (Derives.conjI (Derives.conjI hA1 hs0) (Derives.conjI (Derives.conjI hA2 hs1) (Derives.conjI hA3 hs2))))))
  exact from_chain hZ w z f T C B S U (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) P hb hChain

def targetInput {k m} (test : Formula 1) (Reln : Formula (k+2))
    (w z A1 A2 A3 f T C B S Pre Refl U : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A1 z).conj ((successor A2 A1).conj ((successor A3 A2).conj
    ((ForcingPreorderCode.rawData Reln w z A1 A2 A3 f v).conj
      (ForcingPreorderInstances.targetData test w z f T C B S (v 0) (v 1) (v 2) P Pre Refl U))))))

def targetSentence {k m} (test : Formula 1) (Reln : Formula (k+2))
    (w z A1 A2 A3 f T C B S Pre Refl U : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m) : Source.Sentence :=
  ((targetInput test Reln w z A1 A2 A3 f T C B S Pre Refl U P v).imp
    (normalized w z f T C B S U (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) P)).close

theorem target_kernel_certificate {k m} (test : Formula 1) (Reln : Formula (k+2))
    (w z A1 A2 A3 f T C B S Pre Refl U : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (targetSentence test Reln w z A1 A2 A3 f T C B S Pre Refl U P v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := targetInput test Reln w z A1 A2 A3 f T C B S Pre Refl U P v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact at_target (ZFContext.add (ZFContext.source_ZF m) E) test Reln w z A1 A2 A3 f T C B S Pre Refl U P v
    (Derives.conjL h)    (Derives.conjL (Derives.conjR h))    (Derives.conjL (Derives.conjR (Derives.conjR h)))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))

end PPAC.Migration.ForcingPreorderPrefix
