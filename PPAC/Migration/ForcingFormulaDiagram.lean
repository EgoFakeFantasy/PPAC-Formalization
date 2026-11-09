import PPAC.Migration.ForcingTermDiagram
import PPAC.Migration.ForcingMixedUnary

/-! Four actual mixed FORMULA substitutions, with all output candidates
quantified in the object language. Unary cancellation below is an induction
step; the full internal formula induction and final Con are not asserted. -/
namespace PPAC.Migration.ForcingFormulaDiagram
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def src : Fin 4 → Fin 4 := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun _ => 0)))
private def dst : Fin 4 → Fin 4 := Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (fun _ => 3)))

def step {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (e : Fin 4) (x y : Fin m) : Formula m :=
  SyntaxMixedFormulaJudgmentSyntax.substituted w (R e) (S e) (a (src e)) (b (src e)) (a (dst e)) (b (dst e)) x y

theorem step_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (e : Fin 4) (x y : Fin m) (r : Fin m → Fin l) :
    (step w a b R S e x y).rename r = step (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) e (r x) (r y) := by
  simp only [step, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private def path {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  (step w a b R S 0 x u).conj ((step w a b R S 1 u t).conj ((step w a b R S 2 t y).conj (step w a b R S 3 x o)))
private theorem path_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) (r : Fin m → Fin l) :
    (path w a b R S x u t y o).rename r = path (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) := by
  simp only [path, Formula.rename, step_rename]
private def sourceBody {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x : Fin m) : Formula (m+4) :=
  (path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 x)
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp (.equal (slot 4 2) (slot 4 3))

/-- Four output candidates, including intermediate results, are object-bound. -/
def atSource {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 4 (sourceBody w a b R S x)

theorem atSource_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (x : Fin m) (r : Fin m → Fin l) :
    (atSource w a b R S x).rename r = atSource (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) := by
  simp only [atSource, OriginalUniversalBlock.allMany_rename, sourceBody, Formula.rename, path_rename, lift_old, lift_slot]

theorem apply_atSource {m} {Γ : Context m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m)
    (hc : Derives Γ (atSource w a b R S x)) (h0 : Derives Γ (step w a b R S 0 x u))
    (h1 : Derives Γ (step w a b R S 1 u t)) (h2 : Derives Γ (step w a b R S 2 t y))
    (h3 : Derives Γ (step w a b R S 3 x o)) : Derives Γ (.equal y o) := by
  have hp : Derives Γ ((path w a b R S x u t y o).imp (.equal y o)) := of_eq
    (by simp only [sourceBody, Formula.rename, path_rename, assign_old, assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 4 _ ((Fin.cases u (Fin.cases t (Fin.cases y (fun _ => o))))) hc)
  exact .impE hp (.conjI h0 (.conjI h1 (.conjI h2 h3)))

private def singleData {m} (tag : Nat) (advance : Bool) (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o U T Y O : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.singleCode tag w U u).conj ((SyntaxLogicalSyntax.singleCode tag w T t).conj
    ((SyntaxLogicalSyntax.singleCode tag w Y y).conj ((SyntaxLogicalSyntax.singleCode tag w O o).conj
      ((SyntaxMixedFormulaRecursiveSyntax.check advance w x (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) U).conj
        ((SyntaxMixedFormulaRecursiveSyntax.check advance w U (R 1) (S 1) (a 1) (b 1) (a 2) (b 2) T).conj
          ((SyntaxMixedFormulaRecursiveSyntax.check advance w T (R 2) (S 2) (a 2) (b 2) (a 3) (b 3) Y).conj
            (SyntaxMixedFormulaRecursiveSyntax.check advance w x (R 3) (S 3) (a 0) (b 0) (a 3) (b 3) O)))))))
private theorem singleData_rename {m l} (tag : Nat) (advance : Bool) (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o U T Y O : Fin m) (r : Fin m → Fin l) :
    (singleData tag advance w a b R S x u t y o U T Y O).rename r =
      singleData tag advance (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) (r U) (r T) (r Y) (r O) := by
  simp only [singleData, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxMixedFormulaRecursiveSyntax.check_rename]
private def singleBody {m} (tag : Nat) (advance : Bool) (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula (m+4) :=
  singleData tag advance (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 x) (old 4 u) (old 4 t) (old 4 y) (old 4 o) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
private def singleOutputs {m} (tag : Nat) (advance : Bool) (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  existsMany 4 (singleBody tag advance w a b R S x u t y o)
private theorem singleOutputs_rename {m l} (tag : Nat) (advance : Bool) (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) (r : Fin m → Fin l) :
    (singleOutputs tag advance w a b R S x u t y o).rename r =
      singleOutputs tag advance (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) := by
  simp only [singleOutputs, existsMany_rename, singleBody, singleData_rename, lift_old, lift_slot]

private theorem unary_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (singleOutputs tag advance w a b R S x u t y o) := by
  have he0 := ForcingMixedUnary.single_output hZ tag advance valid w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n x u hw hc (.conjL hp)
  let E0 := (SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) u.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc (R 0).castSucc (S 0).castSucc (a 0).castSucc (b 0).castSucc (a 1).castSucc (b 1).castSucc (Fin.last m))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E0)
  have hp1 := of_eq (path_rename w a b R S n u t y o Fin.castSucc) (under hp E0)
  have he1 := ForcingMixedUnary.single_output hZ1 tag advance valid w.castSucc (R 1).castSucc (S 1).castSucc (a 1).castSucc (b 1).castSucc (a 2).castSucc (b 2).castSucc u.castSucc (Fin.last m) t.castSucc hw1 (.conjL hE0) (.conjL (.conjR hp1))
  let E1 := (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc (Fin.last (m+1)) t.castSucc.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc.castSucc ((Fin.last m)).castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E1)
  have hp2 := of_eq (path_rename w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (R i).castSucc) (fun i => (S i).castSucc) n.castSucc u.castSucc t.castSucc y.castSucc o.castSucc Fin.castSucc) (under hp1 E1)
  have he2 := ForcingMixedUnary.single_output hZ2 tag advance valid w.castSucc.castSucc (R 2).castSucc.castSucc (S 2).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (a 3).castSucc.castSucc (b 3).castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hw2 (.conjL hE1) (.conjL (.conjR (.conjR hp2)))
  let E2 := (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc.castSucc (Fin.last (m+2)) y.castSucc.castSucc.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc.castSucc.castSucc ((Fin.last (m+1))).castSucc (R 2).castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 E2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 E2)
  have hp3 := of_eq (path_rename w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) n.castSucc.castSucc u.castSucc.castSucc t.castSucc.castSucc y.castSucc.castSucc o.castSucc.castSucc Fin.castSucc) (under hp2 E2)
  have hc3 : Derives Δ3 (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under (under (under hc E0) E1) E2)
  have he3 := ForcingMixedUnary.single_output hZ3 tag advance valid w.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc hw3 hc3 (.conjR (.conjR (.conjR hp3)))
  let E3 := (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) o.castSucc.castSucc.castSucc.castSucc).conj
    (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)))
  let Δ4 := Context.add E3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := E3) he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hB0 := (under (under (under hE0 E1) E2) E3)
  have hB1 := (under (under hE1 E2) E3)
  have hB2 := (under hE2 E3)
  have hout : Derives Δ4 (singleOutputs tag advance (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i))
      (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 x) (old 4 u) (old 4 t) (old 4 y) (old 4 o)) := by
    apply HornBinderRules.intro_many 4 _ (fun i => slot 4 i)
    exact of_eq (by simp only [singleBody, assign_old, assign_slot, singleData, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, SyntaxMixedFormulaRecursiveSyntax.check_rename]; rfl)
      (.conjI (.conjL hB0) (.conjI (.conjL hB1) (.conjI (.conjL hB2) (.conjI (.conjL hE3)
        (.conjI (.conjR hB0) (.conjI (.conjR hB1) (.conjI (.conjR hB2) (.conjR hE3))))))))
  exact of_eq (by simp only [Formula.raise, singleOutputs_rename]; rfl) hout

private theorem single_parent_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w Y O y o : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.equal Y O))
    (hy : Derives Γ (SyntaxLogicalSyntax.singleCode tag w Y y))
    (ho : Derives Γ (SyntaxLogicalSyntax.singleCode tag w O o)) : Derives Γ (.equal y o) := by
  let P := SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) y.castSucc
  have hy' : Derives Γ (SyntaxLogicalSyntax.singleCode tag w O y) := of_eq
    (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy))
  exact SyntaxLogicalFields.single_unique hZ tag w O y o hw hy' ho

private theorem negation_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    (hchild : Derives Γ (atSource w a b R S x))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (.equal y o) := by
  let B := singleBody 4 false w a b R S x u t y o
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ (unary_outputs hZ 4 false (Or.inl ⟨rfl, rfl⟩) w a b R S n x u t y o hw hc hp)
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hc4 := of_eq (atSource_rename w a b R S x (old 4)) (HornBinderRules.under_body 4 hchild B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h0 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hB))))
  have h1 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have h2 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))
  have h3 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))
  have q0 := h0
  have q1 := h1
  have q2 := h2
  have q3 := h3
  have he := apply_atSource (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 x) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hc4 q0 q1 q2 q3
  exact single_parent_eq hZ4 4 (old 4 w) (slot 4 2) (slot 4 3) (old 4 y) (old 4 o) hw4 he
    (.conjL (.conjR (.conjR hB))) (.conjL (.conjR (.conjR (.conjR hB))))

/-- Original negation preserve the four-path cancellation property.
The child property is an OBJECT formula, not a host-level equality assumption. -/
theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    (hchild : Derives Γ (atSource w a b R S x))
    : Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  exact negation_point (HornBinderRules.zf_body 4 hZ B) (old 4 w)
    (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 n) (old 4 x) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 4 w x n (old 4)) (HornBinderRules.under_body 4 hc B))
    (of_eq (atSource_rename w a b R S x (old 4)) (HornBinderRules.under_body 4 hchild B))
    (.hyp (Or.inl rfl))

private theorem quantified_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (n x u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hchild : Derives Γ (atSource w A b K H x))
    (hl : Derives Γ (ForcingTermDiagram.lifts w a b A R S K H))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (.equal y o) := by
  let B := singleBody (SyntaxLogicalSyntax.quantifierTag universal) true w a b R S x u t y o
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ (unary_outputs hZ (SyntaxLogicalSyntax.quantifierTag universal) true (by cases universal <;> simp [SyntaxLogicalSyntax.quantifierTag]) w a b R S n x u t y o hw hc hp)
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hc4 := of_eq (atSource_rename w A b K H x (old 4)) (HornBinderRules.under_body 4 hchild B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have h0 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hB))))
  have h1 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have h2 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))
  have h3 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hB))))))
  have hl4 := of_eq (ForcingTermDiagram.lifts_rename w a b A R S K H (old 4)) (HornBinderRules.under_body 4 hl B)
  have q0 := Derives.impE (.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ4 (old 4 w) (old 4 x) (old 4 (R 0)) (old 4 (S 0)) (old 4 (a 0)) (old 4 (b 0)) (old 4 (a 1)) (old 4 (b 1)) (slot 4 0) (old 4 (A 0)) (old 4 (A 1)) (old 4 (K 0)) (old 4 (H 0)) hw4 (.conjL hl4))) h0
  have q1 := Derives.impE (.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ4 (old 4 w) (slot 4 0) (old 4 (R 1)) (old 4 (S 1)) (old 4 (a 1)) (old 4 (b 1)) (old 4 (a 2)) (old 4 (b 2)) (slot 4 1) (old 4 (A 1)) (old 4 (A 2)) (old 4 (K 1)) (old 4 (H 1)) hw4 (.conjL (.conjR hl4)))) h1
  have q2 := Derives.impE (.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ4 (old 4 w) (slot 4 1) (old 4 (R 2)) (old 4 (S 2)) (old 4 (a 2)) (old 4 (b 2)) (old 4 (a 3)) (old 4 (b 3)) (slot 4 2) (old 4 (A 2)) (old 4 (A 3)) (old 4 (K 2)) (old 4 (H 2)) hw4 (.conjL (.conjR (.conjR hl4))))) h2
  have q3 := Derives.impE (.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ4 (old 4 w) (old 4 x) (old 4 (R 3)) (old 4 (S 3)) (old 4 (a 0)) (old 4 (b 0)) (old 4 (a 3)) (old 4 (b 3)) (slot 4 3) (old 4 (A 0)) (old 4 (A 3)) (old 4 (K 3)) (old 4 (H 3)) hw4 (.conjR (.conjR (.conjR hl4))))) h3
  have he := apply_atSource (old 4 w) (fun i => old 4 (A i)) (fun i => old 4 (b i)) (fun i => old 4 (K i)) (fun i => old 4 (H i)) (old 4 x) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hc4 q0 q1 q2 q3
  exact single_parent_eq hZ4 (SyntaxLogicalSyntax.quantifierTag universal) (old 4 w) (slot 4 2) (slot 4 3) (old 4 y) (old 4 o) hw4 he
    (.conjL (.conjR (.conjR hB))) (.conjL (.conjR (.conjR (.conjR hB))))

/-- Both original quantifiers preserve the four-path cancellation property.
The child property is an OBJECT formula, not a host-level equality assumption. -/
theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (n x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hchild : Derives Γ (atSource w A b K H x))
    (hl : Derives Γ (ForcingTermDiagram.lifts w a b A R S K H))
    : Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  exact quantified_point (HornBinderRules.zf_body 4 hZ B) universal (old 4 w)
    (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (A i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (fun i => old 4 (K i)) (fun i => old 4 (H i)) (old 4 n) (old 4 x) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B))
    (of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n (old 4)) (HornBinderRules.under_body 4 hc B))
    (of_eq (atSource_rename w A b K H x (old 4)) (HornBinderRules.under_body 4 hchild B))
    (of_eq (ForcingTermDiagram.lifts_rename w a b A R S K H (old 4)) (HornBinderRules.under_body 4 hl B))
    (.hyp (Or.inl rfl))

def binaryData {m} (kind : Fin 4) (w R S a b c d x y q X Y : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode kind w X Y q).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y))
theorem binaryData_rename {m l} (kind : Fin 4) (w R S a b c d x y q X Y : Fin m) (r : Fin m → Fin l) :
    (binaryData kind w R S a b c d x y q X Y).rename r = binaryData kind (r w) (r R) (r S) (r a) (r b) (r c) (r d) (r x) (r y) (r q) (r X) (r Y) := by
  simp only [binaryData, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]
def binaryBody {m} (kind : Fin 4) (w R S a b c d x y q : Fin m) : Formula (m+2) :=
  binaryData kind (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 x) (old 2 y) (old 2 q) (slot 2 0) (slot 2 1)
def binaryOutput {m} (kind : Fin 4) (w R S a b c d x y q : Fin m) : Formula m := existsMany 2 (binaryBody kind w R S a b c d x y q)
theorem binaryOutput_rename {m l} (kind : Fin 4) (w R S a b c d x y q : Fin m) (r : Fin m → Fin l) :
    (binaryOutput kind w R S a b c d x y q).rename r = binaryOutput kind (r w) (r R) (r S) (r a) (r b) (r c) (r d) (r x) (r y) (r q) := by
  simp only [binaryOutput, existsMany_rename, binaryBody, binaryData_rename, lift_old, lift_slot]

theorem binary_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S a b c d n x y q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hp : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (binaryOutput kind w R S a b c d x y q) := by
  have hs := SyntaxMixedFormulaLogicalKnown.binary_of_substituted hZ kind w R S a b c d n q x y hw hc hp
  let B := SyntaxMixedFormulaRecursiveSyntax.binaryBody kind w R S a b c d n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hs
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hc4 := of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n (old 4)) (HornBinderRules.under_body 4 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have es := SyntaxLogicalFields.binary_fields hZ4 kind (old 4 w) (slot 4 0) (slot 4 1) (old 4 x) (old 4 y) (old 4 n) hw4 (.conjL hB) hc4
  have hx := SyntaxMixedFormulaJudgmentSubst.subst_n (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
    (slot 4 0) (slot 4 2) (old 4 x) (.conjL es) (.conjL (.conjR (.conjR (.conjR (.conjR hB)))))
  have hy := SyntaxMixedFormulaJudgmentSubst.subst_n (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
    (slot 4 1) (slot 4 3) (old 4 y) (.conjR es) (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have hout : Derives Δ (binaryOutput kind (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 x) (old 4 y) (old 4 q)) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (slot 4 2) (slot 4 3))
    exact of_eq (by simp only [binaryBody, binaryData_rename, assign_old, assign_slot]; rfl)
      (.conjI (.conjL (.conjR (.conjR (.conjR hB)))) (.conjI hx hy))
  exact of_eq (binaryOutput_rename kind w R S a b c d x y q (old 4)).symm hout

private theorem binary_parent_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w X Y U V n o : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.equal X U)) (hy : Derives Γ (.equal Y V))
    (hn : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y n))
    (ho : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w U V o)) : Derives Γ (.equal n o) := by
  let P := SyntaxLogicalSyntax.binaryCode kind w.castSucc (Fin.last m) Y.castSucc n.castSucc
  have hn1 : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w U Y n) := of_eq
    (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P hx (of_eq (by simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn))
  let Q := SyntaxLogicalSyntax.binaryCode kind w.castSucc U.castSucc (Fin.last m) n.castSucc
  have hn2 : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w U V n) := of_eq
    (by simp only [Q, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst Q hy (of_eq (by simp only [Q, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn1))
  exact SyntaxLogicalFields.binary_unique hZ kind w U V n o hw hn2 ho

private theorem binary_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x z u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x z n))
    (hx : Derives Γ (atSource w a b R S x)) (hz : Derives Γ (atSource w a b R S z))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (.equal y o) := by
  have he0 := binary_output hZ kind w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n x z u hw hc (.conjL hp)
  let E0 := binaryBody kind w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) x z u
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ E0
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E0)
  have hp1 := of_eq (path_rename w a b R S n u t y o (old 2)) (HornBinderRules.under_body 2 hp E0)
  have he1 := binary_output hZ1 kind w.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc u.castSucc.castSucc (slot 2 0 (m := m+0)) (slot 2 1 (m := m+0)) t.castSucc.castSucc hw1 (.conjL hE0) (.conjL (.conjR hp1))
  let E1 := binaryBody kind w.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (slot 2 0 (m := m+0)) (slot 2 1 (m := m+0)) t.castSucc.castSucc
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hp2 := of_eq (path_rename w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) n.castSucc.castSucc u.castSucc.castSucc t.castSucc.castSucc y.castSucc.castSucc o.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hp1 E1)
  have he2 := binary_output hZ2 kind w.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+2)) (slot 2 1 (m := m+2)) y.castSucc.castSucc.castSucc.castSucc hw2 (.conjL hE1) (.conjL (.conjR (.conjR hp2)))
  let E2 := binaryBody kind w.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+2)) (slot 2 1 (m := m+2)) y.castSucc.castSucc.castSucc.castSucc
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ2 E2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hp3 := of_eq (path_rename w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hp2 E2)
  have hc3 : Derives Δ3 (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hc E0) E1) E2)
  have he3 := binary_output hZ3 kind w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw3 hc3 (.conjR (.conjR (.conjR hp3)))
  let E3 := binaryBody kind w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ4 := Context.add E3 (raisedContext 2 Δ3)
  apply HornBinderRules.eliminate_many 2 E3 _ he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hB0 : Derives Δ4 (binaryData kind (old 8 w) (old 8 (R 0)) (old 8 (S 0)) (old 8 (a 0)) (old 8 (b 0)) (old 8 (a 1)) (old 8 (b 1)) (old 8 x) (old 8 z) (old 8 u) (slot 8 0) (slot 8 1)) := of_eq (by simp only [E0, binaryBody, binaryData_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hE0 E1) E2) E3)
  have hB1 : Derives Δ4 (binaryData kind (old 8 w) (old 8 (R 1)) (old 8 (S 1)) (old 8 (a 1)) (old 8 (b 1)) (old 8 (a 2)) (old 8 (b 2)) (slot 8 0) (slot 8 1) (old 8 t) (slot 8 2) (slot 8 3)) := of_eq (by simp only [E1, binaryBody, binaryData_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hE1 E2) E3)
  have hB2 : Derives Δ4 (binaryData kind (old 8 w) (old 8 (R 2)) (old 8 (S 2)) (old 8 (a 2)) (old 8 (b 2)) (old 8 (a 3)) (old 8 (b 3)) (slot 8 2) (slot 8 3) (old 8 y) (slot 8 4) (slot 8 5)) := of_eq (by simp only [E2, binaryBody, binaryData_rename]; rfl) (HornBinderRules.under_body 2 hE2 E3)
  have hw8 : Derives Δ4 (omega (old 8 w)) := of_eq (by simp only [omega_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw E0) E1) E2) E3)
  have hx8 : Derives Δ4 (atSource (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 x)) := of_eq (by simp only [atSource_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hx E0) E1) E2) E3)
  have hz8 : Derives Δ4 (atSource (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 z)) := of_eq (by simp only [atSource_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hz E0) E1) E2) E3)
  have hZ8 := (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ E0) E1) E2) E3)
  have e0 := apply_atSource (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 x) (slot 8 0) (slot 8 2) (slot 8 4) (slot 8 6) hx8 (.conjL (.conjR hB0)) (.conjL (.conjR hB1)) (.conjL (.conjR hB2)) (.conjL (.conjR hE3))
  have e1 := apply_atSource (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 z) (slot 8 1) (slot 8 3) (slot 8 5) (slot 8 7) hz8 (.conjR (.conjR hB0)) (.conjR (.conjR hB1)) (.conjR (.conjR hB2)) (.conjR (.conjR hE3))
  exact binary_parent_eq hZ8 kind (old 8 w) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 y) (old 8 o) hw8 e0 e1 (.conjL hB2) (.conjL hE3)

/-- All four original binary constructors preserve object four-path cancellation.
All eight actual child outputs are internally generated and eliminated. -/
theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x z : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x z n))
    (hx : Derives Γ (atSource w a b R S x)) (hz : Derives Γ (atSource w a b R S z)) :
    Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  exact binary_point (HornBinderRules.zf_body 4 hZ B) kind (old 4 w)
    (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (old 4 x) (old 4 z) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B))
    (of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x z n (old 4)) (HornBinderRules.under_body 4 hc B))
    (of_eq (atSource_rename w a b R S x (old 4)) (HornBinderRules.under_body 4 hx B))
    (of_eq (atSource_rename w a b R S z (old 4)) (HornBinderRules.under_body 4 hz B))
    (.hyp (Or.inl rfl))

def negationInput {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n x : Fin m) : Formula m :=
  (omega w).conj ((SyntaxLogicalSyntax.singleCode 4 w x n).conj (atSource w a b R S x))

def negationSentence {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n x : Fin m) : Source.Sentence :=
  ((negationInput w a b R S n x).imp (atSource w a b R S n)).close

theorem negation_kernel_certificate {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n x : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (negationSentence w a b R S n x)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := negationInput w a b R S n x
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact negation (ZFContext.add (ZFContext.source_ZF m) E) w a b R S n x
    (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

def quantifiedInput {m} (universal : Bool) (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (n x : Fin m) : Formula m :=
  (omega w).conj ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).conj ((atSource w A b K H x).conj (ForcingTermDiagram.lifts w a b A R S K H)))

def quantifiedSentence {m} (universal : Bool) (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (n x : Fin m) : Source.Sentence :=
  ((quantifiedInput universal w a b A R S K H n x).imp (atSource w a b R S n)).close

theorem quantified_kernel_certificate {m} (universal : Bool) (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (n x : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (quantifiedSentence universal w a b A R S K H n x)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := quantifiedInput universal w a b A R S K H n x
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact quantified (ZFContext.add (ZFContext.source_ZF m) E) universal w a b A R S K H n x
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))

def binaryInput {m} (kind : Fin 4) (w : Fin m) (a b R S : Fin 4 → Fin m) (n x z : Fin m) : Formula m :=
  (omega w).conj ((SyntaxLogicalSyntax.binaryCode kind w x z n).conj ((atSource w a b R S x).conj (atSource w a b R S z)))

def binarySentence {m} (kind : Fin 4) (w : Fin m) (a b R S : Fin 4 → Fin m) (n x z : Fin m) : Source.Sentence :=
  ((binaryInput kind w a b R S n x z).imp (atSource w a b R S n)).close

theorem binary_kernel_certificate {m} (kind : Fin 4) (w : Fin m) (a b R S : Fin 4 → Fin m) (n x z : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (binarySentence kind w a b R S n x z)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := binaryInput kind w a b R S n x z
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact binary (ZFContext.add (ZFContext.source_ZF m) E) kind w a b R S n x z
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))

end PPAC.Migration.ForcingFormulaDiagram
