import PPAC.Migration.ForcingFormulaDiagram
import PPAC.Migration.Internal.SyntaxRenameAtomicSubst

/-! The four original atomic FORMULA branches inherit the already proved
four-table TERM diagram. All operand outputs are actual object witnesses. -/
namespace PPAC.Migration.ForcingFormulaAtoms
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingFormulaDiagram (step atSource atSource_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def path {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  (step w a b R S 0 x u).conj ((step w a b R S 1 u t).conj ((step w a b R S 2 t y).conj (step w a b R S 3 x o)))
private theorem path_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) (r : Fin m → Fin l) :
    (path w a b R S x u t y o).rename r = path (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) := by
  simp only [path, Formula.rename, ForcingFormulaDiagram.step_rename]

/-- A finite external index selects an unchanged original atomic constructor. -/
def atomCode {m} (member : Bool) (w sym x y n : Fin m) : Formula m :=
  if member then SyntaxAtomSyntax.memberCode w sym x y n else SyntaxAtomSyntax.equalCode w x y n

theorem atomCode_rename {m l} (member : Bool) (w sym x y n : Fin m) (r : Fin m → Fin l) :
    (atomCode member w sym x y n).rename r = atomCode member (r w) (r sym) (r x) (r y) (r n) := by
  cases member <;> simp only [atomCode, Bool.false_eq_true, if_false, if_true, SyntaxAtomSyntax.memberCode_rename, SyntaxAtomSyntax.equalCode_rename]

def atomData {m} (member : Bool) (w sym R S a b c d x y q X Y : Fin m) : Formula m :=
  (atomCode member w sym X Y q).conj ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X).conj
    (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y))
theorem atomData_rename {m l} (member : Bool) (w sym R S a b c d x y q X Y : Fin m) (r : Fin m → Fin l) :
    (atomData member w sym R S a b c d x y q X Y).rename r = atomData member (r w) (r sym) (r R) (r S) (r a) (r b) (r c) (r d) (r x) (r y) (r q) (r X) (r Y) := by
  simp only [atomData, Formula.rename, atomCode_rename, SyntaxCodedMixedTermSyntax.substituted_rename]
def atomBody {m} (member : Bool) (w sym R S a b c d x y q : Fin m) : Formula (m+2) :=
  atomData member (old 2 w) (old 2 sym) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 x) (old 2 y) (old 2 q) (slot 2 0) (slot 2 1)
def atomOutput {m} (member : Bool) (w sym R S a b c d x y q : Fin m) : Formula m := existsMany 2 (atomBody member w sym R S a b c d x y q)
theorem atomOutput_rename {m l} (member : Bool) (w sym R S a b c d x y q : Fin m) (r : Fin m → Fin l) :
    (atomOutput member w sym R S a b c d x y q).rename r = atomOutput member (r w) (r sym) (r R) (r S) (r a) (r b) (r c) (r d) (r x) (r y) (r q) := by
  simp only [atomOutput, existsMany_rename, atomBody, atomData_rename, lift_old, lift_slot]

theorem atom_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (member : Bool) (w sym R S a b c d n x y q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (atomCode member w sym x y n))
    (hp : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (atomOutput member w sym R S a b c d x y q) := by
  cases member with
  | false =>
    have hs := SyntaxMixedFormulaTagCases.of_substituted hZ 3 2 w R S a b c d n q (SyntaxAtomSyntax.two x y) hw hc hp
    let B := SyntaxMixedFormulaAtomSyntax.equalityBody w R S a b c d n q
    let Δ := Context.add B (raisedContext 4 Γ)
    apply HornBinderRules.eliminate_many 4 B _ hs
    have hZ4 := HornBinderRules.zf_body 4 hZ B
    have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
    have hc4 := of_eq (atomCode_rename false w sym x y n (old 4)) (HornBinderRules.under_body 4 hc B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxAtomUnique.equal_fields hZ4 (old 4 w) (slot 4 0) (slot 4 1) (old 4 x) (old 4 y) (old 4 n) hw4 (.conjL hB) hc4
    have hx := SyntaxMixedFormulaAtomicSubst.term_source (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
      (slot 4 0) (slot 4 2) (old 4 x) (.conjL es) (.conjL (.conjR (.conjR hB)))
    have hy := SyntaxMixedFormulaAtomicSubst.term_source (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d)
      (slot 4 1) (slot 4 3) (old 4 y) (.conjR es) (.conjR (.conjR (.conjR hB)))
    have hout : Derives Δ (atomOutput false (old 4 w) (old 4 sym) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 x) (old 4 y) (old 4 q)) := by
      apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (slot 4 2) (slot 4 3))
      exact of_eq (by simp only [atomBody, atomData_rename, assign_old, assign_slot]; rfl) (.conjI (.conjL (.conjR hB)) (.conjI hx hy))
    exact of_eq (atomOutput_rename false w sym R S a b c d x y q (old 4)).symm hout
  | true =>
    have hs := SyntaxMixedFormulaTagCases.of_substituted hZ 2 3 w R S a b c d n q (SyntaxAtomSyntax.three sym x y) hw hc hp
    let B := SyntaxMixedFormulaAtomSyntax.membershipBody w R S a b c d n q
    let Δ := Context.add B (raisedContext 5 Γ)
    apply HornBinderRules.eliminate_many 5 B _ hs
    have hZ5 := HornBinderRules.zf_body 5 hZ B
    have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
    have hc5 := of_eq (atomCode_rename true w sym x y n (old 5)) (HornBinderRules.under_body 5 hc B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have es := SyntaxAtomUnique.member_fields hZ5 (old 5 w) (slot 5 0) (slot 5 1) (slot 5 2) (old 5 sym) (old 5 x) (old 5 y) (old 5 n) hw5 (.conjL (.conjR hB)) hc5
    have ht := SyntaxAtomUnique.symbol_subst (old 5 w) (slot 5 0) (old 5 sym) (slot 5 3) (slot 5 4) (old 5 q) (.conjL es) (.conjL (.conjR (.conjR hB)))
    have hx := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 b) (old 5 c) (old 5 d)
      (slot 5 1) (slot 5 3) (old 5 x) (.conjL (.conjR es)) (.conjL (.conjR (.conjR (.conjR hB))))
    have hy := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 R) (old 5 S) (old 5 a) (old 5 b) (old 5 c) (old 5 d)
      (slot 5 2) (slot 5 4) (old 5 y) (.conjR (.conjR es)) (.conjR (.conjR (.conjR (.conjR hB))))
    have hout : Derives Δ (atomOutput true (old 5 w) (old 5 sym) (old 5 R) (old 5 S) (old 5 a) (old 5 b) (old 5 c) (old 5 d) (old 5 x) (old 5 y) (old 5 q)) := by
      apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (slot 5 3) (slot 5 4))
      exact of_eq (by simp only [atomBody, atomData_rename, assign_old, assign_slot]; rfl) (.conjI ht (.conjI hx hy))
    exact of_eq (atomOutput_rename true w sym R S a b c d x y q (old 5)).symm hout

private theorem atom_parent_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (member : Bool) (w sym X Y U V n o : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.equal X U)) (hy : Derives Γ (.equal Y V))
    (hn : Derives Γ (atomCode member w sym X Y n)) (ho : Derives Γ (atomCode member w sym U V o)) : Derives Γ (.equal n o) := by
  cases member with
  | false =>
    have ht := SyntaxRenameAtomicSubst.equal_y w U Y n V hy (SyntaxRenameAtomicSubst.equal_x w X Y n U hx hn)
    exact SyntaxConstructors.unique hZ 2 3 w (SyntaxAtomSyntax.two U V) n o hw ht ho
  | true =>
    have ht := SyntaxRenameAtomicSubst.member_y w sym U Y n V hy (SyntaxRenameAtomicSubst.member_x w sym X Y n U hx hn)
    exact SyntaxConstructors.unique hZ 3 2 w (SyntaxAtomSyntax.three sym U V) n o hw ht ho

private theorem atom_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (member : Bool)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (sym n x z u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (atomCode member w sym x z n))
    (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (.equal y o) := by
  have he0 := atom_output hZ member w sym (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n x z u hw hc (.conjL hp)
  let E0 := atomBody member w sym (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) x z u
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ E0
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E0)
  have hp1 := of_eq (path_rename w a b R S n u t y o (old 2)) (HornBinderRules.under_body 2 hp E0)
  have he1 := atom_output hZ1 member w.castSucc.castSucc sym.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc u.castSucc.castSucc (slot 2 0 (m := m+0)) (slot 2 1 (m := m+0)) t.castSucc.castSucc hw1 (.conjL hE0) (.conjL (.conjR hp1))
  let E1 := atomBody member w.castSucc.castSucc sym.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (slot 2 0 (m := m+0)) (slot 2 1 (m := m+0)) t.castSucc.castSucc
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hp2 := of_eq (path_rename w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) n.castSucc.castSucc u.castSucc.castSucc t.castSucc.castSucc y.castSucc.castSucc o.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hp1 E1)
  have he2 := atom_output hZ2 member w.castSucc.castSucc.castSucc.castSucc sym.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+2)) (slot 2 1 (m := m+2)) y.castSucc.castSucc.castSucc.castSucc hw2 (.conjL hE1) (.conjL (.conjR (.conjR hp2)))
  let E2 := atomBody member w.castSucc.castSucc.castSucc.castSucc sym.castSucc.castSucc.castSucc.castSucc (R 2).castSucc.castSucc.castSucc.castSucc (S 2).castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc (slot 2 0 (m := m+2)) (slot 2 1 (m := m+2)) y.castSucc.castSucc.castSucc.castSucc
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ2 E2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hp3 := of_eq (path_rename w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc (old 2)) (HornBinderRules.under_body 2 hp2 E2)
  have hc3 : Derives Δ3 (atomCode member w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc sym.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [atomCode_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hc E0) E1) E2)
  have he3 := atom_output hZ3 member w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc sym.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw3 hc3 (.conjR (.conjR (.conjR hp3)))
  let E3 := atomBody member w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc sym.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ4 := Context.add E3 (raisedContext 2 Δ3)
  apply HornBinderRules.eliminate_many 2 E3 _ he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hB0 : Derives Δ4 (atomData member (old 8 w) (old 8 sym) (old 8 (R 0)) (old 8 (S 0)) (old 8 (a 0)) (old 8 (b 0)) (old 8 (a 1)) (old 8 (b 1)) (old 8 x) (old 8 z) (old 8 u) (slot 8 0) (slot 8 1)) := of_eq (by simp only [E0, atomBody, atomData_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hE0 E1) E2) E3)
  have hB1 : Derives Δ4 (atomData member (old 8 w) (old 8 sym) (old 8 (R 1)) (old 8 (S 1)) (old 8 (a 1)) (old 8 (b 1)) (old 8 (a 2)) (old 8 (b 2)) (slot 8 0) (slot 8 1) (old 8 t) (slot 8 2) (slot 8 3)) := of_eq (by simp only [E1, atomBody, atomData_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hE1 E2) E3)
  have hB2 : Derives Δ4 (atomData member (old 8 w) (old 8 sym) (old 8 (R 2)) (old 8 (S 2)) (old 8 (a 2)) (old 8 (b 2)) (old 8 (a 3)) (old 8 (b 3)) (slot 8 2) (slot 8 3) (old 8 y) (slot 8 4) (slot 8 5)) := of_eq (by simp only [E2, atomBody, atomData_rename]; rfl) (HornBinderRules.under_body 2 hE2 E3)
  have hw8 : Derives Δ4 (omega (old 8 w)) := of_eq (by simp only [omega_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw E0) E1) E2) E3)
  have hd8 : Derives Δ4 (ForcingTermDiagram.diagram (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i))) := of_eq (by simp only [ForcingTermDiagram.diagram_rename]; rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hd E0) E1) E2) E3)
  have hZ8 := (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ E0) E1) E2) E3)
  have e0 := ForcingTermDiagram.apply_diagram (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 x) (slot 8 0) (slot 8 2) (slot 8 4) (slot 8 6) hd8 (.conjL (.conjR hB0)) (.conjL (.conjR hB1)) (.conjL (.conjR hB2)) (.conjL (.conjR hE3))
  have e1 := ForcingTermDiagram.apply_diagram (old 8 w) (fun i => old 8 (a i)) (fun i => old 8 (b i)) (fun i => old 8 (R i)) (fun i => old 8 (S i)) (old 8 z) (slot 8 1) (slot 8 3) (slot 8 5) (slot 8 7) hd8 (.conjR (.conjR hB0)) (.conjR (.conjR hB1)) (.conjR (.conjR hB2)) (.conjR (.conjR hE3))
  exact atom_parent_eq hZ8 member (old 8 w) (old 8 sym) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 y) (old 8 o) hw8 e0 e1 (.conjL hB2) (.conjL hE3)

/-- Both original two-operand atoms inherit the completed four-table term diagram.
All eight actual child outputs are internally generated and eliminated. -/
theorem atom {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (member : Bool)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (sym n x z : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (atomCode member w sym x z n))
    (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S)) :
    Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  exact atom_point (HornBinderRules.zf_body 4 hZ B) member (old 4 w)
    (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 sym) (old 4 n) (old 4 x) (old 4 z) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B))
    (of_eq (atomCode_rename member w sym x z n (old 4)) (HornBinderRules.under_body 4 hc B))
    (of_eq (ForcingTermDiagram.diagram_rename w a b R S (old 4)) (HornBinderRules.under_body 4 hd B))
    (.hyp (Or.inl rfl))

private theorem nullary_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (hp : Derives Γ (path w a b R S n u t y o)) : Derives Γ (.equal y o) := by
  have h0 := SyntaxMixedFormulaNullary.unique hZ truth w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n u hw hc (.conjL hp)
  have h1 := SyntaxMixedFormulaJudgmentSubst.subst_n w (R 1) (S 1) (a 1) (b 1) (a 2) (b 2) u t n h0 (.conjL (.conjR hp))
  have e1 := SyntaxMixedFormulaNullary.unique hZ truth w (R 1) (S 1) (a 1) (b 1) (a 2) (b 2) n t hw hc h1
  have h2 := SyntaxMixedFormulaJudgmentSubst.subst_n w (R 2) (S 2) (a 2) (b 2) (a 3) (b 3) t y n e1 (.conjL (.conjR (.conjR hp)))
  have e2 := SyntaxMixedFormulaNullary.unique hZ truth w (R 2) (S 2) (a 2) (b 2) (a 3) (b 3) n y hw hc h2
  have e3 := SyntaxMixedFormulaNullary.unique hZ truth w (R 3) (S 3) (a 0) (b 0) (a 3) (b 3) n o hw hc (.conjR (.conjR (.conjR hp)))
  exact eq_trans e2 (eq_symm e3)

/-- Both original constants satisfy object four-path cancellation outright. -/
theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  exact nullary_point (HornBinderRules.zf_body 4 hZ B) truth (old 4 w)
    (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i))
    (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B))
    (of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (HornBinderRules.under_body 4 hc B))
    (.hyp (Or.inl rfl))

private theorem equality_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S))
    (ha : Derives Γ (SyntaxAtomSyntax.equality w (a 0) (b 0) n)) : Derives Γ (atSource w a b R S n) := by
  let B := SyntaxAtomSyntax.equalBody w (a 0) (b 0) n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply SyntaxAtomLogic.eliminate_equality w (a 0) (b 0) n _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := atom (HornBinderRules.zf_body 2 hZ B) false (old 2 w)
    (fun i => old 2 (a i)) (fun i => old 2 (b i)) (fun i => old 2 (R i)) (fun i => old 2 (S i))
    (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)) (.conjR hB)
    (of_eq (ForcingTermDiagram.diagram_rename w a b R S (old 2)) (HornBinderRules.under_body 2 hd B))
  exact of_eq (by simp only [Formula.raise, atSource_rename]; rfl) ho

private theorem membership_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S))
    (ha : Derives Γ (SyntaxAtomSyntax.membership w (a 0) (b 0) n)) : Derives Γ (atSource w a b R S n) := by
  let B := SyntaxAtomSyntax.memberBody w (a 0) (b 0) n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply SyntaxAtomLogic.eliminate_member w (a 0) (b 0) n _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := atom (HornBinderRules.zf_body 3 hZ B) true (old 3 w)
    (fun i => old 3 (a i)) (fun i => old 3 (b i)) (fun i => old 3 (R i)) (fun i => old 3 (S i))
    (slot 3 0) (old 3 n) (slot 3 1) (slot 3 2)
    (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)) (.conjR hB)
    (of_eq (ForcingTermDiagram.diagram_rename w a b R S (old 3)) (HornBinderRules.under_body 3 hd B))
  exact of_eq (by simp only [Formula.raise, atSource_rename]; rfl) ho

/-- The whole original atomic split, with every source field and operand
output eliminated. No child induction hypothesis remains in the base cases. -/
theorem from_atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w (a 0) (b 0) n)) : Derives Γ (atSource w a b R S n) := by
  apply Derives.disjE ha
  · let C := (SyntaxAtomSyntax.nullary false w (a 0) (b 0) n).disj (SyntaxAtomSyntax.nullary true w (a 0) (b 0) n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) false w a b R S n (add (add hw C) _) (.conjR (.hyp (Or.inl rfl)))
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) true w a b R S n (add (add hw C) _) (.conjR (.hyp (Or.inl rfl)))
  · let C := (SyntaxAtomSyntax.membership w (a 0) (b 0) n).disj (SyntaxAtomSyntax.equality w (a 0) (b 0) n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact membership_case (ZFContext.add (ZFContext.add hZ C) _) w a b R S n (add (add hw C) _) (add (add hd C) _) (.hyp (Or.inl rfl))
    · exact equality_case (ZFContext.add (ZFContext.add hZ C) _) w a b R S n (add (add hw C) _) (add (add hd C) _) (.hyp (Or.inl rfl))

def input {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m) : Formula m :=
  (omega w).conj ((ForcingTermDiagram.diagram w a b R S).conj (SyntaxAtomSyntax.atomic w (a 0) (b 0) n))

def sentence {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m) : Source.Sentence :=
  ((input w a b R S n).imp (atSource w a b R S n)).close

theorem kernel_certificate {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a b R S n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w a b R S n
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_atomic (ZFContext.add (ZFContext.source_ZF m) E) w a b R S n
    (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

end PPAC.Migration.ForcingFormulaAtoms
