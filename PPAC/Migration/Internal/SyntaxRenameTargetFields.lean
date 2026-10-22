import PPAC.Migration.Internal.ObjectSyntaxComposeLift

/-! 已知源原构造时，正式Rename实际取得同种目标字段；见证全部保留对象存在量词。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTargetFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxAtomSyntax SyntaxLogicalSyntax
open SyntaxMapCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def singleTarget {m} (tag : Nat) (w q : Fin m) : Formula m := .ex (singleCode tag w.castSucc (Fin.last m) q.castSucc)
def binaryTarget {m} (kind : Fin 4) (w q : Fin m) : Formula m := .ex (.ex (binaryCode kind w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc))
def equalTarget {m} (w q : Fin m) : Formula m := .ex (.ex (equalCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc))
def memberTarget {m} (w q : Fin m) : Formula m := .ex (.ex (.ex (memberCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) q.castSucc.castSucc.castSucc)))

theorem singleTarget_rename {m k} (tag : Nat) (w q : Fin m) (ρ : Fin m → Fin k) :
    (singleTarget tag w q).rename ρ = singleTarget tag (ρ w) (ρ q) := by
  simp only [singleTarget, Formula.rename, singleCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem binaryTarget_rename {m k} (kind : Fin 4) (w q : Fin m) (ρ : Fin m → Fin k) :
    (binaryTarget kind w q).rename ρ = binaryTarget kind (ρ w) (ρ q) := by
  simp only [binaryTarget, Formula.rename, binaryCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equalTarget_rename {m k}  (w q : Fin m) (ρ : Fin m → Fin k) :
    (equalTarget  w q).rename ρ = equalTarget  (ρ w) (ρ q) := by
  simp only [equalTarget, Formula.rename, equalCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem memberTarget_rename {m k}  (w q : Fin m) (ρ : Fin m → Fin k) :
    (memberTarget  w q).rename ρ = memberTarget  (ρ w) (ρ q) := by
  simp only [memberTarget, Formula.rename, memberCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S r s a b c d n q x : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (singleCode tag w x n)) (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) : Derives Γ (singleTarget tag w q) := by
  have hb : Derives Γ (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q) := by
    rcases valid with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact SyntaxRenameTagCases.of_renamed hZ 4 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hn
    · exact SyntaxRenameTagCases.of_renamed hZ 9 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hn
    · exact SyntaxRenameTagCases.of_renamed hZ 10 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hn
  let B := SyntaxRenameRecursiveSyntax.singleBody tag advance w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (singleTarget tag w.castSucc.castSucc q.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, singleTarget_rename]) ho

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S r s a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (binaryCode kind w x y n)) (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) : Derives Γ (binaryTarget kind w q) := by
  have hb : Derives Γ (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q) := by
    have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact SyntaxRenameTagCases.of_renamed hZ 5 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hn
    · exact SyntaxRenameTagCases.of_renamed hZ 6 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hn
    · exact SyntaxRenameTagCases.of_renamed hZ 7 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hn
    · exact SyntaxRenameTagCases.of_renamed hZ 8 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hn
  let B := SyntaxRenameRecursiveSyntax.binaryBody kind w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply SyntaxRenameBinders.eliminate_4 B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (binaryTarget kind w.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2)).castSucc
    apply Derives.exI (Fin.last (m+3))
    exact of_eq (by simp only [Formula.instantiate, binaryCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR (.conjR (.conjR hB))))
  exact of_eq (by simp only [Formula.raise, binaryTarget_rename]) ho

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (w R S r s a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (equalCode w x y n)) (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) : Derives Γ (equalTarget  w q) := by
  have hb := SyntaxRenameTagCases.of_renamed hZ 3 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hn
  let B := SyntaxRenameAtomSyntax.equalityBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply SyntaxRenameBinders.eliminate_4 B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (equalTarget  w.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2)).castSucc
    apply Derives.exI (Fin.last (m+3))
    exact of_eq (by simp only [Formula.instantiate, equalCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR hB))
  exact of_eq (by simp only [Formula.raise, equalTarget_rename]) ho

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (w R S r s a b c d n q z x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (memberCode w z x y n)) (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) : Derives Γ (memberTarget  w q) := by
  have hb := SyntaxRenameTagCases.of_renamed hZ 2 3 w R S r s a b c d n q (SyntaxAtomSyntax.three z x y) hw hr hs hc hn
  let B := SyntaxRenameAtomSyntax.membershipBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))
  apply SyntaxRenameBinders.eliminate_5 B _ hb
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (memberTarget  w.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc.castSucc.castSucc.castSucc
    apply Derives.exI (Fin.last (m+3)).castSucc
    apply Derives.exI (Fin.last (m+4))
    exact of_eq (by simp only [Formula.instantiate, memberCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, memberTarget_rename]) ho
end PPAC.Migration.Internal.SyntaxRenameTargetFields
