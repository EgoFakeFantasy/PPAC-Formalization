import PPAC.Migration.Internal.SyntaxMixedFormulaAtomicSubst
import PPAC.Migration.Internal.SyntaxRenameAtomicSubst
import PPAC.Migration.Internal.SyntaxCodedMixedTermUnique

/-! 全部真实图和内部候选下的 membership/equality 混合替换唯一性；源字段由原同码单射恢复。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaAtomUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameBinders SyntaxAtomSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v x y X Y u z U V : Fin m)
    (hw : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equalityData w r s a b c d n q x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equalityData w r s a b c d n v u z U V)) : Derives Γ (.equal q v) := by
  have he := SyntaxAtomUnique.equal_fields hZ w u z x y n hw (.conjL h2) (.conjL h1)
  have ht := SyntaxMixedFormulaAtomicSubst.term_source w r s a b c d u U x (.conjL he) (.conjL (.conjR (.conjR h2)))
  have hs := SyntaxMixedFormulaAtomicSubst.term_source w r s a b c d z V y (.conjR he) (.conjR (.conjR (.conjR h2)))
  have hU := SyntaxCodedMixedTermUnique.unique hZ w r s a b c d x U X hw ht (.conjL (.conjR (.conjR h1)))
  have hV := SyntaxCodedMixedTermUnique.unique hZ w r s a b c d y V Y hw hs (.conjR (.conjR (.conjR h1)))
  have hc := SyntaxRenameAtomicSubst.equal_y w X V v Y hV (SyntaxRenameAtomicSubst.equal_x w U V v X hU (.conjL (.conjR h2)))
  exact SyntaxConstructors.unique hZ 2 3 w (two X Y) q v hw (.conjL (.conjR h1)) hc

theorem equality_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equalityData w r s a b c d n q x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equality w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaAtomSyntax.equalityBody w r s a b c d n v
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ h2
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hp : Derives Δ (SyntaxMixedFormulaAtomSyntax.equalityData w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaAtomSyntax.equalityData_rename]) (under_4 h1 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact equality_data_unique (zf_under_4 hZ B) w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hwk hp hB

theorem equality_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equality w r s a b c d n q))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.equality w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaAtomSyntax.equalityBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ h1
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hp : Derives Δ (SyntaxMixedFormulaAtomSyntax.equality w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaAtomSyntax.equality_rename]) (under_4 h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact equality_at_data_unique (zf_under_4 hZ B) w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hwk hB hp

theorem membership_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v z x y X Y j u t U V : Fin m)
    (hw : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membershipData w r s a b c d n q z x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membershipData w r s a b c d n v j u t U V)) : Derives Γ (.equal q v) := by
  have he := SyntaxAtomUnique.member_fields hZ w j u t z x y n hw (.conjL (.conjR h2)) (.conjL (.conjR h1))
  have ht := SyntaxMixedFormulaAtomicSubst.term_source w r s a b c d u U x (.conjL (.conjR he)) (.conjL (.conjR (.conjR (.conjR h2))))
  have hs := SyntaxMixedFormulaAtomicSubst.term_source w r s a b c d t V y (.conjR (.conjR he)) (.conjR (.conjR (.conjR (.conjR h2))))
  have hU := SyntaxCodedMixedTermUnique.unique hZ w r s a b c d x U X hw ht (.conjL (.conjR (.conjR (.conjR h1))))
  have hV := SyntaxCodedMixedTermUnique.unique hZ w r s a b c d y V Y hw hs (.conjR (.conjR (.conjR (.conjR h1))))
  have hC := SyntaxAtomUnique.symbol_subst w j z U V v (.conjL he) (.conjL (.conjR (.conjR h2)))
  have hc := SyntaxRenameAtomicSubst.member_y w z X V v Y hV (SyntaxRenameAtomicSubst.member_x w z U V v X hU hC)
  exact SyntaxConstructors.unique hZ 3 2 w (three z X Y) q v hw (.conjL (.conjR (.conjR h1))) hc

theorem membership_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membershipData w r s a b c d n q z x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membership w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaAtomSyntax.membershipBody w r s a b c d n v
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))
  apply eliminate_5 B _ h2
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_5 hw B)
  have hp : Derives Δ (SyntaxMixedFormulaAtomSyntax.membershipData w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaAtomSyntax.membershipData_rename]) (under_5 h1 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact membership_data_unique (zf_under_5 hZ B) w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) hwk hp hB

theorem membership_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membership w r s a b c d n q))
    (h2 : Derives Γ (SyntaxMixedFormulaAtomSyntax.membership w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaAtomSyntax.membershipBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))
  apply eliminate_5 B _ h1
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_5 hw B)
  have hp : Derives Δ (SyntaxMixedFormulaAtomSyntax.membership w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaAtomSyntax.membership_rename]) (under_5 h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact membership_at_data_unique (zf_under_5 hZ B) w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) hwk hB hp

end PPAC.Migration.Internal.SyntaxMixedFormulaAtomUnique
