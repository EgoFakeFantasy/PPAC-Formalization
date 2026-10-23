import PPAC.Migration.Internal.SyntaxMixedFormulaCheckUnique
import PPAC.Migration.Internal.SyntaxMixedFormulaLogicalSubst

/-! 内部 Earlier 下单/双子式原混合替换分支的全候选唯一性；包含两个真实提升量词模式。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w r s a b c d n q v x X u U : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w r s a b c d n q x X))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w r s a b c d n v u U)) : Derives Γ (.equal q v) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 1 tag w (fun _ => x) n hw (.conjL h1)
  have hx := StructuralListTraceOrder.member_member hZ w x n hw hn (.conjL (.conjR h1))
  have hp := earlier_at w n x he hx (.conjL (.conjR h1))
  have eu := SyntaxLogicalFields.single_fields hZ tag w u x n hw (.conjL h2) (.conjL h1)
  have hh := SyntaxMixedFormulaLogicalSubst.check_source advance w u r s a b c d U x eu (.conjR (.conjR (.conjR h2)))
  have eU := SyntaxMixedFormulaCheckUnique.unique hZ advance w x r s a b c d U X hw hp hh (.conjR (.conjR (.conjR h1)))
  have hc := SyntaxMixedFormulaLogicalSubst.single_child tag w U v X eU (.conjL (.conjR (.conjR h2)))
  exact SyntaxLogicalFields.single_unique hZ tag w X q v hw (.conjL (.conjR (.conjR h1))) hc

theorem single_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w r s a b c d n q v x X : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w r s a b c d n q x X))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaRecursiveSyntax.singleBody tag advance w r s a b c d n v
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_2 B _ h2
  have hwk : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hek : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 he B)
  have hp : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.singleData_rename]) (under_2 h1 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact single_data_unique (zf_under_2 hZ B) tag advance w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hwk hek hp hB

theorem single_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w r s a b c d n q))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaRecursiveSyntax.singleBody tag advance w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_2 B _ h1
  have hwk : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hek : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 he B)
  have hp : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.single_rename]) (under_2 h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact single_at_data_unique (zf_under_2 hZ B) tag advance w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hwk hek hB hp

theorem binary_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w r s a b c d n q v x y X Y u t U V : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w r s a b c d n q x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w r s a b c d n v u t U V)) : Derives Γ (.equal q v) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 2 (SyntaxLogicalSyntax.binaryTag kind) w (SyntaxAtomSyntax.two x y) n hw (.conjL h1)
  have hx := StructuralListTraceOrder.member_member hZ w x n hw hn (.conjL (.conjR h1))
  have hy := StructuralListTraceOrder.member_member hZ w y n hw hn (.conjL (.conjR (.conjR h1)))
  have hp := earlier_at w n x he hx (.conjL (.conjR h1))
  have hs := earlier_at w n y he hy (.conjL (.conjR (.conjR h1)))
  have eu := SyntaxLogicalFields.binary_fields hZ kind w u t x y n hw (.conjL h2) (.conjL h1)
  have hu := SyntaxMixedFormulaJudgmentSubst.subst_n w r s a b c d u U x (.conjL eu) (.conjL (.conjR (.conjR (.conjR (.conjR h2)))))
  have hv := SyntaxMixedFormulaJudgmentSubst.subst_n w r s a b c d t V y (.conjR eu) (.conjR (.conjR (.conjR (.conjR (.conjR h2)))))
  have eU := SyntaxMixedFormulaFiberUnique.property_unique hZ w r s a b c d x U X hw hp hu (.conjL (.conjR (.conjR (.conjR (.conjR h1)))))
  have eV := SyntaxMixedFormulaFiberUnique.property_unique hZ w r s a b c d y V Y hw hs hv (.conjR (.conjR (.conjR (.conjR (.conjR h1)))))
  have hc := SyntaxMixedFormulaLogicalSubst.binary_y kind w X V v Y eV (SyntaxMixedFormulaLogicalSubst.binary_x kind w U V v X eU (.conjL (.conjR (.conjR (.conjR h2)))))
  exact SyntaxLogicalFields.binary_unique hZ kind w X Y q v hw (.conjL (.conjR (.conjR (.conjR h1)))) hc

theorem binary_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w r s a b c d n q v x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w r s a b c d n q x y X Y))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaRecursiveSyntax.binaryBody kind w r s a b c d n v
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ h2
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hek : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_4 he B)
  have hp : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.binaryData_rename]) (under_4 h1 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact binary_data_unique (zf_under_4 hZ B) kind w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hwk hek hp hB

theorem binary_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w r s a b c d n q))
    (h2 : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w r s a b c d n v)) : Derives Γ (.equal q v) := by
  let B := SyntaxMixedFormulaRecursiveSyntax.binaryBody kind w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ h1
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hek : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_4 he B)
  have hp : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.binary kind w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.binary_rename]) (under_4 h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact binary_at_data_unique (zf_under_4 hZ B) kind w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hwk hek hB hp

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalUnique
