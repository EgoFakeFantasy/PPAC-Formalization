import PPAC.Migration.Internal.SyntaxRenameAtomicCases

/-! 原假/真空原子的实际自重命名及所有内部候选上的唯一输出；量词仍遍历全部内部集合。 -/
namespace PPAC.Migration.Internal.SyntaxRenameNullary
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameJudgmentSyntax
open SyntaxRenameOutputSyntax SyntaxMapCodeSyntax SyntaxNodeSyntax SyntaxAtomSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem local_nullary {m} {Γ : Context m} (truth : Bool) (w r s a b c d n q : Fin m)
    (hr : Derives Γ (mapCode w a c r)) (hs : Derives Γ (mapCode w b d s))
    (ha : Derives Γ (SyntaxRenameAtomSyntax.nullary truth w a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.localRename w r s a b c d n q) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hs1 : Derives Ξ (mapCode w.castSucc b.castSucc d.castSucc s.castSucc) :=
    of_eq (mapCode_rename w b d s Fin.castSucc) (under hs R)
  let S := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc s.castSucc.castSucc
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) hs1
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hR2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc) :=
    of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hR S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hA : Derives Δ (SyntaxRenameAtomSyntax.nullary truth w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameAtomSyntax.nullary_rename]) (under (under ha R) S)
  have hc : Derives Δ (SyntaxRenameRecursiveSyntax.cases w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := by
    cases truth
    · exact .disjL (.disjL hA)
    · exact .disjL (.disjR hA)
  have ho := SyntaxRenameRecursiveSyntax.intro_localRename _ _ _ _ _ _ _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hR2 (.conjI hS hc))
  exact of_eq (by simp only [Formula.raise, SyntaxRenameRecursiveSyntax.localRename_rename]) ho

theorem intro_self {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (renamed w r s a b c d n n) := by
  have hr := Derives.conjL (.conjR hi)
  have hs := Derives.conjR (.conjR hi)
  have hb := SyntaxMapCodeDecode.contexts w a c r hr
  have hf := SyntaxMapCodeDecode.contexts w b d s hs
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w c d) := .conjI (.conjR hb) (.conjR hf)
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w c d n hw hc)) hctx
  have hA : Derives Γ (SyntaxRenameAtomSyntax.nullary truth w a b c d n n) :=
    .conjI (.conjI (.conjI (.conjL hb) (.conjL hf)) hc) (.conjI hctx hc)
  have hl := local_nullary truth w r s a b c d n n hr hs hA
  have hk : Derives Γ (SyntaxRenameRecursiveSyntax.criterion w r s a b c d n n) :=
    .conjI (SyntaxRenameOutput.input_natural w r s a b c d n hi) (.conjI (.conjI hr (.conjI hs ht)) (.conjI (.conjL hi) hl))
  exact .impE (.conjR (SyntaxRenameRecursive.recursive_iff hZ w r s a b c d n n hw)) hk

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n))
    (hr : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (.equal q n) := by
  have hk := Derives.impE (.conjL (SyntaxRenameRecursive.recursive_iff hZ w r s a b c d n q hw)) hr
  have hl := Derives.conjR (.conjR (.conjR hk))
  let B := SyntaxRenameRecursiveSyntax.localRenameBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_2 B _ hl
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hc2 : Derives Δ (constructor 0 (nullaryTag truth) w.castSucc.castSucc Fin.elim0 n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename, zero_map]) (under_2 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hA : Derives Δ (SyntaxRenameAtomSyntax.nullary truth w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := by
    cases truth
    · exact SyntaxRenameAtomicCases.filter (zf_under_2 hZ B) 0 0 _ _ _ _ _ _ _ _ _ _ _ Fin.elim0 hw2 hc2 (.conjR (.conjR hB))
    · exact SyntaxRenameAtomicCases.filter (zf_under_2 hZ B) 1 0 _ _ _ _ _ _ _ _ _ _ _ Fin.elim0 hw2 hc2 (.conjR (.conjR hB))
  exact SyntaxConstructors.unique (zf_under_2 hZ B) 0 (nullaryTag truth) w.castSucc.castSucc Fin.elim0 q.castSucc.castSucc n.castSucc.castSucc hw2 (.conjR (.conjR hA)) hc2

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (fiber w r s a b c d n) := by
  have hself := intro_self hZ truth w r s a b c d n hw hi hc
  have hu : Derives Γ (uniqueOutput w r s a b c d n n) := by
    apply Derives.allI
    apply Derives.impI
    let Q := renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise Γ)
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
    have hc1 : Derives Δ (constructor 0 (nullaryTag truth) w.castSucc Fin.elim0 n.castSucc) :=
      of_eq (by simp only [Formula.raise, constructor_rename, zero_map]) (under hc Q)
    exact unique (ZFContext.under hZ Q) truth _ _ _ _ _ _ _ _ (Fin.last m) hw1 hc1 (.hyp (Or.inl rfl))
  exact intro_fiber w r s a b c d n n hself hu
theorem property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have hc6 : Derives Δ (constructor 0 (nullaryTag truth) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc Fin.elim0 n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename, zero_map]) (under_6 hc I)
  exact actual_fiber (zf_under_6 hZ I) truth w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6
end PPAC.Migration.Internal.SyntaxRenameNullary
