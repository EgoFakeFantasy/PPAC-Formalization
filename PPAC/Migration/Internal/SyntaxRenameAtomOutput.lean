import PPAC.Migration.Internal.SyntaxRenameAtomConstruct

/-! membership/equality 的实际唯一输出纤维；消去所有映射图见证，六参数全部在对象层量化。 -/
namespace PPAC.Migration.Internal.SyntaxRenameAtomOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMapCodeSyntax SyntaxAtomSyntax SyntaxRenameOutputSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_unique_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n q v x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (equalCode w x y n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (hv : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := SyntaxRenameActualGraphs.atomic_of_renamed hZ 3 2 w R S r s a b c d n q (two x y) hw hr hs hc hq
  have h2 := SyntaxRenameActualGraphs.atomic_of_renamed hZ 3 2 w R S r s a b c d n v (two x y) hw hr hs hc hv
  exact SyntaxRenameAtomUnique.equality_unique hZ w r s a b c d n q v hw h1 h2

theorem equality_fiber_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (equalCode w x y n)) : Derives Γ (fiber w R S a b c d n) := by
  have he := SyntaxRenameAtomConstruct.equality_exists_at_graphs hZ w R S r s a b c d n x y hw hi hr hs hc
  let Q := SyntaxRenameJudgmentSyntax.renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hr) Q) V)
    have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hs) Q) V)
    have hc2 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, equalCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Q, Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under hQ V)
    exact equality_unique_at_graphs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hr2 hs2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem equality_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hc : Derives Γ (equalCode w x y n)) : Derives Γ (fiber w R S a b c d n) := by
  let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (Derives.conjL (.conjR hi))
  have hs1 : Derives Ξ (mapCode w.castSucc b.castSucc d.castSucc S.castSucc) :=
    of_eq (mapCode_rename w b d S Fin.castSucc) (under (Derives.conjR (.conjR hi)) G)
  let H := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) G) H)
  have hi2 : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (under (hi) G) H)
  have hc2 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, equalCode_rename]) (under (under (hc) G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hG H)
  have ho := equality_fiber_at_graphs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hi2 hr2 (.hyp (Or.inl rfl)) hc2
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem equality_property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) : Derives Γ (property w n) := by
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
  have hc6 : Derives Δ (equalCode w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, equalCode_rename]) (under_6 hc I)
  exact equality_fiber (zf_under_6 hZ I) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6

theorem membership_unique_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n q v z x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (memberCode w z x y n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (hv : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := SyntaxRenameActualGraphs.atomic_of_renamed hZ 2 3 w R S r s a b c d n q (three z x y) hw hr hs hc hq
  have h2 := SyntaxRenameActualGraphs.atomic_of_renamed hZ 2 3 w R S r s a b c d n v (three z x y) hw hr hs hc hv
  exact SyntaxRenameAtomUnique.membership_unique hZ w r s a b c d n q v hw h1 h2

theorem membership_fiber_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (fiber w R S a b c d n) := by
  have he := SyntaxRenameAtomConstruct.membership_exists_at_graphs hZ w R S r s a b c d n z x y hw hi hr hs hc
  let Q := SyntaxRenameJudgmentSyntax.renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hr) Q) V)
    have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hs) Q) V)
    have hc2 : Derives Δ (memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, memberCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Q, Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under hQ V)
    exact membership_unique_at_graphs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hr2 hs2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem membership_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (fiber w R S a b c d n) := by
  let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (Derives.conjL (.conjR hi))
  have hs1 : Derives Ξ (mapCode w.castSucc b.castSucc d.castSucc S.castSucc) :=
    of_eq (mapCode_rename w b d S Fin.castSucc) (under (Derives.conjR (.conjR hi)) G)
  let H := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) G) H)
  have hi2 : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (under (hi) G) H)
  have hc2 : Derives Δ (memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, memberCode_rename]) (under (under (hc) G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hG H)
  have ho := membership_fiber_at_graphs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hi2 hr2 (.hyp (Or.inl rfl)) hc2
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem membership_property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (property w n) := by
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
  have hc6 : Derives Δ (memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, memberCode_rename]) (under_6 hc I)
  exact membership_fiber (zf_under_6 hZ I) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6

end PPAC.Migration.Internal.SyntaxRenameAtomOutput
