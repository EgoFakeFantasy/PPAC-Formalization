import PPAC.Migration.Internal.SyntaxRenameActualGraphs

/-! 给定真实完整解码图，实际构造 membership/equality 重命名目标；原零符号保持不变。 -/
namespace PPAC.Migration.Internal.SyntaxRenameAtomConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMapCodeSyntax SyntaxAtomSyntax SyntaxRenameOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_at_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (equalCode w x y n))
    (hx : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d x X))
    (hy : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d y Y)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hxN := SyntaxRenameTermTyping.output_natural hZ w r s a b c d x X hw hx
  have hyN := SyntaxRenameTermTyping.output_natural hZ w r s a b c d y Y hw hy
  have hI : Derives Γ (SyntaxForestSyntax.inputs 2 w (two X Y)) := .conjI hxN (.conjI hyN (.eqRefl w))
  have he := SyntaxConstructors.exists_constructor hZ 2 3 w (two X Y) hw hI
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (equalCode w.castSucc X.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex Q) := of_eq (by simp only [Q, SyntaxNodeSyntax.existsConstructor, equalCode, two_map]) he
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) Q)
  have hi1 : Derives Δ (input w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (hi) Q)
  have hr1 : Derives Δ (encoded w.castSucc r.castSucc a.castSucc c.castSucc R.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (hr) Q)
  have hs1 : Derives Δ (encoded w.castSucc s.castSucc b.castSucc d.castSucc S.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (hs) Q)
  have hc1 : Derives Δ (equalCode w.castSucc x.castSucc y.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, equalCode_rename]) (under (hc) Q)
  have hx1 : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (hx) Q)
  have hy1 : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (hy) Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hTX := SyntaxRenameTermTyping.target_term w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc hx1
  have hTY := SyntaxRenameTermTyping.target_term w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc hy1
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZ1 w.castSucc c.castSucc d.castSucc X.castSucc Y.castSucc (Fin.last m) hw1 (.conjR hQ))) (.conjI hTX hTY)
  have hd : Derives Δ (SyntaxRenameAtomSyntax.equalityData w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc) := .conjI hc1 (.conjI (.conjR hQ) (.conjI hx1 hy1))
  have ha := SyntaxRenameAtomSyntax.intro_equality w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc hd
  have hCases : Derives Δ (SyntaxRenameRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := .disjR (.disjR (.disjL ha))
  have hout := SyntaxRenameActualGraphs.intro_from_cases hZ1 w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hi1 hr1 hs1 ht hCases
  have ho := intro_exists w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hout
  exact of_eq (existsOutput_rename w R S a b c d n Fin.castSucc).symm ho

theorem equality_exists_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (equalCode w x y n)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hT := Derives.impE (.conjL (FormulaCodeKnownAtomic.equal_iff hZ w a b x y n hw hc)) (.conjL hi)
  have hm : Derives Γ (SyntaxIndexMapSyntax.maps w r s a b c d) := .conjI (.conjR hr) (.conjR hs)
  have hx := SyntaxRenameTermExistence.for_term hZ w r s a b c d x hw hm (.conjL hT)
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc (Fin.last m))
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hx
  have hw1 : Derives Ξ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) X)
  have hm1 : Derives Ξ (SyntaxIndexMapSyntax.maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxIndexMapSyntax.maps_rename]) (under (hm) X)
  have hy1 : Derives Ξ (SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc y.castSucc) := of_eq (SyntaxTermSyntax.term_rename w a b y Fin.castSucc) (under (.conjR hT) X)
  have heY := SyntaxRenameTermExistence.for_term (ZFContext.under hZ X) w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc hw1 hm1 hy1
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) heY
  have hZ2 := ZFContext.under (ZFContext.under hZ X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) X) Y)
  have hi2 : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (under (hi) X) Y)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hr) X) Y)
  have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hs) X) Y)
  have hc2 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, equalCode_rename]) (under (under (hc) X) Y)
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hRX : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (Derives.conjR hX) Y)
  have ho := equality_at_outputs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hr2 hs2 hc2 hRX (.conjR hY)
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

theorem membership_at_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n z x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (memberCode w z x y n))
    (hx : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d x X))
    (hy : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d y Y)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hxN := SyntaxRenameTermTyping.output_natural hZ w r s a b c d x X hw hx
  have hyN := SyntaxRenameTermTyping.output_natural hZ w r s a b c d y Y hw hy
  have hT := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w a b z x y n hw hc)) (.conjL hi)
  have hz := Derives.conjL hT
  have hzN := SyntaxZeroScalar.range hZ w z hw hz
  have hI : Derives Γ (SyntaxForestSyntax.inputs 3 w (three z X Y)) := .conjI hzN (.conjI hxN (.conjI hyN (.eqRefl w)))
  have he := SyntaxConstructors.exists_constructor hZ 3 2 w (three z X Y) hw hI
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (memberCode w.castSucc z.castSucc X.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex Q) := of_eq (by simp only [Q, SyntaxNodeSyntax.existsConstructor, memberCode, three_map]) he
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) Q)
  have hi1 : Derives Δ (input w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (hi) Q)
  have hr1 : Derives Δ (encoded w.castSucc r.castSucc a.castSucc c.castSucc R.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (hr) Q)
  have hs1 : Derives Δ (encoded w.castSucc s.castSucc b.castSucc d.castSucc S.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (hs) Q)
  have hc1 : Derives Δ (memberCode w.castSucc z.castSucc x.castSucc y.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, memberCode_rename]) (under (hc) Q)
  have hx1 : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (hx) Q)
  have hy1 : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (hy) Q)
  have hz1 : Derives Δ (zeroScalar w.castSucc z.castSucc) :=
    of_eq (by simp only [Formula.raise, zeroScalar_rename]) (under (hz) Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hTX := SyntaxRenameTermTyping.target_term w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc hx1
  have hTY := SyntaxRenameTermTyping.target_term w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc hy1
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ1 w.castSucc c.castSucc d.castSucc z.castSucc X.castSucc Y.castSucc (Fin.last m) hw1 (.conjR hQ))) (.conjI hz1 (.conjI hTX hTY))
  have hd : Derives Δ (SyntaxRenameAtomSyntax.membershipData w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) z.castSucc x.castSucc y.castSucc X.castSucc Y.castSucc) := .conjI hz1 (.conjI hc1 (.conjI (.conjR hQ) (.conjI hx1 hy1)))
  have ha := SyntaxRenameAtomSyntax.intro_membership w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) z.castSucc x.castSucc y.castSucc X.castSucc Y.castSucc hd
  have hCases : Derives Δ (SyntaxRenameRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := .disjR (.disjL ha)
  have hout := SyntaxRenameActualGraphs.intro_from_cases hZ1 w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hi1 hr1 hs1 ht hCases
  have ho := intro_exists w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hout
  exact of_eq (existsOutput_rename w R S a b c d n Fin.castSucc).symm ho

theorem membership_exists_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hT := Derives.impE (.conjL (FormulaCodeKnownAtomic.member_iff hZ w a b z x y n hw hc)) (.conjL hi)
  have hm : Derives Γ (SyntaxIndexMapSyntax.maps w r s a b c d) := .conjI (.conjR hr) (.conjR hs)
  have hx := SyntaxRenameTermExistence.for_term hZ w r s a b c d x hw hm (.conjL (.conjR hT))
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc (Fin.last m))
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hx
  have hw1 : Derives Ξ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) X)
  have hm1 : Derives Ξ (SyntaxIndexMapSyntax.maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxIndexMapSyntax.maps_rename]) (under (hm) X)
  have hy1 : Derives Ξ (SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc y.castSucc) := of_eq (SyntaxTermSyntax.term_rename w a b y Fin.castSucc) (under (.conjR (.conjR hT)) X)
  have heY := SyntaxRenameTermExistence.for_term (ZFContext.under hZ X) w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc hw1 hm1 hy1
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) heY
  have hZ2 := ZFContext.under (ZFContext.under hZ X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) X) Y)
  have hi2 : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (under (hi) X) Y)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hr) X) Y)
  have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encoded_rename]) (under (under (hs) X) Y)
  have hc2 : Derives Δ (memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, memberCode_rename]) (under (under (hc) X) Y)
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hRX : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (Derives.conjR hX) Y)
  have ho := membership_at_outputs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hr2 hs2 hc2 hRX (.conjR hY)
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

end PPAC.Migration.Internal.SyntaxRenameAtomConstruct
