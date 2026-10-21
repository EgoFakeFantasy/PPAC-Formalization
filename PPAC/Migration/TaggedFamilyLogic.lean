import PPAC.Migration.TaggedFamilyCollection

/-! 原非空族的实际标签行精确族非空逐项且两两不交。 -/
namespace PPAC.Migration.TaggedFamilyLogic
open Source SourceAlgebra SourceLogic TaggedRowSyntax TaggedFamilySyntax ChoiceSyntax

theorem nonempty_at {m} {Γ : Context m} (a x : Fin m) (ha : Derives Γ (familyNonempty a)) :
    Derives Γ ((Formula.mem x a).imp (MinimalPredicates.inhabited x)) := by
  have hi := Derives.allE x ha
  simpa only [Formula.instantiate, Formula.rename, MinimalPredicates.inhabited_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem nonempty {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (b a : Fin m)
    (hf : Derives Γ (family b a)) (ha : Derives Γ (familyNonempty a)) : Derives Γ (familyNonempty b) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := TaggedFamilyContext.rename hA Fin.castSucc
  have hf' : Derives Δ (family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, family_rename] using Derives.rename Fin.castSucc hf
  have ha' : Derives Δ (familyNonempty a.castSucc) := by
    simpa only [Formula.raise, familyNonempty_rename] using Derives.rename Fin.castSucc ha
  apply Derives.impI
  let M := Formula.mem (Fin.last m) b.castSucc
  let Γr := Context.add M Δ
  let X := (Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).conj (row (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add X (Context.image Formula.raise Γr)
  apply eliminate_member b.castSucc a.castSucc (Fin.last m) _ (add hf' M) (.hyp (Or.inl rfl))
  have hAX := TaggedFamilyContext.under (TaggedFamilyContext.add hA' M) X
  have haX : Derives Ξ (familyNonempty a.castSucc.castSucc) := by
    simpa only [Formula.raise, familyNonempty_rename] using under (add ha' M) X
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hx := Derives.impE (nonempty_at a.castSucc.castSucc (Fin.last (m+1)) haX) (.conjL hX)
  simpa only [Formula.raise, MinimalPredicates.inhabited_rename] using
    TaggedRowLogic.nonempty (Fin.last m).castSucc (Fin.last (m+1)) hAX.pairing (.conjR hX) hx

theorem intersecting_members_equal {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (b a r s p : Fin m)
    (hf : Derives Γ (family b a)) (hr : Derives Γ (.mem r b)) (hs : Derives Γ (.mem s b))
    (hp : Derives Γ (.mem p r)) (hq : Derives Γ (.mem p s)) : Derives Γ (.equal r s) := by
  let X := (Formula.mem (Fin.last m) a.castSucc).conj (row r.castSucc (Fin.last m))
  let Γx := Context.add X (Context.image Formula.raise Γ)
  apply eliminate_member b a r _ hf hr
  have hAX := TaggedFamilyContext.under hA X
  have hfX : Derives Γx (family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, family_rename] using under hf X
  have hsX : Derives Γx (.mem s.castSucc b.castSucc) := under hs X
  have hpX : Derives Γx (.mem p.castSucc r.castSucc) := under hp X
  have hqX : Derives Γx (.mem p.castSucc s.castSucc) := under hq X
  have hX : Derives Γx X := .hyp (Or.inl rfl)
  let Y := (Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).conj (row s.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Γx)
  apply eliminate_member b.castSucc a.castSucc s.castSucc _ hfX hsX
  have hAY := TaggedFamilyContext.under hAX Y
  have hrY : Derives Ξ (row r.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, row_rename] using under (.conjR hX) Y
  have hpY : Derives Ξ (.mem p.castSucc.castSucc r.castSucc.castSucc) := under hpX Y
  have hqY : Derives Ξ (.mem p.castSucc.castSucc s.castSucc.castSucc) := under hqX Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  exact TaggedRowLogic.intersecting_rows_equal r.castSucc.castSucc s.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc hAY.extensionality hrY (.conjR hY) hpY hqY

theorem disjoint_point {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (b a r s : Fin m)
    (hf : Derives Γ (family b a)) (hr : Derives Γ (.mem r b)) (hs : Derives Γ (.mem s b)) :
    Derives Γ ((Formula.equal r s).neg.imp (intersection r s).neg) := by
  apply Derives.impI
  apply Derives.impI
  let N := (Formula.equal r s).neg
  let I := intersection r s
  let Γi := Context.add I (Context.add N Γ)
  have hi : Derives Γi I := .hyp (Or.inl rfl)
  have hn : Derives Γi N := .hyp (Or.inr (Or.inl rfl))
  let P := (Formula.mem (Fin.last m) r.castSucc).conj (.mem (Fin.last m) s.castSucc)
  let Ξ := Context.add P (Context.image Formula.raise Γi)
  change Derives Γi (.ex P) at hi
  apply Derives.exE (p := P) hi
  have hAP := TaggedFamilyContext.under (TaggedFamilyContext.add (TaggedFamilyContext.add hA N) I) P
  have hfP : Derives Ξ (family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, family_rename] using under (add (add hf N) I) P
  have hrP : Derives Ξ (.mem r.castSucc b.castSucc) := under (add (add hr N) I) P
  have hsP : Derives Ξ (.mem s.castSucc b.castSucc) := under (add (add hs N) I) P
  have hnP : Derives Ξ (Formula.equal r.castSucc s.castSucc).neg := by
    simpa only [Formula.raise, N, Formula.neg, Formula.rename] using under hn P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  exact .impE hnP (intersecting_members_equal hAP b.castSucc a.castSucc r.castSucc s.castSucc (Fin.last m)
    hfP hrP hsP (.conjL hP) (.conjR hP))

theorem disjoint {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (b a : Fin m)
    (hf : Derives Γ (family b a)) : Derives Γ (ChoiceSyntax.disjoint b) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := TaggedFamilyContext.rename hA Fin.castSucc
  have hf' : Derives Δ (family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, family_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  let R := Formula.mem (Fin.last m) b.castSucc
  let Γr := Context.add R Δ
  apply Derives.allI
  let Γs := Context.image Formula.raise Γr
  have hAS := TaggedFamilyContext.rename (TaggedFamilyContext.add hA' R) Fin.castSucc
  have hfS : Derives Γs (family b.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, family_rename] using Derives.rename Fin.castSucc (add hf' R)
  have hrS : Derives Γs (.mem (Fin.last m).castSucc b.castSucc.castSucc) := Derives.rename Fin.castSucc (.hyp (Γ := Γr) (Or.inl rfl))
  apply Derives.impI
  exact disjoint_point (TaggedFamilyContext.add hAS _) b.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add hfS _) (add hrS _) (.hyp (Or.inl rfl))

theorem exists_admissible {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (a : Fin m)
    (ha : Derives Γ (familyNonempty a)) : Derives Γ (admissibleExists a) := by
  have hx := TaggedFamilyCollection.exists_family hA a
  let B := family (Fin.last m) a.castSucc
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hx
  apply Derives.exE (p := B) hx
  have hAB := TaggedFamilyContext.under hA B
  have haB : Derives Ξ (familyNonempty a.castSucc) := by
    simpa only [Formula.raise, familyNonempty_rename] using under ha B
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hn := nonempty hAB (Fin.last m) a.castSucc hB haB
  have hd := disjoint hAB (Fin.last m) a.castSucc hB
  have hout : Derives Ξ (admissibleExists a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, admissible_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hB (.conjI hn hd)
  simpa only [Formula.raise, admissibleExists_rename] using hout
end PPAC.Migration.TaggedFamilyLogic
