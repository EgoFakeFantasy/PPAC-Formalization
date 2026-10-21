import PPAC.Migration.Internal.SyntaxAtomUnique

/-! 全内部候选字段上的唯一解码纤维；与原子类型关系的对象双条件。 -/
namespace PPAC.Migration.Internal.SyntaxAtomDecode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

def memberUnique {m} (w n s x y : Fin m) : Formula m := (.all (.all (.all ((memberCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc).imp ((Formula.equal (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc).conj ((Formula.equal (Fin.last (m+1)).castSucc x.castSucc.castSucc.castSucc).conj (Formula.equal (Fin.last (m+2)) y.castSucc.castSucc.castSucc)))))))

def memberDecodedBody {m} (w b f n : Fin m) : Formula (m+3) := (memberAt w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc).conj (memberUnique w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))

def memberDecoded {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj (.ex (.ex (.ex (memberDecodedBody w b f n))))

theorem memberUnique_rename {m l} (w n s x y : Fin m) (r : Fin m → Fin l) :
    (memberUnique w n s x y).rename r = memberUnique (r w) (r n) (r s) (r x) (r y) := by
  simp only [memberUnique, Formula.rename, memberCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem memberDecoded_rename {m l} (w b f n : Fin m) (r : Fin m → Fin l) :
    (memberDecoded w b f n).rename r = memberDecoded (r w) (r b) (r f) (r n) := by
  simp only [memberDecoded, memberDecodedBody, Formula.rename, contexts_rename, memberAt_rename, memberUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem member_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) : Derives Γ (memberUnique w n s x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let C := memberCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hw1 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw C
  have hc1 : Derives Δ (memberCode w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, memberCode_rename] using under_three hc C
  exact SyntaxAtomUnique.member_fields (zf_under_three hZ C) _ _ _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hc1

theorem intro_member_decoded {m} {Γ : Context m} (w b f n s x y : Fin m)
    (hd : Derives Γ (memberAt w b f s x y n)) (hu : Derives Γ (memberUnique w n s x y)) : Derives Γ (memberDecoded w b f n) := by
  have hx : Derives Γ (term w b f x) := .conjL (.conjR (.conjL hd))
  apply Derives.conjI (Derives.conjL hx)
  apply Derives.exI s
  apply Derives.exI x
  apply Derives.exI y
  simp only [memberDecodedBody, Formula.instantiate, Formula.rename, memberAt_rename, memberUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu

theorem member_decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (membership w b f n)) : Derives Γ (memberDecoded w b f n) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_member w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hu := member_unique (zf_under_three hZ C) w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw1 (.conjR hC)
  have hout := intro_member_decoded w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hC hu
  simpa only [Formula.raise, memberDecoded_rename] using hout

theorem member_of_decoded {m} {Γ : Context m} (w b f n : Fin m)
    (hd : Derives Γ (memberDecoded w b f n)) : Derives Γ (membership w b f n) := by
  let C := memberDecodedBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply Derives.exE (Derives.conjR hd)
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := intro_member w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc (.conjL hC)
  have hh : Derives Δ (membership w b f n).raise.raise.raise := by
    simpa only [Formula.raise, membership_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨a, ⟨b, hb, h1⟩, h2⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨a, Or.inr ⟨b, Or.inr hb, h1⟩, h2⟩

theorem member_decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((membership w b f n).iff (memberDecoded w b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact member_decode (ZFContext.add hZ _) _ _ _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact member_of_decoded _ _ _ _ (.hyp (Or.inl rfl))

def equalUnique {m} (w n x y : Fin m) : Formula m := (.all (.all ((equalCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc).imp ((Formula.equal (Fin.last m).castSucc x.castSucc.castSucc).conj (Formula.equal (Fin.last (m+1)) y.castSucc.castSucc)))))

def equalDecodedBody {m} (w b f n : Fin m) : Formula (m+2) := (equalAt w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc).conj (equalUnique w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))

def equalDecoded {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj (.ex (.ex (equalDecodedBody w b f n)))

theorem equalUnique_rename {m l} (w n x y : Fin m) (r : Fin m → Fin l) :
    (equalUnique w n x y).rename r = equalUnique (r w) (r n) (r x) (r y) := by
  simp only [equalUnique, Formula.rename, equalCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equalDecoded_rename {m l} (w b f n : Fin m) (r : Fin m → Fin l) :
    (equalDecoded w b f n).rename r = equalDecoded (r w) (r b) (r f) (r n) := by
  simp only [equalDecoded, equalDecodedBody, Formula.rename, contexts_rename, equalAt_rename, equalUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equal_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) : Derives Γ (equalUnique w n x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let C := equalCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, equalCode_rename] using OrderedPairElimination.under_two hc C
  exact SyntaxAtomUnique.equal_fields (ZFContext.under_two hZ C) _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hc1

theorem intro_equal_decoded {m} {Γ : Context m} (w b f n x y : Fin m)
    (hd : Derives Γ (equalAt w b f x y n)) (hu : Derives Γ (equalUnique w n x y)) : Derives Γ (equalDecoded w b f n) := by
  have hx : Derives Γ (term w b f x) := .conjL (.conjL hd)
  apply Derives.conjI (Derives.conjL hx)
  apply Derives.exI x
  apply Derives.exI y
  simp only [equalDecodedBody, Formula.instantiate, Formula.rename, equalAt_rename, equalUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu

theorem equal_decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (equality w b f n)) : Derives Γ (equalDecoded w b f n) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_equality w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hu := equal_unique (ZFContext.under_two hZ C) w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw1 (.conjR hC)
  have hout := intro_equal_decoded w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hC hu
  simpa only [Formula.raise, equalDecoded_rename] using hout

theorem equal_of_decoded {m} {Γ : Context m} (w b f n : Fin m)
    (hd : Derives Γ (equalDecoded w b f n)) : Derives Γ (equality w b f n) := by
  let C := equalDecodedBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply Derives.exE (Derives.conjR hd)
  apply Derives.exE (.hyp (Or.inl rfl))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := intro_equality w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc (.conjL hC)
  have hh : Derives Δ (equality w b f n).raise.raise := by
    simpa only [Formula.raise, equality_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨a, ha, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨a, Or.inr ha, he⟩

theorem equal_decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((equality w b f n).iff (equalDecoded w b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact equal_decode (ZFContext.add hZ _) _ _ _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact equal_of_decoded _ _ _ _ (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxAtomDecode
