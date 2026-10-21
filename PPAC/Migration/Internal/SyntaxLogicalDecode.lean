import PPAC.Migration.Internal.SyntaxLogicalFields

/-! 逻辑节点实际唯一字段解码；候选字段量词不限制在外部标准码或当前scope。 -/
namespace PPAC.Migration.Internal.SyntaxLogicalDecode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def singleUnique {m} (tag : Nat) (w n x : Fin m) : Formula m := (.all ((singleCode tag w.castSucc (Fin.last m) n.castSucc).imp (Formula.equal (Fin.last m) x.castSucc)))

def singleDecodedBody {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Formula (m+1) := (singleData tag advance w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc).conj (singleUnique tag w.castSucc n.castSucc (Fin.last m))

def singleDecoded {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Formula m := (contexts w b f).conj (.ex (singleDecodedBody tag advance w b f h n))

theorem singleUnique_rename {m l} (tag : Nat) (w n x : Fin m) (r : Fin m → Fin l) :
    (singleUnique tag w n x).rename r = singleUnique tag (r w) (r n) (r x) := by
  simp only [singleUnique, Formula.rename, singleCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem singleDecoded_rename {m l} (tag : Nat) (advance : Bool) (w b f h n : Fin m) (r : Fin m → Fin l) :
    (singleDecoded tag advance w b f h n).rename r = singleDecoded tag advance (r w) (r b) (r f) (r h) (r n) := by
  simp only [singleDecoded, singleDecodedBody, Formula.rename, contexts_rename, singleData_rename, singleUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem single_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w n x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n)) : Derives Γ (singleUnique tag w n x) := by
  apply Derives.allI
  apply Derives.impI
  let C := singleCode tag w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hc1 : Derives Δ (singleCode tag w.castSucc x.castSucc n.castSucc) := by
    simpa only [Formula.raise, singleCode_rename] using under hc C
  exact SyntaxLogicalFields.single_fields (ZFContext.under hZ C) tag _ _ _ _ hw1 (.hyp (Or.inl rfl)) hc1

theorem intro_single_decoded {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w b f h n x : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (singleData tag advance w b f h x n))
    (hu : Derives Γ (singleUnique tag w n x)) : Derives Γ (singleDecoded tag advance w b f h n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  simp only [singleDecodedBody, Formula.instantiate, Formula.rename, singleData_rename, singleUnique_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu

theorem single_decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (single tag advance w b f h n)) : Derives Γ (singleDecoded tag advance w b f h n) := by
  let C := singleBody tag advance w b f h n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hc1 : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using under (Derives.conjL hs) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hu := single_unique (ZFContext.under hZ C) tag w.castSucc n.castSucc (Fin.last m) hw1 (.conjL hC)
  have hout := intro_single_decoded tag advance w.castSucc b.castSucc f.castSucc h.castSucc n.castSucc (Fin.last m) hc1 hC hu
  simpa only [Formula.raise, singleDecoded_rename] using hout

theorem single_of_decoded {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w b f h n : Fin m)
    (hd : Derives Γ (singleDecoded tag advance w b f h n)) : Derives Γ (single tag advance w b f h n) := by
  let C := singleDecodedBody tag advance w b f h n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (.conjR hd)
  have hc1 : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using under (Derives.conjL hd) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := intro_single tag advance w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc hc1 (.conjL hC)
  simpa only [Formula.raise, single_rename] using hout

theorem single_decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((single tag advance w b f h n).iff (singleDecoded tag advance w b f h n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact single_decode (ZFContext.add hZ _) tag advance w b f h n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact single_of_decoded tag advance w b f h n (.hyp (Or.inl rfl))

def binaryUnique {m} (kind : Fin 4) (w n x y : Fin m) : Formula m := (.all (.all ((binaryCode kind w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc).imp ((Formula.equal (Fin.last m).castSucc x.castSucc.castSucc).conj (Formula.equal (Fin.last (m+1)) y.castSucc.castSucc)))))

def binaryDecodedBody {m} (kind : Fin 4) (w b f h n : Fin m) : Formula (m+2) := (binaryData kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc).conj (binaryUnique kind w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))

def binaryDecoded {m} (kind : Fin 4) (w b f h n : Fin m) : Formula m := (contexts w b f).conj (.ex (.ex (binaryDecodedBody kind w b f h n)))

theorem binaryUnique_rename {m l} (kind : Fin 4) (w n x y : Fin m) (r : Fin m → Fin l) :
    (binaryUnique kind w n x y).rename r = binaryUnique kind (r w) (r n) (r x) (r y) := by
  simp only [binaryUnique, Formula.rename, binaryCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem binaryDecoded_rename {m l} (kind : Fin 4) (w b f h n : Fin m) (r : Fin m → Fin l) :
    (binaryDecoded kind w b f h n).rename r = binaryDecoded kind (r w) (r b) (r f) (r h) (r n) := by
  simp only [binaryDecoded, binaryDecodedBody, Formula.rename, contexts_rename, binaryData_rename, binaryUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem binary_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) : Derives Γ (binaryUnique kind w n x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let C := binaryCode kind w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, binaryCode_rename] using OrderedPairElimination.under_two hc C
  exact SyntaxLogicalFields.binary_fields (ZFContext.under_two hZ C) kind _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hc1

theorem intro_binary_decoded {m} {Γ : Context m} (kind : Fin 4) (w b f h n x y : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (binaryData kind w b f h x y n))
    (hu : Derives Γ (binaryUnique kind w n x y)) : Derives Γ (binaryDecoded kind w b f h n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  apply Derives.exI y
  simp only [binaryDecodedBody, Formula.instantiate, Formula.rename, binaryData_rename, binaryUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu

theorem binary_decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (binary kind w b f h n)) : Derives Γ (binaryDecoded kind w b f h n) := by
  let C := binaryBody kind w b f h n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using OrderedPairElimination.under_two (Derives.conjL hs) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hu := binary_unique (ZFContext.under_two hZ C) kind w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw1 (.conjL hC)
  have hout := intro_binary_decoded kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc1 hC hu
  simpa only [Formula.raise, binaryDecoded_rename] using hout

theorem binary_of_decoded {m} {Γ : Context m} (kind : Fin 4) (w b f h n : Fin m)
    (hd : Derives Γ (binaryDecoded kind w b f h n)) : Derives Γ (binary kind w b f h n) := by
  let C := binaryDecodedBody kind w b f h n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply Derives.exE (.conjR hd)
  apply Derives.exE (.hyp (Or.inl rfl))
  have hc1 : Derives Δ (contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using OrderedPairElimination.under_two (Derives.conjL hd) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := intro_binary kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hc1 (.conjL hC)
  have hh : Derives Δ (binary kind w b f h n).raise.raise := by
    simpa only [Formula.raise, binary_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨a, ha, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨a, Or.inr ha, he⟩

theorem binary_decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((binary kind w b f h n).iff (binaryDecoded kind w b f h n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact binary_decode (ZFContext.add hZ _) kind w b f h n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact binary_of_decoded kind w b f h n (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxLogicalDecode
