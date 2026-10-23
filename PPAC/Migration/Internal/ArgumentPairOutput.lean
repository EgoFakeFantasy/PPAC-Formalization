import PPAC.Migration.Internal.OriginalArgumentForestProgram

/-! 内部长度2有类型列表的实际双字段森林分解；索引和值均在对象存在量词中构造。 -/
namespace PPAC.Migration.Internal.ArgumentPairOutput
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ArgumentForestProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxForestSyntax SyntaxNumeralSyntax SyntaxAtomSyntax

def body {m} (w a b q : Fin m) : Formula (m+2) :=
  (typedInputs 2 (old 2 w) (old 2 a) (old 2 b) (two (slot 2 0) (slot 2 1))).conj
    (forest 2 (old 2 w) (two (slot 2 0) (slot 2 1)) (old 2 q))

def output {m} (w a b q : Fin m) : Formula m := existsMany 2 (body w a b q)

theorem body_lift {m j} (w a b q : Fin m) (ρ : Fin m → Fin j) :
    (body w a b q).rename (lift 2 ρ) = body (ρ w) (ρ a) (ρ b) (ρ q) := by
  simp only [body, Formula.rename, typedInputs_rename, forest_rename, two_map, lift_old, lift_slot]

theorem output_rename {m j} (w a b q : Fin m) (ρ : Fin m → Fin j) :
    (output w a b q).rename ρ = output (ρ w) (ρ a) (ρ b) (ρ q) := by
  simp only [output, existsMany_rename, body_lift]

theorem intro_output {m} {Γ : Context m} (w a b q x y : Fin m)
    (ht : Derives Γ (typedInputs 2 w a b (two x y))) (hf : Derives Γ (forest 2 w (two x y) q)) : Derives Γ (output w a b q) := by
  apply HornBinderRules.intro_many 2 (body w a b q) (two x y)
  exact of_eq (by simp only [body, Formula.rename, typedInputs_rename, forest_rename, two_map, assign_old, assign_slot]; rfl) (.conjI ht hf)

theorem forest_of_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w len zero one x y q : Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral 2 len)) (hz : Derives Γ (numeral 0 zero)) (ho : Derives Γ (numeral 1 one))
    (hLength : Derives Γ (StructuralListLengthSyntax.hasLength w q len))
    (hx : Derives Γ (StructuralListFieldSyntax.field w q zero x)) (hy : Derives Γ (StructuralListFieldSyntax.field w q one y)) :
    Derives Γ (forest 2 w (two x y) q) := by
  let B := (StructuralListFieldGraphSyntax.fields w.castSucc q.castSucc len.castSucc (Fin.last m)).conj
    (.all ((StructuralListFieldPairSyntax.graph w.castSucc.castSucc q.castSucc.castSucc len.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (StructuralListFieldDecode.at_length hZ w q len hw hLength)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hl1 : Derives Δ (numeral 2 len.castSucc) := of_eq (numeral_rename 2 len Fin.castSucc) (under hl B)
  have hz1 : Derives Δ (numeral 0 zero.castSucc) := of_eq (numeral_rename 0 zero Fin.castSucc) (under hz B)
  have ho1 : Derives Δ (numeral 1 one.castSucc) := of_eq (numeral_rename 1 one Fin.castSucc) (under ho B)
  have hLength1 : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc q.castSucc len.castSucc) := of_eq (StructuralListLengthSyntax.hasLength_rename w q len Fin.castSucc) (under hLength B)
  have hx1 : Derives Δ (StructuralListFieldSyntax.field w.castSucc q.castSucc zero.castSucc x.castSucc) := of_eq (StructuralListFieldSyntax.field_rename w q zero x Fin.castSucc) (under hx B)
  have hy1 : Derives Δ (StructuralListFieldSyntax.field w.castSucc q.castSucc one.castSucc y.castSucc) := of_eq (StructuralListFieldSyntax.field_rename w q one y Fin.castSucc) (under hy B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZeroIn := SyntaxNumeralMembers.index_member hZ1 2 (0 : Fin 2) len.castSucc zero.castSucc hl1 hz1
  have hOneIn := SyntaxNumeralMembers.index_member hZ1 2 (1 : Fin 2) len.castSucc one.castSucc hl1 ho1
  have he0 := Derives.impE (.conjR (StructuralListFieldGraphSyntax.law_at _ _ _ _ _ _ (.conjR (.conjR (.conjL hB))))) (.conjI hZeroIn hx1)
  have he1 := Derives.impE (.conjR (StructuralListFieldGraphSyntax.law_at _ _ _ _ _ _ (.conjR (.conjR (.conjL hB))))) (.conjI hOneIn hy1)
  have hs0 := SyntaxSlotSyntax.intro_slot (Fin.last m) 0 x.castSucc zero.castSucc hz1 he0
  have hs1 := SyntaxSlotSyntax.intro_slot (Fin.last m) 1 y.castSucc one.castSucc ho1 he1
  have hSlots := SyntaxFieldsFromSlots.intro_slots 2 (Fin.last m) (two x.castSucc y.castSucc) (fun i => Fin.cases hs0 (fun j => Fin.cases hs1 (fun z => Fin.elim0 z) j) i)
  have hForest := SyntaxForestFromFields.recover hZ1 2 w.castSucc q.castSucc len.castSucc (Fin.last m) (two x.castSucc y.castSucc) hw1 hLength1 (.conjL hB) hl1 hSlots
  exact of_eq (by simp only [forest_rename, two_map]) hForest

theorem at_indices {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w len zero one a b q : Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral 2 len)) (hz : Derives Γ (numeral 0 zero)) (ho : Derives Γ (numeral 1 one))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w len a b q)) : Derives Γ (output w a b q) := by
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListFieldSyntax.field w.castSucc q.castSucc zero.castSucc (Fin.last m))
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (StructuralListFieldValues.exists_value hZ w q zero hw (SyntaxNumerals.range hZ 0 w zero hw hz))
  have hZ1 := ZFContext.under hZ X
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
  have ho1 : Derives Ξ (numeral 1 one.castSucc) := of_eq (numeral_rename 1 one Fin.castSucc) (under ho X)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListFieldSyntax.field w.castSucc.castSucc q.castSucc.castSucc one.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) (StructuralListFieldValues.exists_value hZ1 w.castSucc q.castSucc one.castSucc hw1 (SyntaxNumerals.range hZ1 1 _ _ hw1 ho1))
  have hZ2 := ZFContext.under hZ1 Y
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := under (under h X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hl2 : Derives Δ (numeral 2 len.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (lift hl)
  have hz2 : Derives Δ (numeral 0 zero.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (lift hz)
  have ho2 : Derives Δ (numeral 1 one.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (lift ho)
  have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc len.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (lift hL)
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hx2 : Derives Δ (StructuralListFieldSyntax.field w.castSucc.castSucc q.castSucc.castSucc zero.castSucc.castSucc (Fin.last m).castSucc) := of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ Fin.castSucc) (under (.conjR hX) Y)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have htx := SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hL2 (SyntaxNumeralMembers.index_member hZ2 2 (0 : Fin 2) _ _ hl2 hz2) hx2
  have hty := SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hL2 (SyntaxNumeralMembers.index_member hZ2 2 (1 : Fin 2) _ _ hl2 ho2) (.conjR hY)
  have hForest := forest_of_fields hZ2 _ _ _ _ _ _ _ hw2 hl2 hz2 ho2 (.conjR (.conjL (.conjR (.conjR hL2)))) hx2 (.conjR hY)
  have hTypes : Derives Δ (typedInputs 2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (two (Fin.last m).castSucc (Fin.last (m+1)))) := .conjI htx (.conjI hty (.eqRefl _))
  have hOut := intro_output _ _ _ _ _ _ hTypes hForest
  simpa only [Formula.raise, output_rename] using hOut

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w len a b q : Fin m) (hw : Derives Γ (omega w)) (hl : Derives Γ (numeral 2 len))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w len a b q)) : Derives Γ (output w a b q) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (numeral 0 (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (SyntaxNumerals.exists_numeral hZ 0 w hw)
  have hZ1 := ZFContext.under hZ Z
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  let O := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (numeral 1 (Fin.last (m+1)))
  let Δ := Context.add O (Context.image Formula.raise Ξ)
  apply Derives.exE (p := O) (SyntaxNumerals.exists_numeral hZ1 1 w.castSucc hw1)
  have hZ2 := ZFContext.under hZ1 O
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw1 O)
  have hl2 : Derives Δ (numeral 2 len.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (under (under hl Z) O)
  have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc len.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (under (under hL Z) O)
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have hz2 : Derives Δ (numeral 0 (Fin.last m).castSucc) := of_eq (numeral_rename 0 _ Fin.castSucc) (under (.conjR hZ) O)
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have hOut := at_indices hZ2 w.castSucc.castSucc len.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc hw2 hl2 hz2 (.conjR hO) hL2
  simpa only [Formula.raise, output_rename] using hOut

end PPAC.Migration.Internal.ArgumentPairOutput
