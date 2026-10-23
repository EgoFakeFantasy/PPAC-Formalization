import PPAC.Migration.Internal.StrictLookupDomainStep

/-! 原对象ω归纳闭合法列表全部内部索引的准确成功域和真实字段对应。 -/
namespace PPAC.Migration.Internal.StrictLookupDomainInduction
open Source SourceAlgebra SourceLogic OmegaSyntax StrictLookupSyntax StrictLookupDomainSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty r)) : Derives Γ (property w r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let L := StructuralListLengthSyntax.hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc
  let M := Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc
  let Δ := Context.add M (Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) L) M
  have lift {p : Formula m} (hh : Derives Γ p) : Derives Δ p.raise.raise.raise := add (add (OrdinalRestriction.raise_three hh) L) M
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hz3 : Derives Δ (empty r.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (lift hz)
  have hNil := StructuralListLengthConstruct.nil_of_empty_length hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc (.hyp (Or.inr (Or.inl rfl))) hz3
  have hReject := StrictLookupFailure.nil_rejected hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (.hyp (Or.inl rfl)) hNil
  apply Derives.conjI
  · apply Derives.impI
    exact .botE (.impE (add hReject _) (intro_hasOutput w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .botE (.impE (empty_at r.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (add hz3 _)) (.conjL (.hyp (Or.inl rfl))))

theorem successor_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w r)) : Derives Γ (property w s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let L := StructuralListLengthSyntax.hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc
  let M := Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc
  let Δ := Context.add M (Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) L) M
  have lift {p : Formula m} (hh : Derives Γ p) : Derives Δ p.raise.raise.raise := add (add (OrdinalRestriction.raise_three hh) L) M
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hs3 : Derives Δ (successor s.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hs)
  have hp3 : Derives Δ (property w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (lift hp)
  exact StrictLookupDomainStep.point hZ3 w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (lift hr) hs3 hp3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.base StrictLookupDomainSyntax.matrix (fun _ : Fin 1 => w)) := by
  simp only [OmegaInductionSyntax.base, StrictLookupDomainSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let Z := empty (Fin.last m)
  have hw1 : Derives (Context.add Z (Context.image Formula.raise Γ)) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  exact empty_property (ZFContext.under hZ Z) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (OmegaInductionSyntax.step StrictLookupDomainSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [OmegaInductionSyntax.step, StrictLookupDomainSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc w.castSucc.castSucc
  let I := property w.castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add I (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) I) S
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename])
    (add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) M) I) S)
  exact successor_property hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_domains {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hh := OmegaInduction.induction_on_omega StrictLookupDomainSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StrictLookupDomainSyntax.matrix) hw (base hZ w hw) (step hZ w hw)
  exact of_eq (by simp only [OmegaInductionSyntax.holds, StrictLookupDomainSyntax.matrix_pred, paramsUp]) hh

theorem at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((returned w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))) := by
  have hh : Derives Γ ((Formula.mem r w).imp (property w r)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE r (all_domains hZ w hw))
  exact at_field w r n i y (.impE hh (StructuralListLengthBasic.length_member w n r hl)) hl hi

end PPAC.Migration.Internal.StrictLookupDomainInduction
