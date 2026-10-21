import PPAC.Migration.Internal.StructuralListSuffixStep

/-! 任意原完整ω值序列的全部内部后缀有实际列表码；原对象ω归纳而非宿主Nat归纳。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixInduction
open Source SourceAlgebra SourceLogic OmegaSyntax SequenceSyntax NaturalAdditionSyntax StructuralListSuffixSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.base StructuralListSuffixSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, StructuralListSuffixSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let E := empty (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ E
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  exact StructuralListSuffixBase.empty_property hZ1 _ _ _ _ hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (sequence (ρ 1) (ρ 2) (ρ 0))) :
    Derives Γ (OmegaInductionSyntax.step StructuralListSuffixSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StructuralListSuffixSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let I := property (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add I (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) I) S
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) M) I) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf2 : Derives Δ (sequence (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (ρ 0).castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  exact StructuralListSuffixStep.property_successor hZ2 _ _ _ _ _ hw2 hf2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_suffixes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hf : Derives Γ (sequence (ρ 1) (ρ 2) (ρ 0))) :
    Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp (property (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc (Fin.last m)))) := by
  have h := OmegaInduction.induction_on_omega StructuralListSuffixSyntax.matrix ρ (ρ 0)
    (ZFContext.separation hZ StructuralListSuffixSyntax.matrix) hw (base hZ ρ hw) (step hZ ρ hw hf)
  simpa only [OmegaInductionSyntax.holds, StructuralListSuffixSyntax.matrix_pred, paramsUp] using h

theorem at_suffix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l r k : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hr : Derives Γ (.mem r w))
    (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l)) : Derives Γ (existsCode w f k r) := by
  have hall := all_suffixes hZ (NaturalAdditionTransport.params3 w f l)
    (by simpa only [NaturalAdditionTransport.params3_0] using hw)
    (by simpa only [NaturalAdditionTransport.params3_0, NaturalAdditionTransport.params3_1, NaturalAdditionTransport.params3_2] using hf)
  have hp : Derives Γ ((Formula.mem r w).imp (property w f l r)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc,
      NaturalAdditionTransport.params3_0, NaturalAdditionTransport.params3_1, NaturalAdditionTransport.params3_2, id_eq] using Derives.allE r hall
  exact code_at w f l r k (.impE hp hr) hk hs

theorem full_suffix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l z : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hl : Derives Γ (.mem l w))
    (hz : Derives Γ (empty z)) : Derives Γ (existsCode w f z l) :=
  at_suffix hZ w f l l z hw hf hl (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (ZFArithmetic.add_zero hZ w l z hw hl hz)
end PPAC.Migration.Internal.StructuralListSuffixInduction
