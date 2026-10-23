import PPAC.Migration.Internal.PureSyntaxTermMatrix
import PPAC.Migration.Internal.EmptyBoundFreeInputs

/-! 完整十五规则纯检查图上的项查询与纯Term对全部内部候选等价；实际闭轨迹在对象ZF中构造。 -/
namespace PPAC.Migration.Internal.PureSyntaxTermCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax SyntaxRenameQuerySyntax
open YesMetaZFC.Automation
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PureSyntaxTrace.termRow w b f n r))
    (hc : Derives Γ (PureSyntaxTrace.condition w r)) : Derives Γ (SyntaxTermSyntax.term w b f n) := by
  let B := PureSyntaxTrace.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hr1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc b.castSucc f.castSucc n.castSucc r.castSucc) := of_eq (PureSyntaxTrace.termRow_rename w b f n r Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := PureSyntaxTrace.closed_at w.castSucc (Fin.last m) r.castSucc (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ht := PureSyntaxTermMatrix.step_sound (ZFContext.under hZ B) w.castSucc b.castSucc f.castSucc n.castSucc r.castSucc (Fin.last m) hw1 hr1 hs
  exact of_eq (SyntaxTermSyntax.term_rename w b f n Fin.castSucc).symm ht

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (PureSyntaxTrace.term w b f n)) :
    Derives Γ (SyntaxTermSyntax.term w b f n) := by
  let B := (PureSyntaxTrace.termRow w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m)).conj
    (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxTermSyntax.term_rename w b f n Fin.castSucc).symm
    (condition_sound (ZFContext.under hZ B) w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m) hw1 (.conjL hB) (.conjR hB))

theorem branch_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.term w b f n))
    (hb : Derives Γ (SyntaxTermSyntax.branch bound w (SyntaxTermSyntax.limit bound b f) n)) :
    Derives Γ (PureSyntaxTrace.term w b f n) := by
  let B := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound b f) n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch bound w (SyntaxTermSyntax.limit bound b f) n _ hb
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have ht1 : Derives Δ (SyntaxTermSyntax.term w.castSucc b.castSucc f.castSucc n.castSucc) := of_eq (SyntaxTermSyntax.term_rename w b f n Fin.castSucc) (under ht B)
  have hB0 : Derives Δ B := .hyp (Or.inl rfl)
  have hB : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit bound b.castSucc f.castSucc)).conj
      (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc)) :=
    of_eq (by simp only [B, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hB0
  have hbn := Derives.conjL (.conjL ht1)
  have hfn := Derives.conjR (.conjL ht1)
  have hn := SyntaxTerms.range hZ1 w.castSucc b.castSucc f.castSucc n.castSucc hw1 ht1
  have hlim : Derives Δ (.mem (SyntaxTermSyntax.limit bound b.castSucc f.castSucc) w.castSucc) := by
    cases bound with
    | false => exact hfn
    | true => exact hbn
  have hi := StructuralListTraceOrder.member_member hZ1 w.castSucc (Fin.last m) (SyntaxTermSyntax.limit bound b.castSucc f.castSucc) hw1 hlim (.conjL hB)
  have hinputs := SyntaxForestSyntax.intro_inputs 3 w.castSucc (SyntaxAtomSyntax.three b.castSucc f.castSucc n.castSucc)
    (fun j => Fin.cases hbn (fun k => Fin.cases hfn (fun l => Fin.cases hn (fun z => Fin.elim0 z) l) k) j)
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (PureSyntaxTrace.termRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (SyntaxConstructors.exists_constructor hZ1 3 0 w.castSucc (SyntaxAtomSyntax.three b.castSucc f.castSucc n.castSucc) hw1 hinputs)
  have hZ2 := ZFContext.under hZ1 C
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 C)
  have hbn2 : Derives Ξ (.mem b.castSucc.castSucc w.castSucc.castSucc) := under hbn C
  have hfn2 : Derives Ξ (.mem f.castSucc.castSucc w.castSucc.castSucc) := under hfn C
  have hi2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hi C
  have hcode : Derives Ξ (SyntaxVariableSyntax.code bound w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc) := of_eq (SyntaxVariableSyntax.code_rename bound w.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under (.conjR hB) C)
  have hmem : Derives Ξ (.mem (Fin.last m).castSucc (SyntaxTermSyntax.limit bound b.castSucc.castSucc f.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, Formula.rename, SyntaxTermSyntax.limit_map]) (under (.conjL hB) C)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  let env : Fin 3 → Fin (m+2) := SyntaxAtomSyntax.three b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc
  have hnat := HornApplicationRules.intro_nat w.castSucc.castSucc env
    (fun j => Fin.cases hbn2 (fun k => Fin.cases hfn2 (fun l => Fin.cases hi2 (fun z => Fin.elim0 z) l) k) j)
  have happ := PureSyntaxTermMatrix.application_complete hZ2 bound w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) w.castSucc.castSucc env hw2 hnat (.conjR hC) hcode hmem
  have hRule : ObjectTermSyntax.variableRule (!bound) ∈ PureSyntaxRules.rules := by
    cases bound with
    | false => exact List.mem_cons_of_mem _ List.mem_cons_self
    | true => exact List.mem_cons_self
  have hc := PureSyntaxTraceRules.premise_free_condition hZ2 (ObjectTermSyntax.variableRule (!bound)) hRule rfl w.castSucc.castSucc (Fin.last (m+1)) (.conjL hC) happ
  have hout := PureSyntaxTrace.intro_term w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (.conjR hC) hc
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.term_rename]) hout

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.term w b f n)) :
    Derives Γ (PureSyntaxTrace.term w b f n) := by
  apply Derives.disjE (.conjR ht)
  · exact branch_complete (ZFContext.add hZ _) true w b f n (add hw _) (add ht _) (.hyp (Or.inl rfl))
  · exact branch_complete (ZFContext.add hZ _) false w b f n (add hw _) (add ht _) (.hyp (Or.inl rfl))

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((PureSyntaxTrace.term w b f n).iff (SyntaxTermSyntax.term w b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact checked_sound (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact checked_complete (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))

theorem empty_bound_free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z f n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ht : Derives Γ (PureSyntaxTrace.term w z f n)) :
    Derives Γ (SyntaxTermSyntax.branch false w f n) :=
  EmptyBoundFreeInputs.term_free w z f n hz (checked_sound hZ w z f n hw ht)

end PPAC.Migration.Internal.PureSyntaxTermCorrectness
