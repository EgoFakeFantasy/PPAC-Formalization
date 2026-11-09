import PPAC.Migration.ForcingFormulaAtoms
import PPAC.Migration.ForcingFormulaLifts
import PPAC.Migration.Internal.SyntaxFormulaComposeInduction

/-! Full INTERNAL formula-code induction for the four actual substitution
paths. All sixteen changing table/scope slots and four output candidates are
object-bound. Original Foundation and Separation discharge the child IH. -/
namespace PPAC.Migration.ForcingFormulaInduction
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingFormulaDiagram (step step_rename atSource atSource_rename apply_atSource)
open ForcingFormulaLifts (input input_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private theorem four_map {α β : Type} (a b c d : α) (r : α → β) :
    (fun i => r (four a b c d i)) = four (r a) (r b) (r c) (r d) := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
private theorem four_eta {α : Type} (a : Fin 4 → α) : four (a 0) (a 1) (a 2) (a 3) = a := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
private def propertyBody {m} (w n : Fin m) : Formula (m+16) :=
  (input (old 16 w) (four (slot 16 0) (slot 16 1) (slot 16 2) (slot 16 3))
    (four (slot 16 4) (slot 16 5) (slot 16 6) (slot 16 7))
    (four (slot 16 8) (slot 16 9) (slot 16 10) (slot 16 11))
    (four (slot 16 12) (slot 16 13) (slot 16 14) (slot 16 15))).imp
  (atSource (old 16 w) (four (slot 16 0) (slot 16 1) (slot 16 2) (slot 16 3))
    (four (slot 16 4) (slot 16 5) (slot 16 6) (slot 16 7))
    (four (slot 16 8) (slot 16 9) (slot 16 10) (slot 16 11))
    (four (slot 16 12) (slot 16 13) (slot 16 14) (slot 16 15)) (old 16 n))

/-- Every changing runtime parameter is quantified INSIDE the object theory. -/
def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 16 (propertyBody w n)

theorem property_rename {m l} (w n : Fin m) (r : Fin m → Fin l) :
    (property w n).rename r = property (r w) (r n) := by
  simp only [property, OriginalUniversalBlock.allMany_rename, propertyBody, Formula.rename,
    input_rename, atSource_rename, four_map, lift_old, lift_slot]

theorem property_at {m} {Γ : Context m} (w n : Fin m) (a b R S : Fin 4 → Fin m)
    (hp : Derives Γ (property w n)) (hi : Derives Γ (input w a b R S)) : Derives Γ (atSource w a b R S n) := by
  let env : Fin 16 → Fin m := (Fin.cases (a 0) (Fin.cases (a 1) (Fin.cases (a 2) (Fin.cases (a 3) (Fin.cases (b 0) (Fin.cases (b 1) (Fin.cases (b 2) (Fin.cases (b 3) (Fin.cases (R 0) (Fin.cases (R 1) (Fin.cases (R 2) (Fin.cases (R 3) (Fin.cases (S 0) (Fin.cases (S 1) (Fin.cases (S 2) (fun _ => (S 3)))))))))))))))))
  have hh : Derives Γ ((input w a b R S).imp (atSource w a b R S n)) := of_eq
    (by simp only [propertyBody, Formula.rename, input_rename, atSource_rename, four_map, assign_old, assign_slot]
        change (input w (four (a 0) (a 1) (a 2) (a 3)) (four (b 0) (b 1) (b 2) (b 3))
          (four (R 0) (R 1) (R 2) (R 3)) (four (S 0) (S 1) (S 2) (S 3))).imp
          (atSource w (four (a 0) (a 1) (a 2) (a 3)) (four (b 0) (b 1) (b 2) (b 3))
            (four (R 0) (R 1) (R 2) (R 3)) (four (S 0) (S 1) (S 2) (S 3)) n) = _
        rw [four_eta, four_eta, four_eta, four_eta])
    (OriginalUniversalBlock.at_many 16 _ env hp)
  exact .impE hh hi

def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem earlier_rename {m l} (w n : Fin m) (r : Fin m → Fin l) :
    (earlier w n).rename r = earlier (r w) (r n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n))
    (hxw : Derives Γ (.mem x w)) (hxn : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hp : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x he)
  exact .impE hp (.conjI hxw hxn)
private theorem child {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n x : Fin m) (a b R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (earlier w n))
    (hxn : Derives Γ (.mem x n)) (hi : Derives Γ (input w a b R S)) : Derives Γ (atSource w a b R S x) := by
  have ht := OmegaStructureInduction.omega_transitive w (ZFContext.separation hZ OmegaStructureSyntax.subsetMatrix) hw
  have hs := Derives.impE (OmegaStructureSyntax.transitive_at w n ht) hn
  have hxw := Derives.impE (RestrictionSyntax.subset_at n w x hs) hxn
  exact property_at w x a b R S (earlier_at w n x he hxw hxn) hi

private theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n x : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x n)) (hi : Derives Γ (input w a b R S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) : Derives Γ (atSource w a b R S n) := by
  let B := ForcingFormulaLifts.frameBody w a b R S
  let Δ := Context.add B (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 B _ (ForcingFormulaLifts.exists_frame hZ w a b R S hw hi)
  have hZ12 := HornBinderRules.zf_body 12 hZ B
  have hw12 := of_eq (omega_rename w (old 12)) (HornBinderRules.under_body 12 hw B)
  have he12 := of_eq (earlier_rename w n (old 12)) (HornBinderRules.under_body 12 he B)
  have hn12 : Derives Δ (.mem (old 12 n) (old 12 w)) := HornBinderRules.under_body 12 hn B
  have hx12 : Derives Δ (.mem (old 12 x) (old 12 n)) := HornBinderRules.under_body 12 hx B
  have hc12 := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n (old 12)) (HornBinderRules.under_body 12 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let A : Fin 4 → Fin (m+12) := four (slot 12 0) (slot 12 1) (slot 12 2) (slot 12 3)
  let K : Fin 4 → Fin (m+12) := four (slot 12 4) (slot 12 6) (slot 12 8) (slot 12 10)
  let H : Fin 4 → Fin (m+12) := four (slot 12 5) (slot 12 7) (slot 12 9) (slot 12 11)
  have hi12 : Derives Δ (input (old 12 w) A (fun i => old 12 (b i)) K H) := .conjR hB
  have hcChild := child hZ12 (old 12 w) (old 12 n) (old 12 x) A (fun i => old 12 (b i)) K H hw12 hn12 he12 hx12 hi12
  have hp := ForcingFormulaDiagram.quantified hZ12 universal (old 12 w)
    (fun i => old 12 (a i)) (fun i => old 12 (b i)) A (fun i => old 12 (R i)) (fun i => old 12 (S i)) K H
    (old 12 n) (old 12 x) hw12 hc12 hcChild (.conjL hB)
  exact of_eq (atSource_rename w a b R S n (old 12)).symm hp

private theorem single_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (earlier w n))
    (hi : Derives Γ (input w a b R S)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase tag advance w (a 0) (b 0) n)) : Derives Γ (atSource w a b R S n) := by
  let B := FormulaCodeRecursiveSyntax.singleCaseBody tag advance w (a 0) (b 0) n
  let Δ := Context.add B (raisedContext 1 Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single tag advance w (a 0) (b 0) n _ hc
  have hZk := HornBinderRules.zf_body 1 hZ B
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hek := of_eq (earlier_rename w n (old 1)) (HornBinderRules.under_body 1 he B)
  have hik := of_eq (input_rename w a b R S (old 1)) (HornBinderRules.under_body 1 hi B)
  have hnk : Derives Δ (.mem (old 1 n) (old 1 w)) := HornBinderRules.under_body 1 hn B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp : Derives Δ (atSource (old 1 w) (fun i => old 1 (a i)) (fun i => old 1 (b i)) (fun i => old 1 (R i)) (fun i => old 1 (S i)) (old 1 n)) := by
    rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ForcingFormulaDiagram.negation hZk (old 1 w) (fun i => old 1 (a i)) (fun i => old 1 (b i)) (fun i => old 1 (R i)) (fun i => old 1 (S i)) (old 1 n) (slot 1 0) hwk (.conjL hB)
        (child hZk (old 1 w) (old 1 n) (slot 1 0) (fun i => old 1 (a i)) (fun i => old 1 (b i)) (fun i => old 1 (R i)) (fun i => old 1 (S i)) hwk hnk hek (.conjL (.conjR hB)) hik)
    · exact quantified hZk true (old 1 w) (fun i => old 1 (a i)) (fun i => old 1 (b i)) (fun i => old 1 (R i)) (fun i => old 1 (S i)) (old 1 n) (slot 1 0) hwk hnk hek (.conjL (.conjR hB)) hik (.conjL hB)
    · exact quantified hZk false (old 1 w) (fun i => old 1 (a i)) (fun i => old 1 (b i)) (fun i => old 1 (R i)) (fun i => old 1 (S i)) (old 1 n) (slot 1 0) hwk hnk hek (.conjL (.conjR hB)) hik (.conjL hB)
  exact of_eq (by simp only [Formula.raise, atSource_rename]; rfl) hp

private theorem binary_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (he : Derives Γ (earlier w n))
    (hi : Derives Γ (input w a b R S)) (hc : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w (a 0) (b 0) n)) : Derives Γ (atSource w a b R S n) := by
  let B := FormulaCodeRecursiveSyntax.binaryCaseBody kind w (a 0) (b 0) n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_binary kind w (a 0) (b 0) n _ hc
  have hZk := HornBinderRules.zf_body 2 hZ B
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hek := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_body 2 he B)
  have hik := of_eq (input_rename w a b R S (old 2)) (HornBinderRules.under_body 2 hi B)
  have hnk : Derives Δ (.mem (old 2 n) (old 2 w)) := HornBinderRules.under_body 2 hn B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := child hZk (old 2 w) (old 2 n) (slot 2 0) (fun i => old 2 (a i)) (fun i => old 2 (b i)) (fun i => old 2 (R i)) (fun i => old 2 (S i)) hwk hnk hek (.conjL (.conjR hB)) hik
  have hy := child hZk (old 2 w) (old 2 n) (slot 2 1) (fun i => old 2 (a i)) (fun i => old 2 (b i)) (fun i => old 2 (R i)) (fun i => old 2 (S i)) hwk hnk hek (.conjL (.conjR (.conjR hB))) hik
  have hp := ForcingFormulaDiagram.binary hZk kind (old 2 w) (fun i => old 2 (a i)) (fun i => old 2 (b i)) (fun i => old 2 (R i)) (fun i => old 2 (S i)) (old 2 n) (slot 2 0) (slot 2 1) hwk (.conjL hB) hx hy
  exact of_eq (by simp only [Formula.raise, atSource_rename]; rfl) hp

private theorem from_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w a b R S))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n (a 0) (b 0))) : Derives Γ (atSource w a b R S n) := by
  have hr := Derives.impE (.conjL (FormulaCodeRecursive.recursive_iff hZ w n (a 0) (b 0) hw)) hc
  have hn := Derives.conjL hr
  have hp : Derives Γ ((FormulaCodeRecursiveSyntax.allCases w n (a 0) (b 0)).imp (atSource w a b R S n)) := by
    apply FormulaCodeCaseLogic.all_imp w n (a 0) (b 0) (atSource w a b R S n)
    · apply Derives.impI
      exact ForcingFormulaAtoms.from_atomic (ZFContext.add hZ _) w a b R S n (add hw _) (.conjL (add hi _)) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl, rfl⟩) w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 0 w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 1 w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 2 w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 3 w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w a b R S n (add hw _) (add hn _) (add he _) (add hi _) (.hyp (Or.inl rfl))
  exact .impE hp (.conjR hr)

private def path {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m) : Formula m :=
  (step w a b R S 0 n u).conj ((step w a b R S 1 u t).conj ((step w a b R S 2 t y).conj (step w a b R S 3 n o)))
private theorem from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b R S : Fin 4 → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w a b R S)) : Derives Γ (atSource w a b R S n) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let B := path (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  let Δ := Context.add B (raisedContext 4 Γ)
  have hZ4 := HornBinderRules.zf_body 4 hZ B
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have he4 := of_eq (earlier_rename w n (old 4)) (HornBinderRules.under_body 4 he B)
  have hi4 := of_eq (input_rename w a b R S (old 4)) (HornBinderRules.under_body 4 hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := Derives.conjL (SyntaxMixedFormulaOutput.input_of_substituted hZ4 (old 4 w) (old 4 (R 0)) (old 4 (S 0)) (old 4 (a 0)) (old 4 (b 0)) (old 4 (a 1)) (old 4 (b 1)) (old 4 n) (slot 4 0) hw4 (.conjL hB))
  have hp := from_code hZ4 (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 n) hw4 he4 hi4 hc
  exact apply_atSource (old 4 w) (fun i => old 4 (a i)) (fun i => old 4 (b i)) (fun i => old 4 (R i)) (fun i => old 4 (S i)) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hp (.conjL hB) (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply OriginalUniversalBlock.intro_many 16
  apply Derives.impI
  let a : Fin 4 → Fin (m+16) := four (slot 16 0) (slot 16 1) (slot 16 2) (slot 16 3)
  let b : Fin 4 → Fin (m+16) := four (slot 16 4) (slot 16 5) (slot 16 6) (slot 16 7)
  let R : Fin 4 → Fin (m+16) := four (slot 16 8) (slot 16 9) (slot 16 10) (slot 16 11)
  let S : Fin 4 → Fin (m+16) := four (slot 16 12) (slot 16 13) (slot 16 14) (slot 16 15)
  let B := input (old 16 w) a b R S
  exact from_earlier (HornBinderRules.zf_body 16 hZ B) (old 16 w) a b R S (old 16 n)
    (of_eq (omega_rename w (old 16)) (HornBinderRules.under_body 16 hw B))
    (of_eq (earlier_rename w n (old 16)) (HornBinderRules.under_body 16 he B)) (.hyp (Or.inl rfl))

open ReplacementPredicates (paramsUp)

def matrix : Formula 2 := property (0 : Fin 1).castSucc (Fin.last 1)

def curried {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem curried_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (curried w n).rename ρ = curried (ρ w) (ρ n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_of_curried {m} {Γ : Context m} (w n : Fin m) (hc : Derives Γ (curried w n)) : Derives Γ (earlier w n) := by
  apply Derives.allI
  apply Derives.impI
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hc1 : Derives Δ (curried w.castSucc n.castSucc) := of_eq (curried_rename w n Fin.castSucc) (under hc C)
  have hh : Derives Δ ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m)))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE (Fin.last m) hc1)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact .impE (.impE hh (.conjL hC)) (.conjR hC)

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := curried w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have he := earlier_of_curried w.castSucc (Fin.last m) (Derives.hyp (Or.inl rfl) : Derives Δ I)
  exact property_from_earlier hZ1 w.castSucc (Fin.last m) hw1 he

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]) hh

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have hp : Derives Γ ((Formula.mem n w).imp (property w n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_properties hZ w hw))
  exact .impE hp hn

/-- All internal natural formula codes, including internally nonstandard
codes, satisfy the four-path formula diagram. No child IH or chosen lift remains. -/
theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (a b R S : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (input w a b R S)) : Derives Γ (atSource w a b R S n) :=
  property_at w n a b R S (at_natural hZ w n hw hn) hi

def sentence {m} (w n : Fin m) (a b R S : Fin 4 → Fin m) : Source.Sentence :=
  (((omega w).conj ((Formula.mem n w).conj (input w a b R S))).imp (atSource w a b R S n)).close

theorem kernel_certificate {m} (w n : Fin m) (a b R S : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w n a b R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (omega w).conj ((Formula.mem n w).conj (input w a b R S))
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact at_code (ZFContext.add (ZFContext.source_ZF m) E) w n a b R S (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

/-- Cancellation at the ACTUAL four formula judgments. All list typings
and source-code naturality are recovered internally, not theorem premises. -/
theorem cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingTermDiagram.diagram w a b R S))
    (h0 : Derives Γ (step w a b R S 0 n u)) (h1 : Derives Γ (step w a b R S 1 u t))
    (h2 : Derives Γ (step w a b R S 2 t y)) (h3 : Derives Γ (step w a b R S 3 n o)) : Derives Γ (.equal y o) := by
  have i0 := SyntaxMixedFormulaOutput.input_of_substituted hZ w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n u hw h0
  have i1 := SyntaxMixedFormulaOutput.input_of_substituted hZ w (R 1) (S 1) (a 1) (b 1) (a 2) (b 2) u t hw h1
  have i2 := SyntaxMixedFormulaOutput.input_of_substituted hZ w (R 2) (S 2) (a 2) (b 2) (a 3) (b 3) t y hw h2
  have i3 := SyntaxMixedFormulaOutput.input_of_substituted hZ w (R 3) (S 3) (a 0) (b 0) (a 3) (b 3) n o hw h3
  have hi : Derives Γ (input w a b R S) := .conjI hd (.conjI (.conjR i0) (.conjI (.conjR i1) (.conjI (.conjR i2) (.conjR i3))))
  have hn := SyntaxMixedFormulaOutput.input_natural w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) n i0
  exact apply_atSource w a b R S n u t y o (at_code hZ w n a b R S hw hn hi) h0 h1 h2 h3

def cancelInput {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m) : Formula m :=
  (omega w).conj ((ForcingTermDiagram.diagram w a b R S).conj (path w a b R S n u t y o))
def cancelSentence {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m) : Source.Sentence :=
  ((cancelInput w a b R S n u t y o).imp (.equal y o)).close

theorem cancel_kernel_certificate {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (n u t y o : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (cancelSentence w a b R S n u t y o)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := cancelInput w a b R S n u t y o
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hp := Derives.conjR (.conjR h)
  exact cancel (ZFContext.add (ZFContext.source_ZF m) E) w a b R S n u t y o
    (.conjL h) (.conjL (.conjR h)) (.conjL hp) (.conjL (.conjR hp)) (.conjL (.conjR (.conjR hp))) (.conjR (.conjR (.conjR hp)))

end PPAC.Migration.ForcingFormulaInduction
