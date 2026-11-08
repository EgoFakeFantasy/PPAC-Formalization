import PPAC.Migration.ForcingCodeRecursion
import PPAC.Migration.BoundedInduction

/-! Actual all-internal code induction closes the history-availability premise.
For every valid source formula at internal empty free scope and arbitrary
internal bound scope, the precise existing recursive forcing-code relation
has an output. All histories, scope successors, states and outputs are object
witnesses. No supplied interpreter output/history availability/standardness.
This is syntactic compilation totality, not uniform coded axiom/proof
correctness, unique formula output, open-proof transport or final Con. -/
namespace PPAC.Migration.ForcingCodeTotal
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open ReplacementPredicates (paramsUp)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def params {m} (w z f j : Fin m) : Fin 4 → Fin m := Fin.cases w (Fin.cases z (SyntaxAtomSyntax.two f j))
private theorem params_map {m l} (w z f j : Fin m) (r : Fin m → Fin l) :
    (fun i => r (params w z f j i)) = params (r w) (r z) (r f) (r j) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun b => Fin.elim0 b) i) i) i) i

def existsCompiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) : Formula m := .ex
  (ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m))
theorem existsCompiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R H w z f j a n).rename r = existsCompiled R H (r w) (r z) (r f) (r j) (r a) (r n) := by
  simp only [existsCompiled, Formula.rename, ForcingCodeRecursion.compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private def property {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .all
  ((formulaCode w.castSucc n.castSucc (Fin.last m) z.castSucc).imp
    (existsCompiled R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc))
private theorem property_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (property R H w z f j n).rename r = property R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [property, Formula.rename, formulaCode_rename, existsCompiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem property_at {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n a : Fin m)
    (hp : Derives Γ (property R H w z f j n)) (hc : Derives Γ (formulaCode w n a z)) : Derives Γ (existsCompiled R H w z f j a n) := by
  have hi : Derives Γ ((formulaCode w n a z).imp (existsCompiled R H w z f j a n)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, formulaCode_rename, existsCompiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE a hp)
  exact .impE hi hc

private def curried {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m))))
private theorem curried_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (curried R H w z f j n).rename r = curried R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem curried_at {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n x : Fin m)
    (hp : Derives Γ (curried R H w z f j n)) (hx : Derives Γ (.mem x w)) (hn : Derives Γ (.mem x n)) :
    Derives Γ (property R H w z f j x) := by
  have hi : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property R H w z f j x))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x hp)
  exact .impE (.impE hi hx) hn

private theorem available_from_induction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g : Fin m)
    (hn : Derives Γ (OrdinalSyntax.ordinal n)) (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hi : Derives Γ (curried R H w z f j n)) : Derives Γ (ForcingCodeStep.available w z f g n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let T := (Formula.mem (Fin.last m).castSucc n.castSucc.castSucc).conj
    (formulaCode w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) z.castSucc.castSucc)
  let Δ := Context.add T (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn2 : Derives Δ (OrdinalSyntax.ordinal n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OrdinalSyntax.ordinal_rename]) (OrderedPairElimination.under_two hn T)
  have hg2 : Derives Δ (ForcingCodeRecursion.graph R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc g.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, ForcingCodeRecursion.graph_rename]) (OrderedPairElimination.under_two hg T)
  have hi2 : Derives Δ (curried R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, curried_rename]) (OrderedPairElimination.under_two hi T)
  have hx := Derives.conjL (FormulaCodeProperties.guards w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) z.castSucc.castSucc (.conjR hT))
  have hp := curried_at R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hi2 hx (.conjL hT)
  have he := property_at R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hp (.conjR hT)
  let U := ForcingCodeRecursion.compiled R H w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add U (Context.image Formula.raise Δ)
  apply Derives.exE (p := U) he
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hn3 := of_eq (OrdinalSyntax.ordinal_rename n.castSucc.castSucc Fin.castSucc) (under hn2 U)
  have hg3 := of_eq (ForcingCodeRecursion.graph_rename R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc g.castSucc.castSucc n.castSucc.castSucc Fin.castSucc) (under hg2 U)
  have hx3 := under (.conjL hT) U
  have hr := ForcingCodeRecursion.compiled_to_read (ZFContext.under (ZFContext.under_two hZ T) U) R H
    w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) hn3 hx3 hg3 hU
  have ho : Derives Ξ (ForcingCodeStep.existsRead w.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc f.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    exact of_eq (by simp only [Formula.instantiate, ForcingCodeStep.read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  exact of_eq (ForcingCodeStep.existsRead_rename w.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc Fin.castSucc).symm ho

private structure Inputs {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (Γ : Context m) (w z f j g n v : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
  hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n)
  hv : Derives Γ (ForcingCodeRecursion.value R H w z f j n g v)
  ha : Derives Γ (ForcingCodeStep.available w z f g n)
private theorem underInputs {k m} {Γ : Context m} {R : Source.Formula (k+2)} {H : Source.Formula (k+1)} {w z f j g n v : Fin m}
    (hI : Inputs R H Γ w z f j g n v) (T : Formula (m+1)) :
    Inputs R H (Context.add T (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc n.castSucc v.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under hI.hw T),
    of_eq (empty_rename z Fin.castSucc) (under hI.hz T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hI.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hI.hj T),
    of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n Fin.castSucc) (under hI.hg T),
    of_eq (ForcingCodeRecursion.value_rename R H w z f j n g v Fin.castSucc) (under hI.hv T),
    of_eq (ForcingCodeStep.available_rename w z f g n Fin.castSucc) (under hI.ha T)⟩

private theorem from_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n v a A B C Q : Fin m)
    (hI : Inputs R H Γ w z f j g n v) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hQ : Derives Γ (ForcingCodeStep.step R H w z f j a A B C g n Q)) : Derives Γ (existsCompiled R H w z f j a n) := by
  have ht := ForcingCodeStep.target_type hZ R H w z f j a A B C g n Q hI.hw hI.hf hQ
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (ForcingCodeStep.state w.castSucc a.castSucc f.castSucc Q.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingCodeStep.state_exists hZ w a f Q hI.hw ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hI1 := underInputs hI T
  have hA1 := of_eq (successor_rename A a Fin.castSucc) (under hA T)
  have hB1 := of_eq (successor_rename B A Fin.castSucc) (under hB T)
  have hC1 := of_eq (successor_rename C B Fin.castSucc) (under hC T)
  have hQ1 := of_eq (ForcingCodeStep.step_rename R H w z f j a A B C g n Q Fin.castSucc) (under hQ T)
  have hr := ForcingCodeRecursion.intro_row R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc (Fin.last m)
    a.castSucc A.castSucc B.castSucc C.castSucc Q.castSucc (.conjR hT) hA1 hB1 hC1 hQ1
  have hm := Derives.impE (.conjR (ForcingCodeRecursion.value_at R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc v.castSucc (Fin.last m) hI1.hv)) (.conjI (.conjL hT) hr)
  have he := ForcingCodeRecursion.intro_evaluation R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc v.castSucc hI1.hg hI1.hv
  have hc := ForcingCodeRecursion.intro_compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc Q.castSucc v.castSucc (Fin.last m) he hm (.conjR hT)
  have ho : Derives Δ (existsCompiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI Q.castSucc
    exact of_eq (by simp only [Formula.instantiate, ForcingCodeRecursion.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename R H w z f j a n Fin.castSucc).symm ho

private theorem scope_stage3 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n v a A B C : Fin m) (hI : Inputs R H Γ w z f j g n v)
    (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A))
    (hC : Derives Γ (successor C B))
    : Derives Γ (existsCompiled R H w z f j a n) := by
  let T := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc A.castSucc B.castSucc C.castSucc g.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingCodeStep.total hZ R H w z f j a A B C g n hI.hw hI.hz hI.hf hI.hj hA hB hC hI.ha hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hA1 := of_eq (successor_rename A a Fin.castSucc) (under hA T)
  have hB1 := of_eq (successor_rename B A Fin.castSucc) (under hB T)
  have hC1 := of_eq (successor_rename C B Fin.castSucc) (under hC T)
  have ho := from_step (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc n.castSucc v.castSucc a.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m) (underInputs hI T) hA1 hB1 hC1 hT
  exact of_eq (existsCompiled_rename R H w z f j a n Fin.castSucc).symm ho

private theorem scope_stage2 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n v a A B : Fin m) (hI : Inputs R H Γ w z f j g n v)
    (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A))
    : Derives Γ (existsCompiled R H w z f j a n) := by
  let T := successor (Fin.last m) B.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert B B (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hA1 := of_eq (successor_rename A a Fin.castSucc) (under hA T)
  have hB1 := of_eq (successor_rename B A Fin.castSucc) (under hB T)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := scope_stage3 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc n.castSucc v.castSucc a.castSucc A.castSucc B.castSucc (Fin.last m) (underInputs hI T) hn1 hA1 hB1 hT
  exact of_eq (existsCompiled_rename R H w z f j a n Fin.castSucc).symm ho

private theorem scope_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n v a A : Fin m) (hI : Inputs R H Γ w z f j g n v)
    (hn : Derives Γ (formulaCode w n a z))
    (hA : Derives Γ (successor A a))
    : Derives Γ (existsCompiled R H w z f j a n) := by
  let T := successor (Fin.last m) A.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert A A (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hA1 := of_eq (successor_rename A a Fin.castSucc) (under hA T)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := scope_stage2 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc n.castSucc v.castSucc a.castSucc A.castSucc (Fin.last m) (underInputs hI T) hn1 hA1 hT
  exact of_eq (existsCompiled_rename R H w z f j a n Fin.castSucc).symm ho

private theorem scope_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n v a : Fin m) (hI : Inputs R H Γ w z f j g n v)
    (hn : Derives Γ (formulaCode w n a z))
    : Derives Γ (existsCompiled R H w z f j a n) := by
  let T := successor (Fin.last m) a.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert a a (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hn1 := of_eq (formulaCode_rename w n a z Fin.castSucc) (under hn T)
  have ho := scope_stage1 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc n.castSucc v.castSucc a.castSucc (Fin.last m) (underInputs hI T) hn1  hT
  exact of_eq (existsCompiled_rename R H w z f j a n Fin.castSucc).symm ho

private theorem property_from_below {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hn : Derives Γ (.mem n w)) (hi : Derives Γ (curried R H w z f j n)) : Derives Γ (property R H w z f j n) := by
  have hno := NaturalOrderBasic.ordinal hZ w n hw hn
  let G := ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (ForcingCodeRecursion.exists_graph hZ R H w z f j n hno)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  let V := ForcingCodeRecursion.value R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (ForcingCodeRecursion.exists_value (ZFContext.under hZ G) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m))
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hG2 := of_eq (ForcingCodeRecursion.graph_rename R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under hG V)
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) V)
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (under (under hz G) V)
  have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral (k+2) f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under hf G) V)
  have hj2 : Derives Ξ (SyntaxNumeralSyntax.numeral (k+1) j.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under hj G) V)
  have hno2 : Derives Ξ (OrdinalSyntax.ordinal n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OrdinalSyntax.ordinal_rename]) (under (under hno G) V)
  have hi2 : Derives Ξ (curried R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, curried_rename]) (under (under hi G) V)
  have hZ2 := ZFContext.under (ZFContext.under hZ G) V
  have ha := available_from_induction hZ2 R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hno2 hG2 hi2
  have hI : Inputs R H Ξ w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)) := ⟨hw2,hz2,hf2,hj2,hG2,hV,ha⟩
  have hp : Derives Ξ (property R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc) := by
    apply Derives.allI
    apply Derives.impI
    let T := formulaCode w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) z.castSucc.castSucc.castSucc
    exact scope_stage0 (ZFContext.under hZ2 T) R H w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (underInputs hI T) (.hyp (Or.inl rfl))
  exact of_eq (by simp only [Formula.raise, property_rename]) hp

private def propertyMatrix {k} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) : Formula (4+1) :=
  property R H (0 : Fin 4).castSucc (1 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)
private theorem matrix_pred {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (ρ : Fin 4 → Fin m) (n : Fin m) :
    MinimalPredicates.pred (propertyMatrix R H) ρ n = property R H (ρ 0) (ρ 1) (ρ 2) (ρ 3) n := by
  simp only [MinimalPredicates.pred, propertyMatrix, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem progressive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)) :
    Derives Γ (BoundedInduction.progressive (propertyMatrix R H) (params w z f j) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := curried R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (add (add (Derives.rename Fin.castSucc hz) M) I)
  have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral (k+2) f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (add (add (Derives.rename Fin.castSucc hf) M) I)
  have hj1 : Derives Δ (SyntaxNumeralSyntax.numeral (k+1) j.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (add (add (Derives.rename Fin.castSucc hj) M) I)
  exact property_from_below hZ1 R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) hw1 hz1 hf1 hj1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem all_properties {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m)))) := by
  have he := BoundedInduction.induction_on_set (propertyMatrix R H) (params w z f j) w
    (ZFContext.separation hZ (propertyMatrix R H).neg) (ZFContext.arithmetic hZ).base.foundation
    (progressive hZ R H w z f j hw hz hf hj)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]; rfl) he

/-- Every internally legal source code has an actual recursive output. No
history availability or supplied output is an input to this theorem. -/
theorem total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (formulaCode w n a z)) : Derives Γ (existsCompiled R H w z f j a n) := by
  have hn := Derives.conjL (FormulaCodeProperties.guards w n a z hc)
  have hp : Derives Γ ((Formula.mem n w).imp (property R H w z f j n)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.allE n (all_properties hZ R H w z f j hw hz hf hj))
  exact property_at R H w z f j n a (.impE hp hn) hc

def typedOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) : Formula m := .ex
  ((ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)).conj
    (formulaCode w.castSucc (Fin.last m) a.castSucc f.castSucc))
theorem typedOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) (r : Fin m → Fin l) :
    (typedOutput R H w z f j a n).rename r = typedOutput R H (r w) (r z) (r f) (r j) (r a) (r n) := by
  simp only [typedOutput, Formula.rename, ForcingCodeRecursion.compiled_rename, formulaCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typed_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (formulaCode w n a z)) : Derives Γ (typedOutput R H w z f j a n) := by
  let T := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (total hZ R H w z f j a n hw hz hf hj hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingCodeRecursion.target_type R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m) hT
  have ho : Derives Δ (typedOutput R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, ForcingCodeRecursion.compiled_rename,
      formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT ht)
  exact of_eq (typedOutput_rename R H w z f j a n Fin.castSucc).symm ho

/-- Every actual parent history now has all legal smaller child results;
the formerly supplied object available premise is discharged. -/
theorem actual_available {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hn : Derives Γ (.mem n w)) (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n)) :
    Derives Γ (ForcingCodeStep.available w z f g n) := by
  have he : Derives Γ (curried R H w z f j n) := by
    apply Derives.allI
    apply Derives.impI
    apply Derives.impI
    let M := Formula.mem (Fin.last m) w.castSucc
    let N := Formula.mem (Fin.last m) n.castSucc
    let Δ := Context.add N (Context.add M (Context.image Formula.raise Γ))
    have hp := all_properties hZ R H w z f j hw hz hf hj
    have hp1 : Derives (Context.image Formula.raise Γ) (.all ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp (property R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1))))) :=
      of_eq (by simp only [Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) (Derives.rename Fin.castSucc hp)
    have hi : Derives (Context.image Formula.raise Γ) ((Formula.mem (Fin.last m) w.castSucc).imp
        (property R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m))) :=
      of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE (Fin.last m) hp1)
    exact .impE (add (add hi M) N) (.hyp (Or.inr (Or.inl rfl)))
  exact available_from_induction hZ R H w z f j n g (NaturalOrderBasic.ordinal hZ w n hw hn) hg he

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp ((formulaCode w n a z).imp (typedOutput R H w z f j a n)))))).close
theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j a n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact typed_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) R H w z f j a n
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
def availabilitySentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp ((Formula.mem n w).imp ((ForcingCodeRecursion.graph R H w z f j g n).imp (ForcingCodeStep.available w z f g n))))))).close
theorem availability_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (availabilitySentence R H w z f j n g)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact actual_available (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) R H w z f j n g
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingCodeTotal
