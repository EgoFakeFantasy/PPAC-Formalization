import PPAC.Migration.Internal.TypedArgumentListConstruction

/-! 有类型原列表的完整内部Nil/Cons分支公式；组件及前驱长度均由对象量词绑定。 -/
namespace PPAC.Migration.Internal.TypedArgumentListCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def nilCase {m} (w k a b n : Fin m) : Formula m :=
  (StructuralListSyntax.nilCode w n).conj ((empty k).conj (SyntaxTermSyntax.contexts w a b))

def consData {m} (w k a b n h t : Fin m) : Formula m :=
  ((Formula.mem h w).conj (.mem t w)).conj ((StructuralListSyntax.consCode w h t n).conj (TypedArgumentListElimination.consParts w k a b h t))

def consBody {m} (w k a b n : Fin m) : Formula (m+2) :=
  consData (old 2 w) (old 2 k) (old 2 a) (old 2 b) (old 2 n) (slot 2 0) (slot 2 1)

def consCase {m} (w k a b n : Fin m) : Formula m := existsMany 2 (consBody w k a b n)

def cases {m} (w k a b n : Fin m) : Formula m := (nilCase w k a b n).disj (consCase w k a b n)

theorem nilCase_rename {m j} (w k a b n : Fin m) (ρ : Fin m → Fin j) :
    (nilCase w k a b n).rename ρ = nilCase (ρ w) (ρ k) (ρ a) (ρ b) (ρ n) := by
  simp only [nilCase, Formula.rename, StructuralListSyntax.nilCode_rename, empty_rename, SyntaxTermSyntax.contexts_rename]

theorem consData_rename {m j} (w k a b n h t : Fin m) (ρ : Fin m → Fin j) :
    (consData w k a b n h t).rename ρ = consData (ρ w) (ρ k) (ρ a) (ρ b) (ρ n) (ρ h) (ρ t) := by
  simp only [consData, Formula.rename, StructuralListSyntax.consCode_rename, TypedArgumentListElimination.consParts_rename]

theorem consBody_lift {m j} (w k a b n : Fin m) (ρ : Fin m → Fin j) :
    (consBody w k a b n).rename (lift 2 ρ) = consBody (ρ w) (ρ k) (ρ a) (ρ b) (ρ n) := by
  simp only [consBody, consData_rename, lift_old, lift_slot]

theorem consCase_rename {m j} (w k a b n : Fin m) (ρ : Fin m → Fin j) :
    (consCase w k a b n).rename ρ = consCase (ρ w) (ρ k) (ρ a) (ρ b) (ρ n) := by
  simp only [consCase, existsMany_rename, consBody_lift]

theorem cases_rename {m j} (w k a b n : Fin m) (ρ : Fin m → Fin j) :
    (cases w k a b n).rename ρ = cases (ρ w) (ρ k) (ρ a) (ρ b) (ρ n) := by
  simp only [cases, Formula.rename, nilCase_rename, consCase_rename]

theorem intro_cons {m} {Γ : Context m} (w k a b n h t : Fin m) (hd : Derives Γ (consData w k a b n h t)) :
    Derives Γ (consCase w k a b n) := by
  let env : Fin 2 → Fin m := Fin.cases h (fun _ => t)
  apply HornBinderRules.intro_many 2 (consBody w k a b n) env
  exact of_eq (by simp only [consBody, consData_rename, assign_old, assign_slot]; rfl) hd

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w k a b n).iff ((empty k).conj (SyntaxTermSyntax.contexts w a b))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxMixedImageCodeSyntax.termList w k a b n
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .conjI (StructuralListLengthRules.nil_empty (ZFContext.add hZ E) w n k (add hw E) (add hn E) (.conjR (.conjL (.conjR (.conjR hE))))) (.conjL (.conjR hE))
  · apply Derives.impI
    have hE : Derives (Context.add ((empty k).conj (SyntaxTermSyntax.contexts w a b)) Γ) ((empty k).conj (SyntaxTermSyntax.contexts w a b)) := .hyp (Or.inl rfl)
    exact TypedArgumentListConstruction.nil_list (ZFContext.add hZ _) w k a b n (add hw _) (.conjL hE) (.conjR hE) (add hn _)

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b n h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w k a b n).iff (TypedArgumentListElimination.consParts w k a b h t)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact TypedArgumentListElimination.cons_parts (ZFContext.add hZ _) w k a b h t n (add hw _) (.hyp (Or.inl rfl)) (add hh _) (add ht _) (add hc _)
  · apply Derives.impI
    let E := TypedArgumentListElimination.consParts w k a b h t
    let B := ((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj
      ((SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc h.castSucc).conj (SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc t.castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under (add hc E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := TypedArgumentListConstruction.cons_list (ZFContext.under (ZFContext.add hZ E) B) w.castSucc (Fin.last m) k.castSucc a.castSucc b.castSucc h.castSucc t.castSucc n.castSucc hw1 (.conjL (.conjR hB)) (.conjR (.conjR hB)) hc1 (.conjR (.conjL hB))
    exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n Fin.castSucc).symm ho

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b n : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n)) : Derives Γ (cases w k a b n) := by
  have hd := StructuralListTraceInvert.valid_decomposition hZ w n hw (StructuralListLengthBasic.valid_of_length w n k (.conjR (.conjL (.conjR (.conjR hL)))))
  apply Derives.disjE hd
  · let E := StructuralListSyntax.nilCode w n
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := Derives.impE (.conjL (nil_iff (ZFContext.add hZ E) w k a b n (add hw E) hE)) (add hL E)
    exact .disjL (.conjI hE he)
  · let E := StructuralListDecodeSyntax.tailCase w n
    let T := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add T (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := T) (.hyp (Or.inl rfl))
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Ξ := Context.add S (Context.image Formula.raise Δ)
    apply Derives.exE (p := S) (.conjR hT)
    have hZ2 := ZFContext.under (ZFContext.under (ZFContext.add hZ E) T) S
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under (add hw E) T) S)
    have hL2 : Derives Ξ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (under (under (add hL E) T) S)
    have ht2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under (StructuralListValidity.range _ _ (.conjL hT)) S
    have hS : Derives Ξ S := .hyp (Or.inl rfl)
    have hp := TypedArgumentListElimination.cons_parts hZ2 w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc hw2 hL2 (.conjL hS) ht2 (.conjR hS)
    have ho : Derives Ξ (cases w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := .disjR
      (intro_cons _ _ _ _ _ _ _ (.conjI (.conjI (.conjL hS) ht2) (.conjI (.conjR hS) hp)))
    simpa only [Formula.raise, cases_rename] using ho

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (cases w k a b n)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n) := by
  apply Derives.disjE hh
  · let E := nilCase w k a b n
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact TypedArgumentListConstruction.nil_list (ZFContext.add hZ E) w k a b n (add hw E) (.conjL (.conjR hE)) (.conjR (.conjR hE)) (.conjL hE)
  · let E := consCase w k a b n
    let B := consBody w k a b n
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := cons_iff hZ2 (old 2 w) (old 2 k) (old 2 a) (old 2 b) (old 2 n) (slot 2 0) (slot 2 1) hw2 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjL (.conjR hB))
    exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n (old 2)).symm (.impE (.conjR he) (.conjR (.conjR hB)))

theorem cases_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w k a b n).iff (cases w k a b n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) w k a b n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward (ZFContext.add hZ _) w k a b n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.TypedArgumentListCases
