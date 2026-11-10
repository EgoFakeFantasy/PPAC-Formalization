import PPAC.Migration.ForcingRelationWeakening
import PPAC.Migration.ForcingFreshPreorder
import PPAC.Migration.ForcingProofContext
import PPAC.Migration.Internal.SyntaxWeakenFreeOutput
import PPAC.Migration.Internal.SyntaxWeakenFreeLogical

/-! SAME-source canonical Global = Extra AND(Pre AND(H1 AND(H2 AND H4))).
All leaf weak relations come from actual existing source records; Extra and
all six new layout codes are produced under object existential quantifiers. -/
namespace PPAC.Migration.ForcingGlobalWeakening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def oldH {m} (x : Fin 48 → Fin m) : Fin 6 → Fin m := ForcingMemberRows.leafFields (fun i => x (i.castAdd 24))
private def newH {m} (x : Fin 48 → Fin m) : Fin 6 → Fin m := ForcingMemberRows.leafFields (fun i => x (i.addNat 24))
private theorem fields_map {m l} (y : Fin 24 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (ForcingMemberRows.leafFields y i)) = ForcingMemberRows.leafFields (fun j => ρ (y j)) := by
  funext ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem oldH_map {m l} (x : Fin 48 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (oldH x i)) = oldH (fun j => ρ (x j)) := fields_map _ ρ
private theorem newH_map {m l} (x : Fin 48 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (newH x i)) = newH (fun j => ρ (x j)) := fields_map _ ρ
private def fresh {m} (P : Fin 2 → Fin 3 → Fin m) (Pre Refl U0 : Fin 2 → Fin m) : Fin 6 → Fin m :=
  Fin.cases (P 1 0) (Fin.cases (P 1 1) (Fin.cases (P 1 2) (Fin.cases (Pre 1) (Fin.cases (Refl 1) (fun _ => U0 1)))))
private theorem fresh_map {m l} (P : Fin 2 → Fin 3 → Fin m) (Pre Refl U0 : Fin 2 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (fresh P Pre Refl U0 i)) = fresh (fun s j => ρ (P s j)) (fun s => ρ (Pre s)) (fun s => ρ (Refl s)) (fun s => ρ (U0 s)) := by
  funext ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def newCtx {m} (y : Fin 7 → Fin m) : Fin 6 → Fin m := fun i => y i.succ

def input {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Formula m :=
  (ForcingRelationWeakening.input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).conj
    ((ForcingFreshPreorder.data test Reln w z A1 A2 A3 f b (C 1) B R S (P 0 1) (P 0 2) (Pre 0) raw v (fresh P Pre Refl U0)).conj
      ((FormulaCodeSyntax.formulaCode w Extra z b).conj (ForcingProofContext.layoutData w z b Extra (Pre 0) (oldH x) oldCtx)))

theorem input_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (input test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx).rename ρ =
      input test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K) (ρ Extra) (fun j => ρ (raw j)) (fun j => ρ (v j))
        (fun s => ρ (C s)) (fun s => ρ (Refl s)) (fun s => ρ (Pre s)) (fun s => ρ (U0 s))
        (fun s j => ρ (P s j)) (fun j => ρ (x j)) (fun j => ρ (oldCtx j)) := by
  simp only [input, Formula.rename, ForcingRelationWeakening.input_rename, ForcingFreshPreorder.data_rename,
    fresh_map, FormulaCodeSyntax.formulaCode_rename, ForcingProofContext.layoutData_rename, oldH_map]

def data {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m) : Formula m :=
  (input test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx).conj
    ((SyntaxWeakenFreeSyntax.weakened w z b B Extra (y 0)).conj
      ((ForcingProofContext.layoutData w z B (y 0) (Pre 1) (newH x) (newCtx y)).conj
        (SyntaxWeakenFreeSyntax.weakened w z b B (oldCtx 3) (newCtx y 3))))

theorem data_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m) (ρ : Fin m → Fin l) :
    (data test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx y).rename ρ =
      data test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K) (ρ Extra) (fun j => ρ (raw j)) (fun j => ρ (v j))
        (fun s => ρ (C s)) (fun s => ρ (Refl s)) (fun s => ρ (Pre s)) (fun s => ρ (U0 s))
        (fun s j => ρ (P s j)) (fun j => ρ (x j)) (fun j => ρ (oldCtx j)) (fun j => ρ (y j)) := by
  simp only [data, Formula.rename, input_rename, SyntaxWeakenFreeSyntax.weakened_rename,
    ForcingProofContext.layoutData_rename, newH_map, newCtx]
  rfl

def body {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Formula (m+7) :=
  data test Reln (old 7 w) (old 7 z) (old 7 A1) (old 7 A2) (old 7 A3) (old 7 f) (old 7 b) (old 7 B) (old 7 R) (old 7 S) (old 7 K) (old 7 Extra) (fun j => old 7 (raw j)) (fun j => old 7 (v j))
    (fun s => old 7 (C s)) (fun s => old 7 (Refl s)) (fun s => old 7 (Pre s)) (fun s => old 7 (U0 s))
    (fun s j => old 7 (P s j)) (fun j => old 7 (x j)) (fun j => old 7 (oldCtx j)) (slot 7)

def produced {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Formula m := existsMany 7 (body test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx)

theorem produced_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (produced test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx).rename ρ = produced test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K) (ρ Extra) (fun j => ρ (raw j)) (fun j => ρ (v j))
      (fun s => ρ (C s)) (fun s => ρ (Refl s)) (fun s => ρ (Pre s)) (fun s => ρ (U0 s))
      (fun s j => ρ (P s j)) (fun j => ρ (x j)) (fun j => ρ (oldCtx j)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private structure Inputs {k m} (Γ : Context m) (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  source : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx)

section
variable {k m : Nat} {Γ : Context m} {test : Formula 1} {Reln : Source.Formula (k+2)}
variable {w z A1 A2 A3 f b B R S K Extra : Fin m} {raw : Fin 16 → Fin m} {v : Fin 10 → Fin m}
variable {C Refl Pre U0 : Fin 2 → Fin m} {P : Fin 2 → Fin 3 → Fin m} {x : Fin 48 → Fin m} {oldCtx : Fin 6 → Fin m}
private theorem Inputs.in_body {l} (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) (F : Formula (m+l)) :
    Inputs (Context.add F (raisedContext l Γ)) test Reln (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l b) (old l B) (old l R) (old l S) (old l K) (old l Extra) (fun j => old l (raw j)) (fun j => old l (v j))
      (fun s => old l (C s)) (fun s => old l (Refl s)) (fun s => old l (Pre s)) (fun s => old l (U0 s))
      (fun s j => old l (P s j)) (fun j => old l (x j)) (fun j => old l (oldCtx j)) :=
  ⟨HornBinderRules.zf_body l h.zf F, of_eq (input_rename test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx (old l)) (HornBinderRules.under_body l h.source F)⟩
private theorem Inputs.relation (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingRelationWeakening.input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) := .conjL h.source
private theorem Inputs.fresh (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingFreshPreorder.data test Reln w z A1 A2 A3 f b (C 1) B R S (P 0 1) (P 0 2) (Pre 0) raw v (fresh P Pre Refl U0)) := .conjL (.conjR h.source)
private theorem Inputs.extra_type (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b) := .conjL (.conjR (.conjR h.source))
private theorem Inputs.old_layout (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingProofContext.layoutData w z b Extra (Pre 0) (oldH x) oldCtx) := .conjR (.conjR (.conjR h.source))
private theorem Inputs.basis (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingMemberRows.input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P) := .conjL (.conjL h.relation)
private theorem Inputs.members (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ ((SyntaxWeakenFreeSyntax.weakened w z b B (oldH x 1) (newH x 1)).conj (SyntaxWeakenFreeSyntax.weakened w z b B (oldH x 2) (newH x 2))) := .conjR (.conjR (.conjR (.conjL h.relation)))
private theorem Inputs.new_row (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) raw (P 1) (fun i => x (i.addNat 24))) := .conjL (.conjR (.conjR (.conjL h.relation)))
private theorem Inputs.base (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (ForcingWeakenedImages.data w z f z b B R S v) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.basis)))))
private theorem Inputs.pre_weak (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B (Pre 0) (Pre 1)) := (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.fresh))))))
private theorem Inputs.omega (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (omega w) := .conjL (.conjL h.base)
private theorem Inputs.successor (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) : Derives Γ (successor B b) := .conjL (.conjR (.conjL h.base))
private theorem Inputs.guard_types (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) (i : Fin 5) : Derives Γ (FormulaCodeSyntax.formulaCode w (newH x i.castSucc) z B) := by
  let D := ForcingMemberRows.prefixFields (fun i => x (i.addNat 24))
  let N := ForcingMemberRows.tailFields (fun i => x (i.addNat 24))
  have hq := ForcingPreorderLeaves.leaf_at w (D 2) (v 9) A3 f z B raw (newH x) N i.castSucc
    (.conjR (.conjR (.conjR (.conjR h.new_row))))
  exact SyntaxMixedFormulaJudgment.target_type w (D 2) (v 9) A3 f z B _ _ hq

private theorem compare (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) (En : Fin m) (ctx : Fin 6 → Fin m)
    (he : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B Extra En))
    (hl : Derives Γ (ForcingProofContext.layoutData w z B En (Pre 1) (newH x) ctx)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B (oldCtx 3) (ctx 3)) := by
  have ops := Derives.conjL (.conjR h.base)
  have hr := ForcingRelationWeakening.from_rows h.zf test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x h.relation
  have join (n q a b' A B' : Fin m)
      (hn : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w a b' n))
      (hq : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w A B' q))
      (ha : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B a A))
      (hb : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B b' B')) :
      Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B n q) :=
    .impE (.conjR (SyntaxWeakenFreeLogical.binary_iff h.zf 0 w z b B n q a b' A B' (v 0) (v 1) h.omega
      (.conjL ops) (.conjL (.conjR ops)) hn hq)) (.conjI ha hb)
  have cold0 := Derives.conjL (.conjL h.old_layout)
  have cnew0 := Derives.conjL (.conjL hl)
  have cold1 := Derives.conjL (.conjL (.conjR h.old_layout))
  have cnew1 := Derives.conjL (.conjL (.conjR hl))
  have cold2 := Derives.conjL (.conjL (.conjR (.conjR h.old_layout)))
  have cnew2 := Derives.conjL (.conjL (.conjR (.conjR hl)))
  have cold3 := Derives.conjL (.conjL (.conjR (.conjR (.conjR h.old_layout))))
  have cnew3 := Derives.conjL (.conjL (.conjR (.conjR (.conjR hl))))
  have w0 := join (oldCtx 0) (ctx 0) (oldH x 2) (oldH x 4) (newH x 2) (newH x 4) cold0 cnew0 (.conjR h.members) hr
  have w1 := join (oldCtx 1) (ctx 1) (oldH x 1) (oldCtx 0) (newH x 1) (ctx 0) cold1 cnew1 (.conjL h.members) w0
  have w2 := join (oldCtx 2) (ctx 2) (Pre 0) (oldCtx 1) (Pre 1) (ctx 1) cold2 cnew2 h.pre_weak w1
  exact join (oldCtx 3) (ctx 3) Extra (oldCtx 2) En (ctx 2) cold3 cnew3 he w2


private theorem at_extra (h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) (En : Fin m)
    (he : Derives Γ (SyntaxWeakenFreeSyntax.weakened w z b B Extra En)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) := by
  have hEn := SyntaxWeakenFreeOutput.target_type w z b B Extra En he
  have hPre := SyntaxWeakenFreeOutput.target_type w z b B (Pre 0) (Pre 1) h.pre_weak
  have hLayout := ForcingProofContext.layout_from_typed h.zf w z B En (Pre 1) (newH x)
    h.omega hEn hPre (fun i => h.guard_types i)
  let F := ForcingProofContext.layoutData (old 6 w) (old 6 z) (old 6 B) (old 6 En) (old 6 (Pre 1))
    (newH (fun j => old 6 (x j))) (slot 6)
  let Δ := Context.add F (raisedContext 6 Γ)
  have hExact : Derives Γ (existsMany 6 F) := of_eq
    (by simp only [ForcingProofContext.layoutExists, ForcingProofContext.layoutBody, newH_map]; rfl) hLayout
  apply HornBinderRules.eliminate_many 6 F _ hExact
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have h6 := h.in_body F
  have he6 := of_eq (SyntaxWeakenFreeSyntax.weakened_rename w z b B Extra En (old 6)) (HornBinderRules.under_body 6 he F)
  have hg6 := compare h6 (old 6 En) (slot 6) he6 hF
  let vals : Fin 7 → Fin (m+6) := Fin.cases (old 6 En) (slot 6)
  have hd : Derives Δ (data test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f)
      (old 6 b) (old 6 B) (old 6 R) (old 6 S) (old 6 K) (old 6 Extra) (fun j => old 6 (raw j)) (fun j => old 6 (v j))
      (fun s => old 6 (C s)) (fun s => old 6 (Refl s)) (fun s => old 6 (Pre s)) (fun s => old 6 (U0 s))
      (fun s j => old 6 (P s j)) (fun j => old 6 (x j)) (fun j => old 6 (oldCtx j)) vals) :=
    .conjI h6.source (.conjI he6 (.conjI hF hg6))
  have ho : Derives Δ (produced test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f)
      (old 6 b) (old 6 B) (old 6 R) (old 6 S) (old 6 K) (old 6 Extra) (fun j => old 6 (raw j)) (fun j => old 6 (v j))
      (fun s => old 6 (C s)) (fun s => old 6 (Refl s)) (fun s => old 6 (Pre s)) (fun s => old 6 (U0 s))
      (fun s j => old 6 (P s j)) (fun j => old 6 (x j)) (fun j => old 6 (oldCtx j))) := by
    apply HornBinderRules.intro_many 7 _ vals
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx (old 6)).symm ho

end

/-- Generate Extra's actual weakening and the SAME new canonical layout;
consume actual source Pre/q/p/R records and all four original AND laws. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K Extra : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (hi : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx)) : Derives Γ (produced test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx) := by
  have h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx := ⟨hZ,hi⟩
  let F := SyntaxWeakenFreeSyntax.weakened (old 1 w) (old 1 z) (old 1 b) (old 1 B) (old 1 Extra) (slot 1 0)
  let Δ := Context.add F (raisedContext 1 Γ)
  have he := SyntaxWeakenFreeOutput.exists_output hZ w z b B Extra h.omega (.conjI h.extra_type h.successor)
  apply HornBinderRules.eliminate_many 1 F _ he
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have h1 := h.in_body F
  have ho := at_extra h1 (slot 1 0) hF
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx (old 1)).symm ho

/-- Consume the generated SAME Global in the existing original guarded
forall pipeline; no weak-Global premise or global abstraction is supplied. -/
theorem generalize_layout {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K Extra Tail : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m)
    (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m)
    (hd : Derives Γ (data test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx y))
    (hp : Derives Γ (ForcingProofUniversal.resultData test w z b (C 1) B (y 0) (Pre 1) Tail (newH x) (newCtx y))) :
    Derives Γ (ForcingProofUniversal.guarded test w z b (C 1) B (oldCtx 3) (newCtx y 3) (newCtx y 4) Tail) := by
  have h : Inputs Γ test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx := ⟨hZ,.conjL hd⟩
  have hf := Derives.conjL h.fresh
  exact ForcingFreshBackground.generalize_layout hZ test w z b (C 1) B (oldCtx 3) (y 0) (Pre 1) Tail (newH x) (newCtx y)
    h.omega (.conjL hf) (.conjL (.conjR hf)) (.conjR (.conjR (.conjR hd))) hp

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Source.Sentence :=
  ((input test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx).imp (produced test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx)).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingGlobalWeakening
