import PPAC.Migration.ForcingMemberWeakening
import PPAC.Migration.ForcingPreorderLeafTarget

/-! Consume both original existential leaf records and compare their actual
q/p members. The fixed 24 slots per row are the original 6 native, 10 matrix,
5 background and 3 prefix witnesses, in precisely that order. -/
namespace PPAC.Migration.ForcingMemberRows
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local irreducible] ForcingPreorderLeaves.data

private def three {m} (a b c : Fin m) : Fin 3 → Fin m := Fin.cases a (Fin.cases b (fun _ => c))
private def five {m} (a b c d e : Fin m) : Fin 5 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))
private def six {m} (a b c d e f : Fin m) : Fin 6 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (fun _ => f)))))
private theorem cases_zero_mk {n} {α : Sort u} (a : α) (f : Fin n → α) (h : 0<n+1) :
    Fin.cases a f ⟨0,h⟩ = a := rfl
private theorem cases_map {a b : Type} {n} (ρ : a → b) (x : a) (f : Fin n → a) :
    (fun i => ρ (Fin.cases x f i)) = Fin.cases (ρ x) (fun j => ρ (f j)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def nativeFields {m} (U0 : Fin m) (x : Fin 24 → Fin m) : Fin 3 → Fin m := three U0 (x 1) (x 3)
def proofFields {m} (x : Fin 24 → Fin m) : Fin 3 → Fin m := three (x 0) (x 2) (x 4)
def leafFields {m} (x : Fin 24 → Fin m) : Fin 6 → Fin m := six (x 6) (x 8) (x 10) (x 12) (x 14) (x 15)
def tailFields {m} (x : Fin 24 → Fin m) : Fin 5 → Fin m := five (x 5) (x 7) (x 9) (x 11) (x 13)
def backgroundFields {m} (x : Fin 24 → Fin m) : Fin 5 → Fin m := five (x 16) (x 17) (x 18) (x 19) (x 20)
def prefixFields {m} (x : Fin 24 → Fin m) : Fin 3 → Fin m := three (x 21) (x 22) (x 23)

def rowData {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f T C Bound S Refl Pre U0 : Fin m) (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m)
    (x : Fin 24 → Fin m) : Formula m :=
  ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f T C Bound S Refl Pre raw
    (backgroundFields x) (leafFields x) (nativeFields U0 x) (proofFields x) P (tailFields x) (prefixFields x)

theorem rowData_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f T C Bound S Refl Pre U0 : Fin m) (raw : Fin 16 → Fin m) (P : Fin 3 → Fin m)
    (x : Fin 24 → Fin m) (ρ : Fin m → Fin l) :
    (rowData test Reln w z A1 A2 A3 f T C Bound S Refl Pre U0 raw P x).rename ρ =
      rowData test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ Bound) (ρ S) (ρ Refl) (ρ Pre) (ρ U0)
        (fun j => ρ (raw j)) (fun j => ρ (P j)) (fun j => ρ (x j)) := by
  simp only [rowData, ForcingPreorderLeaves.data_rename, nativeFields, proofFields, leafFields, tailFields,
    backgroundFields, prefixFields, three, five, six, cases_map]
  rfl

private structure Params (m : Nat) where
  w : Fin m
  z : Fin m
  A1 : Fin m
  A2 : Fin m
  A3 : Fin m
  f : Fin m
  T : Fin m
  C : Fin m
  Bound : Fin m
  S : Fin m
  Refl : Fin m
  Pre : Fin m
  U0 : Fin m
  raw : Fin 16 → Fin m
  P : Fin 3 → Fin m
private def Params.map {m l} (a : Params m) (ρ : Fin m → Fin l) : Params l :=
  ⟨ρ a.w, ρ a.z, ρ a.A1, ρ a.A2, ρ a.A3, ρ a.f, ρ a.T, ρ a.C, ρ a.Bound, ρ a.S, ρ a.Refl, ρ a.Pre, ρ a.U0,
    (fun j => ρ (a.raw j)), (fun j => ρ (a.P j))⟩

private def e6 {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) : Formula (m+6) :=
  ForcingPreorderLeafTarget.instancesBody test Reln a.w a.z a.A1 a.A2 a.A3 a.f a.T a.C a.Bound a.S a.Refl a.Pre a.U0 a.raw a.P
private def u6 {m} (a : Params m) : Fin 3 → Fin (m+6) := three (old 6 a.U0) (slot 6 1) (slot 6 3)
private def f6 {m} (_a : Params m) : Fin 3 → Fin (m+6) := three (slot 6 0) (slot 6 2) (slot 6 4)
private def e10 {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) : Formula (m+6+10) :=
  let b := a.map (old 6)
  ForcingPreorderLeafTarget.matrixBody test Reln b.w b.z b.A1 b.A2 b.A3 b.f b.T b.C b.Bound b.S b.Refl b.Pre (slot 6 5) b.raw (u6 a) (f6 a) b.P
private def h16 {m} (_a : Params m) : Fin 6 → Fin (m+6+10) := six (slot 10 0) (slot 10 2) (slot 10 4) (slot 10 6) (slot 10 8) (slot 10 9)
private def n16 {m} (_a : Params m) : Fin 5 → Fin (m+6+10) := five (old 10 (slot 6 5)) (slot 10 1) (slot 10 3) (slot 10 5) (slot 10 7)
private def e5 {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) : Formula (m+6+10+5) :=
  let b := (a.map (old 6)).map (old 10)
  ForcingPreorderLeafTarget.backgroundBody test Reln b.w b.z b.A1 b.A2 b.A3 b.f b.T b.C b.Bound b.S b.Refl b.Pre b.raw
    (h16 a) (fun j => old 10 (u6 a j)) (fun j => old 10 (f6 a j)) b.P (n16 a)
private def e3 {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) : Formula (m+6+10+5+3) :=
  let b := ((a.map (old 6)).map (old 10)).map (old 5)
  ForcingPreorderLeaves.body test Reln b.w b.z b.A1 b.A2 b.A3 b.f b.T b.C b.Bound b.S b.Refl b.Pre b.raw (slot 5)
    (fun j => old 5 (h16 a j)) (fun j => old 5 (old 10 (u6 a j))) (fun j => old 5 (old 10 (f6 a j))) b.P (fun j => old 5 (n16 a j))
private def rowContext {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) (Γ : Context m) : Context (m+24) :=
  Context.add (e3 test Reln a) (raisedContext 3 (Context.add (e5 test Reln a) (raisedContext 5
    (Context.add (e10 test Reln a) (raisedContext 10 (Context.add (e6 test Reln a) (raisedContext 6 Γ)))))))

private theorem carry {k m} {Γ : Context m} {φ : Formula m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (a : Params m) (hp : Derives Γ φ) : Derives (rowContext test Reln a Γ) (φ.rename (old 24)) := by
  have h := HornBinderRules.under_body 3 (HornBinderRules.under_body 5
    (HornBinderRules.under_body 10 (HornBinderRules.under_body 6 hp (e6 test Reln a)) (e10 test Reln a)) (e5 test Reln a)) (e3 test Reln a)
  exact of_eq (by simp only [rename_comp]; rfl) h
private theorem carry_zf {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (a : Params m) (hZ : ZFContext.Evidence Γ) : ZFContext.Evidence (rowContext test Reln a Γ) :=
  HornBinderRules.zf_body 3 (HornBinderRules.zf_body 5 (HornBinderRules.zf_body 10
    (HornBinderRules.zf_body 6 hZ (e6 test Reln a)) (e10 test Reln a)) (e5 test Reln a)) (e3 test Reln a)

private theorem old_val {m} (n : Nat) (i : Fin m) : (old n i).val = i.val := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem slot_val {m} (n : Nat) (i : Fin n) : (slot (m := m) n i).val = m+i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [slot, Fin.lastCases_last, Fin.val_last]
    · simp only [slot, Fin.lastCases_castSucc, Fin.val_castSucc, ih]

private theorem actual_row {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m) :
    Derives (rowContext test Reln a Γ)
      (rowData test Reln (old 24 a.w) (old 24 a.z) (old 24 a.A1) (old 24 a.A2) (old 24 a.A3) (old 24 a.f)
        (old 24 a.T) (old 24 a.C) (old 24 a.Bound) (old 24 a.S) (old 24 a.Refl) (old 24 a.Pre) (old 24 a.U0)
        (fun j => old 24 (a.raw j)) (fun j => old 24 (a.P j)) (slot 24)) := by
  have hg : ((fun i => old 3 (slot 5 i)) : Fin 5 → Fin (m+24)) = backgroundFields (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> apply Fin.ext <;> simp only [old_val, slot_val, backgroundFields, five, cases_zero_mk, Fin.cases_succ'] <;> omega
  have hh : ((fun i => old 3 (old 5 (h16 a i))) : Fin 6 → Fin (m+24)) = leafFields (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> apply Fin.ext <;> simp only [old_val, slot_val, h16, leafFields, six, cases_zero_mk, Fin.cases_succ'] <;> omega
  have hu : ((fun i => old 3 (old 5 (old 10 (u6 a i)))) : Fin 3 → Fin (m+24)) = nativeFields (old 24 a.U0) (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl | rfl | rfl <;> apply Fin.ext <;> simp only [old_val, slot_val, u6, nativeFields, three, cases_zero_mk, Fin.cases_succ'] <;> omega
  have hf : ((fun i => old 3 (old 5 (old 10 (f6 a i)))) : Fin 3 → Fin (m+24)) = proofFields (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl | rfl | rfl <;> apply Fin.ext <;> simp only [old_val, slot_val, f6, proofFields, three, cases_zero_mk, Fin.cases_succ'] <;> omega
  have hn : ((fun i => old 3 (old 5 (n16 a i))) : Fin 5 → Fin (m+24)) = tailFields (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> apply Fin.ext <;> simp only [old_val, slot_val, n16, tailFields, five, cases_zero_mk, Fin.cases_succ'] <;> omega
  have hd : (slot 3 : Fin 3 → Fin (m+24)) = prefixFields (slot 24) := by
    funext ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl | rfl | rfl <;> apply Fin.ext <;> simp only [slot_val, prefixFields, three, cases_zero_mk, Fin.cases_succ'] <;> omega
  have eqBody : e3 test Reln a = rowData test Reln (old 24 a.w) (old 24 a.z) (old 24 a.A1) (old 24 a.A2) (old 24 a.A3) (old 24 a.f)
      (old 24 a.T) (old 24 a.C) (old 24 a.Bound) (old 24 a.S) (old 24 a.Refl) (old 24 a.Pre) (old 24 a.U0)
      (fun j => old 24 (a.raw j)) (fun j => old 24 (a.P j)) (slot 24) := by
    dsimp only [e3, ForcingPreorderLeaves.body, Params.map, rowData]
    rw [hg, hh, hu, hf, hn, hd]
    rfl
  exact of_eq eqBody (Derives.hyp (Γ := rowContext test Reln a Γ) (Or.inl rfl))

/-- Four applications of the ORIGINAL fixed-block elimination rule.
This is only a continuation for the already-produced original record. -/
private theorem consume {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2)) (a : Params m)
    (φ : Formula m)
    (ht : Derives Γ (ForcingPreorderLeafTarget.instances test Reln a.w a.z a.A1 a.A2 a.A3 a.f a.T a.C a.Bound a.S a.Refl a.Pre a.U0 a.raw a.P))
    (hc : Derives (rowContext test Reln a Γ) (φ.rename (old 24))) : Derives Γ φ := by
  apply HornBinderRules.eliminate_many 6 (e6 test Reln a) φ ht
  apply HornBinderRules.eliminate_many 10 (e10 test Reln a) (φ.rename (old 6)) (.hyp (Or.inl rfl))
  apply HornBinderRules.eliminate_many 5 (e5 test Reln a) ((φ.rename (old 6)).rename (old 10)) (.hyp (Or.inl rfl))
  apply HornBinderRules.eliminate_many 3 (e3 test Reln a) (((φ.rename (old 6)).rename (old 10)).rename (old 5)) (.hyp (Or.inl rfl))
  exact of_eq (by simp only [rename_comp]; rfl) hc


private def left {m} (x : Fin 48 → Fin m) : Fin 24 → Fin m := fun i => x (i.castAdd 24)
private def right {m} (x : Fin 48 → Fin m) : Fin 24 → Fin m := fun i => x (i.addNat 24)

def input {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral k K).conj
      ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((ForcingWeakenedImages.data w z f z b B R S v).conj
        ((ForcingPreorderLeafTarget.instances test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0)).conj
          ((ForcingPreorderLeafTarget.instances test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) raw (P 1)).conj
            ((SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B (P 0 1) (P 1 1)).conj
              (SyntaxRenameTermSyntax.renamed w (v 2) (v 3) z b z B (P 0 2) (P 1 2))))))))))

theorem input_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P).rename ρ =
      input test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) (fun s => ρ (C s)) (fun s => ρ (Refl s))
        (fun s => ρ (Pre s)) (fun s => ρ (U0 s)) (fun s j => ρ (P s j)) := by
  simp only [input, Formula.rename, SyntaxNumeralSyntax.numeral_rename, ForcingWeakenedImages.data_rename,
    ForcingPreorderLeafTarget.instances_rename, SyntaxRenameTermSyntax.renamed_rename]

def data {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) : Formula m :=
  (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P).conj
    ((rowData test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0) (left x)).conj
      ((rowData test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) raw (P 1) (right x)).conj
        ((SyntaxWeakenFreeSyntax.weakened w z b B (leafFields (left x) 1) (leafFields (right x) 1)).conj
          (SyntaxWeakenFreeSyntax.weakened w z b B (leafFields (left x) 2) (leafFields (right x) 2)))))

theorem data_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (x : Fin 48 → Fin m) (ρ : Fin m → Fin l) :
    (data test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x).rename ρ =
      data test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) (fun s => ρ (C s)) (fun s => ρ (Refl s))
        (fun s => ρ (Pre s)) (fun s => ρ (U0 s)) (fun s j => ρ (P s j)) (fun j => ρ (x j)) := by
  simp only [data, Formula.rename, input_rename, rowData_rename, SyntaxWeakenFreeSyntax.weakened_rename, left, right]
  rfl

def body {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) : Formula (m+48) :=
  data test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f) (old 48 b) (old 48 B) (old 48 R) (old 48 S) (old 48 K)
    (fun j => old 48 (raw j)) (fun j => old 48 (v j)) (fun s => old 48 (C s)) (fun s => old 48 (Refl s))
    (fun s => old 48 (Pre s)) (fun s => old 48 (U0 s)) (fun s j => old 48 (P s j)) (slot 48)

def produced {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) : Formula m :=
  existsMany 48 (body test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P)

theorem produced_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (produced test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P).rename ρ =
      produced test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ B) (ρ R) (ρ S) (ρ K)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) (fun s => ρ (C s)) (fun s => ρ (Refl s))
        (fun s => ρ (Pre s)) (fun s => ρ (U0 s)) (fun s j => ρ (P s j)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_rows {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m)
    (hi : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P))
    (ho : Derives Γ (rowData test Reln w z A1 A2 A3 f b (C 0) R S (Refl 0) (Pre 0) (U0 0) raw (P 0) (left x)))
    (hn : Derives Γ (rowData test Reln w z A1 A2 A3 f B (C 1) (v 8) (v 9) (Refl 1) (Pre 1) (U0 1) raw (P 1) (right x))) :
    Derives Γ (data test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P x) := by
  have h0 := Derives.conjL hi
  have h1 := Derives.conjL (.conjR hi)
  have h2 := Derives.conjL (.conjR (.conjR hi))
  have hK := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  have ht := Derives.conjR (.conjR (.conjR (.conjR (.conjR hi))))
  let G : Fin 2 → Fin 5 → Fin m := Fin.cases (backgroundFields (left x)) (fun _ : Fin 1 => backgroundFields (right x))
  let H : Fin 2 → Fin 6 → Fin m := Fin.cases (leafFields (left x)) (fun _ : Fin 1 => leafFields (right x))
  let U : Fin 2 → Fin 3 → Fin m := Fin.cases (nativeFields (U0 0) (left x)) (fun _ : Fin 1 => nativeFields (U0 1) (right x))
  let F : Fin 2 → Fin 3 → Fin m := Fin.cases (proofFields (left x)) (fun _ : Fin 1 => proofFields (right x))
  let N : Fin 2 → Fin 5 → Fin m := Fin.cases (tailFields (left x)) (fun _ : Fin 1 => tailFields (right x))
  let D : Fin 2 → Fin 3 → Fin m := Fin.cases (prefixFields (left x)) (fun _ : Fin 1 => prefixFields (right x))
  have hq := ForcingMemberWeakening.from_rows hZ test Reln 1 w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D
    (.conjI h0 (.conjI h1 (.conjI h2 (.conjI hK (.conjI hf (.conjI (.conjL ht)
      (.conjI ho (.conjI hn (.conjL (.conjR (.conjR (.conjR ht))))))))))))
  have hp := ForcingMemberWeakening.from_rows hZ test Reln 2 w z A1 A2 A3 f b B R S K raw v C Refl Pre G H U F P N D
    (.conjI h0 (.conjI h1 (.conjI h2 (.conjI hK (.conjI hf (.conjI (.conjL ht)
      (.conjI ho (.conjI hn (.conjR (.conjR (.conjR (.conjR ht))))))))))))
  exact .conjI hi (.conjI ho (.conjI hn (.conjI hq hp)))

theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m)
    (hi : Derives Γ (input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P) := by
  let o : Params m := ⟨w,z,A1,A2,A3,f,b,C 0,R,S,Refl 0,Pre 0,U0 0,raw,P 0⟩
  have ht := Derives.conjR (.conjR (.conjR (.conjR (.conjR hi))))
  apply consume test Reln o _ (.conjL (.conjR ht))
  let Δ := rowContext test Reln o Γ
  have hi24 := of_eq (input_rename test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P (old 24)) (carry test Reln o hi)
  have ho24 := actual_row (Γ := Γ) test Reln o
  have hz24 := carry_zf test Reln o hZ
  let n : Params (m+24) := ⟨old 24 w,old 24 z,old 24 A1,old 24 A2,old 24 A3,old 24 f,old 24 B,old 24 (C 1),
    old 24 (v 8),old 24 (v 9),old 24 (Refl 1),old 24 (Pre 1),old 24 (U0 1),(fun j => old 24 (raw j)),(fun j => old 24 (P 1 j))⟩
  have ht24 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hi24))))
  have hout : Derives Δ (produced test Reln (old 24 w) (old 24 z) (old 24 A1) (old 24 A2) (old 24 A3) (old 24 f)
      (old 24 b) (old 24 B) (old 24 R) (old 24 S) (old 24 K) (fun j => old 24 (raw j)) (fun j => old 24 (v j))
      (fun s => old 24 (C s)) (fun s => old 24 (Refl s)) (fun s => old 24 (Pre s)) (fun s => old 24 (U0 s)) (fun s j => old 24 (P s j))) := by
    apply consume test Reln n _ (.conjL (.conjR (.conjR ht24)))
    let Ξ := rowContext test Reln n Δ
    have hi48 : Derives Ξ (input test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f)
        (old 48 b) (old 48 B) (old 48 R) (old 48 S) (old 48 K) (fun j => old 48 (raw j)) (fun j => old 48 (v j))
        (fun s => old 48 (C s)) (fun s => old 48 (Refl s)) (fun s => old 48 (Pre s)) (fun s => old 48 (U0 s)) (fun s j => old 48 (P s j))) :=
      of_eq (by simp only [input_rename]; rfl) (carry test Reln n hi24)
    have ho48 : Derives Ξ (rowData test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f)
        (old 48 b) (old 48 (C 0)) (old 48 R) (old 48 S) (old 48 (Refl 0)) (old 48 (Pre 0)) (old 48 (U0 0))
        (fun j => old 48 (raw j)) (fun j => old 48 (P 0 j)) (fun j => old 24 (slot 24 j))) :=
      of_eq (by simp only [rowData_rename]; rfl) (carry test Reln n ho24)
    have hn48 : Derives Ξ (rowData test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f)
        (old 48 B) (old 48 (C 1)) (old 48 (v 8)) (old 48 (v 9)) (old 48 (Refl 1)) (old 48 (Pre 1)) (old 48 (U0 1))
        (fun j => old 48 (raw j)) (fun j => old 48 (P 1 j)) (slot 24)) := actual_row (Γ := Δ) test Reln n
    have hL : (fun i => old 24 (slot 24 i) : Fin 24 → Fin (m+48)) = left (slot 48) := by
      funext i
      apply Fin.ext
      simp only [left, old_val, slot_val] <;> rfl
    have hR : (slot 24 : Fin 24 → Fin (m+48)) = right (slot 48) := by
      funext i
      apply Fin.ext
      simp only [right, slot_val]
      change m+24+i.val = m+(i.val+24)
      omega
    have hd := at_rows (carry_zf test Reln n hz24) test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f)
      (old 48 b) (old 48 B) (old 48 R) (old 48 S) (old 48 K) (fun j => old 48 (raw j)) (fun j => old 48 (v j))
      (fun s => old 48 (C s)) (fun s => old 48 (Refl s)) (fun s => old 48 (Pre s)) (fun s => old 48 (U0 s)) (fun s j => old 48 (P s j)) (slot 48)
      hi48 (of_eq (by rw [hL]) ho48) (of_eq (by rw [hR]) hn48)
    have hresult : Derives Ξ (produced test Reln (old 48 w) (old 48 z) (old 48 A1) (old 48 A2) (old 48 A3) (old 48 f)
        (old 48 b) (old 48 B) (old 48 R) (old 48 S) (old 48 K) (fun j => old 48 (raw j)) (fun j => old 48 (v j))
        (fun s => old 48 (C s)) (fun s => old 48 (Refl s)) (fun s => old 48 (Pre s)) (fun s => old 48 (U0 s)) (fun s j => old 48 (P s j))) := by
      apply HornBinderRules.intro_many 48 _ (slot 48)
      exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
    exact of_eq (by simp only [produced_rename]; rfl) hresult
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P (old 24)).symm hout

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) : Source.Sentence :=
  ((input test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P).imp
    (produced test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P)).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b B R S K : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z A1 A2 A3 f b B R S K raw v C Refl Pre U0 P (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingMemberRows
