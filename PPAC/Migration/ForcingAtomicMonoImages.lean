import PPAC.Migration.ForcingAtomicMonoTemplate
import PPAC.Migration.ForcingAtomicMono
import PPAC.Migration.ForcingRawModalBody
import PPAC.Migration.ForcingRelationWeakening

/-! Build the shared atomic instance from the actual condition and argument
images, using the original typed Cons producer and field readback. -/
namespace PPAC.Migration.ForcingAtomicMonoImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxNumeralSyntax (numeral numeral_rename)
open SyntaxMixedImageCodeSyntax (termList termList_rename)
open StructuralListFieldSyntax (field field_rename)
open NativeProofQuotation (eliminate_objects)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
open SyntaxMixedFormulaJudgmentSyntax renaming substituted → mixed, substituted_rename → mixed_rename
open ForcingAtomicMonoTemplate (Part depth boundMap freeMap boundIndex freeIndex)
open YesMetaZFC.SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private inductive Prefix {m} (Γ : Context m) (w z b f S : Fin m) :
    List (Fin m) → Fin m → Fin m → Prop
  | base (typed : Derives Γ (termList w f z b S)) : Prefix Γ w z b f S [] f S
  | cons {xs : List (Fin m)} {a L h A V : Fin m}
      (tail : Prefix Γ w z b f S xs a L)
      (head : Derives Γ (SyntaxTermSyntax.term w z b h))
      (next : Derives Γ (successor A a))
      (node : Derives Γ (StructuralListSyntax.consCode w h L V))
      (typed : Derives Γ (termList w A z b V)) : Prefix Γ w z b f S (h :: xs) A V

private theorem Prefix.typed {m} {Γ : Context m} {w z b f S a L : Fin m} {xs : List (Fin m)}
    (h : Prefix Γ w z b f S xs a L) : Derives Γ (termList w a z b L) := by
  cases h with
  | base h => exact h
  | cons _ _ _ _ h => exact h

private theorem Prefix.map {m l} {Γ : Context m} {Δ : Context l} {w z b f S a L : Fin m}
    {xs : List (Fin m)} (h : Prefix Γ w z b f S xs a L)
    (r : Fin m → Fin l) (carry : ∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) :
    Prefix Δ (r w) (r z) (r b) (r f) (r S) (xs.map r) (r a) (r L) := by
  induction h with
  | base h => exact .base (of_eq (termList_rename w f z b S r) (carry h))
  | @cons _ a L h A V _ head next node typed ih =>
    exact .cons ih (of_eq (SyntaxTermSyntax.term_rename w z b h r) (carry head))
      (of_eq (successor_rename A a r) (carry next))
      (of_eq (StructuralListSyntax.consCode_rename w h L V r) (carry node))
      (of_eq (termList_rename w A z b V r) (carry typed))

private theorem Prefix.length_numeral {m k} {Γ : Context m} {w z b f S a L : Fin m}
    {xs : List (Fin m)} (h : Prefix Γ w z b f S xs a L) (hf : Derives Γ (numeral k f)) :
    Derives Γ (numeral (k+xs.length) a) := by
  induction h with
  | base _ => exact hf
  | @cons xs a L h A V _ _ next _ _ ih =>
    exact SyntaxNumeralSyntax.intro_succ (k+xs.length) A a ih next

private theorem list_natural {m} {Γ : Context m} (w z b a L : Fin m)
    (h : Derives Γ (termList w a z b L)) : Derives Γ (.mem L w) := .conjL (.conjL (.conjR (.conjR h)))

private theorem with_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b a h L : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxTermSyntax.term w z b h))
    (hl : Derives Γ (termList w a z b L)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (A V : Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Derives Δ (successor A (r a)) → Derives Δ (StructuralListSyntax.consCode (r w) (r h) (r L) V) →
      Derives Δ (termList (r w) A (r z) (r b) V) → Derives Δ (out.rename r)) : Derives Γ out := by
  apply InternalProofTemplates.eliminate_successor hZ w a hw (.conjL hl) out
  intro l Δ r A hZ1 lift hA
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hh1 := of_eq (SyntaxTermSyntax.term_rename w z b h r) (lift hh)
  have hl1 := of_eq (termList_rename w a z b L r) (lift hl)
  have he := StructuralConsCore.exists_cons hZ1 (r w) (r h) (r L) hw1
    (SyntaxTerms.range hZ1 (r w) (r z) (r b) (r h) hw1 hh1)
    (list_natural (r w) (r z) (r b) (r a) (r L) hl1)
  apply eliminate_objects hZ1 1 (fun s vs => (Formula.mem (vs 0) (s (r w))).conj
    (StructuralListSyntax.consCode (s (r w)) (s (r h)) (s (r L)) (vs 0))) he (out.rename r)
  intro l' Δ' s vs hZ2 move hV
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (proof : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift proof))
  have hA2 := of_eq (successor_rename A (r a) s) (move hA)
  have hNew := TypedArgumentListConstruction.cons_list hZ2 (ρ w) (ρ a) (s A) (ρ z) (ρ b) (ρ h) (ρ L) (vs 0)
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (SyntaxTermSyntax.term_rename w z b h ρ) (carry hh))
    (of_eq (termList_rename w a z b L ρ) (carry hl)) (.conjR hV) hA2
  exact of_eq (rename_comp out r s).symm (use ρ (s A) (vs 0) hZ2 carry hA2 (.conjR hV) hNew)

private theorem with_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f S : Fin m)
    (xs : List (Fin m)) (hw : Derives Γ (omega w)) (hl : Derives Γ (termList w f z b S))
    (heads : ∀ h ∈ xs, Derives Γ (SyntaxTermSyntax.term w z b h)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (a L : Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Prefix Δ (r w) (r z) (r b) (r f) (r S) (xs.map r) a L → Derives Δ (out.rename r)) :
    Derives Γ out := by
  induction xs with
  | nil =>
    exact of_eq (Reverse.source_rename_id out)
      (use id f S hZ (fun p => of_eq (Reverse.source_rename_id _).symm p) (.base hl))
  | cons h xs ih =>
    apply ih (fun t ht => heads t (List.mem_cons_of_mem h ht))
    intro l Δ r a L hZ1 lift hPrefix
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hh1 := of_eq (SyntaxTermSyntax.term_rename w z b h r) (lift (heads h List.mem_cons_self))
    apply with_cons hZ1 (r w) (r z) (r b) a (r h) L hw1 hh1 hPrefix.typed (out.rename r)
    intro l' Δ' s A V hZ2 move hA hV ht
    let ρ := fun i => s (r i)
    have carry {p : Formula m} (proof : Derives Γ p) : Derives Δ' (p.rename ρ) :=
      of_eq (rename_comp p r s) (move (lift proof))
    have pref : Prefix Δ' (ρ w) (ρ z) (ρ b) (ρ f) (ρ S) ((h :: xs).map ρ) A V := by
      have tail := hPrefix.map s move
      rw [List.map_map] at tail
      exact .cons tail (of_eq (SyntaxTermSyntax.term_rename w z b h ρ)
        (carry (heads h List.mem_cons_self))) hA hV ht
    exact of_eq (rename_comp out r s).symm (use ρ A V hZ2 carry pref)

private theorem Prefix.front {m} {Γ : Context m} {w z b f S A V : Fin m}
    {xs : List (Fin m)} (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (h : Prefix Γ w z b f S xs A V) (j : Fin xs.length) (i : Fin m)
    (hi : Derives Γ (numeral j.val i)) : Derives Γ (field w V i xs[j]) := by
  let n := xs.length
  have hn : xs.length ≤ n := Nat.le_refl _
  clear_value n
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
   revert hn
   cases h with
   | base _ => exact Fin.elim0 j
   | @cons xs a L head _ _ tail hh hs hc ht =>
    intro hn
    revert hi
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hi
      exact StructuralListFieldCons.zero_value hZ w head L V i hw
        (SyntaxTerms.range hZ w z b head hw hh) (list_natural w z b a L tail.typed) hc hi
    · intro hi
      let E := (numeral j.val (Fin.last m)).conj (successor i.castSucc (Fin.last m))
      let Δ := Context.add E (Context.image Formula.raise Γ)
      apply SyntaxNumeralSyntax.eliminate_succ j.val i _ hi
      have hE : Derives Δ E := .hyp (Or.inl rfl)
      have hZ1 := ZFContext.under hZ E
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
      have tail1 := tail.map Fin.castSucc (fun p => under p E)
      let j' : Fin (xs.map (Fin.castSucc : Fin m → Fin (m+1))).length :=
        Fin.cast (List.length_map Fin.castSucc).symm j
      have hf := ih xs.length (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)
        hZ1 hw1 tail1 j' (Fin.last m) (.conjL hE) (by simp only [List.length_map, Nat.le_refl])
      have ho := StructuralListFieldCons.successor_backward hZ1 w.castSucc head.castSucc L.castSucc V.castSucc
        (Fin.last m) i.castSucc (xs[j]).castSucc hw1
        (SyntaxTerms.range hZ1 w.castSucc z.castSucc b.castSucc head.castSucc hw1
          (of_eq (SyntaxTermSyntax.term_rename w z b head Fin.castSucc) (under hh E)))
        (list_natural w.castSucc z.castSucc b.castSucc a.castSucc L.castSucc tail1.typed)
        (SyntaxNumerals.range hZ1 j.val w.castSucc (Fin.last m) hw1 (.conjL hE)) (.conjR hE)
        (of_eq (StructuralListSyntax.consCode_rename w head L V Fin.castSucc) (under hc E))
        (of_eq (congrArg (field w.castSucc L.castSucc (Fin.last m)) (List.getElem_map Fin.castSucc)) hf)
      exact of_eq (by simp only [Formula.raise, field_rename] <;> rfl) ho

private theorem Prefix.tail_field {m j} {Γ : Context m} {w z b f S A V : Fin m}
    {xs : List (Fin m)} (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (h : Prefix Γ w z b f S xs A V) (i v Y : Fin m)
    (hi : Derives Γ (numeral j i)) (hv : Derives Γ (numeral (j+xs.length) v))
    (hy : Derives Γ (field w S i Y)) : Derives Γ (field w V v Y) := by
  let n := xs.length
  have hn : xs.length ≤ n := Nat.le_refl _
  clear_value n
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
   revert hn
   cases h with
   | base _ =>
    intro _
    have he := SyntaxNumerals.unique hZ j i v hi hv
    let Q := field w.castSucc S.castSucc (Fin.last m) Y.castSucc
    exact of_eq (by simp only [Q, Formula.instantiate, field_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst Q he (of_eq (by simp only [Q, Formula.instantiate, field_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy))
   | @cons xs a L head _ _ tail hh hs hc ht =>
    intro hn
    let E := (numeral (j+xs.length) (Fin.last m)).conj (successor v.castSucc (Fin.last m))
    let Δ := Context.add E (Context.image Formula.raise Γ)
    apply SyntaxNumeralSyntax.eliminate_succ (j+xs.length) v _ hv
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ E
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
    have tail1 := tail.map Fin.castSucc (fun p => under p E)
    have hf := ih xs.length (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)
      hZ1 hw1 tail1 i.castSucc (Fin.last m) Y.castSucc
      (of_eq (numeral_rename j i Fin.castSucc) (under hi E))
      (of_eq (by simp only [List.length_map]) (.conjL hE))
      (of_eq (field_rename w S i Y Fin.castSucc) (under hy E))
      (by simp only [List.length_map, Nat.le_refl])
    exact of_eq (by simp only [Formula.raise, field_rename])
      (StructuralListFieldCons.successor_backward hZ1 w.castSucc head.castSucc L.castSucc V.castSucc
        (Fin.last m) v.castSucc Y.castSucc hw1
        (SyntaxTerms.range hZ1 w.castSucc z.castSucc b.castSucc head.castSucc hw1
          (of_eq (SyntaxTermSyntax.term_rename w z b head Fin.castSucc) (under hh E)))
        (list_natural w.castSucc z.castSucc b.castSucc a.castSucc L.castSucc tail1.typed)
        (SyntaxNumerals.range hZ1 (j+xs.length) w.castSucc (Fin.last m) hw1 (.conjL hE)) (.conjR hE)
        (of_eq (StructuralListSyntax.consCode_rename w head L V Fin.castSucc) (under hc E)) hf)

private def width (k : Nat) (part : Part) (bound : Bool) : Nat :=
  if bound then depth part else k+2

private def destination (k : Nat) (part : Part) : (bound : Bool) →
    Fin (width k part bound) → Fin (k+7)
  | true => boundIndex k part
  | false => freeIndex k part

private def routeBody {m} (src dst : Nat) (w D L : Fin m) (i p value : Fin m) : Formula m :=
  ((numeral src i).conj ((numeral dst p).conj (field w D i value))).imp (field w L p value)

def route {m} (src dst : Nat) (w D L : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3
    (routeBody src dst (old 3 w) (old 3 D) (old 3 L) (slot 3 0) (slot 3 1) (slot 3 2))

private theorem route_body_rename {m l} (src dst : Nat) (w D L i p value : Fin m)
    (r : Fin m → Fin l) :
    (routeBody src dst w D L i p value).rename r =
      routeBody src dst (r w) (r D) (r L) (r i) (r p) (r value) := by
  simp only [routeBody, Formula.rename, numeral_rename, field_rename]

theorem route_rename {m l} (src dst : Nat) (w D L : Fin m) (r : Fin m → Fin l) :
    (route src dst w D L).rename r = route src dst (r w) (r D) (r L) := by
  simp only [route, OriginalUniversalBlock.allMany_rename, route_body_rename, lift_old, lift_slot]

theorem use_route {m} {Γ : Context m} (src dst : Nat) (w D L i p v : Fin m)
    (h : Derives Γ (route src dst w D L)) (hi : Derives Γ (numeral src i))
    (hp : Derives Γ (numeral dst p)) (hv : Derives Γ (field w D i v)) : Derives Γ (field w L p v) := by
  have hBody : Derives Γ (routeBody src dst w D L i p v) := of_eq
    (by simp only [route_body_rename, assign_old, assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 3 _ (SetLanguage.args3 i p v) h)
  exact .impE hBody (.conjI hi (.conjI hp hv))

theorem intro_route {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (src dst : Nat) (w D L : Fin m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (i p v : Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      Derives Δ (numeral src i) → Derives Δ (numeral dst p) → Derives Δ (field (r w) (r D) i v) →
      Derives Δ (field (r w) (r L) p v)) : Derives Γ (route src dst w D L) := by
  apply OriginalUniversalBlock.intro_many 3
  apply Derives.impI
  let r : Fin m → Fin (m+3) := old 3
  let i : Fin (m+3) := slot 3 0
  let p : Fin (m+3) := slot 3 1
  let v : Fin (m+3) := slot 3 2
  let E := (numeral src i).conj ((numeral dst p).conj (field (r w) (r D) i v))
  have hE : Derives (Context.add E (raisedContext 3 Γ)) E := .hyp (Or.inl rfl)
  exact use r i p v (HornBinderRules.zf_body 3 hZ E) (fun proof => HornBinderRules.under_body 3 proof E)
    (.conjL hE) (.conjL (.conjR hE)) (.conjR (.conjR hE))

private theorem route_tail {m} {Γ : Context m} {w z b f S g L : Fin m} {xs : List (Fin m)}
    (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (pref : Prefix Γ w z b f S xs g L) (j : Nat) : Derives Γ (route j (j+xs.length) w S L) := by
  apply intro_route hZ j (j+xs.length) w S L
  intro l Δ r i p v hZ1 lift hi hp hv
  have hp' : Derives Δ (numeral (j+(xs.map r).length) p) :=
    of_eq (congrArg (fun n => numeral (j+n) p) (List.length_map r).symm) hp
  exact (pref.map r lift).tail_field hZ1 (of_eq (omega_rename w r) (lift hw)) i p v hi hp' hv

private theorem route_head {m} {Γ : Context m} {w z b f S g L : Fin m} {xs : List (Fin m)}
    (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (pref : Prefix Γ w z b f S xs g L) (j : Nat) (p : Fin xs.length) (D i0 : Fin m)
    (hi0 : Derives Γ (numeral j i0)) (hv0 : Derives Γ (field w D i0 xs[p])) :
    Derives Γ (route j p.val w D L) := by
  apply intro_route hZ j p.val w D L
  intro l Δ r i index v hZ1 lift hi hp hv
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hi1 := of_eq (numeral_rename j i0 r) (lift hi0)
  have eq := SyntaxNumerals.unique hZ1 j (r i0) i hi1 hi
  have hOld := StructuralListFieldSyntax.index_subst (r w) (r D) (r i0) i (r xs[p]) eq
    (of_eq (field_rename w D i0 xs[p] r) (lift hv0))
  have hvEq := StructuralListFieldValues.unique hZ1 (r w) (r D) i (r xs[p]) v hw1
    (SyntaxNumerals.range hZ1 j (r w) i hw1 hi) hOld hv
  let p' : Fin (xs.map r).length := Fin.cast (List.length_map r).symm p
  have hFront := Prefix.front hZ1 hw1 (pref.map r lift) p' index hp
  have hNew : Derives Δ (field (r w) (r L) index (r xs[p])) :=
    of_eq (congrArg (field (r w) (r L) index) (List.getElem_map r)) hFront
  exact StructuralListFieldSyntax.output_subst (r w) (r L) index (r xs[p]) v hvEq hNew

private theorem route_overwrite_tail {k m} {Γ : Context m} {w z b f S g L : Fin m} {xs : List (Fin m)}
    (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (pref : Prefix Γ w z b f S xs g L) (j : Fin (k+2)) (hj : j.val ≠ k+1) (J h V : Fin m)
    (hf : Derives Γ (numeral (k+2) f)) (hJ : Derives Γ (numeral (k+1) J))
    (hV : Derives Γ (ForcingReflexiveImages.replacement w f z b S J h V)) :
    Derives Γ (route j.val (j.val+xs.length) w V L) := by
  apply intro_route hZ j.val (j.val+xs.length) w V L
  intro l Δ r i p v hZ1 lift hi hp hv
  have hf1 := of_eq (numeral_rename (k+2) f r) (lift hf)
  have hJ1 := of_eq (numeral_rename (k+1) J r) (lift hJ)
  have hV1 := of_eq (ForcingReflexiveImages.replacement_rename w f z b S J h V r) (lift hV)
  have hDiff := SyntaxNumerals.different hZ1 j.val (k+1) hj i (r J) hi hJ1
  have hChoice := Derives.impE (.conjL (ForcingReflexiveImages.field_iff (r w) (r f) (r z) (r b)
    (r S) (r J) (r h) (r V) i v hV1 (SyntaxNumeralMembers.index_member hZ1 (k+2) j (r f) i hf1 hi))) hv
  have hRoute := of_eq (route_rename j.val (j.val+xs.length) w S L r) (lift (route_tail hZ hw pref j.val))
  apply Derives.disjE hChoice
  · exact .botE (.impE (add hDiff _) (.conjL (.hyp (Or.inl rfl))))
  · exact use_route j.val (j.val+xs.length) (r w) (r S) (r L) i p v
      (add hRoute _) (add hi _) (add hp _) (.conjR (.hyp (Or.inl rfl)))

private theorem route_overwrite_head {k m} {Γ : Context m} {w z b f S g L : Fin m} {xs : List (Fin m)}
    (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (pref : Prefix Γ w z b f S xs g L) (p : Fin xs.length) (J V : Fin m)
    (hf : Derives Γ (numeral (k+2) f)) (hJ : Derives Γ (numeral (k+1) J))
    (hV : Derives Γ (ForcingReflexiveImages.replacement w f z b S J xs[p] V)) :
    Derives Γ (route (k+1) p.val w V L) := by
  have hi := SyntaxNumeralMembers.index_member hZ (k+2) (Fin.last (k+1)) f J hf hJ
  have hField := Derives.impE (.conjR (ForcingReflexiveImages.field_iff w f z b S J xs[p] V J xs[p] hV hi))
    (.disjL (.conjI (.eqRefl J) (.eqRefl xs[p])))
  exact route_head hZ hw pref (k+1) p V J hJ hField

private theorem route_forest {m n} {Γ : Context m} {w z b f S g L : Fin m} {xs : List (Fin m)}
    (hZ : ZFContext.Evidence Γ) (hw : Derives Γ (omega w))
    (pref : Prefix Γ w z b f S xs g L) (j : Fin n) (p : Fin xs.length) (D : Fin m) (terms : Fin n → Fin m)
    (same : terms j = xs[p]) (hD : Derives Γ (SyntaxForestSyntax.forest n w terms D)) :
    Derives Γ (route j.val p.val w D L) := by
  apply intro_route hZ j.val p.val w D L
  intro l Δ r i index v hZ1 lift hi hp hv
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hD1 := of_eq (SyntaxForestSyntax.forest_rename n w terms D r) (lift hD)
  have hvEq := eq_symm (Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ1 n (r w)
    (fun j => r (terms j)) (r D) j i v hw1 hD1 hi)) hv)
  let p' : Fin (xs.map r).length := Fin.cast (List.length_map r).symm p
  have hFront := Prefix.front hZ1 hw1 (pref.map r lift) p' index hp
  have hNew : Derives Δ (field (r w) (r L) index (r xs[p])) :=
    of_eq (congrArg (field (r w) (r L) index) (List.getElem_map r)) hFront
  exact StructuralListFieldSyntax.output_subst (r w) (r L) index (r xs[p]) v
    (of_eq (congrArg (fun x => Formula.equal (r x) v) same) hvEq) hNew

private theorem var_index {n : Nat} (i : Fin n) : (fo_bound_variable i).index = i.val :=
  ProjectNativeRenaming.variable_index (fun _ : Fin 1 => i) (fo_bound_variable 0)

private theorem context_length (n : Nat) : (fo_bound_context n).length = n :=
  List.length_replicate

private theorem static_field {n k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (σ : NativeSubstitutionSyntax.Mapping (fo_bound_context n) [] (fo_bound_context (k+7)))
    (j : Fin n) (dest : Fin (k+7)) (w L i value : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (numeral j.val i))
    (hσ : σ (fo_bound_variable j) = .fvar (fo_bound_variable dest))
    (hL : Derives Γ (TermImageQuotationSyntax.images (NativeSubstitutionImages.images (fo_bound_context n) σ) w L))
    (hv : Derives Γ (field w L i value)) :
    Derives Γ (PureQuotationSyntax.term (bound := []) (.fvar (fo_bound_variable dest)) w value) := by
  let j' := NativeSubstitutionImages.entryIndex σ (fo_bound_variable j)
  have hi' : Derives Γ (numeral j'.val i) := of_eq (by simp only [j', NativeSubstitutionImages.entryIndex, var_index]) hi
  have hf := Derives.impE (.conjL (TermImageQuotationFields.field_at hZ _ w L j' i value hw hL hi')) hv
  exact of_eq (by rw [NativeSubstitutionImages.get_image, hσ]) hf

private theorem quoted_image {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (part : Part) (bound : Bool) (j : Fin (width k part bound)) (w a f z g R S i t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (numeral j.val i))
    (he : Derives Γ (NativeSubstitutionSyntax.environment (boundMap k part) (freeMap k part) w a f z g R S))
    (hv : Derives Γ (field w (SyntaxIndexMapSyntax.selectMap bound R S) i t)) :
    Derives Γ (PureQuotationSyntax.term (bound := [])
      (.fvar (fo_bound_variable (destination k part bound j))) w t) := by
  cases bound with
  | false =>
    exact static_field hZ (freeMap k part) j (freeIndex k part j) w S i t hw hi
      (ForcingRelationSource.mapping_at _ j) (.conjR (.conjL he)) hv
  | true =>
    exact static_field hZ (boundMap k part) j (boundIndex k part j) w R i t hw hi
      (ForcingAtomicMonoTemplate.bound_map_at k part j) (.conjL (.conjL he)) hv

private theorem term_at_index {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (part : Part) (bound : Bool) (j : Fin (width k part bound))
    (w a f z g b R S B L D V x i t y o : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (numeral j.val i))
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (he : Derives Γ (NativeSubstitutionSyntax.environment (boundMap k part) (freeMap k part) w a f z g R S))
    (hm : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hd : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z b D V))
    (hr : Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (h1 : Derives Γ (substituted w R S a f z g x t))
    (h2 : Derives Γ (substituted w B L z g z b t y))
    (h3 : Derives Γ (substituted w D V a f z b x o)) : Derives Γ (.equal y o) := by
  have ht := Derives.conjR (Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ bound
    w R S a f z g x t i hw (.conjR he) hx)) h1)
  have ho := Derives.conjR (Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ bound
    w D V a f z b x o i hw hd hx)) h3)
  let dest := destination k part bound j
  have hquote := quoted_image hZ part bound j w a f z g R S i t hw hi he ht
  apply eliminate_objects hZ 1 (fun r xs => (Formula.mem (xs 0) (r w)).conj (numeral dest.val (xs 0)))
    (SyntaxNumerals.exists_numeral hZ dest.val w hw) (.equal y o)
  intro l Δ r xs hZ1 lift hp
  let p := xs 0
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hi1 := of_eq (numeral_rename j.val i r) (lift hi)
  have ht1 := of_eq (PureQuotationSyntax.term_rename (.fvar (fo_bound_variable dest)) w t r) (lift hquote)
  have hv := OriginalQuotationVariableFields.variable_of_tree hZ1 false dest.val (r w) p (r t) hw1 (.conjR hp)
    (of_eq (by simp only [PureQuotationSyntax.term, PureSyntaxQuotation.termTree, var_index]; rfl) ht1)
  have hy1 := Derives.conjR (Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false
    (r w) (r B) (r L) (r z) (r g) (r z) (r b) (r t) (r y) p hw1
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm)) hv))
    (of_eq (substituted_rename w B L z g z b t y r) (lift h2)))
  let list := SyntaxIndexMapSyntax.selectMap bound D V
  have ho1 := use_route j.val dest.val (r w) (r list) (r L) (r i) p (r o)
    (of_eq (route_rename j.val dest.val w list L r) (lift hr)) hi1 (.conjR hp)
    (of_eq (field_rename w list i o r) (lift ho))
  exact StructuralListFieldValues.unique hZ1 (r w) (r L) p (r y) (r o) hw1 (.conjL hp) hy1 ho1

private theorem compare_terms {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (part : Part) (w a f z g b R S B L D V x t y o : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral (depth part) a))
    (hf : Derives Γ (numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment (boundMap k part) (freeMap k part) w a f z g R S))
    (hm : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hd : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z b D V))
    (hr : ∀ bound (j : Fin (width k part bound)),
      Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (h1 : Derives Γ (substituted w R S a f z g x t))
    (h2 : Derives Γ (substituted w B L z g z b t y))
    (h3 : Derives Γ (substituted w D V a f z b x o)) : Derives Γ (.equal y o) := by
  apply OriginalTermScopeElimination.eliminate w a f x (.equal y o)
    (SyntaxCodedMixedTermTyping.source_type w R S a f z g x t h1)
  intro bound
  let limit := SyntaxTermSyntax.limit bound a f
  let E := SyntaxTermSyntax.branchWitness bound w limit x
  let Δ := Context.add E (Context.image Formula.raise Γ)
  let r : Fin m → Fin (m+1) := Fin.castSucc
  let i := Fin.last m
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hLimit : Derives Γ (numeral (width k part bound) limit) := by
    cases bound with
    | false => exact hf
    | true => exact ha
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w r) (under hw E)
  have hlim1 := of_eq (numeral_rename (width k part bound) limit r) (under hLimit E)
  have hBelow := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ1 _ (r limit) i hlim1)) (.conjL hE)
  apply Derives.impE _ hBelow
  apply SyntaxPositionSyntax.below_imp
  intro j
  apply Derives.impI
  let N := numeral j.val i
  have hroute := of_eq (route_rename j.val (destination k part bound j).val w
    (SyntaxIndexMapSyntax.selectMap bound D V) L r) (under (hr bound j) E)
  have hr1 : Derives Δ (route j.val (destination k part bound j).val (r w)
      (SyntaxIndexMapSyntax.selectMap bound (r D) (r V)) (r L)) :=
    of_eq (by cases bound <;> rfl) hroute
  exact term_at_index (ZFContext.add hZ1 N) part bound j (r w) (r a) (r f) (r z) (r g) (r b)
    (r R) (r S) (r B) (r L) (r D) (r V) (r x) i (r t) (r y) (r o)
    (add hw1 N) (.hyp (Or.inl rfl)) (add (.conjR hE) N)
    (add (of_eq (NativeSubstitutionSyntax.environment_rename (boundMap k part) (freeMap k part) w a f z g R S r)
      (under he E)) N)
    (add (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (under hm E)) N)
    (add (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z b D V r) (under hd E)) N)
    (add hr1 N)
    (add (of_eq (substituted_rename w R S a f z g x t r) (under h1 E)) N)
    (add (of_eq (substituted_rename w B L z g z b t y r) (under h2 E)) N)
    (add (of_eq (substituted_rename w D V a f z b x o r) (under h3 E)) N)

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem term_diagram {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (part : Part) (w a f z g b R S B L D V Ia If R0 S0 : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral (depth part) a))
    (hf : Derives Γ (numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment (boundMap k part) (freeMap k part) w a f z g R S))
    (hm : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hd : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z b D V))
    (hr : ∀ bound (j : Fin (width k part bound)),
      Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (hia : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a Ia))
    (hif : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f If))
    (hi : Derives Γ (IndexTermImageCodeSyntax.environment w Ia If R0 S0 a f a f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four a a z z) (four f f g b) (four R0 R B D) (four S0 S L V)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let r : Fin m → Fin (m+5) := old 5
  let as := four (r a) (r a) (r z) (r z)
  let fs := four (r f) (r f) (r g) (r b)
  let rs := four (r R0) (r R) (r B) (r D)
  let ss := four (r S0) (r S) (r L) (r V)
  let x : Fin (m+5) := slot 5 0
  let u : Fin (m+5) := slot 5 1
  let t : Fin (m+5) := slot 5 2
  let y : Fin (m+5) := slot 5 3
  let o : Fin (m+5) := slot 5 4
  let E := (ForcingTermDiagram.step (r w) as fs rs ss 0 x u).conj
    ((ForcingTermDiagram.step (r w) as fs rs ss 1 u t).conj
      ((ForcingTermDiagram.step (r w) as fs rs ss 2 t y).conj (ForcingTermDiagram.step (r w) as fs rs ss 3 x o)))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 5 hZ E
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename r) := HornBinderRules.under_body 5 h E
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have eq := ForcingBinderFormula.identity_term_output hZ1 (r w) (r a) (r f) (r Ia) (r If) (r R0) (r S0)
    x u hw1 (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a Ia r) (lift hia))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f If r) (lift hif))
    (of_eq (IndexTermImageCodeSyntax.environment_rename w Ia If R0 S0 a f a f r) (lift hi)) (.conjL hE)
  have hFirst := SyntaxMixedFormulaAtomicSubst.term_source (r w) (r R) (r S) (r a) (r f) (r z) (r g)
    u t x (eq_symm eq) (.conjL (.conjR hE))
  refine compare_terms hZ1 part (r w) (r a) (r f) (r z) (r g) (r b) (r R) (r S) (r B) (r L) (r D) (r V)
    x t y o hw1 (of_eq (numeral_rename (depth part) a r) (lift ha))
    (of_eq (numeral_rename (k+2) f r) (lift hf))
    (of_eq (NativeSubstitutionSyntax.environment_rename (boundMap k part) (freeMap k part) w a f z g R S r) (lift he))
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm))
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z b D V r) (lift hd))
    ?_ hFirst (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))
  intro bound j
  exact of_eq (by
    rw [route_rename]
    cases bound <;> rfl) (lift (hr bound j))

private theorem at_paths {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (part : Part) (w a f z g b R S B L D V N Q Y O : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral (depth part) a))
    (hf : Derives Γ (numeral (k+2) f))
    (he : Derives Γ (NativeSubstitutionSyntax.environment (boundMap k part) (freeMap k part) w a f z g R S))
    (hr : ∀ bound (j : Fin (width k part bound)),
      Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (h1 : Derives Γ (mixed w R S a f z g N Q))
    (h2 : Derives Γ (mixed w B L z g z b Q Y))
    (h3 : Derives Γ (mixed w D V a f z b N O)) : Derives Γ (.equal Y O) := by
  apply ForcingAtomicMono.with_identity_images hZ w a f hw
    (SyntaxNumerals.range hZ (depth part) w a hw ha) (SyntaxNumerals.range hZ (k+2) w f hw hf) (.equal Y O)
  intro l Δ r Ia If R0 S0 hZ1 lift hIa hIf hEnv
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hFirst := of_eq (mixed_rename w R S a f z g N Q r) (lift h1)
  have hSecond := of_eq (mixed_rename w B L z g z b Q Y r) (lift h2)
  have hDirect := of_eq (mixed_rename w D V a f z b N O r) (lift h3)
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ1 (r w) (r R) (r S) (r a) (r f)
    (r z) (r g) (r N) (r Q) hw1 hFirst
  have hRefl := SyntaxIdentityInduction.reflexive hZ1 (r w) Ia If (r a) (r f) (r N) hw1 hIa hIf ht
  have hId := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ1 (r w) Ia If R0 S0
    (r a) (r f) (r a) (r f) (r N) (r N) hw1 hEnv)) hRefl
  have hLists := Derives.conjL (SyntaxMixedFormulaJudgment.legal (r w) (r B) (r L) (r z) (r g) (r z) (r b)
    (r Q) (r Y) hSecond)
  have hDirectLists := Derives.conjL (SyntaxMixedFormulaJudgment.legal (r w) (r D) (r V) (r a) (r f) (r z) (r b)
    (r N) (r O) hDirect)
  have hRoutes bound (j : Fin (width k part bound)) : Derives Δ
      (route j.val (destination k part bound j).val (r w) (SyntaxIndexMapSyntax.selectMap bound (r D) (r V)) (r L)) :=
    of_eq (by rw [route_rename]; cases bound <;> rfl) (lift (hr bound j))
  have hDiagram := term_diagram hZ1 part (r w) (r a) (r f) (r z) (r g) (r b)
    (r R) (r S) (r B) (r L) (r D) (r V) Ia If R0 S0 hw1
    (of_eq (numeral_rename (depth part) a r) (lift ha)) (of_eq (numeral_rename (k+2) f r) (lift hf))
    (of_eq (NativeSubstitutionSyntax.environment_rename (boundMap k part) (freeMap k part) w a f z g R S r) (lift he))
    hLists hDirectLists hRoutes hIa hIf hEnv
  exact ForcingFormulaInduction.cancel hZ1 (r w) (four (r a) (r a) (r z) (r z))
    (four (r f) (r f) (r g) (r b)) (four R0 (r R) (r B) (r D)) (four S0 (r S) (r L) (r V))
    (r N) (r N) (r Q) (r Y) (r O) hw1 hDiagram hId hFirst hSecond hDirect

private theorem align_leaf {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (part : Part) (w a f z g b B L D V N Q Y O : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral (depth part) a))
    (hf : Derives Γ (numeral (k+2) f)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (numeral (k+7) g))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicMonoTemplate.leaf equality Reln part) w N))
    (hq : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicMonoTemplate.nativeLeaf equality Reln part) w Q))
    (hr : ∀ bound (j : Fin (width k part bound)),
      Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (h2 : Derives Γ (mixed w B L z g z b Q Y))
    (h3 : Derives Γ (mixed w D V a f z b N O)) : Derives Γ (.equal Y O) := by
  let σ : NativeSubstitutionSyntax.Mapping (fo_bound_context (depth part)) [] (fo_bound_context (k+7)) := boundMap k part
  let τ : NativeSubstitutionSyntax.Mapping (fo_bound_context (k+2)) [] (fo_bound_context (k+7)) := freeMap k part
  have hExists := NativeSubstitutionEnvironment.exists_environment hZ σ τ w a f z g hw
    (of_eq (congrArg (numeral · a) (context_length _).symm) ha)
    (of_eq (congrArg (numeral · f) (context_length _).symm) hf) hz
    (of_eq (congrArg (numeral · g) (context_length _).symm) hg)
  apply eliminate_objects hZ 2 (fun r xs =>
    NativeSubstitutionSyntax.environment σ τ (r w) (r a) (r f) (r z) (r g) (xs 0) (xs 1))
    hExists (.equal Y O)
  intro l Δ r xs hZ1 lift he
  let input := ForcingAtomicMonoTemplate.leaf equality Reln part
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have ha1 := of_eq (numeral_rename (depth part) a r) (lift ha)
  have hf1 := of_eq (numeral_rename (k+2) f r) (lift hf)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hg1 := of_eq (numeral_rename (k+7) g r) (lift hg)
  have hn1 := of_eq (PureQuotationSyntax.formula_rename input w N r) (lift hn)
  have hq1 := of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicMonoTemplate.nativeLeaf equality Reln part) w Q r) (lift hq)
  have hq' : Derives Δ (PureQuotationSyntax.formula (input.substituteMapped σ τ) (r w) (r Q)) :=
    of_eq (congrArg (fun F => PureQuotationSyntax.formula F (r w) (r Q))
      (ForcingAtomicMonoTemplate.leaf_transport equality Reln part).symm) hq1
  have hValue := NativeFormulaQuotationValue.at_candidate hZ1 input σ τ (r w) (xs 0) (xs 1)
    (r a) (r f) (r z) (r g) (r N) (r Q) hw1
    (of_eq (congrArg (numeral · (r a)) (context_length _).symm) ha1)
    (of_eq (congrArg (numeral · (r f)) (context_length _).symm) hf1) hz1
    (of_eq (congrArg (numeral · (r g)) (context_length _).symm) hg1) he hn1 hq'
  refine at_paths hZ1 part (r w) (r a) (r f) (r z) (r g) (r b) (xs 0) (xs 1) (r B) (r L)
    (r D) (r V) (r N) (r Q) (r Y) (r O) hw1 ha1 hf1 he ?_ (.conjL hValue)
    (of_eq (mixed_rename w B L z g z b Q Y r) (lift h2))
    (of_eq (mixed_rename w D V a f z b N O r) (lift h3))
  intro bound j
  exact of_eq (by rw [route_rename]; cases bound <;> rfl) (lift (hr bound j))

private theorem mixed_leaf {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (part : Part) (w a f z g b B L D V N Q O : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral (depth part) a))
    (hf : Derives Γ (numeral (k+2) f)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (numeral (k+7) g))
    (hm : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicMonoTemplate.leaf equality Reln part) w N))
    (hq : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicMonoTemplate.nativeLeaf equality Reln part) w Q))
    (hr : ∀ bound (j : Fin (width k part bound)),
      Derives Γ (route j.val (destination k part bound j).val w (SyntaxIndexMapSyntax.selectMap bound D V) L))
    (hDirect : Derives Γ (mixed w D V a f z b N O)) : Derives Γ (mixed w B L z g z b Q O) := by
  let F := ForcingAtomicMonoTemplate.nativeLeaf equality Reln part
  have hType := PureQuotationFormulaTyping.formula_type hZ F w z g Q hw hz
    (of_eq (congrArg (numeral · g) (context_length _).symm) hg) hq
  have hExists := SyntaxMixedFormulaOutputInduction.actual_exists hZ w B L z g z b Q hw (.conjI hType hm)
  apply eliminate_objects hZ 1 (fun r xs => mixed (r w) (r B) (r L) (r z) (r g) (r z) (r b) (r Q) (xs 0))
    hExists (mixed w B L z g z b Q O)
  intro l Δ r xs hZ1 lift hY
  have hEq := align_leaf hZ1 equality Reln part (r w) (r a) (r f) (r z) (r g) (r b) (r B) (r L)
    (r D) (r V) (r N) (r Q) (xs 0) (r O) (of_eq (omega_rename w r) (lift hw))
    (of_eq (numeral_rename (depth part) a r) (lift ha)) (of_eq (numeral_rename (k+2) f r) (lift hf))
    (of_eq (empty_rename z r) (lift hz)) (of_eq (numeral_rename (k+7) g r) (lift hg))
    (of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicMonoTemplate.leaf equality Reln part) w N r) (lift hn))
    (of_eq (PureQuotationSyntax.formula_rename F w Q r) (lift hq))
    (fun bound j => of_eq (by rw [route_rename]; cases bound <;> rfl) (lift (hr bound j)))
    hY (of_eq (mixed_rename w D V a f z b N O r) (lift hDirect))
  exact of_eq (mixed_rename w B L z g z b Q O r).symm
    (SyntaxMixedFormulaJudgmentSubst.subst_q (r w) (r B) (r L) (r z) (r g) (r z) (r b) (r Q)
      (xs 0) (r O) hEq hY)

private theorem with_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z g b B L X Y N P Q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w B L z g z b N))
    (hN : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w X Y N))
    (hP : Derives Γ (mixed w B L z g z b X P)) (hQ : Derives Γ (mixed w B L z g z b Y Q))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (F : Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      Derives Δ (SyntaxLogicalSyntax.binaryCode 2 (r w) (r P) (r Q) F) →
      Derives Δ (mixed (r w) (r B) (r L) (r z) (r g) (r z) (r b) (r N) F) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have pN := SyntaxMixedFormulaOutput.output_natural w B L z g z b X P hP
  have qN := SyntaxMixedFormulaOutput.output_natural w B L z g z b Y Q hQ
  have he := SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two P Q) hw
    (.conjI pN (.conjI qN (.eqRefl w)))
  apply eliminate_objects hZ 1 (fun r xs => (Formula.mem (xs 0) (r w)).conj
    (SyntaxLogicalSyntax.binaryCode 2 (r w) (r P) (r Q) (xs 0))) he out
  intro l Δ r xs hZ1 lift hCode
  have iff := SyntaxMixedFormulaEndpoints.binary_iff hZ1 2 (r w) (r B) (r L) (r z) (r g) (r z) (r b)
    (r N) (xs 0) (r X) (r Y) (r P) (r Q) (of_eq (omega_rename w r) (lift hw))
    (of_eq (SyntaxMixedFormulaOutputSyntax.input_rename w B L z g z b N r) (lift hi))
    (of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 w X Y N r) (lift hN)) (.conjR hCode)
  exact use r (xs 0) hZ1 lift (.conjR hCode) (.impE (.conjR iff) (.conjI
    (of_eq (mixed_rename w B L z g z b X P r) (lift hP))
    (of_eq (mixed_rename w B L z g z b Y Q r) (lift hQ))))

theorem with_chain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z g b B L last : Fin m) (n : Nat) (source heads : Fin n → Fin m) (tails : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w))
    (hi : ∀ i : Fin n, Derives Γ (SyntaxMixedFormulaOutputSyntax.input w B L z g z b (tails i.castSucc)))
    (hc : ∀ i : Fin n, Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (source i) (tails i.succ) (tails i.castSucc)))
    (hh : ∀ i : Fin n, Derives Γ (mixed w B L z g z b (source i) (heads i)))
    (he : Derives Γ (mixed w B L z g z b (tails (Fin.last n)) last)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (values : Fin (n+1) → Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      values (Fin.last n) = r last →
      (∀ i : Fin n, Derives Δ (SyntaxLogicalSyntax.binaryCode 2 (r w) (r (heads i)) (values i.succ) (values i.castSucc))) →
      Derives Δ (mixed (r w) (r B) (r L) (r z) (r g) (r z) (r b) (r (tails 0)) (values 0)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  induction n generalizing m with
  | zero =>
    exact of_eq (Reverse.source_rename_id out) (use id (fun _ => last) hZ
      (fun h => of_eq (Reverse.source_rename_id _).symm h) rfl (fun i => Fin.elim0 i) he)
  | succ n ih =>
    apply ih hZ w z g b B L last (fun i => source i.succ) (fun i => heads i.succ) (fun i => tails i.succ)
      hw (fun i => hi i.succ) (fun i => hc i.succ) (fun i => hh i.succ) he out
    intro l Δ r vs hZ1 lift hLast hCtor hTail
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hIn := of_eq (SyntaxMixedFormulaOutputSyntax.input_rename w B L z g z b (tails 0) r) (lift (hi 0))
    have hNode := of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 w (source 0) (tails (0 : Fin (n+1)).succ)
      (tails 0) r) (lift (hc 0))
    have hHead := of_eq (mixed_rename w B L z g z b (source 0) (heads 0) r) (lift (hh 0))
    apply with_implication hZ1 (r w) (r z) (r g) (r b) (r B) (r L) (r (source 0))
      (r (tails (0 : Fin (n+1)).succ)) (r (tails 0)) (r (heads 0)) (vs 0) hw1 hIn hNode hHead hTail (out.rename r)
    intro l' Δ' s F hZ2 move hF hMix
    let ρ := fun j => s (r j)
    let values : Fin (n+1+1) → Fin l' := Fin.cases F (fun i => s (vs i))
    have carry {φ : Formula m} (h : Derives Γ φ) : Derives Δ' (φ.rename ρ) :=
      of_eq (rename_comp φ r s) (move (lift h))
    have hLast' : values (Fin.last (n+1)) = ρ last := congrArg s hLast
    have hNodes (i : Fin (n+1)) :
        Derives Δ' (SyntaxLogicalSyntax.binaryCode 2 (ρ w) (ρ (heads i)) (values i.succ) (values i.castSucc)) := by
      refine Fin.cases hF (fun j => ?_) i
      exact of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 (r w) (r (heads j.succ)) (vs j.succ) (vs j.castSucc) s)
        (move (hCtor j))
    exact of_eq (rename_comp out r s).symm (use ρ values hZ2 carry hLast' hNodes hMix)

private def leafSlot (i : Fin 5) : Fin 9 := i.castAdd 4

private def tailSlot : Fin 5 → Fin 9 :=
  Fin.lastCases (leafSlot 4) (fun i : Fin 4 => i.natAdd 5)

private def masterTrees {k} (equality : Bool) (Reln : Formula (k+2)) :
    Fin 9 → YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree := fun i =>
  Fin.addCases (motive := fun _ : Fin (5+4) => YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)
    (fun i : Fin 5 => PureSyntaxQuotation.formulaTree
      (ForcingAtomicMonoTemplate.nativeLeaf equality Reln (ForcingAtomicMonoTemplate.partAt i)))
    (fun i : Fin 4 => PureSyntaxQuotation.formulaTree (ForcingAtomicMonoTemplate.tail equality Reln i.castSucc)) i

private theorem master_leaf {k} (equality : Bool) (Reln : Formula (k+2)) (i : Fin 5) :
    masterTrees equality Reln (leafSlot i) =
      PureSyntaxQuotation.formulaTree (ForcingAtomicMonoTemplate.nativeLeaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) :=
  by rw [masterTrees, leafSlot, Fin.addCases_left]

private theorem master_tail {k} (equality : Bool) (Reln : Formula (k+2)) (i : Fin 5) :
    masterTrees equality Reln (tailSlot i) = PureSyntaxQuotation.formulaTree (ForcingAtomicMonoTemplate.tail equality Reln i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [tailSlot, Fin.lastCases_last, master_leaf]
    rfl
  · rw [tailSlot, Fin.lastCases_castSucc, masterTrees, Fin.addCases_right]

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

attribute [local irreducible] SyntaxMixedFormulaJudgmentSyntax.substituted
  InternalProofBackground.implication ForcingProofContext.layoutData

private theorem at_shared_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w z f g b B L Extra Pre Fp Fq : Fin m)
    (H layout : Fin 6 → Fin m) (a D V N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (numeral (k+2) f)) (hg : Derives Γ (numeral (k+7) g))
    (hm : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w z g z b B L))
    (ha : ∀ i, Derives Γ (numeral (depth (ForcingAtomicMonoTemplate.partAt i)) (a i)))
    (hn : ∀ i, Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (N i)))
    (hr : ∀ i bound (j : Fin (width k (ForcingAtomicMonoTemplate.partAt i) bound)),
      Derives Γ (route j.val (destination k (ForcingAtomicMonoTemplate.partAt i) bound j).val
        w (SyntaxIndexMapSyntax.selectMap bound (D i) (V i)) L))
    (hd : ∀ i, Derives Γ (mixed w (D i) (V i) (a i) f z b (N i)
      (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)))
    (hExtra : Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hFp : Derives Γ (implication test w z b (layout 3) Fp)) :
    Derives Γ (implication test w z b (layout 3) Fq) := by
  let out := implication test w z b (layout 3) Fq
  apply ProjectCompilerQuotation.eliminate_quotations hZ 9 (masterTrees equality Reln) w hw out
  intro l Δ r qs hZ1 lift hQuotes
  let head := ForcingAtomicMono.heads Pre Fp H
  let hCode := fun i => qs (leafSlot i)
  let tCode := fun i => qs (tailSlot i)
  let PartAt := ForcingAtomicMonoTemplate.partAt
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (numeral_rename (k+2) f r) (lift hf)
  have hg1 := of_eq (numeral_rename (k+7) g r) (lift hg)
  have hm1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w z g z b B L r) (lift hm)
  have hLeaf (i : Fin 5) : Derives Δ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.nativeLeaf equality Reln (PartAt i)) (r w) (hCode i)) :=
    of_eq (congrArg (fun t => OriginalTreeQuotationSyntax.tree t (r w) (hCode i)) (master_leaf equality Reln i))
      (hQuotes (leafSlot i))
  have hTail (i : Fin 5) : Derives Δ
      (PureQuotationSyntax.formula (ForcingAtomicMonoTemplate.tail equality Reln i) (r w) (tCode i)) :=
    of_eq (congrArg (fun t => OriginalTreeQuotationSyntax.tree t (r w) (tCode i)) (master_tail equality Reln i))
      (hQuotes (tailSlot i))
  have hRuns (i : Fin 5) : Derives Δ (mixed (r w) (r B) (r L) (r z) (r g) (r z) (r b) (hCode i)
      (r (Fin.lastCases Fq head i))) :=
    mixed_leaf hZ1 equality Reln (PartAt i) (r w) (r (a i)) (r f) (r z) (r g) (r b) (r B) (r L)
      (r (D i)) (r (V i)) (r (N i)) (hCode i) (r (Fin.lastCases Fq head i)) hw1
      (of_eq (numeral_rename (depth (PartAt i)) (a i) r) (lift (ha i))) hf1 hz1 hg1 hm1
      (of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicMonoTemplate.leaf equality Reln (PartAt i)) w (N i) r)
        (lift (hn i))) (hLeaf i)
      (fun bound j => of_eq (by rw [route_rename]; cases bound <;> rfl) (lift (hr i bound j)))
      (of_eq (mixed_rename w (D i) (V i) (a i) f z b (N i) (Fin.lastCases Fq head i) r) (lift (hd i)))
  have hCtor (i : Fin 4) : Derives Δ (SyntaxLogicalSyntax.binaryCode 2 (r w) (hCode i.castSucc)
      (tCode i.succ) (tCode i.castSucc)) := by
    let X := ForcingAtomicMonoTemplate.nativeLeaf equality Reln (PartAt i.castSucc)
    let Y := ForcingAtomicMonoTemplate.tail equality Reln i.succ
    have hNode : Derives Δ (PureQuotationSyntax.formula (.imp X Y) (r w) (tCode i.castSucc)) :=
      of_eq (congrArg (fun p => PureQuotationSyntax.formula p (r w) (tCode i.castSucc))
        (ForcingAtomicMonoTemplate.tail_imp equality Reln i)) (hTail i.castSucc)
    exact OriginalQuotationNodeFields.tree_to_constructor hZ1 7
      [PureSyntaxQuotation.formulaTree X, PureSyntaxQuotation.formulaTree Y]
      (r w) (tCode i.castSucc) (SyntaxAtomSyntax.two (hCode i.castSucc) (tCode i.succ)) hw1
      (.conjI (hLeaf i.castSucc) (.conjI (hTail i.succ) (.eqRefl (r w)))) hNode
  have hInput (i : Fin 4) : Derives Δ (SyntaxMixedFormulaOutputSyntax.input (r w) (r B) (r L)
      (r z) (r g) (r z) (r b) (tCode i.castSucc)) :=
    .conjI (PureQuotationFormulaTyping.formula_type hZ1 (ForcingAtomicMonoTemplate.tail equality Reln i.castSucc)
      (r w) (r z) (r g) (tCode i.castSucc) hw1 hz1
      (of_eq (congrArg (numeral · (r g)) (context_length _).symm) hg1) (hTail i.castSucc)) hm1
  let out1 := implication test (r w) (r z) (r b) (r (layout 3)) (r Fq)
  apply of_eq (implication_rename test w z b (layout 3) Fq r).symm
  apply with_chain hZ1 (r w) (r z) (r g) (r b) (r B) (r L) (r Fq) 4
    (fun i => hCode i.castSucc) (fun i => r (head i)) tCode hw1 hInput hCtor
    (fun i => by simpa only [Fin.lastCases_castSucc] using hRuns i.castSucc)
    (by
      have hEnd : hCode (Fin.last 4) = tCode (Fin.last 4) := by
        change qs (leafSlot (Fin.last 4)) = qs (tailSlot (Fin.last 4))
        rw [tailSlot, Fin.lastCases_last]
        exact congrArg (fun i => qs (leafSlot i)) (Fin.ext rfl)
      exact of_eq (congrArg (fun N => mixed (r w) (r B) (r L) (r z) (r g) (r z) (r b) N (r Fq)) hEnd)
        (by simpa only [Fin.lastCases_last] using hRuns (Fin.last 4))) out1
  intro l' Δ' s values hZ2 move hLast hNodes hMix
  let ρ := fun i => s (r i)
  have carry {φ : Formula m} (hp : Derives Γ φ) : Derives Δ' (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (move (lift hp))
  have hN := of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicMonoTemplate.formula equality Reln)
    (r w) (tCode 0) s) (move (hTail 0))
  have result := ForcingAtomicMono.at_instance hZ2 (ForcingAtomicMonoTemplate.open_proof equality Reln)
    (ρ w) (ρ z) (ρ g) (ρ b) (ρ B) (ρ L) (s (tCode 0)) (ρ Extra) (ρ Pre) (ρ Fp)
    (fun i => ρ (H i)) (fun i => ρ (layout i)) values
    (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
    (of_eq ((numeral_rename (k+7) g ρ).trans
      (congrArg (numeral · (ρ g)) (context_length (k+7)).symm)) (carry hg))
    hN hMix (fun i => of_eq (by refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i) (hNodes i))
    (of_eq (FormulaCodeSyntax.formulaCode_rename w Extra z b ρ) (carry hExtra))
    (of_eq (ForcingProofContext.layoutData_rename w z b Extra Pre H layout ρ) (carry hLayout))
    (of_eq (implication_rename test w z b (layout 3) Fp ρ) (carry hFp))
  exact of_eq (implication_rename test (r w) (r z) (r b) (r (layout 3)) (r Fq) s).symm
    (of_eq (congrArg (implication test (ρ w) (ρ z) (ρ b) (ρ (layout 3))) hLast) result)

private def five {α : Type} (a b c d e : α) : Fin 5 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))

private theorem with_canonical_table {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq : Fin m)
    (H : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hJ : Derives Γ (numeral (k+1) J))
    (hA : Derives Γ (numeral 3 A3)) (ht0 : Derives Γ (numeral 2 t0)) (ht1 : Derives Γ (numeral 2 t1))
    (hTerms : ∀ v, v ∈ [y,x,q,c,p] → Derives Γ (SyntaxTermSyntax.term w z b v))
    (hD3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3))
    (hD0 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D0))
    (hD1 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D1))
    (hS0 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hPre : Derives Γ (mixed w B S z f z b (N 0) Pre))
    (hMem : Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Derives Γ (mixed w D0 S0 t0 f z b (N 3) Fp))
    (hNew : Derives Γ (mixed w D1 S1 t1 f z b (N 4) Fq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (g L : Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      Derives Δ (numeral (k+7) g) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termLists (r w) (r z) g (r z) (r b) (r B) L) →
      ∀ a D V : Fin 5 → Fin l,
        (∀ i, Derives Δ (numeral (depth (ForcingAtomicMonoTemplate.partAt i)) (a i))) →
        (∀ i, Derives Δ (mixed (r w) (D i) (V i) (a i) (r f) (r z) (r b)
          (r (N i)) (r (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)))) →
        (∀ i bound (j : Fin (width k (ForcingAtomicMonoTemplate.partAt i) bound)),
          Derives Δ (route j.val (destination k (ForcingAtomicMonoTemplate.partAt i) bound j).val
            (r w) (SyntaxIndexMapSyntax.selectMap bound (D i) (V i)) L)) →
        (∀ i : Fin (k+2), Derives Δ (route i.val (freeIndex k .newer i).val (r w) (r S1) L)) →
        (∀ i : Fin 2, Derives Δ (route i.val (boundIndex k .newer i).val (r w) (r D1) L)) →
        Derives Δ (out.rename r)) : Derives Γ out := by
  let a := five z A3 A3 t0 t1
  let D := five B D3 D3 D0 D1
  let V := five S S S S0 S1
  have ha : ∀ i, Derives Γ (numeral (depth (ForcingAtomicMonoTemplate.partAt i)) (a i)) :=
    fun i => Fin.cases hz (Fin.cases hA (Fin.cases hA (Fin.cases ht0 (fun _ => ht1)))) i
  have hd : ∀ i, Derives Γ (mixed w (D i) (V i) (a i) f z b (N i)
      (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)) :=
    fun i => Fin.cases hPre (Fin.cases hMem (Fin.cases hOrd (Fin.cases hOld
      (Fin.cases hNew (fun j => Fin.elim0 j))))) i
  have hBase := Derives.conjL (SyntaxMixedFormulaJudgment.legal w B S z f z b (N 0) Pre hPre)
  have hBound : Derives Γ (termList w z z b B) := .conjL hBase
  apply with_prefix hZ w z b f S [y,x,q,c,p] hw (.conjR hBase) hTerms out
  intro l Δ r g L hZ1 lift pref
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hf1 := of_eq (numeral_rename (k+2) f r) (lift hf)
  have hg1 : Derives Δ (numeral (k+7) g) := pref.length_numeral hf1
  have hm1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists (r w) (r z) g (r z) (r b) (r B) L) :=
    .conjI (of_eq (termList_rename w z z b B r) (lift hBound)) pref.typed
  have hJ1 := of_eq (numeral_rename (k+1) J r) (lift hJ)
  have hpS := of_eq (ForcingReflexiveImages.replacement_rename w f z b S J p S0 r) (lift hS0)
  have hqS := of_eq (ForcingReflexiveImages.replacement_rename w f z b S J q S1 r) (lift hS1)
  have hG3 := of_eq (SyntaxForestSyntax.forest_rename 3 w (SetLanguage.args3 p q c) D3 r) (lift hD3)
  have hG0 := of_eq (SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) D0 r) (lift hD0)
  have hG1 := of_eq (SyntaxForestSyntax.forest_rename 2 w (SetLanguage.args2 y x) D1 r) (lift hD1)
  have baseRoute (i : Fin (k+2)) :
      Derives Δ (route i.val (ForcingAtomicMonoTemplate.base i).val (r w) (r S) L) :=
    route_tail hZ1 hw1 pref i.val
  have guardRoute (i : Fin 3) : Derives Δ
      (route i.val (boundIndex k .member i).val (r w) (r D3) L) := by
    have result := route_forest hZ1 hw1 pref i (Fin.cases (4 : Fin 5) (Fin.cases (2 : Fin 5) (fun _ => (3 : Fin 5))) i) (r D3)
      (fun j => r (SetLanguage.args3 p q c j))
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i) hG3
    exact of_eq (by refine Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i) result
  have oldBound (i : Fin 2) : Derives Δ (route i.val (boundIndex k .older i).val (r w) (r D0) L) := by
    have result := route_forest hZ1 hw1 pref i (Fin.cases (0 : Fin 5) (fun _ => (1 : Fin 5)) i) (r D0)
      (fun j => r (SetLanguage.args2 y x j)) (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i) hG0
    exact of_eq (by refine Fin.cases rfl (fun _ => rfl) i) result
  have newBound (i : Fin 2) : Derives Δ (route i.val (boundIndex k .newer i).val (r w) (r D1) L) := by
    have result := route_forest hZ1 hw1 pref i (Fin.cases (0 : Fin 5) (fun _ => (1 : Fin 5)) i) (r D1)
      (fun j => r (SetLanguage.args2 y x j)) (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i) hG1
    exact of_eq (by refine Fin.cases rfl (fun _ => rfl) i) result
  have oldFree (i : Fin (k+2)) : Derives Δ (route i.val (freeIndex k .older i).val (r w) (r S0) L) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact of_eq (by simp only [freeIndex, Fin.lastCases_last]; rfl)
        (route_overwrite_head hZ1 hw1 pref (4 : Fin 5) (r J) (r S0) hf1 hJ1 hpS)
    · exact of_eq (by simp only [freeIndex, Fin.lastCases_castSucc]; rfl)
        (route_overwrite_tail hZ1 hw1 pref j.castSucc (Nat.ne_of_lt j.isLt) (r J) (r p) (r S0) hf1 hJ1 hpS)
  have newFree (i : Fin (k+2)) : Derives Δ (route i.val (freeIndex k .newer i).val (r w) (r S1) L) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact of_eq (by simp only [freeIndex, Fin.lastCases_last]; rfl)
        (route_overwrite_head hZ1 hw1 pref (2 : Fin 5) (r J) (r S1) hf1 hJ1 hqS)
    · exact of_eq (by simp only [freeIndex, Fin.lastCases_castSucc]; rfl)
        (route_overwrite_tail hZ1 hw1 pref j.castSucc (Nat.ne_of_lt j.isLt) (r J) (r q) (r S1) hf1 hJ1 hqS)
  have hr (i : Fin 5) (bound : Bool) (j : Fin (width k (ForcingAtomicMonoTemplate.partAt i) bound)) :
      Derives Δ (route j.val (destination k (ForcingAtomicMonoTemplate.partAt i) bound j).val (r w)
        (SyntaxIndexMapSyntax.selectMap bound (r (D i)) (r (V i))) L) := by
    revert bound j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)))) i
    · intro bound
      cases bound
      · exact baseRoute
      · intro j; exact Fin.elim0 j
    · intro bound; cases bound; exact baseRoute; exact guardRoute
    · intro bound; cases bound; exact baseRoute; exact guardRoute
    · intro bound; cases bound; exact oldFree; exact oldBound
    · intro bound; cases bound; exact newFree; exact newBound
  exact use r g L hZ1 lift hg1 hm1 (fun i => r (a i)) (fun i => r (D i)) (fun i => r (V i))
    (fun i => of_eq (numeral_rename _ (a i) r) (lift (ha i)))
    (fun i => of_eq (mixed_rename w (D i) (V i) (a i) f z b (N i)
      (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i) r) (lift (hd i))) hr newFree newBound

/-- Align the raw queries and retain the routes for both arguments of the new atom. -/
theorem with_aligned_query_routes {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq : Fin m)
    (H : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hJ : Derives Γ (numeral (k+1) J))
    (hA : Derives Γ (numeral 3 A3)) (ht0 : Derives Γ (numeral 2 t0)) (ht1 : Derives Γ (numeral 2 t1))
    (hTerms : ∀ v, v ∈ [y,x,q,c,p] → Derives Γ (SyntaxTermSyntax.term w z b v))
    (hD3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3))
    (hD0 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D0))
    (hD1 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D1))
    (hS0 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hQuotes : ∀ i, Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (N i)))
    (hPre : Derives Γ (mixed w B S z f z b (N 0) Pre))
    (hMem : Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Derives Γ (mixed w D0 S0 t0 f z b (N 3) Fp))
    (hNew : Derives Γ (mixed w D1 S1 t1 f z b (N 4) Fq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (g L : Fin l) (Q : Fin 5 → Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      Derives Δ (numeral (k+7) g) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termLists (r w) (r z) g (r z) (r b) (r B) L) →
      (∀ i, Derives Δ (PureQuotationSyntax.formula
        (ForcingAtomicMonoTemplate.nativeLeaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) (r w) (Q i))) →
      (∀ i, Derives Δ (mixed (r w) (r B) L (r z) g (r z) (r b) (Q i)
        (r (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)))) →
      (∀ i : Fin (k+2), Derives Δ (route i.val (freeIndex k .newer i).val (r w) (r S1) L)) →
      (∀ i : Fin 2, Derives Δ (route i.val (boundIndex k .newer i).val (r w) (r D1) L)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  apply with_canonical_table (k := k) hZ w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq H N
    hw hz hf hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hPre hMem hOrd hOld hNew out
  intro l Δ r g L hZ1 lift hg hm a D V ha hd hr hNewRoute hNewBound
  let parts := ForcingAtomicMonoTemplate.partAt
  let forms := fun i => ForcingAtomicMonoTemplate.nativeLeaf equality Reln (parts i)
  let trees := fun i => PureSyntaxQuotation.formulaTree (forms i)
  have hw1 := of_eq (omega_rename w r) (lift hw)
  apply ProjectCompilerQuotation.eliminate_quotations hZ1 5 trees (r w) hw1 (out.rename r)
  intro l2 Δ2 s Q hZ2 move hTrees
  let ρ := fun i => s (r i)
  have carry {φ : Formula m} (hp : Derives Γ φ) : Derives Δ2 (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hf2 := of_eq (numeral_rename (k+2) f ρ) (carry hf)
  have hg2 := of_eq (numeral_rename (k+7) g s) (move hg)
  have hm2 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename (r w) (r z) g (r z) (r b) (r B) L s) (move hm)
  have hQuote (i : Fin 5) : Derives Δ2 (PureQuotationSyntax.formula (forms i) (ρ w) (Q i)) := hTrees i
  have hRun (i : Fin 5) : Derives Δ2 (mixed (ρ w) (ρ B) (s L) (ρ z) (s g) (ρ z) (ρ b) (Q i)
      (ρ (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i))) :=
    mixed_leaf hZ2 equality Reln (parts i) (ρ w) (s (a i)) (ρ f) (ρ z) (s g) (ρ b) (ρ B) (s L)
      (s (D i)) (s (V i)) (ρ (N i)) (Q i) (ρ (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i))
      hw2 (of_eq (numeral_rename _ (a i) s) (move (ha i))) hf2 hz2 hg2 hm2
      (of_eq (PureQuotationSyntax.formula_rename _ w (N i) ρ) (carry (hQuotes i))) (hQuote i)
      (fun bound j => of_eq (by rw [route_rename]; cases bound <;> rfl) (move (hr i bound j)))
      (of_eq (mixed_rename (r w) (D i) (V i) (a i) (r f) (r z) (r b) (r (N i))
        (r (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)) s) (move (hd i)))
  have hFields (i : Fin (k+2)) : Derives Δ2 (route i.val (freeIndex k .newer i).val (ρ w) (ρ S1) (s L)) :=
    of_eq (route_rename i.val (freeIndex k .newer i).val (r w) (r S1) L s) (move (hNewRoute i))
  have hNames (i : Fin 2) : Derives Δ2 (route i.val (boundIndex k .newer i).val (ρ w) (ρ D1) (s L)) :=
    of_eq (route_rename i.val (boundIndex k .newer i).val (r w) (r D1) L s) (move (hNewBound i))
  exact of_eq (rename_comp out r s).symm (use ρ (s g) (s L) Q hZ2 carry hg2 hm2 hQuote hRun hFields hNames)

/-- Put the actual raw atomic and preorder queries on one common image list. -/
theorem with_aligned_queries {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq : Fin m)
    (H : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hJ : Derives Γ (numeral (k+1) J))
    (hA : Derives Γ (numeral 3 A3)) (ht0 : Derives Γ (numeral 2 t0)) (ht1 : Derives Γ (numeral 2 t1))
    (hTerms : ∀ v, v ∈ [y,x,q,c,p] → Derives Γ (SyntaxTermSyntax.term w z b v))
    (hD3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3))
    (hD0 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D0))
    (hD1 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D1))
    (hS0 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hQuotes : ∀ i, Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (N i)))
    (hPre : Derives Γ (mixed w B S z f z b (N 0) Pre))
    (hMem : Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Derives Γ (mixed w D0 S0 t0 f z b (N 3) Fp))
    (hNew : Derives Γ (mixed w D1 S1 t1 f z b (N 4) Fq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (g L : Fin l) (Q : Fin 5 → Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename r)) →
      Derives Δ (numeral (k+7) g) →
      Derives Δ (SyntaxMixedImageCodeSyntax.termLists (r w) (r z) g (r z) (r b) (r B) L) →
      (∀ i, Derives Δ (PureQuotationSyntax.formula
        (ForcingAtomicMonoTemplate.nativeLeaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) (r w) (Q i))) →
      (∀ i, Derives Δ (mixed (r w) (r B) L (r z) g (r z) (r b) (Q i)
        (r (Fin.lastCases Fq (ForcingAtomicMono.heads Pre Fp H) i)))) →
      (∀ i : Fin (k+2), Derives Δ (route i.val (freeIndex k .newer i).val (r w) (r S1) L)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  apply with_aligned_query_routes hZ equality Reln w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq H N
    hw hz hf hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes hPre hMem hOrd hOld hNew out
  intro l Δ r g L Q hZ1 lift hg hm hQuote hRun hFields _
  exact use r g L Q hZ1 lift hg hm hQuote hRun hFields

/-- Use one actual base list for Pre and both guard leaves, and the original
two condition overwrites for the two compiled atom queries. -/
theorem at_canonical_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Extra Pre Fp Fq : Fin m)
    (H layout : Fin 6 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hJ : Derives Γ (numeral (k+1) J))
    (hA : Derives Γ (numeral 3 A3)) (ht0 : Derives Γ (numeral 2 t0)) (ht1 : Derives Γ (numeral 2 t1))
    (hTerms : ∀ v, v ∈ [y,x,q,c,p] → Derives Γ (SyntaxTermSyntax.term w z b v))
    (hD3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3))
    (hD0 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D0))
    (hD1 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D1))
    (hS0 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hQuotes : ∀ i, Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (N i)))
    (hPre : Derives Γ (mixed w B S z f z b (N 0) Pre))
    (hMem : Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Derives Γ (mixed w D0 S0 t0 f z b (N 3) Fp))
    (hNew : Derives Γ (mixed w D1 S1 t1 f z b (N 4) Fq))
    (hExtra : Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hFp : Derives Γ (implication test w z b (layout 3) Fp)) :
    Derives Γ (implication test w z b (layout 3) Fq) := by
  let out := implication test w z b (layout 3) Fq
  apply with_canonical_table (k := k) hZ w z f J b B S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Pre Fp Fq H N
    hw hz hf hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hPre hMem hOrd hOld hNew out
  intro l Δ r g L hZ1 lift hg hm a D V ha hd hr _ _
  exact of_eq (implication_rename test w z b (layout 3) Fq r).symm
    (at_shared_instance hZ1 equality Reln (r w) (r z) (r f) g (r b) (r B) L (r Extra) (r Pre) (r Fp) (r Fq)
      (fun i => r (H i)) (fun i => r (layout i)) a D V (fun i => r (N i))
      (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
      (of_eq (numeral_rename (k+2) f r) (lift hf)) hg hm ha
      (fun i => of_eq (PureQuotationSyntax.formula_rename _ w (N i) r) (lift (hQuotes i))) hr
      (fun i => of_eq (by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rfl
        · simp only [Fin.lastCases_castSucc]
          refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) j) (hd i))
      (of_eq (FormulaCodeSyntax.formulaCode_rename w Extra z b r) (lift hExtra))
      (of_eq (ForcingProofContext.layoutData_rename w z b Extra Pre H layout r) (lift hLayout))
      (of_eq (implication_rename test w z b (layout 3) Fp r) (lift hFp)))


theorem pair_forest_subst {m} {Γ : Context m} (w D x0 y0 x1 y1 : Fin m)
    (hx : Derives Γ (.equal x1 x0)) (hy : Derives Γ (.equal y1 y0))
    (h : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y1 x1) D)) :
    Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y0 x0) D) := by
  let P := SyntaxForestSyntax.forest 2 w.castSucc (SetLanguage.args2 y1.castSucc (Fin.last m)) D.castSucc
  let Q := SyntaxForestSyntax.forest 2 w.castSucc (SetLanguage.args2 (Fin.last m) x0.castSucc) D.castSucc
  have hX : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y1 x0) D) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxForestSyntax.forest_rename,
      ProofTreeEntryFacts.args2_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P hx (of_eq (by simp only [P, Formula.instantiate, SyntaxForestSyntax.forest_rename,
        ProofTreeEntryFacts.args2_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  exact of_eq (by simp only [Q, Formula.instantiate, SyntaxForestSyntax.forest_rename,
    ProofTreeEntryFacts.args2_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst Q hy (of_eq (by simp only [Q, Formula.instantiate, SyntaxForestSyntax.forest_rename,
      ProofTreeEntryFacts.args2_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hX))

abbrev CanonicalFieldsConsumer {k m} (Γ : Context m) (equality : Bool) (Reln : Formula (k+2))
    (w z b B Fp Fq : Fin m) (layout : Fin 6 → Fin m) (out : Formula m) : Prop :=
  ∀ (f J S A3 D3 t0 t1 D0 D1 S0 S1 x y p q c Extra Pre : Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m),
    Derives Γ (omega w) → Derives Γ (empty z) →
    Derives Γ (numeral (k+2) f) → Derives Γ (numeral (k+1) J) →
    Derives Γ (numeral 3 A3) → Derives Γ (numeral 2 t0) → Derives Γ (numeral 2 t1) →
    (∀ v, v ∈ [y,x,q,c,p] → Derives Γ (SyntaxTermSyntax.term w z b v)) →
    Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3) →
    Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D0) →
    Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 y x) D1) →
    Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0) →
    Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1) →
    (∀ i, Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (N i))) →
    Derives Γ (mixed w B S z f z b (N 0) Pre) →
    Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)) →
    Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)) →
    Derives Γ (mixed w D0 S0 t0 f z b (N 3) Fp) →
    Derives Γ (mixed w D1 S1 t1 f z b (N 4) Fq) →
    Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b) →
    Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout) →
    Derives Γ out

private theorem with_direct_pair_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z a f J b B S A3 D3 D S0 S1 X Y p q c Extra Pre Fp Fq : Fin m)
    (H layout : Fin 6 → Fin m) (N : Fin 3 → Fin m) (v0 v1 : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hJ : Derives Γ (numeral (k+1) J)) (hA : Derives Γ (numeral 3 A3))
    (hX : Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hp : Derives Γ (SyntaxTermSyntax.term w z b p)) (hq : Derives Γ (SyntaxTermSyntax.term w z b q))
    (hc : Derives Γ (SyntaxTermSyntax.term w z b c))
    (hD3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) D3))
    (hS0 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J p S0))
    (hS1 : Derives Γ (ForcingReflexiveImages.replacement w f z b S J q S1))
    (hQP : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.template Reln) w (N 0)))
    (hQM : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.atoms Reln 1) w (N 1)))
    (hQO : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.atoms Reln 4) w (N 2)))
    (hPre : Derives Γ (mixed w B S z f z b (N 0) Pre))
    (hMem : Derives Γ (mixed w D3 S A3 f z b (N 1) (H 1)))
    (hOrd : Derives Γ (mixed w D3 S A3 f z b (N 2) (H 4)))
    (hOld : Derives Γ (ForcingAtomicMono.directData equality Reln w a f z b D S0 X Y Fp v0))
    (hNew : Derives Γ (ForcingAtomicMono.directData equality Reln w a f z b D S1 X Y Fq v1))
    (hExtra : Derives Γ (FormulaCodeSyntax.formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (out : Formula m) (use : CanonicalFieldsConsumer Γ equality Reln w z b B Fp Fq layout out) :
    Derives Γ out := by
  have hx0 := Derives.conjL (.conjR (.conjR hOld))
  have hy0 := Derives.conjL (.conjR (.conjR (.conjR hOld)))
  have hx1 := Derives.conjL (.conjR (.conjR hNew))
  have hy1 := Derives.conjL (.conjR (.conjR (.conjR hNew)))
  have hex := ForcingAtomicMono.closed_image_agreement hZ w a f z b D S1 S0 X (v1 2) (v0 2) hw hz hX hx1 hx0
  have hey := ForcingAtomicMono.closed_image_agreement hZ w a f z b D S1 S0 Y (v1 3) (v0 3) hw hz hY hy1 hy0
  have hF0 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hOld))))
  have hF1 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hNew))))
  let sources := five (N 0) (N 1) (N 2) (v0 1) (v1 1)
  have quotes (i : Fin 5) : Derives Γ (PureQuotationSyntax.formula
      (ForcingAtomicMonoTemplate.leaf equality Reln (ForcingAtomicMonoTemplate.partAt i)) w (sources i)) :=
    Fin.cases hQP (Fin.cases hQM (Fin.cases hQO
      (Fin.cases (.conjL (.conjR hOld)) (fun _ => .conjL (.conjR hNew))))) i
  have terms (v : Fin m) (hv : v ∈ [v0 3,v0 2,q,c,p]) : Derives Γ (SyntaxTermSyntax.term w z b v) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact SyntaxCodedMixedTermTyping.target_type w D S0 a f z b Y (v0 3) hy0
    · exact SyntaxCodedMixedTermTyping.target_type w D S0 a f z b X (v0 2) hx0
    · exact hq
    · exact hc
    · exact hp
  exact use f J S A3 D3 (v0 0) (v1 0) (v0 4) (v1 4) S0 S1 (v0 2) (v0 3) p q c Extra Pre H sources
    hw hz hf hJ hA (.conjL hOld) (.conjL hNew)
    terms hD3 hF0 (pair_forest_subst w (v1 4) (v0 2) (v0 3) (v1 2) (v1 3) hex hey hF1) hS0 hS1 quotes
    hPre hMem hOrd (.conjR (.conjR (.conjR (.conjR (.conjR hOld)))))
    (.conjR (.conjR (.conjR (.conjR (.conjR hNew))))) hExtra hLayout

private theorem with_row_direct_pair_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y Fp Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (v0 v1 : Fin 5 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hX : Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hOld : Derives Γ (ForcingAtomicMono.directData equality Reln w a f z b T S0 X Y Fp v0))
    (hNew : Derives Γ (ForcingAtomicMono.directData equality Reln w a f z b T S1 X Y Fq v1))
    (out : Formula m) (use : CanonicalFieldsConsumer Γ equality Reln w z b R Fp Fq layout out) :
    Derives Γ out := by
  let left := fun i : Fin 24 => rows (i.castAdd 24)
  let H := ForcingMemberRows.leafFields left
  let D := ForcingMemberRows.prefixFields left
  let p := P 0 2
  let q := P 0 1
  let c := P 0 0
  have hGlobal := Derives.conjL hr
  have hAux := Derives.conjR hr
  have hRel := Derives.conjL hGlobal
  have hRows := Derives.conjL hRel
  have hBasis := Derives.conjL hRows
  have hRow : Derives Γ (ForcingMemberRows.rowData test Reln w z A1 A2 A3 f b (C 0) R S
      (Refl 0) (Pre 0) (U0 0) raw (P 0) left) := .conjL (.conjR hRows)
  have hIn := Derives.conjL (.conjL (.conjR hGlobal))
  have hw := Derives.conjL (.conjL (.conjL (.conjR (.conjR hIn))))
  have hz := Derives.conjL hIn
  have hf := Derives.conjL (.conjR (.conjR (.conjR (.conjR (hBasis)))))
  have hJ := Derives.conjL (.conjR hAux)
  have hpS := Derives.conjL (.conjR (.conjR hAux))
  have hqS := Derives.conjR (.conjR (.conjR hAux))
  have hA := Derives.conjR hRel
  have hPre : Derives Γ (mixed w R S z f z b (raw 0) (Pre 0)) :=
    .conjR (.conjR (.conjR (.conjR (.conjR (.conjR hIn)))))
  have hRaw := Derives.conjL hRow
  have hQP := Derives.conjL (.conjL hRaw)
  have hQM := Derives.conjL (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hRaw)))))))))))))
  have hQO := Derives.conjL (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hRaw))))))))))))))))
  have hPrefix := Derives.conjL (.conjR (.conjR (.conjR (hRow))))
  have hQueries : Derives Γ (ForcingPreorderLeaves.queries w (D 2) S A3 f z b raw H (ForcingMemberRows.tailFields left)) :=
    .conjR (.conjR (.conjR (.conjR hRow)))
  have hMem := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hQueries)))))))
  have hOrd := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hQueries))))))))))
  have hP (i : Fin 3) := ForcingRelationWeakening.row_term test Reln w z A1 A2 A3 f b (C 0) R S
    (Refl 0) (Pre 0) (U0 0) raw (P 0) left hRow i
  have hB0 : Derives Γ (termList w z z b R) :=
    .conjL (.conjL (SyntaxMixedFormulaJudgment.legal w R S z f z b (raw 0) (Pre 0) hPre))
  have hn0 : Derives Γ (SyntaxForestSyntax.forest 0 w Fin.elim0 R) :=
    StructuralListLengthConstruct.nil_of_empty_length hZ w R z
      (.conjR (.conjL (.conjR (.conjR hB0)))) hz
  have hn1 : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => c) (D 0)) :=
    SyntaxForestSyntax.intro_cons 0 w (fun _ => c) (D 0) R
      (SyntaxTerms.range hZ w z b c hw (hP 0)) hn0 (.conjL (.conjL hPrefix))
  have hn2 : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 q c) (D 1)) :=
    SyntaxForestSyntax.intro_cons 1 w (SetLanguage.args2 q c) (D 1) (D 0)
      (SyntaxTerms.range hZ w z b q hw (hP 1)) hn1 (.conjL (.conjL (.conjR hPrefix)))
  have hn3 : Derives Γ (SyntaxForestSyntax.forest 3 w (SetLanguage.args3 p q c) (D 2)) :=
    SyntaxForestSyntax.intro_cons 2 w (SetLanguage.args3 p q c) (D 2) (D 1)
      (SyntaxTerms.range hZ w z b p hw (hP 2)) hn2 (.conjL (.conjR (.conjR hPrefix)))
  exact with_direct_pair_fields hZ equality Reln w z a f j b R S A3 (D 2) T S0 S1 X Y p q c Extra (Pre 0) Fp Fq
    H layout (SetLanguage.args3 (raw 0) (raw 11) (raw 14)) v0 v1 hw hz hf hJ hA hX hY (hP 2) (hP 1) (hP 0)
    hn3 hpS hqS hQP hQM hQO hPre hMem hOrd hOld hNew
    (.conjL (.conjR (.conjR hGlobal))) (.conjR (.conjR (.conjR hGlobal))) out use
/-- Expose the original compiler images and preorder fields after eliminating
both actual query records. -/
theorem with_runtime_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fp Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hX : Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hAtom : Derives Γ (ForcingAtomicCode.compiled equality Reln w a X Y A))
    (hOld : Derives Γ (mixed w T S0 a f z b A Fp)) (hNew : Derives Γ (mixed w T S1 a f z b A Fq))
    (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (ρ : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {φ : Formula m}, Derives Γ φ → Derives Δ (φ.rename ρ)) →
      CanonicalFieldsConsumer Δ equality Reln (ρ w) (ρ z) (ρ b) (ρ R) (ρ Fp) (ρ Fq)
        (fun i => ρ (layout i)) (out.rename ρ)) : Derives Γ out := by
  have e0 := ForcingAtomicMono.direct_from_compiled hZ equality Reln w a f z b T S0 X Y A Fp hw hz hf hAtom hX hY hOld
  have e1 := ForcingAtomicMono.direct_from_compiled hZ equality Reln w a f z b T S1 X Y A Fq hw hz hf hAtom hX hY hNew
  apply eliminate_objects hZ 5 (fun r xs => ForcingAtomicMono.directData equality Reln (r w) (r a) (r f) (r z)
    (r b) (r T) (r S0) (r X) (r Y) (r Fp) xs) e0 out
  intro l Δ r v0 hZ1 lift hd0
  apply eliminate_objects hZ1 5 (fun s xs => ForcingAtomicMono.directData equality Reln (s (r w)) (s (r a))
    (s (r f)) (s (r z)) (s (r b)) (s (r T)) (s (r S1)) (s (r X)) (s (r Y)) (s (r Fq)) xs)
    (of_eq (ForcingAtomicMono.direct_rename equality Reln w a f z b T S1 X Y Fq r) (lift e1)) (out.rename r)
  intro l' Δ' s v1 hZ2 move hd1
  let ρ := fun i => s (r i)
  have carry {φ : Formula m} (hp : Derives Γ φ) : Derives Δ' (φ.rename ρ) :=
    of_eq (rename_comp φ r s) (move (lift hp))
  have hh0 := of_eq (ForcingAtomicMono.directData_rename equality Reln (r w) (r a) (r f) (r z)
    (r b) (r T) (r S0) (r X) (r Y) (r Fp) v0 s) (move hd0)
  have hRow := of_eq (ForcingRawModalBody.globalModalInput_rename test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K
    Extra raw v C Refl Pre U0 P rows layout ρ) (carry hr)
  have result := with_row_direct_pair_fields hZ2 equality Reln
    (ρ w) (ρ z) (ρ a) (ρ f) (ρ j) (ρ b) (ρ B) (ρ R) (ρ S) (ρ T) (ρ S0) (ρ S1)
    (ρ A1) (ρ A2) (ρ A3) (ρ K) (ρ Extra) (ρ X) (ρ Y) (ρ Fp) (ρ Fq)
    (fun i => ρ (raw i)) (fun i => ρ (v i)) (fun i => ρ (C i)) (fun i => ρ (Refl i))
    (fun i => ρ (Pre i)) (fun i => ρ (U0 i)) (fun i t => ρ (P i t)) (fun i => ρ (rows i))
    (fun i => ρ (layout i)) (fun i => s (v0 i)) v1 hRow
    (of_eq (SyntaxTermSyntax.term_rename w a z X ρ) (carry hX))
    (of_eq (SyntaxTermSyntax.term_rename w a z Y ρ) (carry hY)) hh0 hd1
    (out.rename ρ) (use ρ hZ2 carry)
  exact of_eq (rename_comp out r s).symm result

/-- Consume the actual atom compiler and both queries in the original global
row. The direct lists and the two term-image equalities are derived inside. -/
theorem from_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2))
    (w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fp Fq : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (rows : Fin 48 → Fin m) (layout : Fin 6 → Fin m)
    (hr : Derives Γ (ForcingRawModalBody.globalModalInput test Reln w z a f j b B R S T S0 S1 A1 A2 A3 K Extra
      raw v C Refl Pre U0 P rows layout))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (numeral (k+2) f))
    (hX : Derives Γ (SyntaxTermSyntax.term w a z X)) (hY : Derives Γ (SyntaxTermSyntax.term w a z Y))
    (hAtom : Derives Γ (ForcingAtomicCode.compiled equality Reln w a X Y A))
    (hOld : Derives Γ (mixed w T S0 a f z b A Fp)) (hNew : Derives Γ (mixed w T S1 a f z b A Fq))
    (hFp : Derives Γ (implication test w z b (layout 3) Fp)) :
    Derives Γ (implication test w z b (layout 3) Fq) := by
  let out := implication test w z b (layout 3) Fq
  apply with_runtime_fields hZ equality Reln
    w z a f j b B R S T S0 S1 A1 A2 A3 K Extra X Y A Fp Fq raw v C Refl Pre U0 P rows layout
    hr hw hz hf hX hY hAtom hOld hNew out
  intro l Δ ρ hZ1 lift
  intro f' J S' A3' D3 t0 t1 D0 D1 S0' S1' x y p q c Extra' Pre' H N
    hw1 hz1 hf1 hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes hPre hMem hOrd hOld1 hNew1 hExtra hLayout
  exact of_eq (implication_rename test w z b (layout 3) Fq ρ).symm
    (at_canonical_fields hZ1 equality Reln
      (ρ w) (ρ z) f' J (ρ b) (ρ R) S' A3' D3 t0 t1 D0 D1 S0' S1' x y p q c Extra' Pre' (ρ Fp) (ρ Fq)
      H (fun i => ρ (layout i)) N hw1 hz1 hf1 hJ hA ht0 ht1 hTerms hD3 hD0 hD1 hS0 hS1 hQuotes
      hPre hMem hOrd hOld1 hNew1 hExtra hLayout
      (of_eq (implication_rename test w z b (layout 3) Fp ρ) (lift hFp)))


end PPAC.Migration.ForcingAtomicMonoImages
