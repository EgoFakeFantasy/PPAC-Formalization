import PPAC.Migration.Internal.PacketTokensBytesSeededTotal

/-! Actual tokens.flatMap varint is the independent coupled trace started at an actual Nil byte list. No reader evaluation occurs in the definition. -/
namespace PPAC.Migration.Internal.PacketTokensBytes
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokensBytesSyntax
open SyntaxRenameQuerySyntax (of_eq)

def encoded {m} (w n a : Fin m) : Formula m := .ex
  ((StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc))

def remaining {m} (w h x a : Fin m) : Formula m := .ex
  ((encoded w.castSucc x.castSucc (Fin.last m)).conj (PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc))

def consBody {m} (w h x a : Fin m) : Formula (m+2) :=
  (PacketVarintSyntax.canonical (old 2 w) (old 2 h) (slot 2 0)).conj
    ((encoded (old 2 w) (old 2 x) (slot 2 1)).conj (StructuralListSpliceSyntax.splice (old 2 w) (slot 2 0) (slot 2 1) (old 2 a)))

def consCase {m} (w h x a : Fin m) : Formula m := existsMany 2 (consBody w h x a)

def uniqueAt {m} (w n a : Fin m) : Formula m := .all
  ((encoded w.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiberBody {m} (w n : Fin m) : Formula (m+1) :=
  ((Formula.mem (Fin.last m) w.castSucc).conj (encoded w.castSucc n.castSucc (Fin.last m))).conj (uniqueAt w.castSucc n.castSucc (Fin.last m))

def fiber {m} (w n : Fin m) : Formula m := .ex (fiberBody w n)

theorem encoded_rename {m k} (w n a : Fin m) (ρ : Fin m → Fin k) :
    (encoded w n a).rename ρ = encoded (ρ w) (ρ n) (ρ a) := by
  simp only [encoded,Formula.rename,StructuralListSyntax.nilCode_rename,seeded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem remaining_rename {m k} (w h x a : Fin m) (ρ : Fin m → Fin k) :
    (remaining w h x a).rename ρ = remaining (ρ w) (ρ h) (ρ x) (ρ a) := by
  simp only [remaining,Formula.rename,encoded_rename,PacketTokensBytesRowSyntax.push_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem consBody_lift {m k} (w h x a : Fin m) (ρ : Fin m → Fin k) :
    (consBody w h x a).rename (lift 2 ρ) = consBody (ρ w) (ρ h) (ρ x) (ρ a) := by
  simp only [consBody,Formula.rename,PacketVarintSyntax.canonical_rename,encoded_rename,StructuralListSpliceSyntax.splice_rename,lift_old,lift_slot]

theorem consCase_rename {m k} (w h x a : Fin m) (ρ : Fin m → Fin k) :
    (consCase w h x a).rename ρ = consCase (ρ w) (ρ h) (ρ x) (ρ a) := by
  simp only [consCase,existsMany_rename,consBody_lift]

theorem uniqueAt_rename {m k} (w n a : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAt w n a).rename ρ = uniqueAt (ρ w) (ρ n) (ρ a) := by
  simp only [uniqueAt,Formula.rename,encoded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n).rename ρ = fiber (ρ w) (ρ n) := by
  simp only [fiber,fiberBody,Formula.rename,encoded_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_encoded {m} {Γ : Context m} (w n a e : Fin m) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hs : Derives Γ (seeded w n e a)) : Derives Γ (encoded w n a) := by
  apply Derives.exI e
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListSyntax.nilCode_rename,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI he hs)

theorem seed_subst {m} {Γ : Context m} (w n t e a : Fin m) (he : Derives Γ (.equal t e))
    (hs : Derives Γ (seeded w n t a)) : Derives Γ (seeded w n e a) := by
  let P := seeded w.castSucc n.castSucc (Fin.last m) a.castSucc
  have h0 : P.instantiate t = seeded w n t a := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate e = seeded w n e a := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem at_seed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a e : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (StructuralListSyntax.nilCode w e)) :
    Derives Γ ((encoded w n a).iff (seeded w n e a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := encoded w n a
    let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under (add he H) R)
    have hEq := StructuralNil.unique hZ1 _ _ _ hw1 (.conjL hR) he1
    simpa only [Formula.raise,seeded_rename] using seed_subst _ _ _ _ _ hEq (.conjR hR)
  · apply Derives.impI
    exact intro_encoded _ _ _ _ (add he _) (.hyp (Or.inl rfl))

theorem input_valid {m} {Γ : Context m} (w n a : Fin m) (he : Derives Γ (encoded w n a)) :
    Derives Γ (StructuralListTraceSyntax.valid w n) := by
  let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using PacketTokensBytesSeeded.prefix_valid _ _ _ _ (.conjR hR)

theorem output_valid {m} {Γ : Context m} (w n a : Fin m) (he : Derives Γ (encoded w n a)) :
    Derives Γ (StructuralListTraceSyntax.valid w a) := by
  let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using PacketTokensBytesSeeded.joined_valid _ _ _ _ (.conjR hR)

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ ((encoded w n a).iff (StructuralListSyntax.nilCode w a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := encoded w n a
    let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hn1 := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under (add hn H) R)
    have hEq := Derives.conjR (.impE (.conjL (PacketTokensBytesSeeded.nil_iff hZ1 _ _ _ _ hw1 hn1)) (.conjR hR))
    simpa only [Formula.raise,StructuralListSyntax.nilCode_rename] using StructuralListTraceOrder.nil_output_subst _ _ _ hEq (.conjL hR)
  · apply Derives.impI
    let H := StructuralListSyntax.nilCode w a
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ H
    have hA := StructuralListTraceBase.valid_nil hZ1 w a (add hw H) hH
    have hSeeded := Derives.impE (.conjR (PacketTokensBytesSeeded.nil_iff hZ1 w n a a (add hw H) (add hn H))) (.conjI hA (.eqRefl a))
    exact intro_encoded w n a a hH hSeeded

theorem intro_remaining {m} {Γ : Context m} (w h x a u : Fin m) (he : Derives Γ (encoded w x u))
    (hp : Derives Γ (PacketTokensBytesRowSyntax.push w h u a)) : Derives Γ (remaining w h x a) := by
  apply Derives.exI u
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,encoded_rename,PacketTokensBytesRowSyntax.push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI he hp)

theorem cons_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (he : Derives Γ (encoded w n a)) : Derives Γ (remaining w h x a) := by
  let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (seeded w.castSucc n.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x n Fin.castSucc) (under hc R)
  have hRem := PacketTokensBytesSeeded.cons_forward hZ1 _ _ _ _ _ _ hw1 (under hh R) (under hx R) hc1 (.conjR hR)
  let S := (seeded w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj (PacketTokensBytesRowSyntax.push w.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hRem
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hNil := of_eq (StructuralListSyntax.nilCode_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hSmall := intro_encoded _ _ _ _ hNil (.conjL hS)
  simpa only [Formula.raise,remaining_rename] using intro_remaining _ _ _ _ _ hSmall (.conjR hS)

theorem cons_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hr : Derives Γ (remaining w h x a)) : Derives Γ (encoded w n a) := by
  let R := (encoded w.castSucc x.castSucc (Fin.last m)).conj (PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  let S := (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1))).conj (seeded w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (.conjL hR)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) S
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) S)
  have hc2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListSyntax.consCode_rename]) (under (under hc R) S)
  have hPush := of_eq (PacketTokensBytesRowSyntax.push_rename w.castSucc h.castSucc (Fin.last m) a.castSucc Fin.castSucc) (under (.conjR hR) S)
  have hRemaining := PacketTokensBytesSeeded.intro_remaining _ _ _ _ _ _ (.conjR hS) hPush
  have hSeeded := PacketTokensBytesSeeded.cons_backward hZ2 _ _ _ _ _ _ hw2 (under (under hh R) S) hc2 hRemaining
  simpa only [Formula.raise,encoded_rename] using intro_encoded _ _ _ _ (.conjL hS) hSeeded

theorem intro_case {m} {Γ : Context m} (w h x a V u : Fin m) (hc : Derives Γ (PacketVarintSyntax.canonical w h V))
    (he : Derives Γ (encoded w x u)) (hs : Derives Γ (StructuralListSpliceSyntax.splice w V u a)) : Derives Γ (consCase w h x a) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two V u)
  exact of_eq (by simp only [consBody,Formula.rename,PacketVarintSyntax.canonical_rename,encoded_rename,StructuralListSpliceSyntax.splice_rename,assign_old,assign_slot]; rfl) (.conjI hc (.conjI he hs))

theorem remaining_to_case {m} {Γ : Context m} (w h x a : Fin m) (hr : Derives Γ (remaining w h x a)) : Derives Γ (consCase w h x a) := by
  let R := (encoded w.castSucc x.castSucc (Fin.last m)).conj (PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  let S := (PacketVarintSyntax.canonical w.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))).conj (StructuralListSpliceSyntax.splice w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc a.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (.conjR (.conjR hR))
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hSmall := of_eq (encoded_rename w.castSucc x.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  simpa only [Formula.raise,consCase_rename] using intro_case _ _ _ _ _ _ (.conjL hS) hSmall (.conjR hS)

theorem case_to_remaining {m} {Γ : Context m} (w h x a : Fin m) (hr : Derives Γ (consCase w h x a)) : Derives Γ (remaining w h x a) := by
  let R := consBody w h x a
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hPush := PacketTokensBytesRowSyntax.intro_push _ _ _ _ _ (.conjL hR) (.conjR (.conjR hR))
  exact of_eq (remaining_rename w h x a (old 2)).symm (intro_remaining _ _ _ _ _ (.conjL (.conjR hR)) hPush)

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) : Derives Γ ((encoded w n a).iff (consCase w h x a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact remaining_to_case _ _ _ _ (cons_forward (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hh _) (add hx _) (add hc _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact cons_backward (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hh _) (add hc _) (case_to_remaining _ _ _ _ (.hyp (Or.inl rfl)))

theorem intro_fiber {m} {Γ : Context m} (w n a : Fin m) (ha : Derives Γ (.mem a w))
    (he : Derives Γ (encoded w n a)) (hu : Derives Γ (uniqueAt w n a)) : Derives Γ (fiber w n) := by
  apply Derives.exI a
  exact of_eq (by simp only [fiberBody,Formula.instantiate,Formula.rename,encoded_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjI ha he) hu)

theorem unique_at {m} {Γ : Context m} (w n a b : Fin m) (hu : Derives Γ (uniqueAt w n a))
    (he : Derives Γ (encoded w n b)) : Derives Γ (.equal b a) := by
  have hh : Derives Γ ((encoded w n b).imp (.equal b a)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,encoded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE b hu)
  exact .impE hh he

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) : Derives Γ (fiber w n) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (OrderedPairElimination.under_two hw U)
  have hn2 : Derives Δ (StructuralListTraceSyntax.valid w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListTraceSyntax.valid_rename]) (OrderedPairElimination.under_two hn U)
  have hNil := StructuralNil.at_unit hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hValid := StructuralListTraceBase.valid_nil hZ2 _ _ hw2 hNil
  let R := PacketTokensBytesSeededTotalSyntax.fiberBody w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add R (Context.image Formula.raise Δ)
  apply Derives.exE (p := R) (PacketTokensBytesSeededTotal.exists_unique hZ2 _ _ _ hw2 hn2 hValid)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 R
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 R)
  have hNil3 := of_eq (StructuralListSyntax.nilCode_rename w.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc) (under hNil R)
  have hEncoded := intro_encoded w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hNil3 (.conjR (.conjL hR))
  have hAll : Derives Ξ (uniqueAt w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))) := by
    apply Derives.allI
    apply Derives.impI
    let H := encoded w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
    let Ω := Context.add H (Context.image Formula.raise Ξ)
    have hZ4 := ZFContext.under hZ3 H
    have hw4 := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 H)
    have hNil4 := of_eq (StructuralListSyntax.nilCode_rename w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc Fin.castSucc) (under hNil3 H)
    have hNorm := at_seed hZ4 w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last (m+1)).castSucc.castSucc hw4 hNil4
    have hSeeded := Derives.impE (.conjL hNorm) (.hyp (Or.inl rfl) : Derives Ω H)
    have hi4 := of_eq (PacketTokensBytesSeededTotalSyntax.uniqueAt_rename w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) Fin.castSucc) (under (.conjR hR) H)
    exact PacketTokensBytesSeededTotalSyntax.unique_at _ _ _ _ _ hi4 hSeeded
  have hout := intro_fiber w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (.conjL (.conjL hR)) hEncoded hAll
  simpa only [Formula.raise,fiber_rename] using hout

theorem natural {m} {Γ : Context m} (w n a : Fin m) (he : Derives Γ (encoded w n a)) : Derives Γ (.mem a w) :=
  StructuralListValidity.range w a (output_valid w n a he)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (encoded w n a)) (hb : Derives Γ (encoded w n b)) : Derives Γ (.equal a b) := by
  let R := fiberBody w n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_unique hZ w n hw (input_valid w n a ha))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha1 := of_eq (encoded_rename w n a Fin.castSucc) (under ha R)
  have hb1 := of_eq (encoded_rename w n b Fin.castSucc) (under hb R)
  exact eq_trans (unique_at _ _ _ _ (.conjR hR) ha1) (eq_symm (unique_at _ _ _ _ (.conjR hR) hb1))

theorem fiber_domain {m} {Γ : Context m} (w n : Fin m) (hf : Derives Γ (fiber w n)) : Derives Γ (StructuralListTraceSyntax.valid w n) := by
  let R := fiberBody w n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using input_valid _ _ _ (.conjR (.conjL hR))

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((fiber w n).iff (StructuralListTraceSyntax.valid w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact fiber_domain w n (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact exists_unique (ZFContext.add hZ _) w n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketTokensBytes
