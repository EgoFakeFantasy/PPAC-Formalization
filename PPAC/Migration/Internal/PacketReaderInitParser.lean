import PPAC.Migration.Internal.PacketReaderInitLiterals

/-! Original 128/0/1/[] initialization is internalized: reader returns exist uniquely exactly on all actual internal input lists. -/
namespace PPAC.Migration.Internal.PacketReaderInitParser
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInitSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_return {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (StructuralListTraceSyntax.valid w L)) : Derives Γ (existsParse w L) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (OrderedPairElimination.under_two hw U)
  have hL2 : Derives Δ (StructuralListTraceSyntax.valid w.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListTraceSyntax.valid_rename]) (OrderedPairElimination.under_two hL U)
  let P := PacketAffineLiteralSyntax.frame false w.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ2 128 w.castSucc.castSucc hw2)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 P
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 P)
  have hL3 := of_eq (StructuralListTraceSyntax.valid_rename w.castSucc.castSucc L.castSucc.castSucc Fin.castSucc) (under hL2 P)
  have hU3 : Derives Ξ ((empty (Fin.last m).castSucc.castSucc).conj (successor (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc)) := by
    simpa only [U,StructuralListSyntax.unitWitness,Formula.raise,Formula.rename,empty_rename,successor_rename] using under hU P
  have hs := PacketReaderInitSeeded.exists_return hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc L.castSucc.castSucc.castSucc hw3 (.conjL hP) (.conjL hU3) (.conjR hU3) hL3
  have hp := PacketReaderInitLiterals.from_seeded_exists _ _ _ _ _ (.conjR hP) (.conjL hU3) (.conjR hU3) hs
  simpa only [Formula.raise,existsParse_rename] using hp

theorem input_valid {m} {Γ : Context m} (w L q : Fin m) (hr : Derives Γ (parse w L q)) :
    Derives Γ (StructuralListTraceSyntax.valid w L) := by
  let R := parseBody w L q
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (StructuralListTraceSyntax.valid_rename w L (old 3)).symm
    (PacketReaderInitSeeded.input_valid _ _ _ _ _ _ (.conjR (.conjR (.conjR hR))))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (parse w L p)) (hq : Derives Γ (parse w L q)) : Derives Γ (.equal p q) := by
  let R := parseBody w L p
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hq3 := of_eq (parse_rename w L q (old 3)) (HornBinderRules.under_body 3 hq R)
  have hNorm := PacketReaderInitLiterals.at_literals hZ3 (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 L) (old 3 q) (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR)))
  have hB := SyntaxNumerals.range hZ3 128 (old 3 w) (slot 3 0) hw3 (.conjL hR)
  exact PacketReaderInitSeeded.unique hZ3 _ _ _ _ _ _ _ hw3 hB (.conjR (.conjR (.conjR hR))) (.impE (.conjL hNorm) hq3)

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (parse w L q)) : Derives Γ (.mem q w) := by
  let R := parseBody w L q
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  exact PacketReaderInitSeeded.natural hZ3 _ _ _ _ _ _ hw3 (.conjR (.conjR (.conjR hR)))

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((existsParse w L).iff (StructuralListTraceSyntax.valid w L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsParse w L
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (parse w.castSucc L.castSucc (Fin.last m))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives (Context.add R (Context.image Formula.raise (Context.add H Γ))) R := .hyp (Or.inl rfl)
    simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using input_valid _ _ _ (.conjR hR)
  · apply Derives.impI
    exact exists_return (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (StructuralListTraceSyntax.valid w L)) : Derives Γ (parseFiber w L) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (parse w.castSucc L.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_return hZ w L hw hL)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all ((parse w.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := parse w.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    have hZ2 := ZFContext.under (ZFContext.under hZ R) T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
    have hOld := of_eq (parse_rename w.castSucc L.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
    exact unique hZ2 _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Δ (parseFiber w.castSucc L.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,parse_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hu)
  simpa only [Formula.raise,parseFiber_rename] using hout

end PPAC.Migration.Internal.PacketReaderInitParser
