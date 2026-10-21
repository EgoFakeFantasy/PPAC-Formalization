import PPAC.Migration.Internal.StructuralNodeProperties

/-! 原节点输出唯一与输入单射；共同后继的前驱以对象自然顺序消去。 -/
namespace PPAC.Migration.Internal.StructuralNodeCore
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem pair_output_subst {m} {Γ : Context m} (w a b q p : Fin m) (he : Derives Γ (.equal q p))
    (hq : Derives Γ (GodelPairSyntax.code w a b q)) : Derives Γ (GodelPairSyntax.code w a b p) := by
  have hi : Derives Γ ((GodelPairSyntax.code w.castSucc a.castSucc b.castSucc (Fin.last m)).instantiate q) := by
    simpa only [Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hq
  have ho := Derives.eqSubst (GodelPairSyntax.code w.castSucc a.castSucc b.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, GodelPairSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem predecessor_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q p : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (.mem q w))
    (hs : Derives Γ (successor n q)) (ht : Derives Γ (successor n p)) : Derives Γ (.equal q p) := by
  have hqp := NaturalOrderBasic.member_successor _ _ _ ht (InsertLogic.new_member n q q hs)
  have hpq := NaturalOrderBasic.member_successor _ _ _ hs (InsertLogic.new_member n p p ht)
  exact NaturalOrderBasic.antisymmetric hZ w q p hw hq hqp hpq

theorem value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n r q p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (GodelPairSyntax.code w a b q)) (hp : Derives Γ (GodelPairSyntax.code w a b p))
    (hn : Derives Γ (successor n q)) (hr : Derives Γ (successor r p)) : Derives Γ (.equal n r) := by
  have he := GodelPairCore.unique hZ _ _ _ _ _ hw ha hb hq hp
  have hs := GodelUnpairArithmetic.successor_base_subst n q p he hn
  exact OmegaUniversal.successor_unique n r p (ZFContext.arithmetic hZ).base.extensionality hs hr

theorem input_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d n q p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hq : Derives Γ (GodelPairSyntax.code w a b q)) (hp : Derives Γ (GodelPairSyntax.code w c d p))
    (hn : Derives Γ (successor n q)) (hr : Derives Γ (successor n p)) : Derives Γ ((Formula.equal a c).conj (.equal b d)) := by
  have hqW := GodelPairCore.range hZ _ _ _ _ hw hq
  have he := predecessor_unique hZ _ _ _ _ hw hqW hn hr
  exact GodelPairInjective.injective hZ _ _ _ _ _ _ hw ha hb hc hd (pair_output_subst _ _ _ _ _ he hq) hp

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hn : Derives Γ (raw w a b n)) (hr : Derives Γ (raw w a b r)) : Derives Γ (Formula.equal n r) := by
  let N := rawWitness w a b n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_raw w a b n _ hn
  have hr1 : Derives Ξ (raw w.castSucc a.castSucc b.castSucc r.castSucc) := by simpa only [Formula.raise, raw_rename] using under hr N
  let R := rawWitness w.castSucc a.castSucc b.castSucc r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_raw w.castSucc a.castSucc b.castSucc r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((GodelPairSyntax.code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
      (successor n.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [N, rawWitness, Formula.raise, Formula.rename, GodelPairSyntax.code_rename, successor_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact value_unique hZ2 _ _ _ _ _ _ _ hw2 (lift ha) (lift hb) (.conjL hN2) (.conjL hR) (.conjR hN2) (.conjR hR)

theorem injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hn : Derives Γ (raw w a b n)) (hr : Derives Γ (raw w c d n)) : Derives Γ ((Formula.equal a c).conj (.equal b d)) := by
  let N := rawWitness w a b n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_raw w a b n _ hn
  have hr1 : Derives Ξ (raw w.castSucc c.castSucc d.castSucc n.castSucc) := by simpa only [Formula.raise, raw_rename] using under hr N
  let R := rawWitness w.castSucc c.castSucc d.castSucc n.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_raw w.castSucc c.castSucc d.castSucc n.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((GodelPairSyntax.code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
      (successor n.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [N, rawWitness, Formula.raise, Formula.rename, GodelPairSyntax.code_rename, successor_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact input_unique hZ2 _ _ _ _ _ _ _ _ hw2 (lift ha) (lift hb) (lift hc) (lift hd) (.conjL hN2) (.conjL hR) (.conjR hN2) (.conjR hR)

theorem unique_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag payload : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem payload w)) : Derives Γ (encodeFiber w tag payload) := by
  have hn := StructuralNodeExistence.exists_raw hZ w tag payload hw ht hp
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (raw w.castSucc tag.castSucc payload.castSucc (Fin.last m))
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  change Derives Γ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ N
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hu : Derives Ξ (.all ((raw w.castSucc.castSucc tag.castSucc.castSucc payload.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let R := raw w.castSucc.castSucc tag.castSucc.castSucc payload.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 R
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 R
    have hOld : Derives Δ (raw w.castSucc.castSucc tag.castSucc.castSucc payload.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, raw_rename] using under (Derives.conjR hN) R
    exact unique hZ2 _ _ _ _ _ hw2 (under (under ht N) R) (under (under hp N) R) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (encodeFiber w.castSucc tag.castSucc payload.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hN hu
  simpa only [Formula.raise, encodeFiber_rename] using hout
end PPAC.Migration.Internal.StructuralNodeCore
