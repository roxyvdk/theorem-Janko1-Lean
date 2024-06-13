import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Coset
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false

#check Subgroup.centralizer
#check alternatingGroup
#check IsSimpleGroup
#check Prod.instMul
#check Quotient.mk'
#check eq_one_div_of_mul_eq_one_left

class IsJanko1 (G:Type*) [Group G] : Prop where
  Sylow2_abelian : ∀(S: Sylow 2 G) (a b: G), a ∈ S → b ∈ S → a*b=b*a
  Centralizer_involution : ∃(ι : G), orderOf ι = 2 ∧
    Nonempty (Subgroup.centralizer {ι} ≃* Subgroup.closure {ι} × alternatingGroup (Fin 5))
  No_index2 : ∀(H: Subgroup G), H.index ≠ 2

namespace IsJanko1

variable (G : Type*) [Group G] [Fintype G] [IsJanko1 G]

-- Johan moet dit fixen
instance [Fintype G] (H : Subgroup G) : Fintype H := sorry
instance [Fintype G] (H : Subgroup G) : Fintype (G ⧸ H) := sorry
instance [Fintype G] (S : Sylow 2 G) : Fintype S := sorry

theorem Sylow_conjugates (S₁ : Sylow 2 G) (S₂ : Sylow 2 G):
  ∃(g : G), ∀(s : S₁), g⁻¹ * s * g ∈ S₂ := by
  sorry

-- All involutions of G are conjugated
-- Sylow 2-subgroups of G are of the type [2,2,2]
lemma type_222 (S : Sylow 2 G) :
  ∀ (s : S), (s ≠ 1) → orderOf s = 2 := by
  intro s hs
  sorry

-- Sylow 2-subgroups and their centralizers
lemma cent_normal_in_norm (H : Type*) [Group H] (K : Subgroup H) :
  ((Subgroup.centralizer K).subgroupOf (Subgroup.normalizer K)).Normal := by
  set N := Subgroup.normalizer (K : Subgroup H)
  set C := Subgroup.centralizer (K : Set H)
  have hc : C ≤ N := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    intro hk
    rw [← hx, mul_assoc, mul_inv_self, mul_one]
    exact hk
    simpa
    intro hK
    have hq : ∃ (q : K), x * h * x⁻¹ = q := by
      use ⟨(x * h * x⁻¹), hK⟩
    obtain ⟨q,hq⟩ := hq
    rw [mul_inv_eq_iff_eq_mul, hx, mul_left_cancel_iff] at hq
    rw [hq]
    simp
    simp
  rw [Subgroup.normal_subgroupOf_iff]
  intro c n hc hn
  have hninv : n⁻¹ ∈ N := by
    apply Subgroup.inv_mem
    exact hn
  rw [Subgroup.mem_normalizer_iff, inv_inv] at hninv
  rw [Subgroup.mem_centralizer_iff] at hc
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  repeat rw [← mul_assoc]
  rw [← eq_mul_inv_iff_mul_eq]
  repeat rw [mul_assoc]
  rw [← inv_mul_eq_iff_eq_mul,inv_inv,← mul_assoc,← mul_assoc, hc, mul_assoc]
  simp at hk
  simp
  rwa [← hninv]
  exact hCN

lemma Sylow_is_cent (S : Sylow 2 G) :
  Subgroup.centralizer (S : Set G) = S := by
  sorry

-- Normalizers act faithful on Sylow 2-subgroups
-- lemma NS_faithful_S

-- The order of the normalizer of a Sylow 2-subgroup
-- def p_normal

-- lemma G_2_normal

-- theorem 2nd_grun

-- lemma

lemma normalizer_S_order_168 (S : Sylow 2 G) :
  Fintype.card (Subgroup.normalizer (S : Subgroup G)) = 168 := by
  set N := Subgroup.normalizer (S : Subgroup G)
  sorry

-- lemma permute_S

-- Involutions are conjugated
theorem involutions_conjugated (ι₁ ι₂ : G) (H₁ : orderOf ι₁ = 2) (H₂ : orderOf ι₂ = 2) :
  IsConj ι₁ ι₂ := by
  simp
  sorry

-- On centralizers of involutions of G
-- lemma conj_subgroup_cong_subgroup

lemma inv_cent (i : G) (hi: orderOf i = 2) :
  Subgroup.centralizer {i} ≃* Subgroup.closure {i} × alternatingGroup (Fin 5) := by
  sorry

-- On normal subgroups of G of odd order
-- Homomorphisms without non-trivial fixed points
lemma comp_id_no_fixed_point_inverse_map (f : G →* G):
  (∀ g : G, (f (f g) = g)) ∧ (∀ (x : G), (f x = x) → x = 1) → ∀(g : G), (f g = g⁻¹) := by
  intro hh
  intro g
  have hxy : ∀ x : G,∀ y : G, (x⁻¹ * (f x))=(y⁻¹ * (f y)) → x = y := by
    intro x y hxy
    apply eq_mul_of_inv_mul_eq at hxy
    rw [← mul_assoc] at hxy
    apply mul_inv_eq_of_eq_mul at hxy
    rw [← f.map_inv,← f.map_mul] at hxy
    apply hh.2 _ at hxy
    rwa [mul_inv_eq_iff_eq_mul, one_mul] at hxy
  have hinj : Function.Injective (fun g : G ↦ (g⁻¹ * (f g))) := by
    exact hxy
  have hbi : Function.Bijective (fun g : G ↦ (g⁻¹ * (f g))) := by
    rw [Finite.injective_iff_bijective] at hinj
    exact hinj
  have h1 : ∃! (x : G), x⁻¹ * f x = g := by
    apply Function.Bijective.existsUnique at hbi
    apply hbi
  obtain ⟨x,hx,hxx⟩ := h1
  symm at hx
  have h2 : g * f g = g * (f x)⁻¹ * x := by
    apply_fun f at hx
    rw [mul_assoc, mul_left_cancel_iff]
    rw [← f.map_inv]
    nth_rw 2 [← hh.1 (x:G)]
    rw [← f.map_mul]
    exact hx
  nth_rewrite 3 [hx] at h2
  rw [mul_assoc,mul_assoc,← mul_assoc (f x),mul_inv_self,one_mul,inv_mul_self] at h2
  rw[mul_eq_one_iff_inv_eq] at h2
  symm at h2
  exact h2

lemma comp_id_no_fixed_point_abelian (f : G →* G) :
  (∀(g : G), (f (f g) = g)) ∧ (∀ (x : G), (f x = x) → x = 1) → (∀(a b : G), a*b=b*a) := by
  intro hh
  intro a b
  have hfinv : ∀ g : G, f g = g⁻¹ := by
    apply comp_id_no_fixed_point_inverse_map
    exact hh
  have invh : f (a*b)= f a * f b := by
    rw [← f.map_mul]
  repeat rw [hfinv] at invh
  rw [mul_inv_rev] at invh
  rw [inv_mul_eq_iff_eq_mul,← mul_assoc] at invh
  symm at invh
  rw [mul_inv_eq_iff_eq_mul,mul_inv_eq_iff_eq_mul,mul_assoc] at invh
  symm at invh
  rw [inv_mul_eq_iff_eq_mul] at invh
  symm
  exact invh

-- No non-trivial normal subgroup of G of odd order
theorem normal_odd_ord_subgroup_trivial (H : Subgroup G) [H.Normal] (Hodd : Odd (Fintype.card H)) :
  H = ⊥ := by
  sorry

-- On normal subgroups of G of odd index
-- Frattini's argument
theorem Frattini (H : Subgroup G) (hN : IsNormalSubgroup (H : Set G)) (S : Sylow 2 H) :
  Subgroup.normalizer ((S : Subgroup H).map H.subtype) ⊔ H = G := by
  have hgSgH : ∀ g : G, ∀ s : S, g * s * g⁻¹ ∈ H := by
    intro g s
    apply IsNormalSubgroup.normal
    exact hN
    sorry
  sorry

--The centralizers of involutions are contained in H
lemma ord_phi_x_div_ord_x (H : Type*) [Group H] (f : G →* H) (g : G) :
  orderOf (f g : H) ∣ orderOf (g : G) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, pow_orderOf_eq_one]
  apply map_one

lemma ord_gH_div_ord_g (H : Subgroup G) [H.Normal] (g : G):
  orderOf (QuotientGroup.mk' H g) ∣ orderOf (g : G) := by
  apply ord_phi_x_div_ord_x

lemma div_two_1or2 (n : ℕ) : n ∣ 2 → n = 1 ∨ n = 2 := by
  rw [Nat.dvd_prime]
  simp
  apply Nat.prime_two

lemma G_even_H_odd_homom_not_inj (H: Type*) [Group H] [Fintype H]
  (Hodd : Odd (Fintype.card H)) (Geven : Even (Fintype.card G)) (f : G →* H) (hf : IsGroupHom f) :
  ¬ (Function.Injective f) := by
  intro hi
  rw [IsGroupHom.injective_iff_trivial_ker] at hi
  have h2 : 2 ∣ Fintype.card G := by
    exact Even.two_dvd Geven
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hfdivH : orderOf (f g) ∣ Fintype.card H := by
    apply orderOf_dvd_card
  have hord : orderOf (f g : H) ∣ 2 := by
    rw [← hg]
    apply ord_phi_x_div_ord_x
  apply div_two_1or2 at hord
  cases hord with
  | inl h => rw [orderOf_eq_one_iff,← IsGroupHom.mem_ker,hi] at h
             rw [IsSubgroup.mem_trivial,← orderOf_eq_one_iff,hg] at h
             contradiction
  | inr h => rw [h] at hfdivH
             apply Odd.not_two_dvd_nat at hfdivH
             contradiction; exact Hodd
  exact hf

lemma homom_inj_iff_trivial_kernel (H : Type*) [Group H] (f : G → H) (hf : IsGroupHom f) (g : G) :
  Function.Injective f ↔ IsGroupHom.ker f = IsSubgroup.trivial G := by
  apply IsGroupHom.injective_iff_trivial_ker
  exact hf

lemma normal_subgroups_simple_product (H₁ : Type*) [Group H₁] (H₂ : Type*) [Group H₂] (h : IsEmpty (H₁ ≃* H₂))
[IsSimpleGroup H₁] [IsSimpleGroup H₂] (N : Subgroup (H₁ × H₂)) [N.Normal] :
  N = ⊥ ∨ N = ⊤ ∨ N = (.prod ⊤ ⊥) ∨ N = (.prod ⊥ ⊤) := by
  sorry

lemma cent_in_H_odd_ind (H : Subgroup G) [H.Normal] (Hodd : Odd H.index) (ι : G) (H₁ : orderOf ι = 2) :
  Subgroup.centralizer {ι} ≤ H := by
  sorry

-- On the intersection of subgroups H of index 2
def InterIndex2 : Subgroup G :=
  ⨅ (K : Subgroup G) (_hK : K.index = 2), K

-- The quotient group H/H′ is a 2-group
instance : Subgroup.Characteristic (InterIndex2 G) := sorry

lemma index_2_contains_squares (H : Subgroup G) (H2 : H.index=2) (g : G) :
  g * g ∈ H := by
  apply Subgroup.mul_self_mem_of_index_two
  exact H2

lemma index_InterIndex2 : ∃ k : ℕ, (InterIndex2 G).index = 2^k := sorry

-- H′ intersected with S is not trivial
lemma div_two_odd_1 (n : ℕ) (hn : Odd n) : n ∣ 2 → n = 1 := by
  intro h
  have hn1 : n ∣ 2 := by
    exact h
  apply Nat.le_of_dvd at hn1
  apply div_two_1or2 at h
  cases h with
  | inl h => exact h
  | inr h => rw [h] at hn
             contradiction
  exact zero_lt_two

lemma index2_normal (H : Subgroup G) (h2 : H.index = 2) : H.Normal := by
  rw [normal_iff_eq_cosets]
  intro g
  by_cases hg : g ∈ H
  · rw [leftCoset_mem_leftCoset]
    rwa [rightCoset_mem_rightCoset]
    exact hg
  · sorry

lemma index_2_contains_odd_elements (H : Subgroup G) (H2: H.index = 2) :
  ∀(g : G), Odd (orderOf g) → g ∈ H := by
  intro g hg
  have hN : H.Normal := by
    apply index2_normal
    exact H2
  set gH := ((QuotientGroup.mk' H) g)
  have hdvd : orderOf ((QuotientGroup.mk' H) g) ∣ (orderOf g) := by
    apply ord_gH_div_ord_g
  have hordgH : Odd (orderOf gH) := by
    apply Odd.of_dvd_nat hg hdvd
  have hdvdh : orderOf gH ∣ H.index := by
    rw [Subgroup.index_eq_card]
    apply orderOf_dvd_card
  have hgH1 : (orderOf gH) = 1 := by
    rw [H2] at hdvdh
    apply div_two_odd_1
    exact hordgH
    exact hdvdh
  rw [orderOf_eq_one_iff] at hgH1
  rw [← QuotientGroup.eq_one_iff]
  exact hgH1

lemma pow_two_odd_1 (n : ℕ) (k : ℕ) (h2 : n = 2^k) : Odd n → k=0 := by
  contrapose!
  intro h
  have hdvd2 : 2 ∣ n := by
    rw [h2]
    apply dvd_pow_self
    exact h
  rwa [← even_iff_two_dvd, Nat.even_iff_not_odd] at hdvd2

lemma Sylow_in_H_odd_index (H : Subgroup G) [H.Normal] (Geven : Even (Fintype.card G)) (Hodd : Odd H.index) (S : Sylow 2 G):
  S ≤ H := by
  intro s hs
  have hS2group : IsPGroup 2 (S : Sylow 2 G) := by
    apply Sylow.isPGroup'
  have hcardS : ∃ m : ℕ, Fintype.card (S : Sylow 2 G) = 2^m := by
    rw [IsPGroup.iff_card] at hS2group
    exact hS2group
  obtain ⟨m, hm⟩ := hcardS
  have hsdvdS : orderOf s ∣ 2^m := by
    rw [← hm, ← Nat.card_eq_fintype_card]
    apply Subgroup.orderOf_dvd_natCard at hs
    exact hs
  have hs : ∃ n ≤ m, orderOf s = 2^n := by
    rw [Nat.dvd_prime_pow] at hsdvdS
    exact hsdvdS
    exact Nat.prime_two
  obtain ⟨n, hnm, hn⟩ := hs
  set sH := ((QuotientGroup.mk' H) s)
  have hdvd : orderOf sH ∣ (orderOf s) := by
    apply ord_gH_div_ord_g
  have hsH : ∃ k ≤ n, orderOf sH = 2^k := by
    rw [hn] at hdvd
    rw [Nat.dvd_prime_pow] at hdvd
    exact hdvd
    exact Nat.prime_two
  obtain ⟨k,hkn,hk⟩ := hsH
  have hsHodd : Odd (orderOf sH) := by
    have horddvd : orderOf sH ∣ H.index := by
      rw [Subgroup.index_eq_card]
      apply orderOf_dvd_card
    apply Odd.of_dvd_nat at horddvd
    exact horddvd
    exact Hodd
  have hk0 : k=0 := by
    apply pow_two_odd_1 at hk
    apply hk at hsHodd
    exact hsHodd
  have hsHord : orderOf sH = 1 := by
    rw [hk0] at hk
    rw [pow_zero] at hk
    exact hk
  rw [orderOf_eq_one_iff] at hsHord
  rw [← QuotientGroup.eq_one_iff]
  exact hsHord

lemma G_even_order : 2 ∣ (Fintype.card G) := by
  obtain ⟨ι,hι⟩ := Centralizer_involution (G := G)
  have hι2 : orderOf ι = 2 := by
    exact hι.1
  rw [← hι2]
  exact orderOf_dvd_card

lemma intersect_Sylow_empty_odd_order (H : Subgroup G) [HN: H.Normal] (S : Sylow 2 G) :
  (H ⊓ S = ⊥) → Odd (Fintype.card H) := by
  contrapose!
  intro h
  simp at h
  have h2 : 2 ∣ Fintype.card H := by
    exact Even.two_dvd h
  obtain ⟨ι,hι⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hdvd : 2 ∣ (Fintype.card G) := by
    apply G_even_order
  have hS2 : 2 ∣ Fintype.card S := by
    convert S.dvd_card_of_dvd_card hdvd
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card 2 hS2
  have := involutions_conjugated G ι s ?_ ?_
  rw [isConj_iff] at this
  obtain ⟨c, hc⟩ := this
  have hin : c * ι * c⁻¹ ∈ H := by
    apply Subgroup.Normal.conj_mem
    exact HN
    simp
  rw [hc] at hin
  have hsand : (↑s ∈ H) ∧ (↑s ∈ S) := by
    simp
    exact hin
  have hint : ↑s ∈ (H ⊓ S) := by
    rw [Subgroup.mem_inf]
    exact hsand
  rw [← Subgroup.nontrivial_iff_ne_bot,nontrivial_iff]
  use 1, ⟨s, hint⟩
  have h1s : 1 ≠ (↑s) := by
    intro hneq
    apply_fun orderOf at hneq
    rw [hs,orderOf_one] at hneq
    contradiction
  simp at h1s
  simp [Subtype.ext_iff]
  simp [Subtype.ext_iff_val] at h1s
  exact h1s
  simpa
  simpa

-- lemma intersect_Hacc_S_non_triv
lemma intersect_Hacc_S_non_triv (H : Subgroup G) [H.Normal] (Hodd : Odd H.index) (S : Sylow 2 G):
  (InterIndex2 G) ⊓ S ≠ ⊥ := by
  intro HS
  have Haccnorm : (InterIndex2 G).Normal := by
    have Haccchar : (InterIndex2 G).Characteristic := by
      apply Hacc_char
    sorry
  have Haccodd : Odd (Fintype.card (InterIndex2 G)) := by
    apply intersect_Sylow_empty_odd_order
    simpa
  have Hacc1 : (InterIndex2 G) = ⊥ := by
    apply normal_odd_ord_subgroup_trivial
    exact Haccodd
  have Helodd : ∀ h : H, Even (orderOf h) := by
    sorry
  sorry

-- No proper normal subgroups of G of odd index
theorem normal_odd_ind_subgroup_G (H : Subgroup G) [H.Normal] (Hodd : Odd H.index) :
  H = ⊤ := by
  let S : Sylow 2 G := default
  have SH : S ≤ H := by
    apply Sylow_in_H_odd_index
    exact Hodd
  have HStriv : (InterIndex2 G) ⊓ S ≠ ⊥ := by
    sorry
  have HSinv : ∃ i ∈ ((InterIndex2 G) ⊓ S), orderOf i ≠ 1 := by
    rw [← Subgroup.nontrivial_iff_ne_bot] at HStriv
    rw [nontrivial_iff] at HStriv
    obtain ⟨x,y,hxy⟩ := HStriv
    sorry
  obtain ⟨i,hi⟩ := HSinv
  have iord : orderOf i = 2 := by
    sorry
  have SinH : S ≤ (InterIndex2 G) := by
    sorry
  have Hquot : Odd (InterIndex2 G).index := by
    sorry
  have H2 : ∃ k : ℕ, (InterIndex2 G).index = 2^k := by
    apply index_InterIndex2
  have H1 : (InterIndex2 G).index = 1 := by
    obtain ⟨k,hk⟩ := H2
    rw [hk] at Hquot
    sorry
  have HH : (InterIndex2 G) = ⊤ := by
    rwa [Subgroup.index_eq_one] at H1
  have Hjanko : IsJanko1 H := by
    have Hind2 : ∀(H: Subgroup G), H.index ≠ 2 := by
      sorry
    sorry
--  set NH := Subgroup.normalizer (S : Subgroup H)
  set NG := Subgroup.normalizer (S : Subgroup G)
  sorry

-- Proof of theorem

-- G is non-trivial
instance : Nontrivial G where
  exists_pair_ne := by
    obtain ⟨ι,hι⟩ := Centralizer_involution (G := G)
    use ι, 1
    intro h
    apply_fun orderOf at h
    rw [hι.1,orderOf_one] at h
    contradiction


lemma index_odd_of_contains_order_2
    (H : Subgroup G) [H.Normal] (hH: ∀ g : G, orderOf g = 2 → g ∈ H) : Odd H.index := by
     sorry

/-- A group of Janko 1 type is simple. -/
instance : IsSimpleGroup G where
  eq_bot_or_eq_top_of_normal := by
    intro H H_normal
    by_cases Hord_odd : Odd (Fintype.card H)
    · left
      apply normal_odd_ord_subgroup_trivial
      assumption
    by_cases Hind_odd : Odd H.index
    · right
      apply normal_odd_ind_subgroup_G
      assumption
    exfalso
    simp only [Nat.odd_iff_not_even, not_not] at Hord_odd Hind_odd
    -- obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
    have h2 : 2 ∣ Fintype.card H := by
      exact Even.two_dvd Hord_odd
    suffices Odd H.index by
      simp only [Nat.odd_iff_not_even] at this
      contradiction
    obtain ⟨ι,hι⟩ := exists_prime_orderOf_dvd_card 2 h2
    apply index_odd_of_contains_order_2
    intro g hg
    have := involutions_conjugated G ι g ?_ hg
    rw [isConj_iff] at this
    obtain ⟨c, hc⟩ := this
    rw [← hc]
    apply H_normal.conj_mem
    simp
    simpa

end IsJanko1
