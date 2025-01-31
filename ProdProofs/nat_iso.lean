
import Mathlib.NumberTheory.PrimeCounting
import ProdProofs.defs

namespace ProdProofs

example : prod_num.pli [prod_num.pli []] = prod_num.pli [prod_num.pli [], prod_num.p0] :=
  by
    have h1 : prod_num.pli [prod_num.pli []] = prod_num.pli ([prod_num.pli []] ++ [prod_num.p0]) := by rw [← prod_pad]
    rw [h1]
    simp




-- Nat conversion

lemma eval_prod_prod_factor_2_eq (n : Nat):  Nat.factorization (eval_prod (prod_factor n)) 2 = Nat.factorization n 2 := by
  induction n using Nat.case_strong_induction_on

  . sorry
  . sorry


lemma eval_prod_prod_factor_eq (n : Nat) : eval_prod (prod_factor n) = n := by
  induction n using Nat.recOnPrimePow
  case h0 => rw [prod_factor, eval_prod]
  case h1 => rw [prod_factor, eval_prod, eval_prod.eval_list]
  case h n p a hp h_div h0_le ih =>
    --WTS: E P (p^a * n) = p^ a * n , given E P n = n and coprime p nodiv n
    let m := p ^ a * n

    sorry

lemma eval_prod_prod_factor_eq_strong (n : Nat) : eval_prod (prod_factor n) = n := by
  induction n using Nat.strongRecOn
  rename_i n2 h
  cases n2
  . rw [prod_factor, eval_prod]
  .sorry


theorem unique_representation (n : Nat) : ∃! p : prod_num, eval_prod p = n := by
  induction n using Nat.caseStrongRecOn
  . apply ExistsUnique.intro (prod_num.p0)
    rw [eval_prod]
    sorry
  . rename_i n h
    sorry -- unique factorization stuff







lemma eval_prod_prod_factor_pn (p n m : Nat) (hp : Nat.Prime p) (hn: 0 < n) (hm : m = p ^ n): eval_prod (prod_factor m) = m := by
  rw [prod_factor.eq_def]
  simp
  split
  case h_1 => rw [eval_prod]
  case h_2 => rw [eval_prod, eval_prod.eval_list]
  case h_3 x2 n2 hneq =>
    simp
    sorry


lemma eval_prod_prod_factor_eq_recComprime (n : Nat) : eval_prod (prod_factor n) = n := by
  induction n using Nat.recOnPosPrimePosCoprime
  case h0 => rw [prod_factor, eval_prod]
  case h1 => rw [prod_factor, eval_prod, eval_prod.eval_list]
  case hp p n hp2 hn =>
    let pn := p ^ n ; rw [← pn]
    --rw [← pn]
    sorry
  case h n m hnpos hmpos hco ha hb =>
    sorry



lemma zero_lt_prime_pow_eval_prod (i: Nat) (p : prod_num) : 0 < prime_at i ^ eval_prod p := by
  apply Nat.one_le_pow
  have hp : Nat.Prime (prime_at i) := by
    simp [prime_at]
  exact Nat.Prime.pos hp




lemma eval_list_geq_one (ps: List prod_num) (i: Nat) : eval_prod.eval_list ps i ≥ 1 := by
  induction ps
  case nil =>
    rw [eval_prod.eval_list.eq_def]
  case cons =>
    rename_i head tail ih_tail
    rw [eval_prod.eval_list.eq_def]
    simp
    have prod_tail_i_plus_one : 1 ≤ eval_prod.eval_list tail (i+1) := by
      sorry
    have left_geq_one : prime_at i ^ eval_prod head ≥ 1 := by
      apply Nat.one_le_pow



lemma prod_factor_eval_prod_eq (p: prod_num) : prod_factor (eval_prod p) = p := by
  induction p using prod_num.induction_on
  case hp0 =>
    rw [eval_prod, prod_factor]
  case hpli ps ih =>
    rw [eval_prod, eval_prod.eval_list.eq_def]
    split
    . simp [prod_factor]
    . rename_i _ x xs
      rw [prod_factor.eq_def]
      split
      . rename_i heq
        simp at heq
        sorry
      . sorry





def nat_prod_equiv : Nat ≃ prod_num where
  toFun := prod_factor
  invFun := eval_prod
  left_inv := eval_prod_prod_factor_eq
  right_inv := prod_factor_eval_prod_eq


end ProdProofs
