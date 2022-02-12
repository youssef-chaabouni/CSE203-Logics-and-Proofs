(* --------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Set Printing Coercions.

(* --------------------------------------------------------------------- *)
(* The goal of this project is to develop a minimal library for          *)
(* arbitrary-precision arithmetic, also called bignums.                  *)
(*                                                                       *)
(* Arbitrary-precision arithmetic refers to the set of techniques used   *)
(* to manipulate numbers (mainly integers or rational) of arbitrary size *)
(* in a computer program. Arbitraty-precision arithmetic is opposed      *)
(* fixed-precision arithmetic (found in most arithmetic logic unit       *)
(* (ALU) hardware) and that deals only with 32 or 64 bit numbers.        *)
(*                                                                       *)
(* Several modern programming languages have built-in support for        *)
(* bignums (e.g. Python or Coq with the type `nat`), and various         *)
(* libraries provide efficient data structures and operations for        *)
(* arbitrary-precision computing.                                        *)
(*                                                                       *)
(* In most bignum libraries, rather than storing values as a fixed       *)
(* number of bits related to the size of the processor register, they    *)
(* typically use a variable-length arrays of machine words.              *)
(*                                                                       *)
(* For example, on a 32-bit machine, one (unsigned) machine word can     *)
(* store integers from 0 to 2^32 (excluded). If we want to store an      *)
(* integer greater or equal than 2^32, we have to use at least two       *)
(* machine words. For example, if we use exactly two machine words       *)
(* w0 & w1, we have then 64 bits at our disposal and can therefore       *)
(* store integers from 0 to 2^64 (excluded).                             *)
(*                                                                       *)
(* One way to do this is to use a base 2^32 numbering system where `w0`  *)
(* is the units digit and `w1` the tens digit. Thus, the pair of machine *)
(* words `(w0, w1)` represents the number `w0 + 2^32 * w1`.              *)
(*                                                                       *)
(* If we need to store a number larger or equal than `2^64`, we can use  *)
(* a third digit `w2`. In this case, `w2` plays the role of the hundreds *)
(* digit and the triplet (w0, w1, w2) represents the integer             *)
(* `w0 + 2^32 * w1 + 2^(2*32) * w2`. Using three words, we can then      *)
(* represent numbers up to 2^96 (excluded).                              *)
(*                                                                       *)
(* In the case of a bignum library, to represent integers, we use a      *)
(* variable-length array (or list) of machine words. Such a list `ws`    *)
(* represents the integer:                                               *)
(*                                                                       *)
(*    \sum_(0 <= i < |ws|) 2^(i*32) * ws_i                               *)
(*                                                                       *)
(* where `|ws|` is the length of the list `ws` and `ws_i` is the i-th    *)
(* element of `ws`.                                                      *)

(* --------------------------------------------------------------------- *)
(* In this project, to represent bignum, we will use lists of machine    *)
(* words of size `(8 * size)`, where `size` is some positive natural     *)
(* number that represents the size (in bytes) of the hardware            *)
(* machine-word:                                                         *)

Context
  (size     :  nat)
  (gt0_size :  (0 < size)%N)
  (wsize    := 2 ^ (8 * size))
  (word     := 'Z_wsize)
  (bignum   := seq word).

(* -------------------------------------------------------------------- *)
(* We provide some basic results on `wsize`                             *)

Lemma gt1_wsize : 1 < wsize.
Proof.
rewrite /wsize -{1}[1](expn0 2) ltn_exp2l // lt0n.
by rewrite muln_eq0 /= -lt0n gt0_size.
Qed.

Hint Extern 0 (is_true (1 < wsize)) => exact: gt1_wsize : core.

Lemma gt0_wsize : 0 < wsize.
Proof. by apply: (@leq_trans 2). Qed.

Hint Extern 0 (is_true (0 < wsize)) => exact: gt0_wsize : core.

(* Here, 'Z_p is the type of integers modulo `p` that provides a good    *)
(* absraction of what a machine word is. You can use the standard ring   *)
(* operations on values of type 'Z_p.                                    *)

(* Note: the command above is equivalent to:                             *)
(*                                                                       *)
(*   Parameter  (size : nat).                                            *)
(*   Hypothesis (gt0_size : (0 < size)%N)                                *)
(*                                                                       *)
(*   Definition wsize  := 2 ^ (8 * size).                                *)
(*   Definition word   := 'Z_wsize.                                      *)
(*   Definition bignum := seq word.                                      *)

(* --------------------------------------------------------------------- *)
(* In this project, you might want to convert values between natural     *)
(* numbers and words. For that purpose, you can use the `toword` and     *)
(* nat_of_ord operators:                                                 *)

Notation toword n := (inord n : word) (only parsing).

Lemma towordK (n : nat) : n < wsize -> nat_of_ord (toword n) = n.
Proof.
by move=> le; rewrite inordK // !prednK // ltn_predRL.
Qed.

Lemma ofwordK (w : word) : toword (nat_of_ord w) = w.
Proof. by rewrite inord_val. Qed.

Lemma ltn_nat_of_ord (w : word) : nat_of_ord w < wsize.
Proof. by case: w => /= w; rewrite !prednK // ltn_predRL. Qed.

(* --------------------------------------------------------------------- *)
(* In the course of this project, you might want to use the following    *)
(* lemmas about natural integer arithmetic:                              *)
(*                                                                       *)
(*   addn0, add0n, addnC, addnA                                          *)
(*   muln0, mul0n, mulnC, mulnA                                          *)
(*   muln1, mul1n, mulnS                                                 *)
(*                                                                       *)
(* You can do a `Check lemma_name` do this what `lemma_name` proves.     *)
(*                                                                       *)
(* As a general note, if you are stuck because you are missing some      *)
(* basic properties about natural numbers, just put it as an axiom and   *)
(* go forward.                                                           *)

(* ===================================================================== *)
(* Changing the representation (nat <-> bignum)                          *)
(* ===================================================================== *)

(* In this first part, we will write the conversion functions between    *)
(* the natural numbers (the values of type `nat`) and the type           *)
(* `bignum`, as well as proving different results about them. These      *)
(* functions will allow us later to state the correctness lemmas of      *)
(* the implementations of the arithmetic operations.                     *)

(* 1. Implement the function `bn2nat` s.t. `bn2nat z` returns the        *)
(*    natural number represented by the bignum `z`, i.e.                 *)
(*                                                                       *)
(*    bn2nat z := z_0 + z_1 * 2^32 + z_2 * 2^64 + ... + 2_n * 2^(n*32)   *)
(*                                                                       *)
(* Values of type 'Z_p are automatically converted to `nat` when needed. *)
(* However, you can force the conversion using the function              *)
(* `nat of ord`.                                                         *)
(*                                                                       *)
(* (In all the question asking you to define a fuction, you are free to  *)
(* change `Definition` to `Fixpoint` if needed).                         *)

Fixpoint bn2nat (z : bignum) : nat :=
(* We follow the Horner scheme *)
  match z with
  | nil => 0
  | cons n l => n + wsize * (bn2nat l)
  end.

(* 2. Implement the function `nat2bn` s.t. `nat2bn n` computes the       *)
(*    bignum that represents the natural number `n`.                     *)
(*                                                                       *)
(* In this function, you can use the following operations:               *)
(*                                                                       *)
(*   - n %% p : computes `n` modulo `p` for `(n p : nat)`                *)
(*   - n %/ p : computes the quotient of the division of `n` by `p`      *)
(*                                                                       *)

(* In this lemma, you might want to use `divn_eq`                        *)
(*                                                                       *)
(*   divn_eq                                                             *)
(*     : forall m d : nat, m = m %/ d * d + m %% d                       *)
(*                                                                       *)
(* We also provide the following lemma:                                  *)

Lemma nat2bn_help1 n p : n < p.+1 -> n.+1 %/ wsize <= p.
Proof.
move/leq_div2r => /(_ wsize) /leq_trans; apply.
case: p => [|p]; first rewrite divn_small //.
have := leq_divDl wsize p.+1 1; rewrite addn1.
move/leq_trans; apply; rewrite [1%/_]divn_small //.
rewrite addn0 addn1; apply: ltn_Pdiv => //.
Qed.

(* Checking syntax *)

Eval compute in [::2 & [::5]].
Eval compute in [::3 & [::2 & [::5]]].


(* We rely on a recursive implementation using fuel as a second argument to 
garantee that our function terminates *)
Fixpoint nat2bn_aux (n m : nat) : bignum :=
(* We follow the Horner scheme *)
  match n, m with
  | _, 0 => [::]
  | 0, _ => [::]
  | S k, S m => [::(inord (n %% wsize)) & (nat2bn_aux (n %/ wsize) m)]
  end.



Definition nat2bn (n : nat) : bignum :=
(* We use n as fuel because we know that the number of words in the bignum
representation (i.e. number of digits in base wsize) is less than n *)
  nat2bn_aux n n.

(* 3. Prove that `nat2bn` and `bn2nat` are self-invert.                  *)
(*                                                                       *)
(*    Such a result is sufficient to prove that you have a               *)
(*    correct & complete representation of arbitrary-precision           *)
(*    numbers:                                                           *)
(*                                                                       *)
(*      - you can represent any natural number using a bignum, and       *)
(*      - two different bignums never represent the same number.         *)
(*                                                                       *)

(* The following are two known facts about the euclidean division *)
Axiom div_euc: forall a b, a%%b + b * (a%/b) = a.
Axiom div_euc_mod: forall a b, a%%b < b.

Lemma nat2bnK_aux : forall m n, m >= n -> (bn2nat (nat2bn_aux n m)) = n.
(*
In order to prove that (bn2nat (nat2bn_aux n n)) = n (i.e. cancel nat2bn bn2nat),
we start by proving a stronger statement: 
    forall m such that m >= n, we have (bn2nat (nat2bn_aux n m)) = n
*)
Proof.
(* Induction on m *)
elim => [|m].
(* Base case *)
  (* We proceed using an induction on n *)
  elim => [|n].
  done.
  done.
(* Inductive case m *)
  move => h1.
  move => n1.
  (* Case analysis on n *)
  (* We are trying to make the codition of nat2bn_help1 appear *)
  case: n1.
  (* Base case *)
    done.
  (* Inductive case *)
    move => n2.
    move => h2.
    (* Now that we have a condition of the form n2 < m+1, we can use nat2bn_help1 *)
    move/nat2bn_help1:h2.
    move => h3.
    (* Now that we have n2.+1 %/ wsize <= m, we can use the induction hypothesis we
    have from the initial induction on m. *)
    move/h1:h3.
    move => h4.
    simpl.
    rewrite h4.
    (* Here we need to change the word inord (n2.+1 %% wsize) to the nat 
    n2.+1 %% wsize using the helper function towordK *)
    rewrite towordK.
    (* And those are exactly the Euclidean division properties *)
    exact (div_euc (n2.+1) wsize).
    exact (div_euc_mod (n2.+1) wsize).
Qed.

Lemma nat2bnK : cancel nat2bn bn2nat.
Proof.
move => n.
apply nat2bnK_aux.
done.
Qed.


(* --------------------------------------------------------------------- *)
(* !! OPTIONAL                                                           *)

Definition canon (z : bignum) :=
  if rev z is x :: _ then x != 0%R else true.

Lemma bn2natK (z : bignum) :
  canon z -> nat2bn (bn2nat z) = z.
Proof. Admitted.

(* ===================================================================== *)
(* Addition of bignums                                                   *)
(* ===================================================================== *)

(* We are now interested in adding bignums: given `z1 z2 : bignum`, we   *)
(* want to compute a bignum `bnadd z1 z2` s.t.                           *)
(*                                                                       *)
(*   bn2nat z = bn2nat z1 + b2nat z2                                     *)
(*                                                                       *)
(* Of course, one could directly use the arithmetical operations of      *)
(* `nat` to implement `bn2nat`, i.e.                                     *)
(*                                                                       *)
(*   Definition bn2nat (z1 z2 : bignum) : bignum :=                      *)
(*     bn2nat (nat2bn z1 + nat2bn z2).                                   *)
(*                                                                       *)
(* However, using a bignum library to implement a bignum library would   *)
(* totally defeat the purpose of this project. AS SUCH, IN ALL THIS      *)
(* PROJECT, IT IS STRICTLY FORBIDDEN TO USE THE ARTIHMTIC OF NAT TO      *)
(* IMPLEMENT THE BIGNUM OPERATIONS.                                      *)

(* Instead, we need to come with a way to implement them by only         *)
(* resorting on the machine word arithmetic operations. For addition,    *)
(* the best algorithm is simply the school-book addition that you all    *)
(* learnt in elementary school (here given in pseudo-code):              *)
(*                                                                       *)
(*   proc bnadd(z1 : bignum, z2 : bignum) : bignum {                     *)
(*     n : nat    <- max (size z1, size z2)                              *)
(*     z : bignum <- [::]                                                *)
(*     c : carry  <- false                                               *)
(*                                                                       *)
(*     for i = 0 to n-1 {                                                *)
(*       c, w <- word_add_with_carry(z1_i, z2_i, c)                      *)
(*       z    <- z ++ [:: w]                                             *)
(*     }                                                                 *)
(*     if (c) {                                                          *)
(*       z <- z ++ [:: 1]                                                *)
(*     }                                                                 *)
(*     return z                                                          *)
(*   }                                                                   *)
(*                                                                       *)
(* where `word_add_with_carry(w1, w2, c)` returns a pair `(c2, w)`       *)
(* where `w` is the result of the addition of `w1 + w2 + c` (using       *)
(* modular arithmetic) and `c` is a carry flag (a boolean) that          *)
(* indicates wether an integer overflow occured. Also, to ease the       *)
(* presentation, note that we assumed that `z_i` is the machine word `0` *)
(* when `i` is out of bounds.                                            *)
(*                                                                       *)
(* The operation `word_add_with carry` is something that is provided by  *)
(* the  ALU of the hardware, and we will assume given its                *)
(* implementation:                                                       *)

Context (word_add_with_carry : word -> word -> bool -> bool * word).

Axiom word_add_with_carry_correct :
  forall (w1 w2 : word) (c : bool),
    let: (c', w) := word_add_with_carry w1 w2 c in
    nat_of_ord w1 + nat_of_ord w2 + nat_of_bool c = w + (nat_of_bool c') * wsize.

(* 4. Implement the function `bnadd` that computes the addition of two   *)
(*    bignums, using the algorithm given above.                          *)

(* We rely on a recursive implementation using fuel as a second argument to 
garantee that our function terminates *)
Fixpoint bnadd_aux (z1 z2 : bignum) (n : nat) : bignum :=
  match n, z1, z2 with 
  | 0, _, _ => [::]
  | _, nil, _ => z2
  | _, _, nil => z1
  | S n, cons n1 l1, cons n2 l2 => 
      let: (c, w) := word_add_with_carry n1 n2 false in
        [:: w & bnadd_aux (bnadd_aux l1 l2 n) [::(toword c)] n]
  end.
      
Definition bnadd (z1 z2 : bignum) : bignum :=
(* 
We use (length z1 + length z2) as fuel:
In fact, we know that (length z1 + length z2) >= max(length z1, length z2)
and that the max(length z1, length z2) is enough as fuel because the lengths the each
of z1 and z2 decrease by 1 after each recursive call.
*)
  bnadd_aux z1 z2 (length z1 + length z2)
.

(* 5. Prove that `bnadd` is correct, as stated below.                    *)

(* The following are very specific corollaries of ring operation that we will need 
later: *) 

Axiom distributivity: forall a b c: nat, a*(b+c) = a*b + a*c.

Axiom commutativity: forall a b c d:nat, a + b + c + d = a + d + b + c.

Axiom successor_leq: forall a b n: nat, a.+1 + b.+1 <= n.+1 -> a + b <= n.

Axiom trans1_leq: forall (a b c d : nat),
        (a <= b + 1 ) -> (b <= c + d) -> a < c.+1 + d.+1.

Axiom trans2_leq: forall (a b c d : nat),
        (a <= b + c) -> (b.+1 + c.+1 <= d.+1) -> a + 1 <= d.

Lemma fuel_max: forall n z1 z2, 
        length (bnadd_aux z1 z2 n) <= length z1 + length z2.
Proof.
(* Induction over n: the fuel *)
induction n.
  (* Base case *)
  done.
  (* Inductive case of induction over n *)
  (* Induction over z1 *)
  induction z1.
    (* Base case *)
    done.
    (* Inductive case of induction over z1 *)
    (* Induction over z2 *)
    induction z2.
      (* Base case *)
      simpl.
      rewrite addn0; done.
      (* Inductive case of induction over z2 *)
      simpl.
      (* Taking c and w into the context *)
      case E: word_add_with_carry => [c w].
      simpl.
      (* We use the induction hypothesis IHn with:
          z1 = (bnadd_aux z1 z2 n)
          z2 = [:: inord c]
      *)
      pose proof IHn (bnadd_aux z1 z2 n) [:: inord c] as h0.
      (* We use the induction hypothesis IHn *)
      pose proof IHn z1 z2 as h1.
      (*
      We use a simple corollary of transitivity:
        (a <= b + c) -> (b.+1 + c.+1 <= d.+1) -> a + 1 <= d
      *)
      apply (trans1_leq h0 h1).
Qed.

Lemma bnadd_correct_aux: forall n z1 z2, n >= length z1 + length z2 ->
        bn2nat (bnadd_aux z1 z2 n) = bn2nat z1 + bn2nat z2.
Proof.
(* Induction over n: the fuel *)
induction n.
(* Base case *)
  induction z1.
  induction z2.
  done.
  done.
  done.
(* Inductive case of induction on n*)
  (* Now induction on z1 *)
  case => [| w1 z1].
  (* Base case *)
    move => z2 _.
    induction z2.
    done.
    done.
  (* Inductive case of induction on z1 *)
    (* Now induction on z2 *)
    (* Base case *)
    case => [| w2 z2].
    move => _.
    simpl.
    rewrite addn0.
    done.
    (* Inductive case of induction on z2 *)
    simpl.
    (* Let (c, w) := word_add_with_carry w1 w2 false *)
    case E: word_add_with_carry => [c w].
    (* 
    Now we use the fact that:
          word_add_with_carry_correct w1 w2 false
    (given axiom)
    *)
    have := word_add_with_carry_correct w1 w2 false.
    rewrite E.
    simpl.
    (*Now we use the induction hypothesis *)
    rewrite addn0.
    move => h1 h2.
    rewrite IHn.
    rewrite IHn.
    (* Now we're done. We just need to do some integer manipulations: *)
    rewrite distributivity.
    rewrite distributivity.
    simpl.
    rewrite towordK.
    rewrite muln0; rewrite addn0; rewrite addnA; rewrite addnA; rewrite addnA; rewrite commutativity; rewrite mulnC.
    rewrite -h1.
    ring.
    (* Now we need to prove that c < wsize *)
    case c.
    apply gt1_wsize.
    apply gt0_wsize.
    (* Now we use the fact that (length z1).+1 + (length z2).+1 <= n.+1 *)
    apply successor_leq.
    exact h2.
    simpl.
    (* Now for the last subgoal, we use the lemma we've proven above: fuel_mmax n z1 z2 *)
    pose proof (fuel_max n z1 z2) as h3.
    apply (trans2_leq h3 h2).
Qed.


Lemma bnadd_correct (z1 z2 : bignum) :
  bn2nat (bnadd z1 z2) = bn2nat z1 + bn2nat z2.
Proof. 
apply bnadd_correct_aux.
done.
Qed.

(* ===================================================================== *)
(* Multiplication of bignums                                             *)
(* ===================================================================== *)

(* We are now interested in adding bignums: given `z1 z2 : bignum`, we   *)
(* want to compute a bignum `bnadd z1 z2` s.t.                           *)
(*                                                                       *)
(*   bn2nat z = bn2nat z1 * b2nat z2                                     *)
(*                                                                       *)
(* Here, there exists numerous algorithms for computing the multipli-    *)
(* cation of two bignums, with different complexity (from quadratic to   *)
(* quasi-linear). Here, we are again going to use the school-book        *)
(* algorithm to implement the multiplication of bignums. It has a        *)
(* quadratic complexity and is then avoided in real-word bignum          *)
(* libraries:                                                            *)
(*                                                                       *)
(*   proc bnmul(z1 : bignum, z2 : bignum) : bignum {                     *)
(*     z : bignum <- [::]                                                *)
(*     for i = 0 to (size z2) - 1 {                                      *)
(*       z <- bnadd(z, bnshift(bnmul1(z1, z2_i), i))                     *)
(*     }                                                                 *)
(*     return z                                                          *)
(*   }                                                                   *)
(*                                                                       *)
(*   proc bnmul1(z : bignum, w : word) : bignum {                        *)
(*     aout  : bignum <- [::]                                            *)
(*     carry : word   <- 0                                               *)
(*                                                                       *)
(*     for i = 0 to (size z) - 1 {                                       *)
(*       w1, carry <- dword_mul_with_carry(z_i, w, carry)                *)
(*       aout <- aout ++ [:: w1]                                         *)
(*     }                                                                 *)
(*     if (carry != 0) {                                                 *)
(*       aout <- aout ++ [:: carry]                                      *)
(*     }                                                                 *)
(*   }                                                                   *)
(*                                                                       *)
(*  proc dword_mul_with_carry (w1 : word, w2 : word, carry : word) {     *)
(*    w1, w2 <- dword_mul(w1, w2)                                        *)
(*    c , w1 <- word add with_carry(w1, carry, false)                    *)
(*    if (c) {                                                           *)
(*      _, w2 <- word add with carry(w2, 1, false)                       *)
(*    }                                                                  *)
(*    return (w1, w2)                                                    *)
(*  }                                                                    *)
(*                                                                       *)
(*  proc bnshift(w : bignum, n : nat) : bignum {                         *)
(*    for i = 0 to n-1 {                                                 *)
(*      w <- [:: 0] ++ w                                                 *)
(*    }                                                                  *)
(*    return w                                                           *)
(*                                                                       *)
(* where `dword_mul` does the double-word multiplication, whose speci-   *)
(* fication is given below.                                              *)

Context (dword_mul : word -> word -> word * word).

Axiom dword_mul_correct :
  forall (w1 w2 : word),
    let: (w'1, w'2) := dword_mul w1 w2 in
    nat_of_ord w1 * nat_of_ord w2 = w'1 + w'2 * wsize.

(* 6. Implement the functions `bnshift`, `dword_mul_with_carry`,         *)
(*    `bnmul1` & `bnmul`, using the pseudo-code implementations give     *)
(*    above.                                                             *)

Definition bnshift (z : bignum) (n : nat) : bignum :=
  [::].

Definition dword_mul_with_carry (w1 w2 c : word) : word * word :=
  (inord 0, inord 0).

Definition bnmul1 (z : bignum) (w : word) : bignum :=
  [::].

Definition bnmul (z1 z2 : bignum) : bignum :=
  [::].

(* 7. Prove the following arithmetical property about `bnshift`.         *)

Lemma bnshiftE (z : bignum) (n : nat) :
  bn2nat (bnshift z n) = bn2nat z * (2^(n * (8 * size))).
Proof. Admitted.

(* 8. Prove that `dword_mul_with_carry` implements a double-word         *)
(*    multiplication with carry, as stated below.                        *)

Lemma dword_mul_with_carry_correct (w1 w2 c : word) :
  let: (w'1, w'2) := dword_mul_with_carry w1 w2 c in
  bn2nat [:: w'1; w'2] = val w1 * val w2 + val c.
Proof. Admitted.

(* 9. Prove that `bnmul1` implements a bignum by word multiplication,    *)
(*    as stated below.                                                   *)

Lemma bnmul1_correct (z : bignum) (w : word) :
  bn2nat (bnmul1 z w) = bn2nat z * val w.
Proof. Admitted.

(* 10. Prove the correctness of `bnmul`, as stated below.                *)

Lemma bnmul_correct (z1 z2 : bignum) :
  bn2nat (bnmul z1 z2) = bn2nat z1 * bn2nat z2.
Proof. Admitted.
