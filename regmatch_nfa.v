From mathcomp Require Import all_ssreflect.
From RegLang Require Import setoid_leq misc nfa dfa minimization languages regexp.

From RegMatch Require Import regexp regmatch regmatch_reglang.

Section RegLangNFA.

Variable char : finType.

Definition nfa_void : nfa char :=
  {| nfa_s := @set0 char; nfa_fin := set0; nfa_trans p a q := false |}.

Lemma nfa_void_correct: nfa_lang (nfa_void) =i pred0.
Proof.
  move => w. apply/idP.
  rewrite /= inE => H_e.
  move/exists_inP: H_e => [x H_e] H_v.
  move: H_e.
  by rewrite inE.
Qed.

Lemma plus_nfa_void : forall N : nfa char, nfa_lang (nfa_plus N nfa_void) =i nfa_lang N.
Proof.
move => N w.
rewrite nfa_plus_correct.
apply/plusP.
rewrite nfa_void_correct /= inE.
case: ifP; first by left.
move/exists_inP => H_x H_n.
case: H_x.
case: H_n => //.
exact/exists_inP.
Qed.

Definition nfa_char_conc (c : char) (N : nfa char) : nfa char :=
  {| nfa_s := [set q | match q with inl tt => true | inr q => false end];
     nfa_fin := [set q | match q with inl q => false | inr q => q \in nfa_fin N end ];
     nfa_trans p a q := match p,a,q with
                       | inl p,a,inr q => (a == c) && (q \in nfa_s N)
                       | inr p,a,inr q => nfa_trans p a q
                       | _,_,_ => false
                       end |}.

Lemma nfa_char_conc_correct (c : char) (N : nfa char) :
  nfa_lang (nfa_char_conc c N) =i conc (atom c) (nfa_lang N).
Proof.
move => w. apply/idP/idP.
- case/exists_inP; case.
  * case.
    rewrite inE => H_tt.
    case: w => [|c' w] //=; first by rewrite inE.
    move/exists_inP; case => //; case => //.
    move => b.
    move/andP => [H_c H_b].
    move/eqP: H_c => H_eq.
    rewrite H_eq => H_acc.
    apply/concP.
    exists [:: c], w; split => //=.
    split; first by rewrite inE.
    rewrite /nfa_lang.
    rewrite inE.
    apply/exists_inP.
    exists b; first by [].
    move: H_acc.
    clear.
    move: b.
    elim: w => //=.
    + move => b.
      by rewrite inE.
    + move => c' w IH b.
      move/exists_inP => [x H_x]; case: x H_x; first by case.
      move => b' H_tr H_acc.
      apply/exists_inP.
      exists b'; first by [].
      exact: IH.
  * by move => b; rewrite inE.
- move/concP => [w1 [w2 [H_w [H_in H_in']]]].
  subst.
  rewrite inE.
  rewrite inE in H_in.
  case: w1 H_in => //.
  move => c' w.
  move/eqP.
  case: w => //.
  case => H_eq.
  subst.
  apply/exists_inP.
  exists (inl tt); first by rewrite inE.
  move/exists_inP: H_in' => [b H_b] H_acc.
  apply/exists_inP.
  exists (inr b).
  * by rewrite /=; apply/andP.
  * rewrite -/(nfa_accept _ _).
    move: w2 b H_acc {H_b}.
    elim => [|c' w IH] b; first by rewrite /= inE.
    move/exists_inP => [b' H_b'].
    rewrite -/(nfa_accept _ _) => H_acc.
    apply/exists_inP.
    by exists (inr b'); last exact: IH.
Qed.

(*
Fixpoint nfa_residual (r : regexp char) : nfa char :=
if r is Eps
then nfa_eps char 
else if r is Void
then nfa_void
else
  foldl
    (fun N c => 
       let: exist res _ := residuals (r, c) in       
       foldl
         (fun M r0 => 
            let nfa_r0 := nfa_eps char in
            nfa_plus (nfa_char_conc c nfa_r0) M) 
         N res)
    nfa_void (enum char).

Definition dfa_residual (r : regexp char) : dfa char :=
nfa_to_dfa (nfa_residual r).

Lemma dfa_residual_correct : forall r, nfa_lang (nfa_residual r) =i dfa_lang (dfa_residual r).
Proof. by move => r; apply nfa_to_dfa_correct. Qed.

Definition min_dfa_residual (r : regexp char) : dfa char :=
minimize (dfa_residual r).

Lemma min_dfa_residual_correct : forall r, nfa_lang (nfa_residual r) =i dfa_lang (min_dfa_residual r).
Proof.
move => r.
rewrite /min_dfa_residual.
move => w.
rewrite minimize_correct.
exact: dfa_residual_correct.
Qed.

Lemma min_dfa_residual_minimal : forall r, minimal (min_dfa_residual r).
Proof.
move => r.
exact: minimize_minimal.
Qed.
*)

Lemma c_w_residual : forall w c (r : regexp char),
    (c :: w \in re_lang r) = (w \in residual c (re_lang r)).
Proof.
move => w c r.
by split; rewrite inE.
Qed.

Definition residual_eq_mem (c : char) (L1 L2 : dlang char) :=
residual c L1 =i residual c L2.

Lemma residual_eq_mem_all :
  forall L1 L2, ([::] \in L1) = ([::] \in L2) -> (forall c, c \in enum char -> residual_eq_mem c L1 L2) -> L1 =i L2.
Proof.
move => L1 L2 H_eps H_c w.
case: w => [|c' w] //=.
have H_in: c' \in enum char by apply mem_enum.
apply H_c in H_in.
exact/(H_in w).
Qed.

(*(forall w, w \in residual c (nfa_lang N) -> exists r, r \in l /\ w \in (re_lang r))*)

Fixpoint nfa_constr_l (c : char) (l : seq (regexp char)) : 
  (forall r, r \in l -> { M | re_lang r =i nfa_lang M }) ->
  { N | (forall r, r \in l -> forall w, w \in re_lang r -> w \in residual c (nfa_lang N)) /\
        (forall w, w \in nfa_lang N -> exists w', w = c :: w' /\ exists r, r \in l /\ w' \in re_lang r) }.
refine
  (fun nfa_constr_rec =>
     match l as l0 return l = l0 -> _ with
     | [::] => fun H_eq => exist _ nfa_void _
     | r :: l' => 
       fun H_eq =>
         let: exist M H_rM := nfa_constr_rec r _ in
         let: exist N H_rN := nfa_constr_l c l' _ in
         exist _ (nfa_plus (nfa_char_conc c M) N) _
     end (refl_equal _)); rewrite ?H_eq.
- split => //=.
  move => w.
  move/exists_inP => [w' H_w'].
  by rewrite inE in H_w'.
- by rewrite inE; apply/orP; left.
- move => r' H_r'.
  apply nfa_constr_rec.
  rewrite H_eq inE.
  apply/orP.
  by right.
- move: H_rM H_rN => /= H_rM [H_rN1 H_rN2]; split.
  * move => r'; rewrite inE.
    move/orP; case.
    + move/eqP => H_r'; subst.
      move => w H_r.
      rewrite inE nfa_plus_correct.
      apply/plusP.
      left.
      rewrite nfa_char_conc_correct.
      apply/concP.
      exists [:: c], w; split => //=; split => //; first by rewrite inE.
      by rewrite -(H_rM w).
    + move => H_r' w H_w.
      rewrite inE nfa_plus_correct.
      apply/plusP.
      right.
      move: H_w.
      exact: H_rN1.
  * move => w.
    rewrite nfa_plus_correct.
    move/plusP.
    case.
    + rewrite nfa_char_conc_correct.
      move/concP => [w1 [w2 [H_w12 [H_wa H_n]]]].
      move: H_wa.
      rewrite inE /=.
      move/eqP: H_w12.
      case: w1 => //= c'.
      case => [|c0 w1] //=; last by move => H_eq'; move/eqP.
      move/eqP => H_w.
      move/eqP => H_c.
      injection H_c => H_c'.
      subst.
      exists w2; split => //.
      exists r; split; first by rewrite inE; apply/orP; left.
      by rewrite (H_rM w2).
    + move/H_rN2 => [w' [H_w' [r' [H_in H_r']]]].
      exists w'; split => //=.
      exists r'; split => //.
      rewrite inE.
      apply/orP.
      by right.
Defined.

(*
Definition nfa_constr_t (r : regexp char) (c : char) :=
{ N | residual_eq_mem c (re_lang r) (nfa_lang N) }.
*)

Definition nfa_constr_res (r : regexp char) (c : char) :
 (forall r', {subset re_lang r' <= residual c (re_lang r)} -> { M | re_lang r' =i nfa_lang M }) ->
 { N | residual_eq_mem c (re_lang r) (nfa_lang N) }.
refine (fun nfa_constr_rec =>
          let: exist l H_l := residuals r c in
          let: exist N H_N := @nfa_constr_l c l _ in
          exist _ N _).
- move: H_l => /= [H_l H_l'] r' H_r'.
  apply: nfa_constr_rec.
  move => w H_w.
  exact: (H_l r').
- move: H_N => /= [H_N1 H_N2].
  move: H_l => /= [H_l H_l'].
  move => w /=.
  rewrite 2!inE.
  apply/idP/idP.
  * move/H_l' => [r' [H_r' H_wr']].
    exact: (H_N1 r').
  * move/H_N2 => [w' [H_w' [r' [H_r' H_rw']]]].
    injection H_w' => H_eq_w'.
    subst.
    exact: (H_l r').
Defined.

Fixpoint nfa_constr_enum (r : regexp char) :
  (forall c r', {subset re_lang r' <= residual c (re_lang r)} -> { M | re_lang r' =i nfa_lang M }) ->
  enum char <> [::] ->
  { N | re_lang r =i nfa_lang N }.
  refine 
    (fun nfa_constr_rec H_neq =>
       match enum char as e0 return _ = e0 -> _ with
       | [::] => fun H_eq => False_rect _ _
       | c :: e => 
         fun H_eq =>
           let: exist M H_M := @nfa_constr_res r c _ in
           exist _ M _
       end (refl_equal _)).
- by rewrite H_eq in H_neq.
- by admit.
- by admit.
Admitted.
                
(* { N | forall w, c :: w \in re_lang r -> c :: w \in nfa_lang N }. *)

(*
Fixpoint nfa_constr r c l : 
  residuals_of_re r c l ->   
  (forall r', r' \in l -> { M | re_lang r' =i nfa_lang M }) ->
  nfa_constr_t r c.
refine (fun H_re nfa_residual_rec =>
          match l as l0 return _ = l0 -> _ with
          | [::] => fun H_eq => exist _ nfa_void _ 
          | r' :: l' => 
            fun H_eq =>
              match nfa_residual_rec r' _ with
              | exist M H_M =>
                match nfa_constr r c l' _ _ with
                | exist _ _ => _
                end
              end
          end (refl_equal _)); subst.
- rewrite /residual_eq_mem /=.
  move => w.
  move: H_re => [H_re H_re'] {H_re}.
  apply H_re' in H_w.
  by move: H_w => [r' [H_in H_w]].
- by rewrite inE; apply/orP; left.
- simpl in H_M.
  rewrite /residuals_of_re /=.
*)


(*

Definition enum_nfa : nfa char :=
foldl (fun n c => nfa_plus (nfa_char c) n) nfa_void (enum char).

Inductive regexp_residual_lt : regexp char -> regexp char -> Prop :=
| regexp_residual_lt_stars : forall r r' : regexp char,
  re_stars r < re_stars r' ->
  regexp_residual_lt r r'
| regexp_residual_lt_size : forall r r' : regexp char,
  re_stars r = re_stars r' ->
  re_size r < re_size r' ->
  regexp_residual_lt r r'.


Eval compute in [set tt].

Print foldr.

Fixpoint enum_fold (f : regexp char -> nfa) (s : seq char) : nfa :=
if s is x :: s' then 

Fixpoint nfa_residual (r : regexp char) : nfa :=

Check enum char.

Check nfa_char.
*)

End RegLangNFA.
