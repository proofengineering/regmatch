Require Import RegExp.regexp.
Require Import RegExp.regexp_metatheory.

From mathcomp
Require Import all_ssreflect.

From RegLang 
Require Import setoid_leq misc nfa dfa minimization languages regexp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RegLangExp.

Variable char : eqType.

Lemma re_eq_dec (e1 e2 : re char) : {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply: eq_comparable. Qed.

Definition re_eqMixin := EqMixin (compareP re_eq_dec).
Canonical Structure re_eqType := EqType _ re_eqMixin.

Fixpoint regexp2re (r : regexp char) : re char :=
  match r with
  | Void => re_zero
  | Eps => re_unit
  | Atom c' => re_char c'
  | Star r' => re_star (regexp2re r')
  | Plus r1 r2 => re_plus (regexp2re r1) (regexp2re r2)
  | Conc r1 r2 => re_times (regexp2re r1) (regexp2re r2)
  end.

Fixpoint re2regexp (r : re char) : regexp char :=
  match r with
  | re_zero => Void
  | re_unit => Eps
  | re_char c' => Atom c'
  | re_star r' => Star (re2regexp r')
  | re_plus r1 r2 => Plus (re2regexp r1) (re2regexp r2)
  | re_times r1 r2 => Conc (re2regexp r1) (re2regexp r2)
  end.

Fixpoint re_stars (e : regexp char) : nat :=
  match e with
  | Star s => (re_stars s).+1
  | Plus s t => ((re_stars s)+(re_stars t)).+1
  | Conc s t => ((re_stars s)+(re_stars t)).+1
  | _ => 0
  end.

Lemma cancel_re_regexp : cancel re2regexp regexp2re.
Proof.
rewrite /cancel.
elim => //=.
- move => r IH r' IH'.
  by rewrite IH IH'.
- move => r IH r' IH'.
  by rewrite IH IH'.
- move => r IH.
  by rewrite IH.
Qed.

Lemma cancel_regexp_re : cancel regexp2re re2regexp.
Proof.
rewrite /cancel.
elim => //=.
- move => r IH.
  by rewrite IH.
- move => r IH r' IH'.
  by rewrite IH IH'.
- move => r IH r' IH'.
  by rewrite IH IH'.
Qed.

Lemma regexp_re_in : forall (r : re char) (w : seq char), s_in_regexp_lang _ w r -> w \in re_lang (re2regexp r).
Proof.
move => r w H.
remember r as r0.
remember w as w0.
revert r w Heqr0 Heqw0.
induction H => //=.
- move => r w H_eq H_eq'.
  subst.
  by rewrite inE.
- move => r w H_eq H_eq'.
  subst.    
  apply/plusP; left.
  exact: IHs_in_regexp_lang.
- move => r w H_eq H_eq'.
  subst.
  apply/plusP; right.
  exact: IHs_in_regexp_lang.
- move => r w H_eq H_eq'.
  subst.
  apply/concP.
  exists s5, s'.
  split => //.
  split.
  * exact: IHs_in_regexp_lang1.
  * exact: IHs_in_regexp_lang2.
- move => r' w H_eq H_eq'.
  subst.
  apply/star_cat.
  * exact: IHs_in_regexp_lang1.
  * exact: IHs_in_regexp_lang2.
Qed.

Lemma regexp_re_in' : forall (r : regexp char) (w : seq char), s_in_regexp_lang _ w (regexp2re r) -> w \in re_lang r.
Proof.
move => r w H.
remember (regexp2re r) as r0.
remember w as w0.
revert r w Heqr0 Heqw0.
induction H => //=.
- move => r w H_eq H_eq'.
  subst.
  by destruct r.
- move => r w H_eq H_eq'.
  subst.
  destruct r => //.
  rewrite /= in H_eq.
  injection H_eq => H_eq'.
  subst.
  by rewrite inE.
- move => r w H_eq H_eq'.
  subst.
  destruct r => //.
  rewrite /= in H_eq.
  injection H_eq => H_eq1 H_eq2.
  subst.
  apply/plusP.
  left.
  by apply (IHs_in_regexp_lang _ w).
- move => r w H_eq H_eq'.
  subst.
  destruct r => //.
  rewrite /= in H_eq.
  injection H_eq => H_eq1 H_eq2.
  subst.
  apply/plusP.
  right.
  by apply (IHs_in_regexp_lang _ w).
- move => r w H_eq H_eq'.
  subst.
  destruct r => //.
  rewrite /= in H_eq.
  injection H_eq => H_eq1 H_eq2.
  subst.
  apply/concP.
  exists s5, s'.
  split => //.
  split.
  * exact: IHs_in_regexp_lang1.
  * exact: IHs_in_regexp_lang2.
- move => r' w H_eq H_eq'.
  subst.
  by destruct r'.
- move => r' w H_eq H_eq'.
  subst.
  destruct r' => //.
  rewrite /= in H_eq.
  injection H_eq => H_eq'.
  subst.
  apply/star_cat.
  * exact: IHs_in_regexp_lang1.
  * rewrite -/(re_lang _).
    have ->: star (re_lang r') = re_lang (Star r') by [].
    exact: IHs_in_regexp_lang2.
Qed.

Lemma re_lang_ind : forall (char : eqType) (P : seq char -> regexp char -> Prop),
    P [::] Eps ->
    (forall c' : char, P [:: c'] (Atom c')) ->
    (forall (w : seq char) (r1 r2 : regexp char), w \in (re_lang r1) -> P w r1 -> P w (Plus r1 r2)) ->
    (forall (w : seq char) (r1 r2 : regexp char), w \in (re_lang r2) -> P w r2 -> P w (Plus r1 r2)) ->
    (forall (w1 w2 : seq char) (r1 r2 : regexp char), 
        w1 \in (re_lang r1) -> P w1 r1 -> w2 \in (re_lang r2) -> P w2 r2 -> P (w1 ++ w2) (Conc r1 r2)) ->
    (forall r : regexp char, P [::] (Star r)) ->
    (forall (w1 w2 : seq char) (r :regexp char), 
        w1 \in (re_lang r) -> P w1 r -> w2 \in (re_lang (Star r)) -> P w2 (Star r) -> P (w1 ++ w2) (Star r)) ->
    forall (w : seq char) (r : regexp char), w \in (re_lang r) -> P w r.
Proof.
move => c0 P H_e H_a H_p1 H_p2 H_c H_s1 H_s2.
move => w r.
elim: r w => //=.
- by case.
- move => c' w.
  rewrite inE /=.
  move/eqP => H_eq.
  subst.
  exact: H_a.
- move => r IH w.
  move/starP => [vv H_vv] H_f.
  subst.
  move/allP: H_vv.
  move => IH'.
  elim: vv IH' => //=.
  move => w0 vv' IH' H_in.
  have H_in_vv: w0 \in w0 :: vv'.
    rewrite inE.
    apply/orP.
    by left.
  have H_in_vv' := H_in _ H_in_vv.
  move/andP: H_in_vv' => [H_not_in_vv H_in_vv'].
  apply H_s2 => //.
  * exact: IH.
  * apply/starI.
    move => w H_w.
    rewrite -/(re_lang _).
    have H_w_in: w \in w0 :: vv'.
      rewrite inE.
      apply/orP.
      by right.
    apply H_in in H_w_in.
    move: H_w_in.
    by move/andP => [H_w_in H_w_in'].
  * apply: IH'.
    move => w' H_w'.
    apply: H_in.
    rewrite inE.
    apply/orP.
    by right.
- move => r1 IH1 r2 IH2.
  move => w.
  move/plusP => [H_rp1|H_rp2].
  * apply: H_p1 => //.
    exact: IH1.
  * apply: H_p2 => //.
    exact: IH2.
- move => r1 IH1 r2 IH2.
  move => w.
  move/concP => [w1 [w2 [H_eq [H_w1 H_w2]]]].
  subst.
  apply: H_c => //.
  * exact: IH1.
  * exact: IH2.
Qed.

Lemma regexp_in_re : forall (r : regexp char) (w : seq char), w \in re_lang r  -> s_in_regexp_lang _ w (regexp2re r).
Proof.
move => r w H_st.
remember r as r0.
remember w as w0.
move: H_st r w Heqr0 Heqw0.
elim/re_lang_ind => //=.
- move => r w H_eq H_eq'.
  subst.
  exact: s_in_regexp_lang_unit.
- move => c' r w H_eq H_eq'.
  subst.
  exact: s_in_regexp_lang_char.
- move => w r1 r2 H_in IH r' w1 H_eq H_eq'.
  subst.
  apply: s_in_regexp_lang_plus_1.
  exact: IH.
- move => w r1 r2 H_in IH r' w1 H_eq H_eq'.
  subst.
  apply: s_in_regexp_lang_plus_2.
  exact: IH.
- move => w1 w2 r1 r2 H_in1 IH1 H_in2 IH2 r w H_eq H_eq'.
  subst.
  apply s_in_regexp_lang_times.
  * exact: IH1.
  * exact: IH2.
- move => r r2 w H_eq H_eq'.
  subst.
  exact: s_in_regexp_lang_star_1.
- move => w1 w2 r H_in1 IH1 H_in2 IH2 r1 w H_eq H_eq'.
  subst.
  apply s_in_regexp_lang_star_2.
  * exact: IH1.
  * exact: IH2.
Qed.

Definition residuals_re (r : regexp char) (c : char) (l : seq (regexp char)) :=
  (forall r', r' \in l -> (forall w, w \in re_lang r' -> w \in residual c (re_lang r))) /\
  (forall w, w \in residual c (re_lang r) -> exists r', r' \in l /\ w \in re_lang r').

Definition residuals_t (r : regexp char) (c : char) :=
{ l : seq (regexp char) | residuals_re r c l }.

Lemma s_in_regexp_c_lang_residual : forall r w c',
  s_in_regexp_c_lang char w (regexp2re r) c' ->
  w \in residual c' (re_lang r).
Proof.
move => r w c' H_c.
inversion H_c; subst.
rewrite /= in H.
by apply regexp_re_in'.
Qed.

Lemma residual_s_in_regexp_c_lang : forall r w c',
  w \in residual c' (re_lang r) ->
  s_in_regexp_c_lang char w (regexp2re r) c'.
Proof.
move => r w c' H_c.
apply s_in_regexp_c_lang_cs.
rewrite /=.
by apply regexp_in_re.
Qed.

Definition residuals : forall (r : regexp char) (c : char), residuals_t r c.
refine
  (fun r c => 
     match regexps_no_c (@eq_comparable char) (regexp2re r, c) with
     | exist l H_l => exist _ (map re2regexp l) _
     end).
split.
- move => r' H_in /= w H_w.
  rewrite /residual.
  rewrite inE.
  move: H_l => [H_l H_l'] {H_l'}.
  rewrite /= in H_l.
  apply s_in_regexp_c_lang_residual.
  apply regexp_in_re in H_w.
  apply (H_l (regexp2re r')) => //.
  move: H_in.
  move/mapP => [r0 H_in] H_eq.
  rewrite H_eq {H_eq}.
  rewrite cancel_re_regexp.
  move: H_in.
  clear.
  elim: l => //.
  move => r' l IH.
  rewrite inE.
  move/orP => [H_in|H_in].
  * by left; move/eqP: H_in.
  * right; exact: IH.
- move => w /= H_in.
  apply residual_s_in_regexp_c_lang in H_in.
  move: H_l => [H_l' H_l] {H_l'}.
  rewrite /= in H_l.
  apply H_l in H_in.
  move: H_in => [r' [H_in H_r']].
  exists (re2regexp r').
  split; last exact: regexp_re_in.
  apply List.in_split in H_in.
  rewrite /= in H_in.
  move: H_in => [l1 [l2 H_eq]].
  rewrite H_eq /=.  
  rewrite map_cat mem_cat.
  apply/orP.
  right.
  rewrite inE.
  apply/orP.
  by left.
Defined.

Definition accept : forall (r : regexp char) (w : seq char), {w \in re_lang r}+{w \notin re_lang r}.
refine
  (fun r w => 
     match accept (@eq_comparable char) (regexp2re r, w) with
     | left H_l => left _
     | right H_r => right _
     end).
- exact: regexp_re_in'.
- apply/negP.
  move => H_acc.
  case: H_r.
  exact: regexp_in_re.
Defined.

End RegLangExp.

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
     match l as l0 return _ = l0 -> _ with
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
