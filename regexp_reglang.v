Require Import regexp.
Require Import regexp_metatheory.

From mathcomp
Require Import all_ssreflect.

From RegLang Require Import setoid_leq misc nfa languages.
From RegLang Require Import regexp.

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

Definition residuals_t (rc : regexp char * char) :=
{ l : seq (regexp char) |
  (forall r : regexp char, r \in l -> (forall w, w \in re_lang r -> w \in residual (snd rc) (re_lang (fst rc)))) /\
  (forall w, w \in residual (snd rc) (re_lang (fst rc)) -> exists r, r \in l /\ w \in re_lang r) }.

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

Definition residuals : forall (rc : regexp char * char), residuals_t rc.
refine
  (fun rc => 
     match regexps_no_c (@eq_comparable char) (regexp2re (fst rc), snd rc) with
     | exist l H_l => exist _ (map re2regexp l) _
     end); destruct rc.
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

Definition accept_rl_p (rw : regexp char * seq char) :=
   (snd rw) \in re_lang (fst rw).

Definition accept_rl_t (rs : regexp char * seq char) :=
{ accept_rl_p rs }+{ ~ accept_rl_p rs }.

Definition accept_rl : forall (rw : regexp char * seq char), accept_rl_t rw.
refine
  (fun rw => 
     match accept (@eq_comparable char) (regexp2re (fst rw), snd rw) with
     | left H_l => left _
     | right H_r => right _
     end); destruct rw.
- rewrite /accept_rl_p /=.
  rewrite /accept_p /= in H_l.
  exact: regexp_re_in'.
- move => H_acc.
  case: H_r.
  rewrite /accept_p /=.
  rewrite /accept_rl_p /= in H_acc.
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
