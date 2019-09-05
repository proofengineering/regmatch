From RegMatch Require Import regexp regmatch.

From mathcomp Require Import all_ssreflect.
From RegLang Require Import setoid_leq misc nfa dfa minimization languages regexp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RegLangExp.

Variable char : eqType.

Lemma re_eq_dec (e1 e2 : r char) : {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply: eq_comparable. Qed.

Definition re_eqMixin := EqMixin (compareP re_eq_dec).
Canonical Structure re_eqType := EqType _ re_eqMixin.

Fixpoint regexp2r (re : regexp char) : r char :=
  match re with
  | Void => r_zero
  | Eps => r_unit
  | Atom c' => r_char c'
  | Star r' => r_star (regexp2r r')
  | Plus r1 r2 => r_plus (regexp2r r1) (regexp2r r2)
  | Conc r1 r2 => r_times (regexp2r r1) (regexp2r r2)
  end.

Fixpoint r2regexp (r : r char) : regexp char :=
  match r with
  | r_zero => Void
  | r_unit => Eps
  | r_char c' => Atom c'
  | r_star r' => Star (r2regexp r')
  | r_plus r1 r2 => Plus (r2regexp r1) (r2regexp r2)
  | r_times r1 r2 => Conc (r2regexp r1) (r2regexp r2)
  end.

Fixpoint r_stars (e : regexp char) : nat :=
  match e with
  | Star s => (r_stars s).+1
  | Plus s t => ((r_stars s)+(r_stars t)).+1
  | Conc s t => ((r_stars s)+(r_stars t)).+1
  | _ => 0
  end.

Lemma cancel_r_regexp : cancel r2regexp regexp2r.
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

Lemma cancel_regexp_re : cancel regexp2r r2regexp.
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

Lemma regexp_r_in : forall (r : r char) (w : seq char), s_in_regexp_lang _ w r -> w \in re_lang (r2regexp r).
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

Lemma regexp_r_in' : forall (r : regexp char) (w : seq char), s_in_regexp_lang _ w (regexp2r r) -> w \in re_lang r.
Proof.
move => r w H.
remember (regexp2r r) as r0.
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

Lemma regexp_in_re : forall (r : regexp char) (w : seq char), w \in re_lang r  -> s_in_regexp_lang _ w (regexp2r r).
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
  s_in_regexp_c_lang char w (regexp2r r) c' ->
  w \in residual c' (re_lang r).
Proof.
move => r w c' H_c.
inversion H_c; subst.
rewrite /= in H.
by apply regexp_r_in'.
Qed.

Lemma residual_s_in_regexp_c_lang : forall r w c',
  w \in residual c' (re_lang r) ->
  s_in_regexp_c_lang char w (regexp2r r) c'.
Proof.
move => r w c' H_c.
apply s_in_regexp_c_lang_cs.
rewrite /=.
by apply regexp_in_re.
Qed.

Definition residuals : forall (r : regexp char) (c : char), residuals_t r c.
refine
  (fun r c => 
     match regexps_no_c (@eq_comparable char) (regexp2r r, c) with
     | exist l H_l => exist _ (map r2regexp l) _
     end).
split.
- move => r' H_in /= w H_w.
  rewrite /residual.
  rewrite inE.
  move: H_l => [H_l H_l'] {H_l'}.
  rewrite /= in H_l.
  apply s_in_regexp_c_lang_residual.
  apply regexp_in_re in H_w.
  apply (H_l (regexp2r r')) => //.
  move: H_in.
  move/mapP => [r0 H_in] H_eq.
  rewrite H_eq {H_eq}.
  rewrite cancel_r_regexp.
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
  exists (r2regexp r').
  split; last exact: regexp_r_in.
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

Program Definition acc' (r : regexp char) (w : seq char) : {w \in re_lang r}+{w \notin re_lang r} :=
  match acc (@eq_comparable char) (regexp2r r, w) with
  | left H_l => left _
  | right H_r => right _
  end.
Next Obligation.
exact: regexp_r_in'.
Qed.
Next Obligation.
clear Heq_anonymous.
apply/negP.
move => H_acc.
case: H_r.
exact: regexp_in_re.
Defined.
  
End RegLangExp.
