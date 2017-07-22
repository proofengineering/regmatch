Require Import regexp.

Require Import mathcomp.ssreflect.ssreflect.

Require Import List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Wf_nat.
Require Import Wellfounded.
Require Import Wellfounded.Lexicographic_Product.
Require Import Omega.

Import ListNotations.
Open Scope string_scope.

Lemma string_append_assoc : forall s0 s1 s2, s0 ++ s1 ++ s2 = (s0 ++ s1) ++ s2.
elim => //.
move => a s0 IH s1 s2.
by rewrite /= IH.
Qed.

Fixpoint regexp_size (r : regexp) : nat :=
match r with
| regexp_zero => 1
| regexp_unit => 1
| regexp_char _ => 1
| regexp_plus r1 r2 => regexp_size r1 + regexp_size r2 + 1
| regexp_times r1 r2 => regexp_size r1 + regexp_size r2 + 1
| regexp_star r => regexp_size r + 1
end.

Definition regexp_size_lt (r r' : regexp) := regexp_size r < regexp_size r'.

Lemma regexp_size_wf : well_founded regexp_size_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_size r)).
Defined.

Fixpoint regexp_subsize (r : regexp) : nat :=
match r with
| regexp_times r1 r2 => regexp_size r1
| _ => 0
end.

Definition regexp_subsize_lt (r r' : regexp) := regexp_subsize r < regexp_subsize r'.

Lemma regexp_subsize_wf : well_founded regexp_subsize_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_subsize r)).
Defined.

Section lexprod'.

Variable A : Type.

Variable ltA : A -> A -> Prop.

Inductive lexprod' : A * A -> A * A -> Prop :=
| left_lex' : forall (x1 x2 y1 y2 : A), ltA x1 x2 -> lexprod' (x1, y1) (x2, y2)
| right_lex' : forall (x y1 y2 : A), ltA y1 y2 -> lexprod' (x, y1) (x, y2).

Lemma lexprod'_Acc : well_founded ltA -> forall x, Acc ltA x -> forall y, Acc ltA y -> Acc lexprod' (x, y).
Proof.
intros H x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
apply Acc_intro.
intros (x1, y1) HA.
inversion HA; subst.
- apply IHacc; auto.
- apply IHacc0; auto.
Defined.

Theorem wf_lexprod' : well_founded ltA -> well_founded lexprod'.
Proof.
intros H_wf (x, y).
by auto using lexprod'_Acc.
Defined.

End lexprod'.

Definition regexp_lt_size_subsize_lexprod' (r r' : regexp) :=
lexprod' _ lt (regexp_size r, regexp_subsize r) (regexp_size r', regexp_subsize r').

Lemma regexp_lt_size_subsize_lexprod'_wf : well_founded regexp_lt_size_subsize_lexprod'.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun r => (regexp_size r, regexp_subsize r))).
by apply wf_lexprod'; apply lt_wf.
Defined.

Inductive regexp_lt : regexp -> regexp -> Prop :=
| regexp_lt_lt : forall r r' : regexp, 
    regexp_size r < regexp_size r' -> 
    regexp_lt r r'
| regexp_lt_times_lt : forall r11 r12 r21 r22,
    regexp_size (regexp_times r11 r12) = regexp_size (regexp_times r21 r22) ->
    regexp_size r11 < regexp_size r21 ->
    regexp_lt (regexp_times r11 r12) (regexp_times r21 r22).

Lemma regexp_lt_size_subsize_symprod_incl_impl : forall r r', regexp_lt r r' -> regexp_lt_size_subsize_lexprod' r r'.
Proof.
move => r r'.
elim => {r r'}.
- move => r r' H_lt.
  rewrite /regexp_lt_size_subsize_lexprod'.
  exact: left_lex'.
- move => r11 r12 r21 r22 H_eq H_lt.
  rewrite /regexp_lt_size_subsize_lexprod' H_eq /=.
  exact: right_lex'.
Defined.

Lemma regexp_lt_size_subsize_symprod_incl : inclusion _ regexp_lt regexp_lt_size_subsize_lexprod'.
Proof.
move => x y.
exact: regexp_lt_size_subsize_symprod_incl_impl.
Defined.

Lemma regexp_lt_well_founded : well_founded regexp_lt.
Proof.
apply (wf_incl _ _ _ regexp_lt_size_subsize_symprod_incl).
exact: regexp_lt_size_subsize_lexprod'_wf.
Defined.

Definition regexps_no_c_lt (rc rc' : regexp * ascii) := regexp_lt (fst rc) (fst rc').

Lemma regexps_no_c_lt_well_founded : well_founded regexps_no_c_lt.
Proof.
apply (wf_inverse_image _ _ _ (fun rs => fst rs)).
apply regexp_lt_well_founded.
Defined.

Definition regexps_no_c_t (rc : regexp * a) :=
{ l : list regexp | forall r, In r l -> (forall s, s_in_regexp_lang s r -> s_in_regexp_c_lang s (fst rc) (snd rc)) }.

Section FoldLeftFun.

Variable A : Type.
Variable f : A -> A.

Lemma fold_left_f_list_app :
  forall l1 l0,
    fold_left (fun (l : list A) (a : A) => f a :: l) l1 l0 =
    app (fold_left (fun (l : list A) (a : A) => f a :: l) l1 []) l0.
Proof.
elim => //=.
move => a l IH l'.
rewrite IH /=.
have IH' := IH [f a].
rewrite IH' /=.
set fl := fold_left _ _ _.
by rewrite -app_assoc app_assoc.
Qed.

Lemma fold_left_list_f_in : 
  forall l1 a,
    In a (fold_left (fun (l : list A) (a' : A) => f a' :: l) l1 []) ->
    exists a0, In a0 l1 /\ a = f a0.
Proof.
elim => //=.
move => a l IH a' H_in.
rewrite fold_left_f_list_app in H_in.
apply in_app_or in H_in.
case: H_in => H_in.
* have [a0 [H_in' H_eq]] := IH _ H_in.
  subst.
  exists a0.
  split => //.
  by right.
* case: H_in => H_eq //.
  exists a.
  split => //.
  by left.
Qed.

End FoldLeftFun.

Section PListDec.

Variables A B : Type.

Variable ABlt : A * B -> A * B -> Prop.

Variable P : A * B -> Prop.

Variable ab : A * B.

Variable P_dec : forall ab', ABlt ab' ab -> { P ab' }+{ ~ P ab' }.

Variable f : A -> A * B.
Hypothesis f_ABlt : forall a' : A, ABlt (f a') ab.

Definition list_t (l : list A) := { a0 | In a0 l /\ P (f a0) }+{ (forall a', In a' l -> ~ P (f a')) }.

Fixpoint P_list_dec (l : list A) : list_t l.
refine
  (match l as l0 return _ = l0 -> _ with
   | [] => fun H_eq_l => inright _
   | a :: l' =>
     fun H_eq_l => 
       match P_dec (f a) _ with
       | left H_dec => inleft (exist _ a _)
       | right H_dec =>
         match P_list_dec l' with
         | inleft (exist a' H_l') => inleft (exist _ a' _)
         | inright H_l' => inright _
         end
       end
   end (refl_equal _)).
- move => a' H_in H_p; subst.
  by inversion H_in.
- subst.
  exact: f_ABlt.
- subst.
  by split; first by left.
- subst.
  simpl in *.
  move: H_l' => [H_l' H_p].
  by split; first by right.
- move => a' H_in H_p.
  subst.
  case: H_in => H_in; first by subst.
  by apply H_l' in H_in.
Defined.

End PListDec.

Definition regexps_no_c_F : forall rc : regexp * a,
  (forall rc', regexps_no_c_lt rc' rc -> regexps_no_c_t rc') -> regexps_no_c_t rc.
refine
  (fun rc regexps_no_c_rec =>
     match fst rc as r0 return _ = r0 -> _ with
     | regexp_zero => fun H_eq => exist _ [] _
     | regexp_unit => fun H_eq => exist _ [] _
     | regexp_char c =>
       fun H_eq =>
         match ascii_dec c (snd rc) with
         | left H_a => exist _ [regexp_unit] _
         | right H_a => exist _ [] _
         end
     | regexp_plus r1 r2 => 
       fun H_eq =>
         match regexps_no_c_rec (r1, snd rc) _, regexps_no_c_rec (r2, snd rc) _ with
         | exist l1 H_ex1, exist l2 H_ex2 => exist _ (app l1 l2) _
         end
     | regexp_star r =>
       fun H_eq =>
         match regexps_no_c_rec (r, snd rc) _ with
         | exist l H_ex =>
           exist _ (fold_left (fun l' r' => regexp_times r' (regexp_star r) :: l') l []) _
         end
     | regexp_times regexp_zero _ => fun H_eq => exist _ [] _
     | regexp_times regexp_unit r2 =>
       fun H_eq =>
         match regexps_no_c_rec (r2, snd rc) _ with
         | exist l H_ex => exist _ l _
         end
     | regexp_times (regexp_char c) r2 =>
       fun H_eq =>
         match ascii_dec c (snd rc) with
         | left H_a => exist _ [r2] _
         | right H_a => exist _ [] _
         end
     | regexp_times (regexp_plus r11 r12) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (regexp_times r11 r2, snd rc) _, regexps_no_c_rec (regexp_times r12 r2, snd rc) _ with
         | exist l11 H_ex11, exist l12 H_ex12 => exist _ (app l11 l12) _
         end
     | regexp_times (regexp_times r11 r12) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (regexp_times r11 (regexp_times r12 r2), snd rc) _ with
         | exist l H_ex => exist _ l _
         end
     | regexp_times (regexp_star r1) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (r2, snd rc) _, regexps_no_c_rec (r1, snd rc) _ with
         | exist l2 H_ex2, exist l1 H_ex1 =>
           exist _ (app l2 (fold_left (fun l r' => regexp_times r' (regexp_times (regexp_star r1) r2) :: l) l1 [])) _
         end
     end (refl_equal _)); destruct rc; simpl in *; subst => //=.
- move => r; case => //.
  move => H_eq; subst.
  move => s H_in.
  inversion H_in; subst.
  apply: s_in_regexp_c_lang_cs.
  rewrite /=.
  exact: s_in_regexp_lang_char.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move => r H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  * have H_s' := H_ex1 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    exact: s_in_regexp_lang_plus_1.
  * have H_s' := H_ex2 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    exact: s_in_regexp_lang_plus_2.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move => r' H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have H_s' := H_ex _ H_in _ H_s.
  inversion H_s'; subst.
  simpl in *.
  have ->: String a s = "" ++ String a s by [].
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_unit.
- move => r'; case => // H_eq; subst.
  move => s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have ->: String a s = String a "" ++ s by [].
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_char.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move => r' H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  * have H_s' := H_ex11 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_plus_1.
  * have H_s' := H_ex12 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_plus_2.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_times_lt => /=; omega.
- move => r' H_in s' H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have H_s' := H_ex _ H_in _ H_s.
  inversion H_s'; subst.
  simpl in *.
  inversion H; subst.
  inversion H4; subst.
  rewrite string_append_assoc. 
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_times.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move => r' H_in s' H_s'.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  * have H_s0 := H_ex2 _ H_in _ H_s'.
    inversion H_s0; subst.
    simpl in *.
    have ->: String a s' = "" ++ String a s' by [].    
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_star_1.
  * apply fold_left_list_f_in in H_in.
    move: H_in => [r0 [H_in' H_eq_r0]].
    subst.
    inversion H_s'; subst.
    have H_s0 := H_ex1 _ H_in' _ H2.
    inversion_clear H3; subst.
    inversion_clear H_s0; subst.
    simpl in *.
    have ->: String a (s5 ++ s0 ++ s') = (String a s5 ++ s0) ++ s' by rewrite -string_append_assoc.      
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_star_2.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move => r' H_in s' H_s'.
  apply: s_in_regexp_c_lang_cs => /=.
  apply fold_left_list_f_in in H_in.
  move: H_in => [r0 [H_in' H_eq_r0]].
  subst.
  inversion_clear H_s'; subst.
  have H_ex' := H_ex _ H_in' _ H.
  inversion_clear H_ex'; subst.
  simpl in *.
  have ->: String a (s5 ++ s'0) = (String a s5) ++ s'0 by [].
  exact: s_in_regexp_lang_star_2.
Defined.

Definition regexps_no_c : forall (rs : regexp * a), regexps_no_c_t rs :=
@well_founded_induction _ _ regexps_no_c_lt_well_founded regexps_no_c_t regexps_no_c_F.

Definition string_lt (s s' : string) := String.length s < String.length s'.

Lemma string_lt_well_founded : well_founded string_lt.
Proof.
exact: (well_founded_lt_compat _ (fun s => String.length s)).
Defined.

Inductive accept_lt : regexp * string -> regexp * string -> Prop :=
| accept_lt_string : forall rs rs' : regexp * string,
  String.length (snd rs) < String.length (snd rs') ->
  accept_lt rs rs'
| accept_lt_regexp : forall rs rs' : regexp * string,
  String.length (snd rs) = String.length (snd rs') ->
  regexp_lt (fst rs) (fst rs') ->
  accept_lt rs rs'.

Section lexprod''.

Variable A : Type.

Variable ltA : A -> A -> Prop.

Inductive lexprod'' : A * A * A -> A * A * A -> Prop :=
| left_lex'' : forall (x1 x2 y1 y2 z1 z2 : A), ltA x1 x2 -> lexprod'' (x1, y1, z1) (x2, y2, z2)
| mid_lex'' : forall (x y1 y2 z1 z2 : A), ltA y1 y2 -> lexprod'' (x, y1, z1) (x, y2, z2)
| right_lex'' : forall (x y z1 z2 : A), ltA z1 z2 -> lexprod'' (x, y, z1) (x, y, z2).

Lemma lexprod''_Acc : well_founded ltA -> forall x, Acc ltA x -> forall y, Acc ltA y -> forall z, Acc ltA z -> Acc lexprod'' (x, y, z).
Proof.
intros H x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
intros z Hz.
induction Hz as [z _ IHacc1].
apply Acc_intro.
intros ((x1, y1), z1) HA.
inversion HA; subst; auto.
Defined.

Theorem wf_lexprod'' : well_founded ltA -> well_founded lexprod''.
Proof.
intros H_wf ((x, y), z).
by auto using lexprod''_Acc.
Defined.

End lexprod''.

Definition accept_lt_lexprod'' (rs rs' : regexp * string) :=
lexprod'' _ lt 
          (String.length (snd rs), regexp_size (fst rs), regexp_subsize (fst rs))
          (String.length (snd rs'), regexp_size (fst rs'), regexp_subsize (fst rs')).

Lemma accept_lt_lexprod''_wf : well_founded accept_lt_lexprod''.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun rs => (String.length (snd rs), regexp_size (fst rs), regexp_subsize (fst rs)))).
by apply wf_lexprod''; apply lt_wf.
Defined.

Lemma accept_lt_lexprod''_impl : forall rs rs', accept_lt rs rs' -> accept_lt_lexprod'' rs rs'.
Proof.
move => rs rs'.
elim => {rs rs'}.
- move => rs rs' H_lt.
  rewrite /accept_lt_lexprod''.
  exact: left_lex''.
- move => rs rs' H_eq H_lt.
  rewrite /accept_lt_lexprod'' H_eq /=.
  inversion H_lt; subst.
  * exact: mid_lex''.
  * rewrite H1.
    exact: right_lex''.
Defined.

Lemma accept_lt_lexprod''_incl : inclusion _ accept_lt accept_lt_lexprod''.
Proof.
move => x y.
exact: accept_lt_lexprod''_impl.
Defined.

Lemma accept_lt_well_founded : well_founded accept_lt.
Proof.
apply (wf_incl _ _ _ accept_lt_lexprod''_incl).
exact: accept_lt_lexprod''_wf.
Defined.

Definition accept_p (rs : regexp * string) :=
  s_matches_r (fst rs) (snd rs).

Definition accept_t (rs : regexp * string) :=
{ accept_p rs }+{ ~ accept_p rs }.

Definition accept_list_dec := P_list_dec regexp string accept_lt accept_p.

Check accept_list_dec.

(* 
accept_list_dec
     : forall ab : regexp * string,
       (forall ab' : regexp * string, accept_lt ab' ab -> {accept_p ab'} + {~ accept_p ab'}) ->
       forall f : regexp -> regexp * string,
       (forall a' : regexp, accept_lt (f a') ab) -> forall l : list regexp, list_t regexp string accept_p f l
*)

Definition accept_F : forall rs : regexp * string,
  (forall rs', accept_lt rs' rs -> accept_t rs') -> accept_t rs.
  refine
    (fun rs accept_rec =>
       match snd rs as s0 return _ = s0 -> _ with
       | "" =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | regexp_zero => fun H_eq_r => right _
           | regexp_unit => fun H_eq_r => left _
           | regexp_char _ => fun H_eq_r => right _
           | regexp_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, "") _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, "") _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | regexp_times r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, "") _ with
               | left H_r1 =>
                 match accept_rec (r2, "") _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_r1 => right _
               end
           | regexp_star r' => fun H_eq_r => left _
           end (refl_equal _)
       | String c s' =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | regexp_zero => fun H_eq_r => right _
           | regexp_unit => fun H_eq_r => right _
           | regexp_char c' =>
             fun H_eq_r =>
               match s' as s1 return _ = s1 -> _ with
               | "" =>
                 fun H_eq_s' =>
                   match ascii_dec c c' with
                   | left H_c => left _
                   | right H_c => right _
                   end
               | _ => fun H_eq_s' => right _ 
               end (refl_equal _)
           | regexp_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, String c s') _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, String c s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | regexp_times regexp_unit r2 =>
             fun H_eq_r =>
               match accept_rec (r2, String c s') _ with
               | left H_r2 => left _
               | right H_r2 => right _
               end
           | regexp_times (regexp_char c') r2 =>
             fun H_eq_r =>
               match ascii_dec c c' with
               | left H_c =>
                 match accept_rec (r2, s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_c => right _
               end
           | regexp_times (regexp_times r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (regexp_times r11 (regexp_times r12 r2), String c s') _ with
               | left H_r => left _
               | right H_r => right _
               end
           | regexp_times (regexp_plus r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (regexp_times r11 r2, String c s') _ with
               | left H_r11 => left _
               | right H_r11 =>
                 match accept_rec (regexp_times r12 r2, String c s') _ with
                 | left H_r12 => left _
                 | right H_r12 => right _
                 end
               end
           | regexp_times (regexp_star r1) r2 =>
             fun H_eq_r => right _
           | regexp_star r' =>
             fun H_eq_r =>
               match regexps_no_c (r', c) with
               | exist l H_l => 
                 match accept_list_dec rs accept_rec (fun r0 => (regexp_times r0 (regexp_star r'), s')) _ l with
                 | inleft (exist _ H_ex) => left _
                 | inright H_l' => right _ 
                 end
               end                       
           | _ => fun H_eq_r => right _
           end (refl_equal _)
       end (refl_equal _)); destruct rs; simpl in *; subst.
- by move => H_m; inversion H_m.
- exact: s_matches_r_unit.
- by move => H_m; inversion H_m.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_2.
- by move => H_m; inversion H_m; subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_times _ _ _ _ H_r1 H_r2.
- move => H_m; inversion H_m; subst.
  by destruct s1, s2.
- move => H_m; inversion H_m; subst.
  by destruct s1.
- by apply s_matches_r_star_1.
- by move => H_m; inversion H_m.
- by move => H_m; inversion H_m.
- exact: s_matches_r_char.
- by move => H_m; inversion H_m; subst.
- by move => H_m; inversion H_m; subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_2.
- by move => H_m; inversion H_m.
- move => H_m; inversion H_m; subst.
  by inversion H2.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- have H_eq: append "" (String c s') = String c s' by [].
  rewrite -H_eq.
  apply s_matches_r_times => //.
  exact: s_matches_r_unit.
- move => H_s.
  inversion H_s; subst.
  inversion H2; subst.
  simpl in *.
  subst.
  by contradict H_r2.
- exact: accept_lt_string.
- have H_eq: append (String c' "") s' = String c' s' by [].
  rewrite -H_eq.
  apply s_matches_r_times => //.
  exact: s_matches_r_char.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H1 => H_eq.
  by subst.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H1 => H_eq H_eq'.
  by subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r11; subst.
  apply s_matches_r_times => //.
  exact: s_matches_r_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r12; subst.
  apply s_matches_r_times => //.
  exact: s_matches_r_plus_2.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  * contradict H_r11.
    rewrite -H1.
    exact: s_matches_r_times.
  * contradict H_r12.
    rewrite -H1.
    exact: s_matches_r_times.
- apply accept_lt_regexp => //.
  by apply regexp_lt_times_lt => /=; omega.
- inversion H_r; subst.
  inversion H3; subst.
  rewrite string_append_assoc.
  apply s_matches_r_times => //.
  exact: s_matches_r_times.
- move => H_s; inversion H_s; subst.
  inversion H2; subst.
  contradict H_r.
  rewrite -string_append_assoc in H1.
  rewrite -H1.
  apply s_matches_r_times => //.
  exact: s_matches_r_times.
- by admit.
- move => r0.
  exact: accept_lt_string.
- move: H_ex => [H_in H_acc].
  inversion H_acc; subst.
  have H_l' := H_l _ H_in _ H1.
- by admit.
Defined 

Definition accept : forall (rs : regexp * string), accept_t rs :=
@well_founded_induction _ _ accept_lt_well_founded accept_t accept_F.
