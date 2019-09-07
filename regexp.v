Require Import List.

Import ListNotations.

Section RegExp.

Variable char : Type.

Definition c : Type := char.

Inductive r : Type :=
 | r_zero
 | r_unit
 | r_char (c5:c)
 | r_plus (r0:r) (r1:r)
 | r_times (r0:r) (r1:r)
 | r_star (r0:r).

Definition s : Type := list char.

Inductive s_in_regexp_lang : s -> r -> Prop :=
 | s_in_regexp_lang_unit : 
     s_in_regexp_lang  []  r_unit
 | s_in_regexp_lang_char : forall (c5:c),
     s_in_regexp_lang  ( c5  :: [])  (r_char c5)
 | s_in_regexp_lang_plus_1 : forall (s5:s) (r1 r2:r),
     s_in_regexp_lang s5 r1 ->
     s_in_regexp_lang s5 (r_plus r1 r2)
 | s_in_regexp_lang_plus_2 : forall (s5:s) (r1 r2:r),
     s_in_regexp_lang s5 r2 ->
     s_in_regexp_lang s5 (r_plus r1 r2)
 | s_in_regexp_lang_times : forall (s5 s':s) (r1 r2:r),
     s_in_regexp_lang s5 r1 ->
     s_in_regexp_lang s' r2 ->
     s_in_regexp_lang  ( s5  ++  s' )  (r_times r1 r2)
 | s_in_regexp_lang_star_1 : forall (r:r),
     s_in_regexp_lang  []  (r_star r)
 | s_in_regexp_lang_star_2 : forall (s5 s':s) (r0:r),
     s_in_regexp_lang s5 r0 ->
     s_in_regexp_lang s' (r_star r0) ->
     s_in_regexp_lang  ( s5  ++  s' )  (r_star r0).

Inductive s_in_regexp_c_lang : s -> r -> c -> Prop :=
 | s_in_regexp_c_lang_cs : forall (s5:s) (r0:r) (c5:c),
     s_in_regexp_lang  (  ( c5  :: [])   ++  s5 )  r0 ->
     s_in_regexp_c_lang s5 r0 c5.

End RegExp.

Arguments r_zero [char].
Arguments r_unit [char].
Arguments r_char [char] _.
Arguments r_plus [char] _ _.
Arguments r_times [char] _ _.
Arguments r_star [char] _.
