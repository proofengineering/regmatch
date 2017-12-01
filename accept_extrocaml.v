Require Import List.

Require Import RegExp.regexp.
Require Import RegExp.regexp_metatheory.

Require Import ExtrOcamlBasic.

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant app => "List.append".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".

Extraction "accept.ml" accept.
