Require Import String.
Require Import List.

Require Import regexp.
Require Import regexp_metatheory.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant app => "List.append".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".

Extraction "accept.ml" accept.
