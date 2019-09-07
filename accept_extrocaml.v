Require Import List.

Require Import RegMatch.regmatch.

Require Import ExtrOcamlBasic.

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant app => "List.append".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".
Extract Inlined Constant map => "List.map".

Extraction "accept.ml" accept.
