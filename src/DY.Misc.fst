module DY.Misc

open FStar.List.Tot

val index_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> i:nat{i < List.Tot.length l} -> Lemma (
  index (map f l) i == f (index l i)
)
let rec index_map #a #b f l i =
  let h::t = l in
  if i = 0 then ()
  else index_map f t (i-1)
