
  module SS = Set.Make(String)
  let values = ref SS.empty
    
  let write_to_file value=
    let oc = open_out_gen [Open_append; Open_creat] 0o777 "/home/anabrendel/lfind/vfa-benchmarks/Sort/benchmarks/sources/backward_reasoning/_lfind_sort_lemma_simple_insert_IN_insert_sortedd/examples_Sort.txt" in
    if not(SS.mem value !values) then 
      (
        values := SS.add value !values;
        Printf.fprintf oc "%s\n"  value;
      );
    close_out oc; ()
  
  let print n nstr=
    write_to_file (String.of_seq (List.to_seq nstr));
    (n)
    