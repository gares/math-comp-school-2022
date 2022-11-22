(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This used to be coqdoc *)

open Cdglobals
open Printf

let usage () =
  prerr_endline "";
  prerr_endline "Usage: udoc <options and files>";
  prerr_endline "  --stdout             write output to stdout";
  prerr_endline "  -o <file>            write output in file <file>";
  prerr_endline "  -s                   (short) no titles for files";
  prerr_endline "  -t <string>          give a title to the document";
  prerr_endline "  --body-only          suppress LaTeX/HTML header and trailer";
  prerr_endline "  --with-header <file> prepend <file> as html reader";
  prerr_endline "  --with-footer <file> append <file> as html footer";
  prerr_endline "  --toc                output a table of contents";
  prerr_endline "  --toc-depth <int>    don't include TOC entries for sections below level <int>";
  prerr_endline "  --quiet              quiet mode (default)";
  prerr_endline "  --verbose            verbose mode";
  prerr_endline "";
  exit 1

(*s \textbf{Banner.} Always printed. Notice that it is printed on error
    output, so that when the output of [coqdoc] is redirected this header
    is not (unless both standard and error outputs are redirected, of
    course). *)

let banner () =
  eprintf "This is udoc version %s, compiled on %s\n"
    Cdglobals.version Cdglobals.compile_date;
  flush stderr

let target_full_name f = f ^ ".html"

let parse () =
  let files = ref [] in
  let add_file f = files := f :: !files in
  let rec parse_rec = function
    | [] -> ()

    | ("-nopreamble" | "--nopreamble" | "--no-preamble"
      |  "-bodyonly"   | "--bodyonly"   | "--body-only") :: rem ->
	opts := { !opts with header_trailer = false } ;
        parse_rec rem
    | ("-with-header" | "--with-header") :: f ::rem ->
        opts := { !opts with header_trailer   = true;
                             header_file_spec = true;
                             header_file      = f;
                }; parse_rec rem
    | ("-with-header" | "--with-header") :: [] ->
	usage ()
    | ("-with-footer" | "--with-footer") :: f ::rem ->
        opts := { !opts with header_trailer   = true;
                             footer_file_spec = true;
                             footer_file      = f;
                }; parse_rec rem
    | ("-with-footer" | "--with-footer") :: [] ->
	usage ()
    | ("-p" | "--preamble") :: [] ->
	usage ()
    | ("-noindex" | "--noindex" | "--no-index") :: rem ->
	opts := { !opts with index = false; }; parse_rec rem
    | ("-multi-index" | "--multi-index") :: rem ->
	opts := { !opts with multi_index = true; }; parse_rec rem
    | ("-index" | "--index") :: s :: rem ->
	opts := { !opts with index_name = s; }; parse_rec rem
    | ("-index" | "--index") :: [] ->
	usage ()
    | ("-toc" | "--toc" | "--table-of-contents") :: rem ->
	opts := { !opts with toc = true; }; parse_rec rem
    | ("-stdout" | "--stdout") :: rem ->
	out_to := StdOut; parse_rec rem
    | ("-o" | "--output") :: f :: rem ->
	out_to := File (Filename.basename f);
        output_dir := Filename.dirname f; parse_rec rem
    | ("-o" | "--output") :: [] ->
	usage ()
    | ("-d" | "--directory") :: dir :: rem ->
	output_dir := dir; parse_rec rem
    | ("-d" | "--directory") :: [] ->
	usage ()
    | ("-t" | "-title" | "--title") :: s :: rem ->
	opts := { !opts with title = s; }; parse_rec rem
    | ("-t" | "-title" | "--title") :: [] ->
	usage ()
    | ("-toc-depth" | "--toc-depth") :: [] ->
      usage ()
    | ("-toc-depth" | "--toc-depth") :: ds :: rem ->
      let d = try int_of_string ds with
                Failure _ ->
                  (eprintf "--toc-depth must be followed by an integer\n";
                   exit 1)
      in
      opts := { !opts with toc_depth = Some d; }; parse_rec rem

    | ("-h" | "-help" | "-?" | "--help") :: rem ->
	banner (); usage ()
    | ("-V" | "-version" | "--version") :: _ ->
	banner (); exit 0

    | "-Q" :: ([] | [_]) ->
	usage ()
    | ("--coqlib_path" | "-coqlib_path") :: [] ->
	usage ()
    | f :: rem ->
	add_file f; parse_rec rem
  in
    parse_rec (List.tl (Array.to_list Sys.argv));
    List.rev !files

(* XXX: Uh *)
let copy src dst =
  let cin = open_in src in
  try
    let cout = open_out dst in
    try
      while true do output_char cout (input_char cin) done
    with End_of_file ->
      close_out cout;
      close_in cin
  with Sys_error e ->
    eprintf "%s\n" e;
    exit 1

(*s Functions for generating output files *)

module OutB    = Out_jscoq.JsCoq

(** gen_one_file [l] *)
let gen_one_file out (l : string list) =
  let out_module f =
    Cpretty.coq_file f
  in
  OutB.start_file out
    ~toc:!opts.toc
    ~index:!opts.index
    ~split_index:!opts.multi_index
    ~standalone:!opts.header_trailer;
  List.iter out_module l;
  OutB.end_file ()

(** [copy_style_file files] Copy support files to output. *)
let copy_style_files (files : string list) : unit =
  let copy_file file =
    let src = List.fold_left
              Filename.concat !Cdglobals.udoc_path ["html"; file] in
    let dst = file                                                in
    if Sys.file_exists src then copy src dst
    else eprintf "Warning: file %s does not exist\n" src
  in List.iter copy_file files

(** [produce_document l] produces a document from list of files [l] *)

let produce_document (l : string list) =

  copy_style_files OutB.support_files;

  match !out_to with
    | StdOut ->
      gen_one_file (Format.formatter_of_out_channel stdout) l
    | File f ->
      with_outfile f (fun fmt ->
          gen_one_file fmt l
        )

let produce_output fl = produce_document fl

(*s \textbf{Main program.} Print the banner, parse the command line,
    read the files and then call [produce_document] from module [Web]. *)

let _ =
  let files = parse () in
    if files <> [] then produce_output files
