.DEFAULT_GOAL := generate

generate:
	ocamllex lexer.mll
	menhir parser.mly
	ocamlc -c ast.mli
	ocamlc -c parser.mli
	ocamlc -c parser.ml
	ocamlc -c lexer.ml
	ocamlc -c Pretty.ml

	ocamlc -c -o Rewriting.cmo  BackEnd/Rewriting.ml

	ocamlc -c -o Forward.cmo  FrontEnd/Forward.ml

	ocamlc -c -o sleek.cmo  BackEnd/sleek.ml

	ocamlc -c -o LTL_Traslator.cmo  LTL_Traslator.ml

	ocamlc -o _build/hip parser.cmo  lexer.cmo Pretty.cmo Rewriting.cmo Forward.cmo

	ocamlc -o _build/sleek parser.cmo lexer.cmo Pretty.cmo Rewriting.cmo sleek.cmo

	ocamlc -o _build/ltl parser.cmo  lexer.cmo Pretty.cmo LTL_Traslator.cmo


clean:
	rm *.cmi
	rm *.cmo

	rm lexer.ml
	rm parser.ml
	rm parser.mli
	rm hip
	rm 
