(*
 * Università di Pisa - Corso di Programmazione II (273AA)
 * Progetto Ocaml - Sessione estiva-autunnale A.A. 2018/2019 (settembre 2019)
 * Candidato Alessandro Antonelli (matricola 507264, corso A)
 *)

(* DEFINIZIONI *)

let mioAmbiente = emptyenv Unbound;;

let expBase = FunCall (Fun ("y", Sum (Den "y", Eint 1)), Eint 3);;

let expLet = FunCall (Let ("x", Eint 2, Fun ("y", Sum (Den "y", Den "x"))), Eint 3);;

let funzioneFattoriale = Fun( "n", Ifthenelse
	( IsZero (Den "n"), Eint 1,
	Prod (Den "n", FunCall (Den "fattoriale", Diff (Den "n", Eint 1))) ) );;
	
let invocazioneFattoriale = Letrec ("fattoriale", funzioneFattoriale, FunCall (Den "fattoriale", Eint 5));;

let expAlberoUnivoco = 
	ETree(Node(
		"a",
		Eint 1,
		Node("b", Eint 2, Empty, Empty),
		Node("c", Eint 1, Empty, Empty)));;

let expAlberoNonUnivoco =
	ETree(Node(
		"a",
		Eint 1,
		Node("b", Eint 2, Empty, Empty),
		Node("a", Eint 1, Empty, Empty)));;
		
let expAlberoGigante = 
	ETree(Node(
		"a",
		Eint 1,
		Node("b", Eint 2, 
			Node("c", Eint 3,
				Node("d", Eint 4, Empty, Empty),
				Node("e", Eint 5, Empty, Empty)),
			Node("f", Eint 6,
				Node("g", Eint 7, Empty, Empty),
				Node("h", Eint 8, Empty, Empty))),
		Node("i", Eint 9,
			Node("j", Eint 10, Empty, Empty), 
			Node("k", Eint 11, Empty, Empty))));;

let expAlberoVuoto = ETree(Empty);;

let expSelectRadice = Select ("a", expAlberoUnivoco);;

let expSelectFiglio = Select ("b", expAlberoUnivoco);;

let expSelectNonEsiste = Select ("z", expAlberoUnivoco);;

let expApplyOver = ApplyOver (["a"; "c"], Fun ("k", Prod (Den "k", Eint 5)), expAlberoUnivoco);;

let expApplyOverRicorsivo = Letrec ("fattoriale", funzioneFattoriale, ApplyOver (["a"], Den "fattoriale", ETree(Node("a", Eint 5, Empty, Empty))));;

let expSelectAlberoGigante = Select("h", expAlberoGigante);;

let expApplyOverDiUnaSelect = ApplyOver ( ["d"; "g"], Fun ("k", Prod (Den "k", Den "k")), Select ("a", expAlberoGigante));;

(* ESECUZIONE DEI TEST *)

match(eval expBase mioAmbiente) with
| Int 4 -> print_string "Test 1 passato\n"
| _ -> failwith("Test 1 fallito!\n");;

match(eval expLet mioAmbiente) with
| Int 5 -> print_string "Test 2 passato\n"
| _ -> failwith("Test 2 fallito!\n");;

match(eval invocazioneFattoriale mioAmbiente) with
| Int 120 -> print_string "Test 3 passato\n"
| _ -> failwith("Test 3 fallito!\n");;

match(eval expAlberoUnivoco mioAmbiente) with
| (EvTree(EvNode("a", Int 1, EvNode("b", Int 2, Empty, Empty), EvNode("c", Int 1, Empty, Empty)))) -> print_string "Test 4 passato\n"
| _ -> failwith("Test 4 fallito!\n");;

try match (eval expAlberoNonUnivoco mioAmbiente) with
	|_ -> failwith("Test 5 fallito!\n")
with Failure _ -> print_string "Test 5 passato\n";;

match(eval expAlberoVuoto mioAmbiente) with
| (EvTree(Empty)) -> print_string "Test 6 passato\n"
| _ -> failwith("Test 6 fallito!\n");;

match(eval expSelectRadice mioAmbiente) with
| (EvTree(EvNode("a", Int 1, EvNode("b", Int 2, Empty, Empty), EvNode("c", Int 1, Empty, Empty)))) -> print_string "Test 7 passato\n"
| _ -> failwith("Test 7 fallito!\n");;

match(eval expSelectFiglio mioAmbiente) with
| (EvTree(EvNode("b", Int 2, Empty, Empty))) -> print_string "Test 8 passato\n"
| _ -> failwith("Test 8 fallito!\n");;

match(eval expSelectNonEsiste mioAmbiente) with
| (EvTree(Empty)) -> print_string "Test 9 passato\n"
| _ -> failwith("Test 9 fallito!\n");;

match(eval expApplyOver mioAmbiente) with
| (EvTree(EvNode("a", Int 5, EvNode("b", Int 2, Empty, Empty), EvNode("c", Int 5, Empty, Empty)))) -> print_string "Test 10 passato\n"
| _ -> failwith("Test 10 fallito!\n");;

match(eval expApplyOverRicorsivo mioAmbiente) with
| (EvTree(EvNode("a", Int 120, Empty, Empty))) -> print_string "Test 11 passato\n"
| _ -> failwith("Test 11 fallito!\n");;

match(eval expAlberoGigante mioAmbiente) with
| (EvTree(EvNode(
		"a",
		Int 1,
		EvNode("b", Int 2, 
			EvNode("c", Int 3,
				EvNode("d", Int 4, Empty, Empty),
				EvNode("e", Int 5, Empty, Empty)),
			EvNode("f", Int 6,
				EvNode("g", Int 7, Empty, Empty),
				EvNode("h", Int 8, Empty, Empty))),
		EvNode("i", Int 9,
			EvNode("j", Int 10, Empty, Empty), 
			EvNode("k", Int 11, Empty, Empty))))) -> print_string "Test 12 passato\n"
| _ -> failwith("Test 12 fallito!\n");;

match(eval expSelectAlberoGigante mioAmbiente) with
| (EvTree(EvNode("h", Int 8, Empty, Empty))) -> print_string "Test 13 passato\n"
| _ -> failwith("Test 13 fallito!\n");;

match(eval expApplyOverDiUnaSelect mioAmbiente) with
| (EvTree(EvNode(
		"a",
		Int 1,
		EvNode("b", Int 2, 
			EvNode("c", Int 3,
				EvNode("d", Int 16, Empty, Empty),
				EvNode("e", Int 5, Empty, Empty)),
			EvNode("f", Int 6,
				EvNode("g", Int 49, Empty, Empty),
				EvNode("h", Int 8, Empty, Empty))),
		EvNode("i", Int 9,
			EvNode("j", Int 10, Empty, Empty), 
			EvNode("k", Int 11, Empty, Empty))))) -> print_string "Test 14 passato\n"
| _ -> failwith("Test 14 fallito!\n");;

print_string "*** Tutti i test sono stati superati! ***\n";;
