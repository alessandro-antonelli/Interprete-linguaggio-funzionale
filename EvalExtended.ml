(*
 * Università di Pisa - Corso di Programmazione II (273AA)
 * Progetto Ocaml - Sessione estiva-autunnale A.A. 2018/2019 (settembre 2019)
 * Candidato Alessandro Antonelli (matricola 507264, corso A)
 *)
 
type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp |
	ETree of tree | ApplyOver of (ide list) * exp * exp | Select of ide * exp
and tree = Empty | Node of ide * exp * tree * tree;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | EvTree of evTree
and evFun = ide * exp * evT env
and evTree = Empty | EvNode of ide * evT * evTree * evTree

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"tree" -> (match v with
		EvTree (_) -> true |
		_ -> false ) |
	"funzione" -> (match v with
		FunVal _ -> true |
		RecFunVal _ -> true|
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;
		
(*------------------------------------------------------------------------------*)
(* Funzioni ausiliarie *)

(* Restituisce il primo elemento di una coppia *)
let takeFirst (x, y) = x;;
	
(* Indica se la lista contiene o meno un certo tag *)
let rec contains (tagCercato : ide) (lista : ide list) : bool = (match lista with
	e :: tl when e <> tagCercato -> contains tagCercato tl |
	e :: tl when e = tagCercato -> true |
	[] -> false);;
	
(* Funzione che controlla se un albero contiene tag duplicati.
 La chiamata eseguita su un certo sottoalbero restituisce una coppia che indica rispettivamente:
 - se nel sottoalbero tutti i tag sono univoci oppure no;
 - la lista dei tag di tutti i nodi visitati nel sottoalbero. *)
let rec tagSonoUnivociCore (albero : tree) : (bool * ide list) =
	(match albero with
		Node(tag, _, lTree, rTree) ->
			(match (tagSonoUnivociCore lTree, tagSonoUnivociCore rTree) with
				((univociSX, visitaSX), (univociDX, visitaDX)) ->
					if(univociSX && univociDX && not(contains tag (visitaSX @ visitaDX)))
					then (true, tag :: (visitaSX @ visitaDX)) (* Finora tutti i tag sono univoci *)
					else (false, tag :: (visitaSX @ visitaDX))) | (* Trovato duplicato, nel nodo o nei sottoalberi *)
		Empty -> (true, []) );; (* Caso base (foglia): restituisco che i tag sono univoci, e lista tag visitati vuota *)
	
let tagSonoUnivoci (albero : tree) : bool = takeFirst (tagSonoUnivociCore albero);;
		
(*------------------------------------------------------------------------------*)
	
(* Implementazione della primitiva Select come visita dell'albero. Viene invocata dalla eval. *)
let rec select (tagCercato : ide) (albero : evT) : evT = (match albero with
	(* Il nodo corrente NON È quello cercato: continuo la ricerca ricorsivamente nei sottoalberi *)
	EvTree(EvNode(tag, _, lTree, rTree)) when (tag <> tagCercato) -> (let risultatoSX = (select tagCercato (EvTree lTree)) in
		(if(risultatoSX <> EvTree(Empty)) then risultatoSX
		else (select tagCercato (EvTree rTree)))) |
	(* Il nodo corrente È quello cercato: fine ricerca *)
	EvTree(EvNode(tag, _, _, _)) when (tag = tagCercato) -> albero |
	(* Caso base (sono arrivato in fondo): restituisco l'albero vuoto *)
	EvTree(Empty) -> EvTree(Empty));;

(*------------------------------------------------------------------------------*)

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
	Letrec(f, funDef, letBody) ->
			(match funDef with
	    		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
	                 			                eval letBody r1 |
	    		_ -> failwith("non functional def")) |
		    		
	(*---------------------------*)
	ETree t -> (if(tagSonoUnivoci t) (* Controllo l'univocità dei tag *)
		then (match t with
			Node(tag, exp, lTree, rTree) -> (let expValutata = (eval exp r) in (* Valuto l'espressione contenuta nel nodo *)
				(match ((eval (ETree lTree) r), (eval (ETree rTree) r)) with (* Valuto ricorsivamente i sottoalberi *)
					((EvTree lTreeValutato), (EvTree rTreeValutato)) -> EvTree(EvNode(tag, expValutata, lTreeValutato, rTreeValutato))) ) |
			Empty -> EvTree(Empty))
		else failwith ("Albero non valido: i tag non sono univoci")) |
	(*---------------------------*)
	ApplyOver(lista, expFunzione, expAlbero) -> ( let evtFunzione = (eval expFunzione r) in (* Valuto la funzione/chiusura *)
		(if (typecheck "funzione" evtFunzione)
		then (let evtAlbero = (eval expAlbero r) in (* Valuto l'albero *)
			(if(typecheck "tree" evtAlbero)
			then EvTree(applyOver lista evtFunzione evtAlbero) (* posso procedere con l'invocazione del metodo ausiliario *)
			else failwith("Errore di tipo: l'espressione deve essere un albero")))
		else failwith("Errore di tipo: l'espressione deve essere una funzione o una funzione ricorsiva") )) |
	(*---------------------------*)
	Select(tag, expAlbero) -> let evtAlbero = (eval expAlbero r) in (* Valuto l'albero *)
		(if (typecheck "tree" evtAlbero)
			then (select tag evtAlbero) (* ok, chiamo metodo ausiliario *)
			else failwith("Errore di tipo: l'espressione deve essere un albero") ) (* il secondo argomento non è un albero *)
	(*---------------------------*)
	
(* Implementazione della primitiva ApplyOver. Viene invocata dalla eval.
Prende l'albero e la lista, e restituisce un nuovo albero con contenuto dei nodi opportunamente aggiornato. *)
and applyOver (lista : ide list) (funzione : evT) (albero : evT) : evTree = match albero with
	EvTree(EvNode(tag, valore, lTree, rTree)) -> (if(contains tag lista)
		(* Il tag È nella lista: applico la funzione e restituisco il nodo col valore modificato, e proseguo ricorsivamente nei sottoalberi *)
		then (match funzione with
			(* La funzione non è ricorsiva: costruisco l'invocazione e la valuto *)
			(FunVal (paramFormaleFun, corpoFunz, ambienteDichiarazioneFun)) ->
				(let valoreModificato = (eval corpoFunz (bind ambienteDichiarazioneFun paramFormaleFun valore))
				(* Costruisco e restituisco il nodo aggiornato *)
				in EvNode(tag, valoreModificato, (applyOver lista funzione (EvTree lTree)), (applyOver lista funzione (EvTree rTree)) ) ) |
			(* La funzione è ricorsiva: costruisco l'invocazione e la valuto *)
			(RecFunVal (ident, (paramFormaleFun, corpoFunz, ambienteDichiarazioneFun))) -> 
				(let rEnv = (bind ambienteDichiarazioneFun ident funzione) in
					( let aEnv = (bind rEnv paramFormaleFun valore) in
						(let valoreModificato = (eval corpoFunz aEnv)
							(* Costruisco e restituisco il nodo aggiornato *)
							in EvNode(tag, valoreModificato,
							(applyOver lista funzione (EvTree lTree)),
							(applyOver lista funzione (EvTree rTree)))
			))))
		(* Il tag NON È nella lista: restituisco il nodo senza modificare il valore, e proseguo ricorsivamente nei sottoalberi *)
		else EvNode(tag, valore, (applyOver lista funzione (EvTree lTree)), (applyOver lista funzione (EvTree rTree)) )) |
	EvTree(Empty) -> Empty;;
