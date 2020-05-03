; Cours 04 : Les boîtes avec macro simplificatrice

#lang plait

;;;;;;;;;
; Macro ;
;;;;;;;;;

(define-syntax-rule (with [(v-id sto-id) call] body)
  (type-case Result call
    [(v*s v-id sto-id) body]))

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [boxE (val : Exp)]
  [unboxE (b : Exp)]
  [setboxE (b : Exp) (val : Exp)]
  [beginE (list : (Listof Exp))]
  [recordE (fields : (Listof Symbol)) (args : (Listof Exp))]
  [getE (record : Exp) (field : Symbol)]
  [setE (record : Exp) (field : Symbol) (val : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [boxV (l : Location)]
  [recV (fields : (Listof Symbol)) (vals : (Listof Value))]
  [nullV];une value vide.
  )

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

; Manipulation de la mémoire
(define-type-alias Store (Listof Storage))
(define mt-store empty)

(define (override-store [c : Storage] [sto : Store]) : Store
  (cond
    [(empty? sto) (cons c mt-store)]
    [(equal? (cell-location c) (cell-location (first sto))) (cons c (rest sto))]
    [else (cons (first sto) (override-store c (rest sto)))])
  )

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [(s-exp-match? `{box ANY} s)
     (let ([sl (s-exp->list s)])
       (boxE (parse (second sl))))]
    [(s-exp-match? `{unbox ANY} s)
     (let ([sl (s-exp->list s)])
       (unboxE (parse (second sl))))]
    [(s-exp-match? `{set-box! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (setboxE (parse (second sl)) (parse (third sl))))]

    ;;Modif ici.
    [(s-exp-match? `{begin ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (beginE (map parse (rest sl))))]

    ;ici
    [(s-exp-match? `{record {SYMBOL ANY} ...} s)
     (let ([sl (s-exp->list s)])
       (recordE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) (rest sl))
                (map (lambda (l) (parse (second (s-exp->list l)))) (rest sl))))]

    [(s-exp-match? `{get ANY SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (getE (parse (second sl)) (s-exp->symbol (third sl))))]

    [(s-exp-match? `{set! ANY SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (parse (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl))))]
    
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store]) : Result
  (type-case Exp e
    [(numE n) (v*s (numV n) sto)]
    [(idE s) (v*s (lookup s env) sto)]
    [(plusE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num+ v-l v-r) sto-r)))]
    [(multE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num* v-l v-r) sto-r)))]
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (with [(v-f sto-f) (interp f env sto)]
           (type-case Value v-f
             [(closV par body c-env)
              (with [(v-arg sto-arg) (interp arg env sto-f)]
                    (interp body (extend-env (bind par v-arg) c-env) sto-arg))]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (interp body (extend-env (bind s v-rhs) env) sto-rhs))]
    [(boxE val)
     (with [(v-val sto-val) (interp val env sto)]
           (let ([l (new-loc sto-val)])
             (v*s (boxV l) (override-store (cell l v-val) sto-val))))]
    [(unboxE b)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l) (v*s (fetch l sto-b) sto-b)]
             [else (error 'interp "not a box")]))]
    [(setboxE b val)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l)
              (with [(v-val sto-val) (interp val env sto-b)]
                    (v*s v-val (override-store (cell l v-val) sto-val)))]
             [else (error 'interp "not a box")]))]
    [(beginE list)
     (interpBegin list env sto (v*s (nullV) mt-store))];Voir plus haut, null value ne vaut rien.
    ;La valeur initiale de res importe peu elle sera remplacer car begin à forcement une Exp...

    ;Modif ici
    [(recordE fds args);On renvoie maintenant une boite qui a une adresse pointant sur un recV
     (with [(v-val sto-val) (interpRecord fds args env sto (v*s (recV empty empty) sto))]
           (let ([l (new-loc sto-val)])
             (v*s (boxV l) (override-store (cell l v-val) sto-val))))]

    [(getE recordBox fd);recordBox est une boite..
     (with [(v-b sto-b) (interp recordBox env sto)]
           (type-case Value v-b
             [(boxV l)
              (with [(v-r sto-r) (v*s (fetch l sto-b) sto-b)];On recupere ce qui se trouve a l'adresse..
                    (type-case Value v-r
                      [(recV fds vals)
                       (v*s (find fd fds vals) sto-r)]
                      [else (error 'interp "not a record")]))]
             [else (error 'interp "not a record")];On renvoie l'erreur de not a record (meme si on devrait mettre not a box)
             ))]

    [(setE recordBox fd val);recordBox est une boite..
     (with [(v-b sto-b) (interp recordBox env sto)]
           (type-case Value v-b
             [(boxV l)
              (with [(v-r sto-r) (v*s (fetch l sto-b) sto-b)];On recupere ce qui se trouve a l'adresse..
                    (type-case Value v-r
                      [(recV fds vals);Il s'agit bien d'un record
                       (with [(v-val sto-val) (interp val env sto-r)];on interp la nouvelle valeur
                             (let ([r (recV fds (update fd v-val fds vals))])
                               (v*s;on prepare le renvoie de la valeur.
                                r;on la rattache au record.
                                (override-store (cell l r) sto-val))))];Avec la memoire modifiée
                      [else (error 'interp "not a record")]))]
             [else (error 'interp "not a record")];On renvoie l'erreur de not a record (meme si on devrait mettre not a box)
             ))]
    ))


; pour ce tp :
(define (interpBegin [list : (Listof Exp)] [env : Env] [sto : Store] [res : Result]): Result
  (cond
    [(empty? list) res]
    [else
     (with [(v-beg sto-beg) (interp (first list) env sto)]
           (interpBegin (rest list) env sto-beg (v*s v-beg sto-beg)))]))

;record
(define (interpRecord [fds : (Listof Symbol)] [args : (Listof Exp)] [env : Env] [sto : Store] [acc : Result]) : Result
  (cond
    [(empty? args) acc]
    [else
     (with [(val-rec sto-rec) (interp (first args) env sto)]
           (interpRecord (rest fds) (rest args) env sto-rec
                         (v*s (recV (cons (first fds) (recV-fields (v*s-v acc)))
                                    (cons val-rec (recV-vals (v*s-v acc))))
                              sto-rec)
                         ))]))


(define (find [fd : Symbol] [fds : (Listof Symbol)] [vs : (Listof Value)]) : Value
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (first vs)]
    [else (find fd (rest fds) (rest vs))]))

(define (update [fd : Symbol] [new-val : Value]
                [fds : (Listof Symbol)] [vs : (Listof Value)]) : (Listof Value)
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (cons new-val (rest vs))]
    [else (cons (first vs) (update fd new-val (rest fds) (rest vs)))]))

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))]
    [else (lookup n (rest env))]))

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))

;(test (interp (parse `{set-box!{box 2}3}) mt-env  mt-store)
;     (v*s (numV 3) (list (cell 1 (numV 3)) (cell 1 (numV 2)))))


(test (interp (parse `{set-box!{box 2}3}) mt-env  mt-store)
      (v*s (numV 3) (list (cell 1 (numV 3)))))

(test (interp (parse `{begin
                        {box 2}
                        {set-box! {box 5} 6}}) mt-env  mt-store)
      (v*s (numV 6) (list (cell 1 (numV 2)) (cell 2 (numV 6)))))

(test (interp-expr `{begin
                      {box 2}
                      {set-box! {box 5} 6}})
      (numV 6))

;(interp (parse `{let {[b {box 0}]}
;                  {record {x {set-box! b 1}}
;                          {y {unbox b}}}})
;        mt-env
;        mt-store)


(test (interp-expr `{let{[b{box 0}]}
                      {begin
                        {set-box! b{+ 1{unbox b}}}
                        {set-box! b{* 2{unbox b}}}
                        {set-box! b{+ 3{unbox b}}}}})
      (numV 5))

(test (interp-expr `{ let {[a { box 1}]}
                       { let {[r { record {a { set-box! a {* 2 { unbox a} } } }
                                          {b { set-box! a {* 2 { unbox a} } } } }]}
                          {+ { unbox a} {+ { get r a} { get r b} } } } })
      (numV 10))

(test/exn (interp-expr `{get 5 a})
          "not a record")

(test/exn (interp-expr `{ let {[a { box 1}]}
                           { let {[r { record {a { set-box! a {* 2 { unbox a} } } }
                                              {b { set-box! a {* 2 { unbox a} } } } }]}
                              {+ { unbox a} {+ { get r c} { get r b} } } } })
          "no such field")

(test/exn (interp-expr `{let {[a {box 1}]}
                          {let {[r {record {a {set-box! a {* 2 {unbox a}}}}
                                           {b {set-box! a {* 2 {unbox a}}}}}]}
                            {+ {unbox a} r}}})
          "not a number")


( test ( interp-expr `{ let {[r { record {a 1} }]}
                         { begin { set! r a 2} { get r a} } })
       ( numV 2))
( test ( interp-expr `{ let {[r { record {a 1} {b 2} }]}
                         { begin
                            { set! r a {+ { get r b} 3} }
                            { set! r b {* { get r a} 4} }
                            {+ { get r a} { get r b} } } })
       ( numV 25))
